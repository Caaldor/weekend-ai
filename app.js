const axios = require("axios");
const cheerio = require("cheerio");
const fs = require("fs");
const path = require("path");
const crypto = require("crypto");
const puppeteer = require("puppeteer");
const pdfParse = require("pdf-parse");

// --------------------------------------------------
// CONFIG
// --------------------------------------------------

const MODE = (process.argv[2] || "weekend").toLowerCase(); // today | weekend | next7days | upcoming
const MAX_RADIUS_KM = 30;
const MAX_FUTURE_DAYS = 60;
const REQUIRE_DETECTED_DATE = true;

const userLocation = {
  lat: 48.6333,
  lon: 2.8000 // Guignes
};

const ROOT_DIR = __dirname;
const TOWNS_FILE = path.join(ROOT_DIR, "towns.json");
const EVENTS_JSON_FILE = path.join(ROOT_DIR, "events.json");
const REPORT_HTML_FILE = path.join(ROOT_DIR, "index.html");

const CACHE_DIR = path.join(ROOT_DIR, ".cache");
const HTML_CACHE_DIR = path.join(CACHE_DIR, "html");
const PDF_CACHE_DIR = path.join(CACHE_DIR, "pdf");
const FAIL_CACHE_DIR = path.join(CACHE_DIR, "fail");

const HTML_CACHE_TTL_MS = 24 * 60 * 60 * 1000;
const PDF_CACHE_TTL_MS = 24 * 60 * 60 * 1000;
const FAIL_CACHE_TTL_MS = 6 * 60 * 60 * 1000;

let browserInstance = null;

// --------------------------------------------------
// CACHE
// --------------------------------------------------

function ensureDir(dir) {
  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir, { recursive: true });
  }
}

function initCache() {
  ensureDir(CACHE_DIR);
  ensureDir(HTML_CACHE_DIR);
  ensureDir(PDF_CACHE_DIR);
  ensureDir(FAIL_CACHE_DIR);
}

function hashUrl(url) {
  return crypto.createHash("sha1").update(url).digest("hex");
}

function getCachePath(type, url) {
  const hash = hashUrl(url);

  if (type === "html") return path.join(HTML_CACHE_DIR, `${hash}.json`);
  if (type === "pdf") return path.join(PDF_CACHE_DIR, `${hash}.json`);
  if (type === "fail") return path.join(FAIL_CACHE_DIR, `${hash}.json`);

  return null;
}

function readJsonIfExists(filePath) {
  try {
    if (!fs.existsSync(filePath)) return null;
    return JSON.parse(fs.readFileSync(filePath, "utf-8"));
  } catch {
    return null;
  }
}

function writeJson(filePath, data) {
  fs.writeFileSync(filePath, JSON.stringify(data, null, 2), "utf-8");
}

function getCachedHtml(url) {
  const data = readJsonIfExists(getCachePath("html", url));
  if (!data) return null;
  if (Date.now() - data.savedAt > HTML_CACHE_TTL_MS) return null;
  return data.html || null;
}

function setCachedHtml(url, html) {
  writeJson(getCachePath("html", url), {
    url,
    savedAt: Date.now(),
    html
  });
}

function getCachedPdfText(url) {
  const data = readJsonIfExists(getCachePath("pdf", url));
  if (!data) return null;
  if (Date.now() - data.savedAt > PDF_CACHE_TTL_MS) return null;
  return data.text || null;
}

function setCachedPdfText(url, text) {
  writeJson(getCachePath("pdf", url), {
    url,
    savedAt: Date.now(),
    text
  });
}

function isRecentlyFailed(url) {
  const data = readJsonIfExists(getCachePath("fail", url));
  if (!data) return false;
  return Date.now() - data.savedAt <= FAIL_CACHE_TTL_MS;
}

function markFailed(url, reason = "unknown") {
  writeJson(getCachePath("fail", url), {
    url,
    savedAt: Date.now(),
    reason
  });
}

// --------------------------------------------------
// DATE HELPERS
// --------------------------------------------------

function startOfDay(date) {
  const d = new Date(date);
  d.setHours(0, 0, 0, 0);
  return d;
}

function endOfDay(date) {
  const d = new Date(date);
  d.setHours(23, 59, 59, 999);
  return d;
}

function addDays(date, nbDays) {
  const d = new Date(date);
  d.setDate(d.getDate() + nbDays);
  return d;
}

function areSameDay(a, b) {
  return startOfDay(a).getTime() === startOfDay(b).getTime();
}

function uniqueDates(items) {
  const result = [];

  for (const item of items) {
    if (!result.some(x => areSameDay(x.parsed, item.parsed) && x.raw === item.raw)) {
      result.push(item);
    }
  }

  return result;
}

function isPastEvent(parsedDate) {
  if (!parsedDate) return false;
  return startOfDay(parsedDate) < startOfDay(new Date());
}

function isTooFarInFuture(parsedDate) {
  if (!parsedDate) return false;
  const today = startOfDay(new Date());
  const limit = addDays(today, MAX_FUTURE_DAYS);
  return startOfDay(parsedDate) > startOfDay(limit);
}

function getWeekendWindow() {
  const today = startOfDay(new Date());
  const day = today.getDay(); // 0 dimanche, 6 samedi

  let saturday;
  let sunday;

  if (day === 6) {
    saturday = today;
    sunday = addDays(today, 1);
  } else if (day === 0) {
    saturday = addDays(today, -1);
    sunday = today;
  } else {
    const daysUntilSaturday = (6 - day + 7) % 7;
    saturday = addDays(today, daysUntilSaturday);
    sunday = addDays(saturday, 1);
  }

  return {
    start: startOfDay(saturday),
    end: endOfDay(sunday)
  };
}

function isDateInMode(parsedDate, mode) {
  if (!parsedDate) return false;

  const eventDay = startOfDay(parsedDate);
  const today = startOfDay(new Date());

  switch (mode) {
    case "today":
      return eventDay.getTime() === today.getTime();

    case "next7days": {
      const limit = endOfDay(addDays(today, 7));
      return eventDay >= today && eventDay <= limit;
    }

    case "weekend": {
      const weekend = getWeekendWindow();
      return eventDay >= weekend.start && eventDay <= weekend.end;
    }

    case "upcoming":
    default:
      return eventDay >= today;
  }
}

function formatModeLabel(mode) {
  switch (mode) {
    case "today":
      return "Aujourd'hui";
    case "next7days":
      return "Prochains 7 jours";
    case "weekend":
      return "Week-end";
    case "upcoming":
    default:
      return "À venir";
  }
}

function formatReadableDate(date) {
  const jours = ["Dimanche", "Lundi", "Mardi", "Mercredi", "Jeudi", "Vendredi", "Samedi"];
  const mois = [
    "janvier", "février", "mars", "avril", "mai", "juin",
    "juillet", "août", "septembre", "octobre", "novembre", "décembre"
  ];

  return `${jours[date.getDay()]} ${date.getDate()} ${mois[date.getMonth()]}`;
}

function formatIsoDate(date) {
  return startOfDay(date).toISOString().slice(0, 10);
}

function getFrenchMonthIndex(monthName) {
  const months = {
    janvier: 0,
    février: 1,
    fevrier: 1,
    mars: 2,
    avril: 3,
    mai: 4,
    juin: 5,
    juillet: 6,
    août: 7,
    aout: 7,
    septembre: 8,
    octobre: 9,
    novembre: 10,
    décembre: 11,
    decembre: 11
  };

  return months[monthName.toLowerCase()];
}

function weekdayNameToIndex(weekday) {
  const days = {
    dimanche: 0,
    lundi: 1,
    mardi: 2,
    mercredi: 3,
    jeudi: 4,
    vendredi: 5,
    samedi: 6
  };

  return days[weekday.toLowerCase()];
}

function parseFrenchWeekdayToNextDate(weekday) {
  const targetDay = weekdayNameToIndex(weekday);
  if (targetDay === undefined) return null;

  const today = startOfDay(new Date());
  const currentDay = today.getDay();

  let diff = targetDay - currentDay;
  if (diff < 0) diff += 7;

  return addDays(today, diff);
}

function parseDateParts(day, month, year) {
  const d = parseInt(day, 10);
  const m = parseInt(month, 10);
  let y = parseInt(year, 10);

  if (y < 100) y += 2000;

  return new Date(y, m - 1, d);
}

function buildDateWithPossibleNextYear(day, monthIndex) {
  const today = startOfDay(new Date());
  let date = new Date(today.getFullYear(), monthIndex, day);

  if (date < today) {
    date = new Date(today.getFullYear() + 1, monthIndex, day);
  }

  return date;
}

function extractPublicationDate(text) {
  const lower = text.toLowerCase();

  let match = lower.match(/publié le\s+(?:lundi|mardi|mercredi|jeudi|vendredi|samedi|dimanche)?\s*(\d{1,2})\s+(janvier|février|fevrier|mars|avril|mai|juin|juillet|août|aout|septembre|octobre|novembre|décembre|decembre)\s+(\d{4})/i);
  if (match) {
    const day = parseInt(match[1], 10);
    const month = getFrenchMonthIndex(match[2]);
    const year = parseInt(match[3], 10);
    return new Date(year, month, day);
  }

  match = lower.match(/publié le\s+(\d{1,2})\/(\d{1,2})\/(\d{2,4})/i);
  if (match) {
    return parseDateParts(match[1], match[2], match[3]);
  }

  return null;
}

function removePublicationMentions(text) {
  return text
    .replace(/publié le\s+(?:lundi|mardi|mercredi|jeudi|vendredi|samedi|dimanche)?\s*\d{1,2}\s+(janvier|février|fevrier|mars|avril|mai|juin|juillet|août|aout|septembre|octobre|novembre|décembre|decembre)\s+\d{4}/gi, "")
    .replace(/publié le\s+\d{1,2}\/\d{1,2}\/\d{2,4}/gi, "")
    .trim();
}

function extractDateCandidates(text) {
  const cleanedText = removePublicationMentions(text);
  const lower = cleanedText.toLowerCase();
  const found = [];

  // 12/06/2026
  let match = lower.match(/\b(\d{1,2})\/(\d{1,2})\/(\d{2,4})\b/);
  if (match) {
    found.push({
      raw: match[0],
      parsed: parseDateParts(match[1], match[2], match[3])
    });
  }

  // 12-06-2026
  match = lower.match(/\b(\d{1,2})-(\d{1,2})-(\d{2,4})\b/);
  if (match) {
    found.push({
      raw: match[0],
      parsed: parseDateParts(match[1], match[2], match[3])
    });
  }

  // 12 juin 2026
  match = lower.match(/\b(\d{1,2})\s+(janvier|février|fevrier|mars|avril|mai|juin|juillet|août|aout|septembre|octobre|novembre|décembre|decembre)\s+(\d{4})\b/i);
  if (match) {
    const day = parseInt(match[1], 10);
    const month = getFrenchMonthIndex(match[2]);
    const year = parseInt(match[3], 10);

    found.push({
      raw: match[0],
      parsed: new Date(year, month, day)
    });
  }

  // 12 juin
  match = lower.match(/\b(\d{1,2})\s+(janvier|février|fevrier|mars|avril|mai|juin|juillet|août|aout|septembre|octobre|novembre|décembre|decembre)\b/i);
  if (match) {
    const day = parseInt(match[1], 10);
    const month = getFrenchMonthIndex(match[2]);

    found.push({
      raw: match[0],
      parsed: buildDateWithPossibleNextYear(day, month)
    });
  }

  // 30 et 31 mai
  match = lower.match(/\b(\d{1,2})\s+et\s+(\d{1,2})\s+(janvier|février|fevrier|mars|avril|mai|juin|juillet|août|aout|septembre|octobre|novembre|décembre|decembre)(?:\s+(\d{4}))?\b/i);
  if (match) {
    const day1 = parseInt(match[1], 10);
    const day2 = parseInt(match[2], 10);
    const month = getFrenchMonthIndex(match[3]);
    const explicitYear = match[4] ? parseInt(match[4], 10) : null;
    const year = explicitYear || startOfDay(new Date()).getFullYear();

    let d1 = new Date(year, month, day1);
    let d2 = new Date(year, month, day2);

    if (!explicitYear) {
      const today = startOfDay(new Date());
      if (d1 < today && d2 < today) {
        d1 = new Date(year + 1, month, day1);
        d2 = new Date(year + 1, month, day2);
      }
    }

    found.push({ raw: `${day1} ${match[3]}`, parsed: d1 });
    found.push({ raw: `${day2} ${match[3]}`, parsed: d2 });
  }

  // 30-31 mai
  match = lower.match(/\b(\d{1,2})\s*-\s*(\d{1,2})\s+(janvier|février|fevrier|mars|avril|mai|juin|juillet|août|aout|septembre|octobre|novembre|décembre|decembre)(?:\s+(\d{4}))?\b/i);
  if (match) {
    const day1 = parseInt(match[1], 10);
    const day2 = parseInt(match[2], 10);
    const month = getFrenchMonthIndex(match[3]);
    const explicitYear = match[4] ? parseInt(match[4], 10) : null;
    const year = explicitYear || startOfDay(new Date()).getFullYear();

    let d1 = new Date(year, month, day1);
    let d2 = new Date(year, month, day2);

    if (!explicitYear) {
      const today = startOfDay(new Date());
      if (d1 < today && d2 < today) {
        d1 = new Date(year + 1, month, day1);
        d2 = new Date(year + 1, month, day2);
      }
    }

    found.push({ raw: `${day1} ${match[3]}`, parsed: d1 });
    found.push({ raw: `${day2} ${match[3]}`, parsed: d2 });
  }

  // du 30 au 31 mai
  match = lower.match(/\bdu\s+(\d{1,2})\s+au\s+(\d{1,2})\s+(janvier|février|fevrier|mars|avril|mai|juin|juillet|août|aout|septembre|octobre|novembre|décembre|decembre)(?:\s+(\d{4}))?\b/i);
  if (match) {
    const day1 = parseInt(match[1], 10);
    const day2 = parseInt(match[2], 10);
    const month = getFrenchMonthIndex(match[3]);
    const explicitYear = match[4] ? parseInt(match[4], 10) : null;
    const year = explicitYear || startOfDay(new Date()).getFullYear();

    let d1 = new Date(year, month, day1);
    let d2 = new Date(year, month, day2);

    if (!explicitYear) {
      const today = startOfDay(new Date());
      if (d1 < today && d2 < today) {
        d1 = new Date(year + 1, month, day1);
        d2 = new Date(year + 1, month, day2);
      }
    }

    found.push({ raw: `${day1} ${match[3]}`, parsed: d1 });
    found.push({ raw: `${day2} ${match[3]}`, parsed: d2 });
  }

  // aujourd'hui / demain / week-end
  if (lower.includes("aujourd'hui") || lower.includes("aujourdhui")) {
    found.push({
      raw: "aujourd'hui",
      parsed: startOfDay(new Date())
    });
  }

  if (lower.includes("demain")) {
    found.push({
      raw: "demain",
      parsed: addDays(startOfDay(new Date()), 1)
    });
  }

  if (lower.includes("ce week-end") || lower.includes("ce weekend")) {
    const weekend = getWeekendWindow();
    found.push({ raw: "samedi", parsed: weekend.start });
    found.push({ raw: "dimanche", parsed: addDays(weekend.start, 1) });
  }

  if (lower.includes("samedi et dimanche") || lower.includes("samedi & dimanche")) {
    const saturday = parseFrenchWeekdayToNextDate("samedi");
    const sunday = parseFrenchWeekdayToNextDate("dimanche");

    if (saturday) found.push({ raw: "samedi", parsed: saturday });
    if (sunday) found.push({ raw: "dimanche", parsed: sunday });
  }

  // jours de semaine isolés
  const weekdayMatches = [...lower.matchAll(/\b(lundi|mardi|mercredi|jeudi|vendredi|samedi|dimanche)\b/g)];
  for (const item of weekdayMatches) {
    const parsed = parseFrenchWeekdayToNextDate(item[1]);
    if (parsed) {
      found.push({
        raw: item[1],
        parsed
      });
    }
  }

  return uniqueDates(found);
}

// --------------------------------------------------
// GEO / SCORING
// --------------------------------------------------

function getDistanceKm(lat1, lon1, lat2, lon2) {
  const R = 6371;

  const dLat = (lat2 - lat1) * Math.PI / 180;
  const dLon = (lon2 - lon1) * Math.PI / 180;

  const a =
    Math.sin(dLat / 2) * Math.sin(dLat / 2) +
    Math.cos(lat1 * Math.PI / 180) *
    Math.cos(lat2 * Math.PI / 180) *
    Math.sin(dLon / 2) * Math.sin(dLon / 2);

  const c = 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a));
  return R * c;
}

function normalizeWhitespace(text) {
  return text.replace(/\s+/g, " ").trim();
}

function isLocalEvent(event) {
  const keywords = [
    "vide",
    "brocante",
    "fête",
    "balade",
    "marché",
    "festival",
    "salon",
    "visite",
    "sortie",
    "animation",
    "randonnée",
    "atelier",
    "nature",
    "enfant",
    "feu",
    "loisir",
    "plein air",
    "village",
    "kermesse",
    "guinguette",
    "base de loisirs",
    "portes ouvertes",
    "marathon",
    "semi-marathon",
    "course"
  ];

  const text = `${event.title || ""} ${event.description || ""}`.toLowerCase();
  return keywords.some(k => text.includes(k));
}

function scoreBlock(block) {
  let score = 0;
  const lower = block.toLowerCase();

  if (lower.includes("fête")) score += 5;
  if (lower.includes("festival")) score += 5;
  if (lower.includes("marché")) score += 4;
  if (lower.includes("brocante")) score += 4;
  if (lower.includes("vide-grenier")) score += 5;
  if (lower.includes("atelier")) score += 4;
  if (lower.includes("balade")) score += 4;
  if (lower.includes("randonnée")) score += 4;
  if (lower.includes("visite")) score += 3;
  if (lower.includes("animation")) score += 3;
  if (lower.includes("enfant")) score += 3;
  if (lower.includes("famille")) score += 3;
  if (lower.includes("samedi") || lower.includes("dimanche")) score += 3;
  if (lower.includes("juin") || lower.includes("juillet") || lower.includes("août")) score += 2;

  if (block.length > 40 && block.length < 220) score += 2;
  if (/\d{1,2}\/\d{1,2}\/\d{2,4}/.test(block)) score += 3;

  return score;
}

function scoreEvent(event) {
  let score = 0;

  score += Math.max(0, 30 - event.distance);

  if (event.price === 0) score += 10;
  if (event.audience === "family") score += 10;
  if (event.type === "local") score += 15;
  if (isLocalEvent(event)) score += 20;

  if (event.parsedDate) {
    const today = startOfDay(new Date());
    const diffDays = Math.round(
      (startOfDay(event.parsedDate) - today) / (1000 * 60 * 60 * 24)
    );

    if (diffDays >= 0 && diffDays <= 7) score += 8;
    else if (diffDays <= 14) score += 4;
  }

  return score;
}

// --------------------------------------------------
// FETCH HTML / PDF
// --------------------------------------------------

function isPdfUrl(url) {
  return /\.pdf(\?|$)/i.test(url);
}

function shouldSkipUrl(url) {
  if (!url) return true;

  const lower = url.toLowerCase();

  return (
    lower.endsWith(".jpg") ||
    lower.endsWith(".jpeg") ||
    lower.endsWith(".png") ||
    lower.endsWith(".zip") ||
    lower.startsWith("mailto:")
  );
}

async function getBrowser() {
  if (!browserInstance) {
    browserInstance = await puppeteer.launch({ headless: true });
  }
  return browserInstance;
}

async function fetchHtmlWithBrowser(url) {
  try {
    const browser = await getBrowser();
    const page = await browser.newPage();

    await page.setUserAgent(
      "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 " +
      "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"
    );

    await page.goto(url, {
      waitUntil: "networkidle2",
      timeout: 20000
    });

    const html = await page.content();
    await page.close();

    return html;
  } catch {
    return null;
  }
}

async function fetchHtml(url) {
  if (!url || shouldSkipUrl(url) || isPdfUrl(url)) return null;

  const cached = getCachedHtml(url);
  if (cached) return cached;

  if (isRecentlyFailed(url)) return null;

  try {
    const response = await axios.get(url, {
      timeout: 10000,
      maxRedirects: 5,
      validateStatus: status => status < 500,
      headers: {
        "User-Agent":
          "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 " +
          "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36",
        "Accept-Language": "fr-FR,fr;q=0.9,en;q=0.8",
        "Accept": "text/html,application/xhtml+xml",
        "Connection": "keep-alive"
      }
    });

    if (response.status === 404) {
      markFailed(url, "404");
      return null;
    }

    if (typeof response.data === "string" && response.data.length > 100) {
      setCachedHtml(url, response.data);
      return response.data;
    }
  } catch {
    // fallback browser
  }

  const html = await fetchHtmlWithBrowser(url);
  if (html && html.length > 100) {
    setCachedHtml(url, html);
    return html;
  }

  markFailed(url, "html_failed");
  return null;
}

async function fetchPdfText(url) {
  if (!url || shouldSkipUrl(url) || !isPdfUrl(url)) return null;

  const cached = getCachedPdfText(url);
  if (cached) return cached;

  if (isRecentlyFailed(url)) return null;

  try {
    const response = await axios.get(url, {
      timeout: 15000,
      responseType: "arraybuffer",
      maxRedirects: 5,
      validateStatus: status => status < 500,
      headers: {
        "User-Agent":
          "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 " +
          "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"
      }
    });

    if (response.status === 404) {
      markFailed(url, "pdf_404");
      return null;
    }

    const parsed = await pdfParse(response.data);
    const text = parsed.text ? parsed.text.trim() : "";

    if (text.length > 50) {
      setCachedPdfText(url, text);
      return text;
    }
  } catch {
    // ignore
  }

  markFailed(url, "pdf_failed");
  return null;
}

// --------------------------------------------------
// PAGE / CONTEXT / TEXT
// --------------------------------------------------

function classifyPageContext(url) {
  const lower = url.toLowerCase();

  if (/\/actualites\/\d+/.test(lower) || /\/actualites\/[a-z0-9_-]+/.test(lower)) {
    return "news-article";
  }

  if (lower.includes("/actualites")) return "news-list";
  if (lower.includes("/agenda") || lower.includes("/evenements") || lower.includes("/manifestations")) return "agenda";
  if (isPdfUrl(url)) return "pdf";

  return "generic";
}

function cleanText(text) {
  return normalizeWhitespace(
    String(text || "")
      .replace(/cookies?/gi, " ")
      .replace(/politique de confidentialité/gi, " ")
      .replace(/mentions légales/gi, " ")
      .replace(/newsletter/gi, " ")
      .replace(/\baccueil\b/gi, " ")
      .replace(/\bmenu\b/gi, " ")
      .replace(/\bplan du site\b/gi, " ")
      .replace(/\binscription\b/gi, " ")
      .replace(/\bcontact\b/gi, " ")
  );
}

function discoverCandidateLinks(baseUrl, html) {
  const $ = cheerio.load(html);

  const keywords = [
    "agenda",
    "événement",
    "évènements",
    "evenement",
    "evenements",
    "sortir",
    "sorties",
    "actualités",
    "actualites",
    "loisirs",
    "manifestations",
    "culture",
    "animations",
    "fête",
    "fete",
    "programme",
    "pdf"
  ];

  const links = [];

  links.push({
    text: "Accueil",
    url: baseUrl,
    kind: "html",
    context: classifyPageContext(baseUrl)
  });

  const manualCandidates = [
    "/agenda",
    "/evenements",
    "/manifestations",
    "/actualites"
  ];

  for (const guess of manualCandidates) {
    try {
      const url = new URL(guess, baseUrl).toString();
      links.push({
        text: guess,
        url,
        kind: isPdfUrl(url) ? "pdf" : "html",
        context: classifyPageContext(url)
      });
    } catch {
      // ignore
    }
  }

  $("a").each((i, el) => {
    const text = cleanText($(el).text() || "");
    const href = $(el).attr("href");
    if (!href) return;

    try {
      const absoluteUrl = new URL(href, baseUrl).toString();
      const combined = `${text} ${href}`.toLowerCase();

      if (keywords.some(k => combined.includes(k)) || isPdfUrl(absoluteUrl)) {
        links.push({
          text,
          url: absoluteUrl,
          kind: isPdfUrl(absoluteUrl) ? "pdf" : "html",
          context: classifyPageContext(absoluteUrl)
        });
      }
    } catch {
      // ignore
    }
  });

  const unique = [];
  const seen = new Set();

  for (const link of links) {
    if (!seen.has(link.url)) {
      seen.add(link.url);
      unique.push(link);
    }
  }

  return unique.slice(0, 12);
}

function extractStructuredBlocksFromHtml(html) {
  const $ = cheerio.load(html);

  $("script").remove();
  $("style").remove();
  $("noscript").remove();
  $("header").remove();
  $("footer").remove();
  $("nav").remove();

  const blocks = [];
  const selectors = [
    "article",
    ".event",
    ".events",
    ".agenda-item",
    ".card",
    ".content",
    ".news-item",
    ".item",
    "li",
    "p"
  ];

  selectors.forEach(selector => {
    $(selector).each((i, el) => {
      const text = cleanText($(el).text() || "");
      if (text.length >= 30 && text.length <= 600) {
        blocks.push(text);
      }
    });
  });

  if (blocks.length < 10) {
    const bodyText = cleanText($("body").text() || "");
    const rough = bodyText
      .split(/\n{2,}|[\.\!\?]+/)
      .map(t => cleanText(t))
      .filter(t => t.length >= 30 && t.length <= 350);

    blocks.push(...rough);
  }

  const unique = [];
  const seen = new Set();

  for (const block of blocks) {
    if (!block) continue;
    if (seen.has(block)) continue;
    seen.add(block);
    unique.push(block);
  }

  return unique;
}

function extractStructuredBlocksFromPdfText(pdfText) {
  const cleaned = cleanText(pdfText);

  const roughBlocks = cleaned
    .split(/\n{2,}|(?<=\.)\s{2,}/)
    .map(b => cleanText(b))
    .filter(b => b.length >= 30 && b.length <= 600);

  const unique = [];
  const seen = new Set();

  for (const block of roughBlocks) {
    if (!seen.has(block)) {
      seen.add(block);
      unique.push(block);
    }
  }

  return unique;
}

// --------------------------------------------------
// SMART EXTRACTION HELPERS
// --------------------------------------------------

function containsPastOnlySignals(text) {
  const lower = text.toLowerCase();

  return (
    lower.includes("terminé") ||
    lower.includes("résultats") ||
    lower.includes("resultats") ||
    lower.includes("classements") ||
    lower.includes("chrono") ||
    lower.includes("retrouve ta photo") ||
    lower.includes("retour en images") ||
    lower.includes("revivez")
  );
}

function allDatesArePast(dateCandidates) {
  if (!dateCandidates || dateCandidates.length === 0) return false;
  return dateCandidates.every(d => d.parsed && isPastEvent(d.parsed));
}

function getWeekdayLabelFromDate(date) {
  const weekdays = [
    "dimanche",
    "lundi",
    "mardi",
    "mercredi",
    "jeudi",
    "vendredi",
    "samedi"
  ];
  return weekdays[date.getDay()];
}

function extractWeekdaysFromText(text) {
  const matches = [...text.toLowerCase().matchAll(/\b(lundi|mardi|mercredi|jeudi|vendredi|samedi|dimanche)\b/g)];
  return [...new Set(matches.map(m => m[1]))];
}

function splitBlockByDay(block) {
  const normalized = block
    .replace(/\s+/g, " ")
    .replace(/([:;])\s*/g, "$1 ")
    .trim();

  const parts = normalized.split(/(?=\b(?:lundi|mardi|mercredi|jeudi|vendredi|samedi|dimanche)\b)/gi);

  const cleaned = parts
    .map(p => p.trim())
    .filter(p => p.length >= 20);

  return cleaned.length ? cleaned : [normalized];
}

function resolveDatesForSubBlock(subBlock, parentDateCandidates = []) {
  const localDates = extractDateCandidates(subBlock);
  const weekdays = extractWeekdaysFromText(subBlock);

  if (localDates.length > 0 && weekdays.length > 0) {
    const filtered = localDates.filter(d =>
      weekdays.includes(getWeekdayLabelFromDate(d.parsed))
    );
    if (filtered.length > 0) return filtered;
  }

  if (localDates.length > 0 && weekdays.length === 0) {
    return localDates;
  }

  if (localDates.length === 0 && weekdays.length > 0) {
    return weekdays
      .map(day => {
        const parsed = parseFrenchWeekdayToNextDate(day);
        if (!parsed) return null;
        return { raw: day, parsed };
      })
      .filter(Boolean);
  }

  if (parentDateCandidates.length > 0 && weekdays.length > 0) {
    const filteredParent = parentDateCandidates.filter(d =>
      weekdays.includes(getWeekdayLabelFromDate(d.parsed))
    );
    if (filteredParent.length > 0) return filteredParent;
  }

  return parentDateCandidates;
}

function extractCleanTitle(block) {
  let title = removePublicationMentions(block);

  title = title.replace(/\b\d{1,2}\s*(\/|-)\s*\d{1,2}\s*(\/|-)\s*\d{2,4}\b/gi, "");
  title = title.replace(/\b\d{1,2}\s+(janvier|février|fevrier|mars|avril|mai|juin|juillet|août|aout|septembre|octobre|novembre|décembre|decembre)(\s+\d{4})?\b/gi, "");
  title = title.replace(/\b(aujourd'hui|aujourdhui|demain|samedi|dimanche|lundi|mardi|mercredi|jeudi|vendredi|ce week-end|ce weekend)\b/gi, "");
  title = title.replace(/^[\s,:;.\-–—]+/, "");

  if (title.includes(".")) {
    title = title.split(".")[0];
  }

  title = cleanText(title);

  if (!title || title.length < 8) {
    title = cleanText(block).slice(0, 80);
  }

  if (title.length > 90) {
    title = title.slice(0, 90) + "...";
  }

  return title.charAt(0).toUpperCase() + title.slice(1);
}

// --------------------------------------------------
// EVENT EXTRACTION
// --------------------------------------------------

function extractEventsFromBlocks(blocks, sourceUrl, town, sourceKind = "html", pageContext = "generic") {
  const events = [];

  for (const block of blocks) {
    const publicationDate = extractPublicationDate(block);
    const parentDates = extractDateCandidates(block);
    const subBlocks = splitBlockByDay(block);

    for (const subBlock of subBlocks) {
      const sanitizedSubBlock = removePublicationMentions(subBlock);
      const lower = sanitizedSubBlock.toLowerCase();
      const dateCandidates = resolveDatesForSubBlock(sanitizedSubBlock, parentDates);

      if (containsPastOnlySignals(sanitizedSubBlock)) continue;
      if (allDatesArePast(dateCandidates)) continue;

      const eventLike =
        lower.includes("fête") ||
        lower.includes("festival") ||
        lower.includes("marché") ||
        lower.includes("brocante") ||
        lower.includes("vide-grenier") ||
        lower.includes("animation") ||
        lower.includes("balade") ||
        lower.includes("randonnée") ||
        lower.includes("visite") ||
        lower.includes("atelier") ||
        lower.includes("feu d'artifice") ||
        lower.includes("base de loisirs") ||
        lower.includes("sortie") ||
        lower.includes("portes ouvertes") ||
        lower.includes("marathon") ||
        lower.includes("semi-marathon") ||
        lower.includes("course");

      if (!eventLike) continue;
      if (scoreBlock(sanitizedSubBlock) < 5) continue;

      if (
        lower.includes("conseil municipal") ||
        lower.includes("marché public") ||
        lower.includes("recrutement") ||
        lower.includes("urbanisme") ||
        lower.includes("démarches") ||
        lower.includes("appel d'offres")
      ) {
        continue;
      }

      if (
        pageContext === "news-article" &&
        publicationDate &&
        isPastEvent(publicationDate) &&
        dateCandidates.length === 0
      ) {
        continue;
      }

      if (REQUIRE_DETECTED_DATE && dateCandidates.length === 0) {
        continue;
      }

      const cleanTitle = extractCleanTitle(sanitizedSubBlock);

      for (const dateInfo of dateCandidates) {
        const parsedDate = dateInfo.parsed;
        const rawDate = dateInfo.raw;

        if (!parsedDate) continue;
        if (isPastEvent(parsedDate)) continue;
        if (isTooFarInFuture(parsedDate)) continue;
        if (!isDateInMode(parsedDate, MODE)) continue;

        // garde-fou jour de semaine
        if (lower.includes("samedi") && parsedDate.getDay() !== 6) continue;
        if (lower.includes("dimanche") && parsedDate.getDay() !== 0) continue;
        if (lower.includes("lundi") && parsedDate.getDay() !== 1) continue;
        if (lower.includes("mardi") && parsedDate.getDay() !== 2) continue;
        if (lower.includes("mercredi") && parsedDate.getDay() !== 3) continue;
        if (lower.includes("jeudi") && parsedDate.getDay() !== 4) continue;
        if (lower.includes("vendredi") && parsedDate.getDay() !== 5) continue;

        const audience =
          lower.includes("enfant") ||
          lower.includes("famille") ||
          lower.includes("familial")
            ? "family"
            : "unknown";

        events.push({
          title: cleanTitle,
          original: sanitizedSubBlock,
          date: rawDate,
          parsedDate,
          description: sanitizedSubBlock,
          audience,
          type:
            lower.includes("randonnée") ||
            lower.includes("balade") ||
            lower.includes("nature")
              ? "nature"
              : "local",
          price: lower.includes("gratuit") ? 0 : 0,
          sourceKind,
          town: town.name,
          sourceUrl,
          pageContext,
          lat: town.lat,
          lon: town.lon,
          distance: getDistanceKm(
            userLocation.lat,
            userLocation.lon,
            town.lat,
            town.lon
          )
        });
      }
    }
  }

  return events;
}

// --------------------------------------------------
// OUTPUT HELPERS
// --------------------------------------------------

function deduplicateEvents(events) {
  const seen = new Set();
  const result = [];

  for (const event of events) {
    const parsedDayKey = event.parsedDate
      ? formatIsoDate(event.parsedDate)
      : "";

    const key =
      `${(event.title || "").toLowerCase()}|` +
      `${parsedDayKey}|` +
      `${(event.town || "").toLowerCase()}`;

    if (!seen.has(key)) {
      seen.add(key);
      result.push(event);
    }
  }

  return result;
}

function sortAndScoreEvents(events) {
  return events
    .map(e => ({ ...e, score: scoreEvent(e) }))
    .sort((a, b) => b.score - a.score);
}

function groupEvents(events) {
  const grouped = {};

  for (const e of events) {
    const town = e.town;
    const dateKey = e.parsedDate ? formatIsoDate(e.parsedDate) : "unknown";

    if (!grouped[town]) grouped[town] = {};
    if (!grouped[town][dateKey]) grouped[town][dateKey] = [];

    grouped[town][dateKey].push({
      title: e.title,
      day: formatReadableDate(e.parsedDate),
      isoDate: dateKey,
      distance: Number(e.distance.toFixed(1)),
      score: e.score,
      audience: e.audience,
      sourceKind: e.sourceKind,
      source: e.sourceUrl
    });
  }

  return grouped;
}

function loadTowns() {
  const raw = fs.readFileSync(TOWNS_FILE, "utf-8");
  const towns = JSON.parse(raw);

  return towns
    .map(town => ({
      ...town,
      distanceFromUser: getDistanceKm(
        userLocation.lat,
        userLocation.lon,
        town.lat,
        town.lon
      )
    }))
    .filter(town => town.distanceFromUser <= MAX_RADIUS_KM)
    .sort((a, b) => a.distanceFromUser - b.distanceFromUser);
}

function escapeHtml(str) {
  return String(str)
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#39;");
}

function generateHtmlReport(events) {
  const simplifiedEvents = events.map(e => ({
    title: e.title,
    day: formatReadableDate(e.parsedDate),
    isoDate: formatIsoDate(e.parsedDate),
    town: e.town,
    distance: Number(e.distance.toFixed(1)),
    score: e.score,
    audience: e.audience,
    sourceKind: e.sourceKind,
    sourceUrl: e.sourceUrl
  }));

  const towns = [...new Set(simplifiedEvents.map(e => e.town))].sort();
  const dates = [...new Set(simplifiedEvents.map(e => e.isoDate))].sort();
  const sourceKinds = [...new Set(simplifiedEvents.map(e => e.sourceKind))].sort();
  const audiences = [...new Set(simplifiedEvents.map(e => e.audience))].sort();

  const townsOptions = towns.map(t => `<option value="${escapeHtml(t)}">${escapeHtml(t)}</option>`).join("");
  const datesOptions = dates.map(d => `<option value="${escapeHtml(d)}">${escapeHtml(d)}</option>`).join("");
  const sourceOptions = sourceKinds.map(s => `<option value="${escapeHtml(s)}">${escapeHtml(s.toUpperCase())}</option>`).join("");
  const audienceOptions = audiences.map(a => `<option value="${escapeHtml(a)}">${escapeHtml(a)}</option>`).join("");

  const jsonData = JSON.stringify(simplifiedEvents);

  return `
<!DOCTYPE html>
<html lang="fr">
<head>
  <meta charset="UTF-8" />
  <title>Weekend AI - Rapport</title>
  <style>
    * { box-sizing: border-box; }
    html, body {
      height: auto;
      overflow-y: auto;
      overflow-x: hidden;
    }
    body {
      font-family: Arial, sans-serif;
      margin: 0;
      background: #f5f7fb;
      color: #1f2937;
      min-height: 100vh;
    }
    header {
      background: linear-gradient(135deg, #2563eb, #1d4ed8);
      color: white;
      padding: 24px;
    }
    header h1 { margin: 0 0 6px 0; font-size: 28px; }
    header .meta { opacity: 0.9; font-size: 14px; }
    .container {
      padding: 20px;
      max-width: 1400px;
      margin: 0 auto;
      height: auto;
    }
    .filters {
      background: white;
      border-radius: 14px;
      padding: 16px;
      margin-bottom: 18px;
      box-shadow: 0 2px 10px rgba(0,0,0,0.06);
      display: grid;
      grid-template-columns: repeat(auto-fit, minmax(180px, 1fr));
      gap: 12px;
      align-items: end;
    }
    .field { display: flex; flex-direction: column; gap: 6px; }
    .field label { font-size: 13px; color: #6b7280; font-weight: bold; }
    .field input, .field select {
      padding: 10px 12px;
      border: 1px solid #d1d5db;
      border-radius: 10px;
      font-size: 14px;
      background: white;
    }
    .actions { display: flex; gap: 10px; flex-wrap: wrap; }
    button {
      border: none;
      border-radius: 10px;
      padding: 10px 14px;
      cursor: pointer;
      font-weight: bold;
    }
    .btn-primary { background: #2563eb; color: white; }
    .btn-secondary { background: #e5e7eb; color: #111827; }
    .summary { margin-bottom: 16px; color: #4b5563; font-size: 14px; }
    .results {
      display: grid;
      grid-template-columns: repeat(auto-fill, minmax(320px, 1fr));
      gap: 16px;
      height: auto;
    }
    .card {
      background: white;
      border-radius: 14px;
      padding: 16px;
      box-shadow: 0 2px 10px rgba(0,0,0,0.06);
      display: flex;
      flex-direction: column;
      gap: 10px;
    }
    .title { font-size: 17px; font-weight: bold; color: #111827; line-height: 1.3; }
    .line { font-size: 14px; color: #374151; }
    .badges { display: flex; gap: 8px; flex-wrap: wrap; }
    .badge {
      display: inline-block;
      background: #eef2ff;
      color: #3730a3;
      padding: 4px 8px;
      border-radius: 999px;
      font-size: 12px;
      font-weight: bold;
    }
    .footer-line {
      margin-top: auto;
      display: flex;
      justify-content: space-between;
      align-items: center;
      gap: 10px;
      flex-wrap: wrap;
    }
    a.source-link {
      color: #2563eb;
      text-decoration: none;
      font-weight: bold;
    }
    a.source-link:hover {
      text-decoration: underline;
    }
    .empty {
      background: white;
      border-radius: 14px;
      padding: 24px;
      box-shadow: 0 2px 10px rgba(0,0,0,0.06);
      color: #6b7280;
    }
  </style>
</head>
<body>
  <header>
    <h1>Weekend AI</h1>
    <div class="meta">
      Mode : ${escapeHtml(formatModeLabel(MODE))} • Rayon : ${MAX_RADIUS_KM} km • Généré le ${escapeHtml(new Date().toLocaleString("fr-FR"))}
    </div>
  </header>

  <div class="container">
    <div class="filters">
      <div class="field">
        <label for="search">Recherche</label>
        <input id="search" type="text" placeholder="fête, brocante, balade..." />
      </div>

      <div class="field">
        <label for="town">Commune</label>
        <select id="town">
          <option value="">Toutes</option>
          ${townsOptions}
        </select>
      </div>

      <div class="field">
        <label for="date">Date</label>
        <select id="date">
          <option value="">Toutes</option>
          ${datesOptions}
        </select>
      </div>

      <div class="field">
        <label for="audience">Audience</label>
        <select id="audience">
          <option value="">Toutes</option>
          ${audienceOptions}
        </select>
      </div>

      <div class="field">
        <label for="sourceKind">Source</label>
        <select id="sourceKind">
          <option value="">Toutes</option>
          ${sourceOptions}
        </select>
      </div>

      <div class="field">
        <label for="sortBy">Trier par</label>
        <select id="sortBy">
          <option value="score">Score</option>
          <option value="distance">Distance</option>
          <option value="date">Date</option>
        </select>
      </div>

      <div class="actions">
        <button class="btn-primary" onclick="applyFilters()">Filtrer</button>
        <button class="btn-secondary" onclick="resetFilters()">Réinitialiser</button>
      </div>
    </div>

    <div class="summary" id="summary"></div>
    <div id="results"></div>
  </div>

<script>
const EVENTS = ${jsonData};

function render(events) {
  const summary = document.getElementById("summary");
  const results = document.getElementById("results");

  summary.textContent = events.length + " événement(s) affiché(s)";

  if (!events.length) {
    results.innerHTML = '<div class="empty">Aucun événement ne correspond aux filtres actuels.</div>';
    return;
  }

  const html = events.map(event => \`
    <div class="card">
      <div class="title">\${escapeHtmlClient(event.title)}</div>
      <div class="line">📅 \${escapeHtmlClient(event.day)}</div>
      <div class="line">📍 \${escapeHtmlClient(event.town)} • \${event.distance} km</div>
      <div class="badges">
        <span class="badge">Score \${event.score}</span>
        <span class="badge">\${escapeHtmlClient(event.audience)}</span>
        <span class="badge">\${escapeHtmlClient((event.sourceKind || "").toUpperCase())}</span>
      </div>
      <div class="footer-line">
        <div class="line">Date ISO : \${escapeHtmlClient(event.isoDate)}</div>
        <a class="source-link" href="\${event.sourceUrl}" target="_blank" rel="noopener noreferrer">Ouvrir la source</a>
      </div>
    </div>
  \`).join("");

  results.innerHTML = '<div class="results">' + html + '</div>';
}

function applyFilters() {
  const search = document.getElementById("search").value.trim().toLowerCase();
  const town = document.getElementById("town").value;
  const date = document.getElementById("date").value;
  const audience = document.getElementById("audience").value;
  const sourceKind = document.getElementById("sourceKind").value;
  const sortBy = document.getElementById("sortBy").value;

  let filtered = [...EVENTS];

  if (search) {
    filtered = filtered.filter(e =>
      e.title.toLowerCase().includes(search) ||
      e.town.toLowerCase().includes(search)
    );
  }

  if (town) filtered = filtered.filter(e => e.town === town);
  if (date) filtered = filtered.filter(e => e.isoDate === date);
  if (audience) filtered = filtered.filter(e => e.audience === audience);
  if (sourceKind) filtered = filtered.filter(e => e.sourceKind === sourceKind);

  if (sortBy === "score") {
    filtered.sort((a, b) => b.score - a.score);
  } else if (sortBy === "distance") {
    filtered.sort((a, b) => a.distance - b.distance);
  } else if (sortBy === "date") {
    filtered.sort((a, b) => a.isoDate.localeCompare(b.isoDate));
  }

  render(filtered);
}

function resetFilters() {
  document.getElementById("search").value = "";
  document.getElementById("town").value = "";
  document.getElementById("date").value = "";
  document.getElementById("audience").value = "";
  document.getElementById("sourceKind").value = "";
  document.getElementById("sortBy").value = "score";
  render([...EVENTS].sort((a, b) => b.score - a.score));
}

function escapeHtmlClient(str) {
  return String(str)
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#39;");
}

render([...EVENTS].sort((a, b) => b.score - a.score));
</script>
</body>
</html>
`;
}

async function processTown(town) {
  console.log(`\n🏘️ Analyse de ${town.name} (${town.distanceFromUser.toFixed(1)} km)`);

  let allTownEvents = [];

  for (const source of town.sources || []) {
    console.log(`   🌐 Source : ${source.type} -> ${source.url}`);

    const homepageHtml = await fetchHtml(source.url);
    if (!homepageHtml) continue;

    const candidateLinks = discoverCandidateLinks(source.url, homepageHtml);

    if (!candidateLinks.length) {
      console.log("   ⚠️ Aucun lien candidat détecté");
      continue;
    }

    console.log("   🔎 Pages candidates :");
    candidateLinks.forEach(link => {
      console.log(`   - ${link.text || "[sans texte]"} -> ${link.url} (${link.kind})`);
    });

    for (const link of candidateLinks) {
      if (link.kind === "pdf") {
        const pdfText = await fetchPdfText(link.url);
        if (!pdfText) continue;

        const pdfBlocks = extractStructuredBlocksFromPdfText(pdfText);
        const extracted = extractEventsFromBlocks(
          pdfBlocks,
          link.url,
          town,
          "pdf",
          link.context
        );

        if (extracted.length > 0) {
          console.log(`   ✅ ${extracted.length} événement(s) trouvé(s) dans PDF ${link.url}`);
          allTownEvents = allTownEvents.concat(extracted);
        } else {
          console.log(`   ℹ️ Aucun événement retenu dans PDF ${link.url}`);
        }
      } else {
        const candidateHtml = await fetchHtml(link.url);
        if (!candidateHtml) continue;

        const htmlBlocks = extractStructuredBlocksFromHtml(candidateHtml);
        const extracted = extractEventsFromBlocks(
          htmlBlocks,
          link.url,
          town,
          "html",
          link.context
        );

        if (extracted.length > 0) {
          console.log(`   ✅ ${extracted.length} événement(s) trouvé(s) sur ${link.url}`);
          allTownEvents = allTownEvents.concat(extracted);
        } else {
          console.log(`   ℹ️ Aucun événement retenu sur ${link.url}`);
        }
      }
    }
  }

  return allTownEvents;
}

async function closeBrowserIfNeeded() {
  if (browserInstance) {
    await browserInstance.close();
    browserInstance = null;
  }
}

async function main() {
  initCache();

  console.log("🚀 Weekend AI - crawler avancé");
  console.log("📍 Position : Guignes");
  console.log(`📏 Rayon max : ${MAX_RADIUS_KM} km`);
  console.log(`🗓️ Mode temporel : ${formatModeLabel(MODE)}`);

  const towns = loadTowns();

  console.log("\n📋 Communes chargées :");
  towns.forEach(town => {
    console.log(`- ${town.name} (${town.distanceFromUser.toFixed(1)} km)`);
  });

  let allEvents = [];

  for (const town of towns) {
    const townEvents = await processTown(town);
    allEvents = allEvents.concat(townEvents);
  }

  allEvents = deduplicateEvents(allEvents);

  const filtered = allEvents.filter(event => {
    return (
      event.distance <= MAX_RADIUS_KM &&
      isLocalEvent(event) &&
      event.parsedDate &&
      !isPastEvent(event.parsedDate) &&
      !isTooFarInFuture(event.parsedDate) &&
      isDateInMode(event.parsedDate, MODE)
    );
  });

  const ranked = sortAndScoreEvents(filtered);

  console.log(`\n✅ Événements retenus : ${ranked.length}`);

  fs.writeFileSync(EVENTS_JSON_FILE, JSON.stringify(ranked, null, 2), "utf-8");
  fs.writeFileSync(REPORT_HTML_FILE, generateHtmlReport(ranked), "utf-8");

  console.log(`💾 events.json généré`);
  console.log(`💾 report.html généré`);

  await closeBrowserIfNeeded();
}

main().catch(async (error) => {
  console.error("❌ Erreur fatale :", error.message);
  await closeBrowserIfNeeded();
});