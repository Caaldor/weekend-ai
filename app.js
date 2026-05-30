const fs = require("fs");

// Exemple simple (à remplacer par ton crawler plus tard)
const events = [
  {
    title: "Marché local",
    date: "2026-06-01",
    town: "Guignes",
    distance: 0
  },
  {
    title: "Fête de village",
    date: "2026-06-02",
    town: "Melun",
    distance: 15
  }
];

// ✅ Générer le JSON utilisé par le site
fs.writeFileSync(
  "events.json",
  JSON.stringify(events, null, 2),
  "utf-8"
);

console.log("✅ events.json généré");