// Screenshot all Slidev slides across 3 decks
// Usage: node screenshot-all.js [--deck N]
const { chromium } = require('playwright-core');
const fs = require('fs');
const path = require('path');

const DECK_FILES = {
  'deck-1': 'deck-1-fondamentaux.md',
  'deck-2': 'deck-2-strategies.md',
  'deck-3': 'deck-3-pratique-lean.md',
};

const PORTS = { 'deck-1': 3030, 'deck-2': 3031, 'deck-3': 3032 };

function countSlides(mdPath) {
  const content = fs.readFileSync(mdPath, 'utf-8');
  const matches = content.match(/^# /gm);
  return matches ? matches.length : 0;
}

const targetDeck = process.argv.includes('--deck')
  ? `deck-${process.argv[process.argv.indexOf('--deck') + 1]}`
  : null;

const DECKS = Object.keys(DECK_FILES)
  .filter((name) => !targetDeck || name === targetDeck)
  .map((name) => ({
    name,
    port: PORTS[name],
    slides: countSlides(path.join(__dirname, DECK_FILES[name])),
  }));

const OUT_DIR = path.join(__dirname, 'screenshots');

(async () => {
  if (!fs.existsSync(OUT_DIR)) fs.mkdirSync(OUT_DIR, { recursive: true });

  const browser = await chromium.launch();
  const context = await browser.newContext({
    viewport: { width: 1280, height: 720 },
    colorScheme: 'light',
  });

  for (const deck of DECKS) {
    console.log(`\n=== ${deck.name} (${deck.slides} slides, port ${deck.port}) ===`);
    for (let i = 1; i <= deck.slides; i++) {
      const url = `http://localhost:${deck.port}/${i}?clicks=99`;
      const page = await context.newPage();
      try {
        await page.goto(url, { waitUntil: 'networkidle', timeout: 15000 });
        await page.waitForTimeout(800);
        const file = path.join(OUT_DIR, `${deck.name}-slide-${String(i).padStart(2, '0')}.png`);
        await page.screenshot({ path: file });
        console.log(`  slide ${i}/${deck.slides} OK`);
      } catch (e) {
        console.log(`  slide ${i}/${deck.slides} ERROR: ${e.message}`);
      }
      await page.close();
    }
  }

  await browser.close();
  console.log(`\nDone. Screenshots in ${OUT_DIR}`);
})();
