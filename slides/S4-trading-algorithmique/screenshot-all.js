// Screenshot all Slidev slides across 3 decks
// Usage: node screenshot-all.js
const { chromium } = require('playwright-core');
const fs = require('fs');
const path = require('path');

const DECKS = [
  { name: 'deck-1', port: 3030, slides: 31 },
  { name: 'deck-2', port: 3031, slides: 49 },
  { name: 'deck-3', port: 3032, slides: 37 },
];

const OUT_DIR = path.join(__dirname, 'screenshots');

(async () => {
  if (!fs.existsSync(OUT_DIR)) fs.mkdirSync(OUT_DIR, { recursive: true });

  const browser = await chromium.launch();
  const context = await browser.newContext({
    viewport: { width: 1280, height: 720 },
    colorScheme: 'light',
  });

  for (const deck of DECKS) {
    console.log(`\n=== ${deck.name} (port ${deck.port}) ===`);
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
