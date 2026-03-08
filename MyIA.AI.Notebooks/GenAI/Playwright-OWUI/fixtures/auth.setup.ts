/**
 * Setup d'authentification — s'execute une fois avant tous les tests.
 *
 * Pourquoi un setup separe ?
 * - Evite de se reconnecter a chaque test (gain de temps)
 * - Sauvegarde l'etat du navigateur (cookies, localStorage) dans .auth/owui.json
 * - Tous les tests suivants reutilisent cette session authentifiee
 *
 * C'est un pattern standard Playwright : https://playwright.dev/docs/auth
 */
import { test as setup } from '@playwright/test';
import path from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

setup('authenticate', async ({ page }) => {
  const email = process.env.OWUI_EMAIL;
  const password = process.env.OWUI_PASSWORD;

  if (!email || !password) {
    throw new Error(
      'Missing OWUI_EMAIL or OWUI_PASSWORD in .env file.\n' +
      'Copy .env.example to .env and fill in your credentials.'
    );
  }

  const authFile = path.resolve(__dirname, '../.auth/owui.json');

  // 1. Naviguer vers la page de login
  await page.goto('/auth');

  // 2. Remplir le formulaire
  //    Open WebUI utilise des champs standard avec autocomplete="email"
  await page.locator('input[autocomplete="email"]').fill(email);
  await page.locator('input[type="password"]').fill(password);
  await page.locator('button[type="submit"]').click();

  // 3. Attendre la redirection vers la page principale
  await page.waitForURL('**/', { timeout: 30_000 });
  await page.waitForLoadState('networkidle', { timeout: 15_000 });

  // 4. Sauvegarder l'etat authentifie
  await page.context().storageState({ path: authFile });
});
