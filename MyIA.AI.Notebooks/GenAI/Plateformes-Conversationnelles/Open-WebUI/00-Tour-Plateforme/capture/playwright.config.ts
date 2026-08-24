/**
 * Configuration Playwright des captures du tour (projet autonome capture/).
 * -----------------------------------------------------------------------------
 * Le spec tour-captures.spec.ts vit hors du testDir de la série QA
 * (Playwright-OWUI/) et signe lui-même — il capture la page de connexion AVANT
 * authentification, incompatible avec le storageState authentifié exigé par la
 * config QA. Ce dossier est donc un projet npm autonome (package.json dédié) :
 * CLI, config et spec résolvent la même instance unique de @playwright/test.
 *
 * Exécution (depuis ce dossier) :
 *   npm ci && npx playwright test
 */
import { defineConfig, devices } from '@playwright/test';
import dotenv from 'dotenv';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

// Identifiants de capture : capture/.env (non commité — voir .env.example).
dotenv.config({ path: path.resolve(__dirname, '.env') });

export default defineConfig({
  testDir: '.',
  testMatch: '**/tour-captures.spec.ts',
  fullyParallel: false,
  workers: 1, // séquentiel — l'instance cible est une vraie instance
  reporter: [['list']],
  timeout: 120_000,
  use: {
    ...devices['Desktop Chrome'],
    viewport: { width: 1440, height: 900 }, // format canonique des figures existantes
    ignoreHTTPSErrors: true,
    locale: 'fr-FR',
    screenshot: 'only-on-failure',
  },
});
