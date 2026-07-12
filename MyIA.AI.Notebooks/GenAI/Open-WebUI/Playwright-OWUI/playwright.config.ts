/**
 * Configuration Playwright pour la serie pedagogique Open WebUI.
 *
 * Charge les credentials depuis .env (copie de .env.example).
 * Un seul projet "owui" avec setup d'authentification prealable.
 */
import { defineConfig, devices } from '@playwright/test';
import dotenv from 'dotenv';
import path from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

// Charger .env depuis le repertoire courant
dotenv.config({ path: path.resolve(__dirname, '.env') });

const OWUI_URL = process.env.OWUI_URL || 'http://localhost:3000';
const TIMEOUT = parseInt(process.env.PLAYWRIGHT_TIMEOUT || '120000', 10);
const LOCALE = process.env.PLAYWRIGHT_LOCALE || 'fr-FR';

export default defineConfig({
  // Les tests sont dans les sous-repertoires de modules
  testDir: '.',
  testMatch: '**/*.spec.ts',

  fullyParallel: false,   // Sequentiel — les reponses LLM sont lentes
  forbidOnly: !!process.env.CI,
  retries: process.env.CI ? 1 : 0,
  workers: 1,             // Un seul worker — eviter la charge LLM concurrente

  reporter: [
    ['html', { open: 'never' }],
    ['list'],
  ],

  use: {
    screenshot: 'only-on-failure',
    video: 'on-first-retry',
    trace: 'on-first-retry',
    ignoreHTTPSErrors: true, // Certificats auto-signes sur LAN
    locale: LOCALE,
  },

  timeout: TIMEOUT,
  expect: { timeout: 10_000 },

  projects: [
    // Setup : authentification unique, reutilisee par tous les tests
    {
      name: 'owui-setup',
      testDir: './fixtures',
      testMatch: /auth\.setup\.ts/,
      use: {
        ...devices['Desktop Chrome'],
        baseURL: OWUI_URL,
      },
    },
    // Projet principal
    {
      name: 'owui',
      dependencies: ['owui-setup'],
      use: {
        ...devices['Desktop Chrome'],
        baseURL: OWUI_URL,
        storageState: path.resolve(__dirname, '.auth/owui.json'),
      },
    },
  ],
});
