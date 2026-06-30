/**
 * Captures du « Tour de la plateforme » — utilitaire de génération, PAS un test QA.
 * -----------------------------------------------------------------------------
 * Ce script produit, de façon reproductible, les images annotées du tour
 * (../assets/*.png) en visitant un TENANT DE DÉMONSTRATION dédié avec un compte
 * NON-ADMINISTRATEUR et des données fictives.
 *
 * Anti-fuite (voir capture/README.md) :
 *   - tenant de démonstration uniquement (jamais une instance de production) ;
 *   - compte non-admin → pas d'accès aux panneaux d'administration sensibles ;
 *   - masquage (`mask`) des zones d'identité sur CHAQUE capture ;
 *   - identifiants/URL lus depuis un .env NON commité (placeholders ci-dessous).
 *
 * Exécution différée : tant que les variables d'environnement du tenant de démo
 * ne sont pas fournies, tout le fichier est `skip` — il ne s'exécute donc jamais,
 * et n'échoue jamais, en intégration continue.
 */
import { test, type Page, type Locator } from '@playwright/test';
import path from 'node:path';

const URL = process.env.DEMO_OWUI_URL;
const EMAIL = process.env.DEMO_OWUI_EMAIL;
const PASSWORD = process.env.DEMO_OWUI_PASSWORD;

// Dossier de sortie : ../assets relativement à ce fichier.
const ASSETS = path.resolve(__dirname, '..', 'assets');

// Sans tenant de démo configuré, on ne fait rien (pas d'exécution en CI).
const configured = Boolean(URL && EMAIL && PASSWORD);
test.skip(
  !configured,
  'Tenant de démonstration non configuré — voir 00-Tour-Plateforme/capture/README.md',
);

/**
 * Zones sensibles masquées sur toutes les captures. Les sélecteurs sont
 * volontairement larges (rôles ARIA + libellés multilingues) et devront être
 * confirmés contre la version live du tenant de démonstration.
 */
function sensitiveZones(page: Page): Locator[] {
  return [
    page.locator('[data-tour-mask]'), // points de masquage explicites si présents
    page.getByRole('button', { name: /account|compte|profil|profile/i }),
    page.getByText(/@/), // adresses e-mail visibles
  ];
}

async function capture(page: Page, fileName: string): Promise<void> {
  await page.screenshot({
    path: path.join(ASSETS, fileName),
    mask: sensitiveZones(page),
    animations: 'disabled',
  });
}

async function signIn(page: Page): Promise<void> {
  await page.goto(URL!);
  await page.getByPlaceholder(/email/i).fill(EMAIL!);
  await page.getByPlaceholder(/password|mot de passe/i).fill(PASSWORD!);
  await page
    .getByRole('button', { name: /sign in|se connecter|connexion|log in/i })
    .click();
  await page.waitForLoadState('networkidle');
}

test.describe('Tour de la plateforme — captures (tenant démo)', () => {
  // 1 — page de connexion (avant authentification, champs masqués).
  test('01 — page de connexion', async ({ page }) => {
    await page.goto(URL!);
    await capture(page, '01-connexion.png');
  });

  test.describe('après connexion', () => {
    test.beforeEach(async ({ page }) => {
      await signIn(page);
    });

    // 1 — première vue (écran de chat).
    test('01 — première vue', async ({ page }) => {
      await capture(page, '01-premiere-vue.png');
    });

    // 2 — chat : sélecteur de modèle + réponse en streaming.
    test('02 — chat & modèles', async ({ page }) => {
      await page
        .getByRole('button', { name: /select a model|choisir un modèle|model/i })
        .first()
        .click()
        .catch(() => {}); // tolérant : la capture vaut même si l'ouverture échoue
      await capture(page, '02-selecteur-modele.png');
      await page.keyboard.press('Escape').catch(() => {});
      await capture(page, '02-chat-streaming.png');
    });

    // 3 — Workspace : modèles personnalisés + bases de connaissances.
    test('03 — workspace', async ({ page }) => {
      await page
        .getByRole('link', { name: /workspace|espace de travail/i })
        .first()
        .click()
        .catch(() => {});
      await page.waitForLoadState('networkidle');
      await capture(page, '03-workspace-modele.png');
      await page
        .getByRole('link', { name: /knowledge|connaissance/i })
        .first()
        .click()
        .catch(() => {});
      await page.waitForLoadState('networkidle');
      await capture(page, '03-base-connaissances.png');
    });

    // 4 — Canaux.
    test('04 — canaux', async ({ page }) => {
      await page
        .getByRole('link', { name: /channel|canal|canaux/i })
        .first()
        .click()
        .catch(() => {});
      await page.waitForLoadState('networkidle');
      await capture(page, '04-canal.png');
    });

    // 5 — Paramètres personnels.
    test('05 — paramètres', async ({ page }) => {
      await page
        .getByRole('button', { name: /account|compte|profil|profile/i })
        .first()
        .click()
        .catch(() => {});
      await page
        .getByRole('menuitem', { name: /settings|paramètres/i })
        .first()
        .click()
        .catch(() => {});
      await capture(page, '05-parametres.png');
    });
  });
});
