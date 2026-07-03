/**
 * Captures du « Tour de la plateforme » — utilitaire de génération, PAS un test QA.
 * -----------------------------------------------------------------------------
 * Ce script produit, de façon reproductible, les images annotées du tour
 * (../assets/*.png) en visitant une INSTANCE RÉELLE avec un compte
 * NON-ADMINISTRATEUR et des données fictives ou fraîches (compte neuf).
 *
 * Anti-fuite (voir capture/README.md) :
 *   - compte NON-ADMIN, de préférence neuf → aucune donnée réelle
 *     d'établissement visible (ni listes de modèles/bases internes, ni canaux) ;
 *   - on ne capture QUE des surfaces sans contenu réel (connexion, chat neuf sur
 *     invite fictive, réglages vides) ; les surfaces à contenu restent
 *     schématisées dans ../architecture.md ;
 *   - masquage (`mask`) des zones d'identité sur CHAQUE capture ;
 *   - revue anti-fuite de CHAQUE image avant de la commiter ;
 *   - identifiants/URL lus depuis un .env NON commité (placeholders ci-dessous).
 *
 * Exécution différée : tant que les variables d'environnement de capture ne sont
 * pas fournies, tout le fichier est `skip` — il ne s'exécute donc jamais, et
 * n'échoue jamais, en intégration continue.
 */
import { test, type Page, type Locator } from '@playwright/test';
import path from 'node:path';

const URL = process.env.DEMO_OWUI_URL;
const EMAIL = process.env.DEMO_OWUI_EMAIL;
const PASSWORD = process.env.DEMO_OWUI_PASSWORD;
// Optionnel : nom d'un modèle « thinking » pour la capture du raisonnement (v0.10).
const REASONING_MODEL = process.env.DEMO_OWUI_REASONING_MODEL;

// Dossier de sortie : ../assets relativement à ce fichier.
const ASSETS = path.resolve(__dirname, '..', 'assets');

// Sans compte de capture configuré, on ne fait rien (pas d'exécution en CI).
const configured = Boolean(URL && EMAIL && PASSWORD);
test.skip(
  !configured,
  'Compte de capture non configuré — voir 00-Tour-Plateforme/capture/README.md',
);

/**
 * Zones sensibles masquées sur toutes les captures. Les sélecteurs sont
 * volontairement larges (rôles ARIA + libellés multilingues) et devront être
 * confirmés contre la version live de l'instance ciblée.
 */
function sensitiveZones(page: Page): Locator[] {
  return [
    page.locator('[data-tour-mask]'), // points de masquage explicites si présents
    page.getByRole('button', { name: /account|compte|profil|profile/i }),
    page.getByText(/@/), // adresses e-mail visibles
    // Marque / logo de l'instance (identité du tenant) — visible en haut de la
    // sidebar sur toutes les vues authentifiées. Sélecteurs volontairement larges,
    // à CONFIRMER contre l'UI live lors de la génération (revue anti-fuite).
    page.locator('nav a[href="/"], #sidebar a[href="/"], header a[href="/"]'),
  ];
}

async function capture(page: Page, fileName: string): Promise<void> {
  await page.screenshot({
    path: path.join(ASSETS, fileName),
    mask: sensitiveZones(page),
    animations: 'disabled',
  });
}

/**
 * Ferme les fenêtres modales qui recouvrent la vue à capturer : nouveautés
 * (« What's New » v0.10) et onboarding, affichées à la première connexion d'un
 * compte neuf. Tolérant et borné dans le temps (ne bloque jamais la capture).
 */
async function dismissModals(page: Page): Promise<void> {
  const deadline = Date.now() + 8000;
  while (Date.now() < deadline) {
    const dialog = page.locator('[role="dialog"], .modal').first();
    if (!(await dialog.isVisible().catch(() => false))) return;
    const cta = page
      .getByRole('button', {
        name: /d'accord, allons-y|allons-y|got it|get started|commencer|fermer|close|dismiss|plus tard|skip|ignorer/i,
      })
      .first();
    if (await cta.isVisible().catch(() => false)) {
      await cta.click().catch(() => {});
    } else {
      await page.keyboard.press('Escape').catch(() => {});
    }
    await page.waitForTimeout(500);
  }
}

async function signIn(page: Page): Promise<void> {
  await page.goto(URL!);
  // Le libellé français est « adresse e-mail » (avec trait d'union) : /mail/i
  // le couvre, /email/i non.
  await page.getByPlaceholder(/e-?mail|adresse/i).first().fill(EMAIL!);
  await page
    .getByPlaceholder(/password|mot de passe/i)
    .first()
    .fill(PASSWORD!);
  await page
    .getByRole('button', { name: /sign in|se connecter|connexion|log in/i })
    .first()
    .click();
  await page.waitForLoadState('networkidle').catch(() => {});
  await dismissModals(page);
}

test.describe('Tour de la plateforme — captures (compte de capture)', () => {
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

      // Réponse en cours de streaming sur une invite FICTIVE (aucun contenu réel).
      // Sans envoi d'invite, l'écran resterait vide : le fichier serait mal nommé.
      // On saisit une invite neutre dans l'éditeur TipTap (#chat-input requiert
      // keyboard.type, pas fill) puis on capture dès que la réponse de l'assistant
      // commence à s'afficher. Sélecteurs à confirmer contre l'UI live.
      await page.locator('#chat-input').click().catch(() => {});
      await page.keyboard.type('Rédige un court poème sur la mer.', { delay: 8 });
      await page.keyboard.press('Enter');
      await page
        .locator('[id^="message-"], .chat-assistant, [class*="assistant" i]')
        .first()
        .waitFor({ state: 'visible', timeout: 30_000 })
        .catch(() => {});
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

    // ================================================================
    // Nouveautés v0.10 — surfaces sans contenu réel (compte neuf)
    // ================================================================

    // 2 — raisonnement affiché en direct (v0.10) : bloc de réflexion d'un
    // modèle « thinking » sur une invite FICTIVE. Nécessite un modèle de
    // raisonnement ; sans DEMO_OWUI_REASONING_MODEL, on saute.
    test('02 — raisonnement en direct (v0.10)', async ({ page }) => {
      test.skip(!REASONING_MODEL, 'DEMO_OWUI_REASONING_MODEL non défini');
      await page.goto(URL!);
      await page.waitForLoadState('networkidle').catch(() => {});
      await dismissModals(page);
      // Ouvrir le sélecteur de modèle et choisir le modèle de raisonnement.
      await page
        .locator('button[id^="model-selector-"]')
        .first()
        .click()
        .catch(() => {});
      await page
        .locator('#model-search-input, [role="listbox"] input')
        .first()
        .fill(REASONING_MODEL!)
        .catch(() => {});
      await page.waitForTimeout(400);
      await page.locator('[role="option"]').first().click().catch(() => {});
      // Envoyer une invite neutre qui déclenche du raisonnement.
      await page.locator('#chat-input').click().catch(() => {});
      await page.keyboard.type(
        'Explique étape par étape pourquoi le ciel est bleu.',
        { delay: 8 },
      );
      await page.keyboard.press('Enter');
      // Attendre l'apparition du bloc de raisonnement, puis capturer.
      await page
        .locator(
          'details[class*="reason" i], details[class*="think" i], [class*="reasoning" i], [class*="thinking" i]',
        )
        .first()
        .waitFor({ state: 'visible', timeout: 30_000 })
        .catch(() => {});
      await capture(page, '02-raisonnement-direct.png');
    });

    // 3 — dossiers d'équipe partageables (v0.10) : création d'un dossier dans la
    // sidebar (compte neuf → aucun dossier réel visible).
    test("03 — dossier d'équipe (v0.10)", async ({ page }) => {
      await page.goto(URL!);
      await page.waitForLoadState('networkidle').catch(() => {});
      await dismissModals(page);
      await page
        .getByRole('button', {
          name: /nouveau dossier|new folder|cr[ée]er un dossier/i,
        })
        .first()
        .click()
        .catch(() => {});
      await capture(page, '03-dossier-equipe.png');
    });

    // 5 — mémoire (v0.10) : Menu utilisateur > Réglages > Personnalisation >
    // Mémoire > Gérer (compte neuf → panneau « Mémoire 0 », aucun souvenir réel).
    test('05 — mémoire (v0.10)', async ({ page }) => {
      await page.goto(URL!);
      await page.waitForLoadState('networkidle').catch(() => {});
      await dismissModals(page);
      // Ouvrir le menu utilisateur (avatar) puis les Réglages.
      await page
        .getByRole('button', { name: /menu utilisateur|user menu/i })
        .first()
        .click()
        .catch(() => {});
      await page.waitForTimeout(500);
      await page
        .getByRole('button', { name: /r[ée]glages|param[èe]tres|settings/i })
        .first()
        .click()
        .catch(() => {});
      await page.waitForTimeout(1000);
      const dialog = page.locator('[role="dialog"], .modal').last();
      // Onglet Personnalisation → section Mémoire → bouton « Gérer ».
      await dialog
        .getByText(/personnalisation|personalization/i)
        .first()
        .click()
        .catch(() => {});
      await page.waitForTimeout(800);
      await dialog
        .getByRole('button', { name: /g[ée]rer|manage/i })
        .first()
        .click()
        .catch(() => {});
      await page
        .getByText(
          /aucun|les souvenirs|no memories|seront affich/i,
        )
        .first()
        .waitFor({ state: 'visible', timeout: 8000 })
        .catch(() => {});
      await capture(page, '05-memoire.png');
    });
  });
});
