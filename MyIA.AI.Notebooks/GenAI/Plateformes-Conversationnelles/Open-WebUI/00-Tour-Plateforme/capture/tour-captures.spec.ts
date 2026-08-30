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
import { fileURLToPath } from 'node:url';

// ESM : pas de __dirname natif (le projet capture/ est "type": "module").
const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const URL = process.env.DEMO_OWUI_URL;
const EMAIL = process.env.DEMO_OWUI_EMAIL;
const PASSWORD = process.env.DEMO_OWUI_PASSWORD;
// Optionnel : nom d'un modèle « thinking » pour la capture du raisonnement (v0.10).
const REASONING_MODEL = process.env.DEMO_OWUI_REASONING_MODEL;

// Surfaces exposant du CONTENU RÉEL d'établissement (listes de modèles/bases,
// canaux) : NON capturées par défaut. Le principe « anti-fuite par construction »
// (capture/README.md §2) veut qu'on ne capture QUE des surfaces sans contenu réel.
// Opt-in EXPLICITE (=== '1') réservé à une instance à DONNÉES FICTIVES, où ces
// surfaces deviennent sûres. Par défaut désactivé : la génération standard ne
// produit que le sous-ensemble sûr, sans dépendre de la relecture pour écarter
// des PNG à contenu établissement.
const CAPTURE_REAL_CONTENT = process.env.DEMO_OWUI_CAPTURE_REAL_CONTENT === '1';

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
    // Contrôle « Open Terminal (…) » du composer : son libellé porte le nom du
    // workspace terminal de l'instance (identifiant interne — constaté à
    // l'audit vision du 2026-08-30). On masque le BOUTON entier : le texte
    // tronqué vit dans un <span class="truncate"> (150 px) et masquer ce seul
    // span laissait dépasser le libellé sur les vues où la géométrie diffère.
    page.getByRole('button', { name: /open terminal/i }),
    page.getByText(/open terminal|terminal\s*\(/i),
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
  // 1 — page de connexion (avant authentification : champs vides, rien de saisi).
  test('01 — page de connexion', async ({ page }) => {
    await page.goto(URL!);
    // Attendre le rendu du formulaire : une capture immédiate après goto fige
    // le shell pré-hydratation (résidu de texte « ol » sur fond blanc, sans
    // aucun champ) — constaté à l'audit vision du 2026-08-30.
    await page
      .getByRole('button', { name: /sign in|se connecter|connexion|log in/i })
      .first()
      .waitFor({ state: 'visible', timeout: 30_000 })
      .catch(() => {});
    await page.waitForTimeout(800);
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
      // Le sélecteur ouvert liste des modèles réels (contenu établissement) :
      // capture réservée à l'opt-in données fictives (CAPTURE_REAL_CONTENT).
      if (CAPTURE_REAL_CONTENT) {
        await page
          .getByRole('button', { name: /select a model|choisir un modèle|model/i })
          .first()
          .click()
          .catch(() => {}); // tolérant : la capture vaut même si l'ouverture échoue
        await capture(page, '02-selecteur-modele.png');
        await page.keyboard.press('Escape').catch(() => {});
      }

      // Réponse en cours de streaming sur une invite FICTIVE (aucun contenu réel).
      // Sélection explicite d'un modèle fonctionnel : le modèle présélectionné
      // peut être indisponible côté serveur (constat 2026-08-30 : tuteurs à base
      // MistralAI en erreur « Model not found » sanitizée — base sans ligne DB
      // = admin-only en v0.11, ET abonnement MistralAI épuisé). Sur l'instance
      // de capture, « TP Prompt Engineering » est rebasé sur le modèle local.
      await page.locator('button[id^="model-selector-"]').first().click().catch(() => {});
      await page.waitForTimeout(400);
      await page
        .locator('#model-search-input, [role="listbox"] input')
        .first()
        .fill('TP Prompt Engineering')
        .catch(() => {});
      await page.waitForTimeout(400);
      await page
        .getByRole('option', { name: /tp prompt engineering/i })
        .first()
        .click()
        .catch(() => {});
      await page.waitForTimeout(600);
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
      // Si le modèle « réfléchit » en direct (indicateur « En train de
      // réfléchir… » de v0.11), attendre d'abord son apparition PUIS sa
      // disparition — un simple wait hidden passe immédiatement tant que
      // l'indicateur n'est pas encore rendu, et la capture figerait le seul
      // indicateur au lieu de la réponse en streaming.
      const thinking = page
        .getByText(/en train de r[ée]fl[ée]chir|thinking/i)
        .first();
      await thinking.waitFor({ state: 'visible', timeout: 10_000 }).catch(() => {});
      await thinking.waitFor({ state: 'hidden', timeout: 90_000 }).catch(() => {});
      await page.waitForTimeout(1500);
      // Laisser le composer se stabiliser AVANT de capturer : le contrôle
      // « Open Terminal » de la barre du bas n'apparaît qu'après le rendu de la
      // réponse — capturer dès l'apparition de la réponse figeait son libellé
      // NON masqué (race constatée à l'audit vision du 2026-08-30). L'attente
      // est tolérante : sur une instance sans terminal, elle expire sans bloquer.
      await page
        .getByText(/open terminal|terminal\s*\(/i)
        .first()
        .waitFor({ state: 'visible', timeout: 5000 })
        .catch(() => {});
      await page.waitForTimeout(800);
      await capture(page, '02-chat-streaming.png');
    });

    // 3 — Workspace : modèles personnalisés + bases de connaissances.
    // Contenu établissement (modèles/bases internes) : opt-in données fictives.
    test('03 — workspace', async ({ page }) => {
      test.skip(
        !CAPTURE_REAL_CONTENT,
        'Surface à contenu réel (modèles/bases) — opt-in DEMO_OWUI_CAPTURE_REAL_CONTENT=1 requis (données fictives) ; sinon schématisée dans architecture.md',
      );
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
    // Contenu établissement (noms de canaux) : opt-in données fictives.
    test('04 — canaux', async ({ page }) => {
      test.skip(
        !CAPTURE_REAL_CONTENT,
        'Surface à contenu réel (canaux) — opt-in DEMO_OWUI_CAPTURE_REAL_CONTENT=1 requis (données fictives) ; sinon schématisée dans architecture.md',
      );
      await page
        .getByRole('link', { name: /channel|canal|canaux/i })
        .first()
        .click()
        .catch(() => {});
      await page.waitForLoadState('networkidle');
      await capture(page, '04-canal.png');
    });

    // 5 — Paramètres personnels. Le bouton du menu utilisateur porte le libellé
    // FR « Menu utilisateur » (pas « account/compte/profil ») et l'entrée
    // « Réglages » du menu déroulant est un <button>, pas un role=menuitem.
    test('05 — paramètres', async ({ page }) => {
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
      await page.waitForTimeout(1500);
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

    // 5 — mémoire (v0.10) : Menu utilisateur > Réglages > Personnalisation.
    // Compte neuf → panneau « Saved Memories 0 » (aucun souvenir réel). En v0.11
    // l'état vide de la section Mémoire est visible sur l'onglet Personnalisation,
    // sans bouton « Gérer » (l'UX v0.10 qui ouvrait un sous-dialogue a été remplacée).
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
      await page.waitForTimeout(1200);
      const dialog = page.locator('[role="dialog"], .modal').last();
      // Onglet Personnalisation → section Mémoire (état vide directement visible).
      await dialog
        .getByText(/personnalisation|personalization/i)
        .first()
        .click()
        .catch(() => {});
      await page.waitForTimeout(1200);
      await page
        .getByText(
          /les souvenirs|saved memories|aucun|seront affich/i,
        )
        .first()
        .waitFor({ state: 'visible', timeout: 8000 })
        .catch(() => {});
      await capture(page, '05-memoire.png');
    });
  });
});
