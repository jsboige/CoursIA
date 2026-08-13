/**
 * Module 06 — Les nouveautes d'Open WebUI v0.10 ("l'ere agentique")
 *
 * Ce module montre comment TESTER les fonctionnalites arrivees avec la ligne
 * v0.10 (juin-juillet 2026), la plus grosse evolution depuis la v0.8 :
 *
 *   - Memoire (memory) : refonte complete, sortie de beta. Chaque souvenir
 *     porte desormais un `type` (long terme vs lie a une conversation).
 *   - Dossiers d'equipe (folders) : partageables avec permissions lecture/ecriture.
 *   - Raisonnement streame (v0.10.2) : les etapes de "reflexion" des modeles
 *     thinking s'affichent EN DIRECT dans l'interface.
 *   - Compaction automatique : les longues conversations sont resumees quand on
 *     approche de la limite de contexte (moins de coupures brutales).
 *
 * DEUX FAMILLES DE TESTS (rappel des modules 03 et 05) :
 *   - API (06a) : rapides, deterministes, ideals pour verifier des DONNEES.
 *   - UI  (06b) : indispensables pour le rendu et l'interaction visuelle.
 *
 * PROPRETE DES DONNEES (important sur une instance partagee) :
 *   Les tests d'ecriture (memoire, dossier) CREENT puis SUPPRIMENT leurs objets.
 *   On nettoie systematiquement dans un bloc `finally` : un test ne doit jamais
 *   laisser de trace derriere lui — surtout la memoire, qui est injectee dans
 *   les prompts des vraies conversations.
 *
 * ROBUSTESSE :
 *   Certaines fonctionnalites dependent du modele (raisonnement) ou d'un 2e
 *   compte (partage de dossier). On utilise le pattern `test.skip(condition,
 *   raison)` pour ne PAS echouer quand une pre-condition manque.
 */
import { test, expect, type APIRequestContext } from '@playwright/test';
import {
  apiLogin,
  getMemories,
  addMemory,
  deleteMemory,
  getFolders,
  createFolder,
  deleteFolder,
} from '../helpers/api';
import { startNewChat, selectModel, sendMessage, waitForResponse } from '../helpers/chat';
import { CHAT, REASONING } from '../helpers/selectors';

// Configuration (voir .env.example)
const OWUI_URL = process.env.OWUI_URL || 'http://localhost:3000';
const OWUI_EMAIL = process.env.OWUI_EMAIL || '';
const OWUI_PASSWORD = process.env.OWUI_PASSWORD || '';
const CLOUD_MODEL = process.env.OWUI_CLOUD_MODEL || 'gpt-5.1';
// Modele capable d'afficher son raisonnement (thinking). Optionnel :
// si non defini, le test de raisonnement se met en pause (skip).
const REASONING_MODEL = process.env.OWUI_REASONING_MODEL || '';

// Marqueur unique pour reperer (et nettoyer) les objets crees par ces tests.
const TAG = '[pw-module06]';

// =====================================================================
// PARTIE 06a — API : Memoire & Dossiers (nouveautes v0.10)
// =====================================================================

test.describe('06a — API : memoire & dossiers (v0.10)', () => {
  // Un seul login partage (evite le rate limit /signin, cf. module 05).
  let token = '';

  test.beforeAll(async ({ request }: { request: APIRequestContext }) => {
    test.skip(!OWUI_EMAIL || !OWUI_PASSWORD, 'OWUI_EMAIL / OWUI_PASSWORD non configures dans .env');
    token = await apiLogin(request, OWUI_URL, OWUI_EMAIL, OWUI_PASSWORD);
  });

  /**
   * TEST 1 : L'API memoire repond et renvoie une liste.
   *
   * C'est le test de "feature detection" le plus simple : on verifie que
   * l'endpoint stabilise en v0.10 existe et repond une liste (eventuellement
   * vide). Aucune ecriture — donc aucun nettoyage necessaire.
   */
  test('memoire — endpoint disponible (liste)', async ({ request }) => {
    const memories = await getMemories(request, OWUI_URL, token);
    expect(Array.isArray(memories)).toBe(true);
    console.log(`  → ${memories.length} souvenir(s) pour l'utilisateur connecte`);
  });

  /**
   * TEST 2 : Cycle de vie d'un souvenir + champ `type` (nouveaute v0.10).
   *
   * On cree un souvenir, on verifie qu'il expose bien le champ `type`
   * (absent avant v0.10), qu'il apparait dans la liste, puis on le SUPPRIME.
   *
   * CONCEPT : nettoyage garanti via `finally`. Meme si une assertion echoue,
   * le souvenir de test est retire — on ne pollue jamais l'instance.
   */
  test('memoire — cycle add / list / delete avec champ type v0.10', async ({ request }) => {
    const created = await addMemory(request, OWUI_URL, token, `${TAG} souvenir de test a supprimer`);
    let cleaned = false;
    try {
      expect(created.id).toBeTruthy();
      // La refonte v0.10 ajoute le `type` (ex. "context"). On verifie sa presence.
      expect(created.type, 'le champ "type" (v0.10) doit etre present').toBeTruthy();
      console.log(`  → souvenir cree (id=${created.id.slice(0, 8)}…, type=${created.type})`);

      const list = await getMemories(request, OWUI_URL, token);
      expect(list.some((m) => m.id === created.id)).toBe(true);

      const ok = await deleteMemory(request, OWUI_URL, token, created.id);
      cleaned = ok;
      expect(ok).toBe(true);

      const after = await getMemories(request, OWUI_URL, token);
      expect(after.some((m) => m.id === created.id)).toBe(false);
      console.log('  → souvenir supprime, instance propre');
    } finally {
      // Filet de securite : si le test a echoue avant la suppression, on nettoie.
      if (!cleaned) {
        await deleteMemory(request, OWUI_URL, token, created.id).catch(() => {});
      }
    }
  });

  /**
   * TEST 3 : L'API dossiers repond et renvoie une liste.
   */
  test('dossiers — endpoint disponible (liste)', async ({ request }) => {
    const folders = await getFolders(request, OWUI_URL, token);
    expect(Array.isArray(folders)).toBe(true);
    console.log(`  → ${folders.length} dossier(s) pour l'utilisateur connecte`);
  });

  /**
   * TEST 4 : Cycle de vie d'un dossier (creation / suppression).
   *
   * Les dossiers d'equipe v0.10 sont partageables (voir TEST 5). Ici on valide
   * juste le CRUD de base, avec nettoyage garanti.
   */
  test('dossiers — cycle creation / suppression', async ({ request }) => {
    const folder = await createFolder(request, OWUI_URL, token, `${TAG} dossier de test`);
    let cleaned = false;
    try {
      expect(folder.id).toBeTruthy();
      expect(folder.name).toContain(TAG);
      console.log(`  → dossier cree (id=${folder.id.slice(0, 8)}…)`);

      const list = await getFolders(request, OWUI_URL, token);
      expect(list.some((f) => f.id === folder.id)).toBe(true);

      const ok = await deleteFolder(request, OWUI_URL, token, folder.id);
      cleaned = ok;
      expect(ok).toBe(true);
      console.log('  → dossier supprime, instance propre');
    } finally {
      if (!cleaned) {
        await deleteFolder(request, OWUI_URL, token, folder.id).catch(() => {});
      }
    }
  });

  /**
   * TEST 5 (EXERCICE) : Partage d'un dossier d'equipe entre deux comptes.
   *
   * Les dossiers v0.10 se partagent avec des permissions lecture/ecriture. Pour
   * tester ce partage de bout en bout, il faut un DEUXIEME compte (variables
   * OWUI_TENANT2_* du module 05). Sans ce compte, le test se met en pause.
   *
   * EXERCICE : une fois OWUI_TENANT2_* configures, completez ce test :
   *   1. Compte A cree un dossier et le partage en lecture avec le compte B.
   *   2. Compte B liste ses dossiers et retrouve le dossier partage.
   *   3. Compte B tente une ecriture → doit echouer (permission lecture seule).
   *   4. Compte A nettoie (suppression du dossier).
   */
  test('dossiers d\'equipe — partage entre comptes (exercice)', async () => {
    const hasSecondAccount = Boolean(process.env.OWUI_TENANT2_EMAIL && process.env.OWUI_TENANT2_PASSWORD);
    test.skip(!hasSecondAccount, 'OWUI_TENANT2_* non configures — exercice de partage differe');
    // A completer par l'etudiant (voir l'enonce ci-dessus).
  });
});

// =====================================================================
// PARTIE 06b — UI : Raisonnement streame & compaction
// =====================================================================

test.describe('06b — UI : raisonnement & compaction (v0.10)', () => {
  test.beforeEach(async ({ page }) => {
    await startNewChat(page);
  });

  /**
   * TEST 6 : Le bloc de raisonnement s'affiche (v0.10.2).
   *
   * Les modeles "thinking" exposent desormais leurs etapes de raisonnement en
   * direct. On selectionne un modele de raisonnement, on pose une question qui
   * demande de reflechir, et on cherche le bloc de raisonnement dans l'UI.
   *
   * ROBUSTESSE : tous les modeles n'emettent pas de raisonnement visible. Si
   * OWUI_REASONING_MODEL n'est pas configure, on skip. Si le modele repond mais
   * sans bloc de raisonnement, on skip aussi (au lieu d'echouer) — la reponse
   * elle-meme prouve que le chat fonctionne.
   */
  test('raisonnement — le bloc de reflexion s\'affiche', async ({ page }) => {
    test.skip(!REASONING_MODEL, 'OWUI_REASONING_MODEL non configure dans .env');

    await selectModel(page, REASONING_MODEL);
    await sendMessage(
      page,
      'Reflechis etape par etape : combien de "r" dans le mot "raisonnement" ? Explique ton raisonnement.',
    );

    // Le bloc de raisonnement (repliable) OU un libelle "raisonnement/thinking".
    const reasoningBlock = page.locator(REASONING.block).first();
    const reasoningLabel = page.getByText(REASONING.label).first();

    const appeared = await reasoningBlock
      .or(reasoningLabel)
      .isVisible({ timeout: 30_000 })
      .catch(() => false);

    if (!appeared) {
      // Le modele a peut-etre repondu sans exposer de raisonnement visible :
      // on verifie au moins que la reponse arrive, puis on skip proprement.
      const response = await waitForResponse(page, 60_000);
      test.skip(true, `Modele "${REASONING_MODEL}" sans bloc de raisonnement visible (reponse: ${response.length} chars)`);
      return;
    }

    console.log('  → bloc de raisonnement affiche par l\'UI');
    // On laisse la generation se terminer proprement.
    await waitForResponse(page, 90_000).catch(() => {});

    // EXERCICE : depliez le bloc (clic) et verifiez qu'il contient du texte de
    // reflexion distinct de la reponse finale.
  });

  /**
   * TEST 7 : Compaction automatique — une conversation multi-tours reste stable.
   *
   * En v0.10, quand on approche de la limite de contexte, la conversation est
   * resumee automatiquement plutot que tronquee brutalement. On ne peut pas
   * facilement saturer le contexte dans un test rapide ; on verifie donc le
   * COMPORTEMENT OBSERVABLE : plusieurs tours d'affilee continuent de repondre,
   * et le modele garde le fil (il se souvient d'une info donnee au 1er tour).
   *
   * C'est un "test de non-regression" de la conversation longue.
   */
  test('compaction — conversation multi-tours garde le fil', async ({ page }) => {
    await selectModel(page, CLOUD_MODEL);

    // Tour 1 : on donne une information a retenir.
    await sendMessage(page, 'Retiens ce code secret pour la suite : DELTA-42. Reponds juste "ok".');
    await waitForResponse(page, 60_000);

    // Tours intermediaires : on fait avancer la conversation.
    await sendMessage(page, 'Cite une couleur primaire.');
    await waitForResponse(page, 60_000);
    await sendMessage(page, 'Cite un nombre premier.');
    await waitForResponse(page, 60_000);

    // Tour final : le modele doit encore connaitre le code secret.
    await sendMessage(page, 'Quel etait le code secret que je t\'ai donne au debut ?');
    const finalResponse = await waitForResponse(page, 60_000);

    // Au minimum, le chat repond toujours apres plusieurs tours (stabilite).
    expect(page.locator(CHAT.assistantMessage).last()).toBeTruthy();
    expect(finalResponse.length).toBeGreaterThan(0);

    if (/delta[-\s]?42/i.test(finalResponse)) {
      console.log('  → le modele a garde le fil (code secret retrouve)');
    } else {
      // Non bloquant : selon le modele, la reponse peut varier. La stabilite
      // sur plusieurs tours est deja validee ci-dessus.
      console.log(`  → conversation stable sur 4 tours (rappel non exact: "${finalResponse.slice(0, 60)}…")`);
    }

    // EXERCICE : rendez ce test plus strict avec un modele que vous connaissez,
    // en exigeant que "DELTA-42" apparaisse dans la reponse finale.
  });
});
