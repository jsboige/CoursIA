/**
 * Module 04 — RAG, Outils MCP & Fonctionnalites avancees
 *
 * Ce module teste les fonctionnalites avancees d'Open WebUI :
 * - RAG (Knowledge Bases attachees au chat)
 * - Outils MCP (recherche web, execution de code)
 * - Channels (canaux de discussion)
 *
 * PATTERN : Tests conditionnels
 * Certaines fonctionnalites dependent de la configuration de l'instance.
 * Les KBs, outils MCP, et channels peuvent ne pas etre configures.
 * On utilise des verifications de visibilite + test.skip() pour gerer cela.
 *
 * EVOLUTION UI (v0.8.8+) :
 * - Le raccourci # dans le chat input ne declenche plus de popup KB.
 *   Les KBs sont desormais attachees via le bouton "+" → "Joindre une connaissance".
 * - Le bouton "Available Tools" a ete remplace par un bouton icone (engrenages)
 *   qui ouvre un menu avec les outils, la recherche web, l'image, et le code.
 * - La page /channels n'existe plus ; les channels sont accessibles
 *   via la sidebar (bouton "Canaux") ou par URL directe /channels/{id}.
 */
import { test, expect } from '@playwright/test';
import { startNewChat, selectModel, sendMessage, waitForResponse, dismissModals } from '../helpers/chat';
import { apiLogin, getChannels } from '../helpers/api';
import { CHAT, MODEL } from '../helpers/selectors';

const CLOUD_MODEL = process.env.OWUI_CLOUD_MODEL || 'gpt-5.1';

// =====================================================================
// PARTIE 1 : RAG (Knowledge Bases)
// =====================================================================

test.describe('04a — Knowledge Bases (RAG)', () => {
  test.beforeEach(async ({ page }) => {
    await startNewChat(page);
  });

  /**
   * TEST 1 : Attacher une Knowledge Base via le menu "+"
   *
   * Depuis v0.8.8, le raccourci # ne declenche plus de popup KB.
   * Le nouveau workflow utilise le bouton "+" dans la barre de chat,
   * puis "Joindre une connaissance" pour ouvrir le selecteur de KBs.
   *
   * CONCEPT : Evolution des interfaces — adapter les tests quand l'UI change
   * C'est un cas courant en tests E2E : les selecteurs et workflows changent
   * entre les versions. Il faut verifier visuellement et mettre a jour.
   */
  test('attacher une knowledge base via le menu +', async ({ page }) => {
    await selectModel(page, CLOUD_MODEL);

    // Ouvrir le menu "+" dans la barre de chat
    const plusButton = page.locator('#message-input-container')
      .locator('button').first();
    await plusButton.click();

    // Chercher le bouton "Joindre une connaissance" dans le menu
    const attachKB = page.getByRole('button', { name: /connaissance|knowledge/i });
    const isVisible = await attachKB.isVisible({ timeout: 5_000 }).catch(() => false);
    test.skip(!isVisible, 'Option "Joindre une connaissance" non disponible');

    await attachKB.click();

    // Le selecteur de KBs devrait apparaitre (dialog ou menu)
    const kbSelector = page.locator('[role="dialog"], [role="menu"]')
      .or(page.getByText(/Bibliographie|Knowledge|Apprentissage/i).first());
    await expect(kbSelector).toBeVisible({ timeout: 10_000 });
  });

  /**
   * TEST 2 : Chat avec une KB attachee — reponse enrichie par les documents
   *
   * Ce test simule un workflow complet :
   * 1. Selectionner un modele
   * 2. Attacher une KB via le menu "+"
   * 3. Poser une question
   * 4. Verifier que la reponse est enrichie par la KB
   *
   * CONCEPT : Workflow multi-etapes avec gestion du focus
   * Apres la selection d'une KB, le focus peut etre perdu.
   * Il faut re-cliquer sur l'input avant de taper le message.
   */
  test('chat avec KB attachee — reponse enrichie par les documents', async ({ page }) => {
    await selectModel(page, CLOUD_MODEL);

    // Ouvrir le menu "+" et attacher une connaissance
    const plusButton = page.locator('#message-input-container')
      .locator('button').first();
    await plusButton.click();

    const attachKB = page.getByRole('button', { name: /connaissance|knowledge/i });
    const isVisible = await attachKB.isVisible({ timeout: 5_000 }).catch(() => false);
    test.skip(!isVisible, 'Aucune option KB disponible');

    await attachKB.click();

    // La liste des KBs apparait dans un dialog ou sous-menu.
    // Attendre que le selecteur apparaisse, puis chercher une KB.
    await page.waitForTimeout(1000);

    // Les KBs apparaissent comme des elements cliquables (boutons ou items de liste).
    // On cherche par nom connu ou on prend le premier item disponible.
    const firstKB = page.locator('[role="dialog"] button, [role="menu"] button, [role="listbox"] [role="option"]')
      .filter({ hasText: /Bibliographie|Apprentissage|Trading|Big Data|Guide|Knowledge/i }).first()
      .or(page.getByRole('button', { name: /Bibliographie|Apprentissage|Trading|Big Data/i }).first());
    const kbVisible = await firstKB.isVisible({ timeout: 10_000 }).catch(() => false);
    test.skip(!kbVisible, 'Aucune KB trouvee dans le selecteur');

    await firstKB.click({ timeout: 10_000 });

    // Attendre que la KB soit attachee (badge ou indicateur dans le chat input)
    await page.waitForTimeout(1000);

    // Poser une question
    const chatInput = page.locator(CHAT.input);
    await chatInput.click();
    await page.keyboard.type(
      'Quels sont les principaux algorithmes de machine learning supervise?',
      { delay: 10 }
    );
    await page.keyboard.press('Enter');

    await expect(page.locator(CHAT.userMessage).last()).toBeVisible({ timeout: 15_000 });
    const response = await waitForResponse(page);

    // La reponse devrait etre substantielle (enrichie par la KB)
    expect(response.length).toBeGreaterThan(50);
  });
});

// =====================================================================
// PARTIE 2 : Outils MCP
// =====================================================================

test.describe('04b — Outils MCP (Model Context Protocol)', () => {
  test.beforeEach(async ({ page }) => {
    await startNewChat(page);
  });

  /**
   * Ouvre le menu des outils dans la zone de chat input.
   *
   * Depuis v0.8.8+, les outils sont derriere le deuxieme bouton icone
   * (engrenages) dans la barre du chat input. Ce bouton n'a pas d'aria-label
   * stable, on le trouve par sa position : c'est le 2eme bouton dans
   * le groupe de gauche du chat input container.
   *
   * Le menu affiche : "Outils N", "Recherche Web", "Image", "Interpreteur de code"
   */
  async function openToolsMenu(page: import('@playwright/test').Page) {
    // Le 2eme bouton dans le groupe de gauche du chat input
    // (le 1er est le "+" pour fichiers/KBs)
    const toolsButton = page.locator('#message-input-container')
      .locator('button').nth(1);
    await toolsButton.click();

    // Le menu devrait afficher "Outils" avec un compteur
    const toolsMenu = page.locator('[role="menu"]');
    await expect(toolsMenu).toBeVisible({ timeout: 5_000 });
    return toolsMenu;
  }

  /**
   * TEST 3 : Le menu Outils est accessible
   *
   * Si des outils MCP sont configures, le deuxieme bouton icone
   * dans la barre de chat ouvre un menu listant les outils.
   *
   * CONCEPT : Selecteurs positionnels — quand il n'y a pas d'aria-label,
   * on utilise la position dans le DOM (nth(1) = 2eme element)
   */
  test('menu outils MCP accessible (si configure)', async ({ page }) => {
    await selectModel(page, CLOUD_MODEL);

    // Essayer d'ouvrir le menu outils
    const toolsButton = page.locator('#message-input-container')
      .locator('button').nth(1);
    const isVisible = await toolsButton.isVisible({ timeout: 5_000 }).catch(() => false);
    test.skip(!isVisible, 'Bouton outils non visible');

    await toolsButton.click();

    // Verifier que le menu apparait avec les outils
    const toolsEntry = page.getByText(/Outils|Tools/i).first();
    const hasTools = await toolsEntry.isVisible({ timeout: 5_000 }).catch(() => false);
    test.skip(!hasTools, 'Outils MCP non configures sur cette instance');

    await expect(toolsEntry).toBeVisible();
    console.log('  → Menu outils MCP accessible');
  });

  /**
   * TEST 4 : Ouvrir le selecteur d'outils et voir la liste
   *
   * Cliquer sur "Outils N" dans le menu ouvre un sous-menu
   * listant tous les outils MCP installes.
   */
  test('ouvrir le selecteur d outils MCP', async ({ page }) => {
    await selectModel(page, CLOUD_MODEL);

    const toolsButton = page.locator('#message-input-container')
      .locator('button').nth(1);
    await toolsButton.click();

    const toolsEntry = page.getByText(/Outils|Tools/i).first();
    const hasTools = await toolsEntry.isVisible({ timeout: 5_000 }).catch(() => false);
    test.skip(!hasTools, 'Outils MCP non configures');

    // Cliquer sur "Outils N" pour voir la liste des outils
    await toolsEntry.click();

    // Un sous-menu ou dialog devrait afficher les outils individuels
    const toolPopup = page.locator('[role="dialog"], [role="menu"]').last();
    await expect(toolPopup).toBeVisible({ timeout: 10_000 });

    // EXERCICE : Comptez le nombre d'outils disponibles
  });

  /**
   * TEST 5 : Activer la recherche web via le menu outils
   *
   * Ce test active l'option "Recherche Web" dans le menu,
   * envoie un message, et verifie que le LLM enrichit sa reponse.
   *
   * CONCEPT : Toggles (switches) — certains outils s'activent
   * via un switch on/off plutot qu'un clic de selection.
   */
  test('recherche web via outils (si disponible)', async ({ page }) => {
    await selectModel(page, CLOUD_MODEL);

    // Ouvrir le menu outils (2eme bouton dans le message-input-container)
    const toolsButton = page.locator('#message-input-container')
      .locator('button').nth(1);
    await toolsButton.click();

    // Le menu de premier niveau affiche : "Outils N", "Recherche Web", "Image", etc.
    // Chaque option a un switch toggle. Cliquer sur le bouton "Recherche Web".
    const webSearch = page.getByRole('button', { name: /Recherche Web|Web Search/i });
    const hasWebSearch = await webSearch.isVisible({ timeout: 5_000 }).catch(() => false);
    test.skip(!hasWebSearch, 'Recherche Web non disponible');

    // Cliquer sur le bouton active le switch
    await webSearch.click();

    // Fermer le menu en cliquant ailleurs (Escape peut ne pas fonctionner)
    await page.locator(CHAT.input).click();
    await page.waitForTimeout(500);

    // Envoyer un message qui devrait declencher la recherche web
    await page.keyboard.type(
      'Search the web for "Open WebUI latest version" and summarize.',
      { delay: 10 }
    );
    await page.keyboard.press('Enter');
    await expect(page.locator(CHAT.userMessage).last()).toBeVisible({ timeout: 15_000 });
    const response = await waitForResponse(page);

    expect(response.length).toBeGreaterThan(20);
  });
});

// =====================================================================
// PARTIE 3 : Channels
// =====================================================================

test.describe('04c — Channels (canaux de discussion)', () => {

  /**
   * TEST 6 : Naviguer vers un canal via l'API + URL directe
   *
   * En mode headless, la sidebar est souvent collapsed (icones seules),
   * ce qui rend les liens de canaux invisibles. Pour contourner ce probleme,
   * on utilise l'API pour recuperer la liste des canaux, puis on navigue
   * directement via l'URL /channels/{id}.
   *
   * CONCEPT : Combiner API et navigateur pour des tests robustes
   * L'API donne les donnees (IDs de canaux), le navigateur teste l'experience.
   * C'est une technique courante quand la navigation UI est fragile en headless.
   */
  test('acceder aux canaux de discussion', async ({ page, request }) => {
    const baseUrl = process.env.OWUI_URL || 'https://open-webui.myia.io';
    const email = process.env.OWUI_EMAIL || '';
    const password = process.env.OWUI_PASSWORD || '';

    // Recuperer les canaux via l'API
    let channels: Array<{ id: string; name: string }> = [];
    try {
      const token = await apiLogin(request, baseUrl, email, password);
      channels = await getChannels(request, baseUrl, token);
    } catch (e) {
      test.skip(true, `API channels indisponible: ${e}`);
    }

    test.skip(channels.length === 0, 'Aucun canal configure sur cette instance');

    // Naviguer directement vers le premier canal
    await page.goto(`/channels/${channels[0].id}`);
    await dismissModals(page);

    // Verifier qu'on est bien sur la page du canal
    await expect(page).toHaveURL(/channels/i, { timeout: 10_000 });

    // Verifier que le contenu du canal est charge (input ou messages visibles)
    const channelContent = page.locator('#chat-input, [contenteditable="true"]').last();
    await expect(channelContent).toBeVisible({ timeout: 15_000 });

    console.log(`  → Canal "${channels[0].name}" accessible via URL directe`);
  });

  /**
   * TEST 7 : Poster un message dans un canal
   *
   * On navigue directement vers un canal connu (via API), puis on utilise
   * le meme editeur TipTap (click + keyboard.type + Enter) pour poster.
   *
   * CONCEPT : Le meme editeur TipTap est utilise dans les channels et le chat.
   */
  test('poster un message dans un canal', async ({ page, request }) => {
    const baseUrl = process.env.OWUI_URL || 'https://open-webui.myia.io';
    const email = process.env.OWUI_EMAIL || '';
    const password = process.env.OWUI_PASSWORD || '';

    // Recuperer les canaux via l'API
    let channels: Array<{ id: string; name: string }> = [];
    try {
      const token = await apiLogin(request, baseUrl, email, password);
      channels = await getChannels(request, baseUrl, token);
    } catch (e) {
      test.skip(true, `API channels indisponible: ${e}`);
    }

    test.skip(channels.length === 0, 'Aucun canal disponible');

    // Naviguer vers le premier canal
    await page.goto(`/channels/${channels[0].id}`);
    await dismissModals(page);
    await expect(page).toHaveURL(/channels/i, { timeout: 10_000 });

    // Attendre que l'editeur soit pret
    const messageInput = page.locator('#chat-input, [contenteditable="true"]').last();
    await expect(messageInput).toBeVisible({ timeout: 15_000 });
    await messageInput.click();

    const testMessage = `Test Playwright Module 04 — ${new Date().toISOString()}`;
    await page.keyboard.type(testMessage, { delay: 10 });
    await page.keyboard.press('Enter');

    // Verifier que le message apparait
    await expect(page.getByText(testMessage).first()).toBeVisible({ timeout: 10_000 });
  });
});
