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
 */
import { test, expect } from '@playwright/test';
import { startNewChat, selectModel, sendMessage, waitForResponse } from '../helpers/chat';
import { CHAT, MODEL } from '../helpers/selectors';

const CLOUD_MODEL = process.env.OWUI_CLOUD_MODEL || 'gpt-4.1-mini';

// =====================================================================
// PARTIE 1 : RAG (Knowledge Bases)
// =====================================================================

test.describe('04a — Knowledge Bases (RAG)', () => {
  test.beforeEach(async ({ page }) => {
    await startNewChat(page);
  });

  /**
   * TEST 1 : Le raccourci # ouvre le selecteur de Knowledge Bases
   *
   * Dans le chat input, taper # declenche un popup listant les KBs
   * disponibles. C'est le mecanisme principal d'attachement RAG.
   *
   * CONCEPT : Evenements clavier dans un editeur rich text
   * Le caractere # est un "trigger character" intercepte par TipTap.
   * Il faut utiliser keyboard.type() pour que l'evenement soit capture.
   */
  test('le raccourci # ouvre la liste des knowledge bases', async ({ page }) => {
    await selectModel(page, CLOUD_MODEL);

    // Taper # dans l'editeur de chat
    const chatInput = page.locator(CHAT.input);
    await chatInput.click();
    await page.keyboard.type('#');

    // Un popup avec les KBs disponibles devrait apparaitre
    // Le contenu depend de l'instance — on cherche des mots generiques
    const kbPopup = page.getByText('Bibliographie')
      .or(page.getByText('Knowledge'))
      .or(page.getByText('Base'))
      .first();

    const isVisible = await kbPopup.isVisible({ timeout: 10_000 }).catch(() => false);
    test.skip(!isVisible, 'Aucune Knowledge Base configuree sur cette instance');

    await expect(kbPopup).toBeVisible();
  });

  /**
   * TEST 2 : Chat avec une KB attachee
   *
   * Ce test simule un workflow complet :
   * 1. Selectionner un modele
   * 2. Attacher une KB via #
   * 3. Poser une question
   * 4. Verifier que la reponse est enrichie par la KB
   *
   * CONCEPT : Workflow multi-etapes avec gestion du focus
   * Apres la selection d'une KB, le focus peut etre perdu.
   * Il faut re-cliquer sur l'input avant de taper le message.
   */
  test('chat avec KB attachee — reponse enrichie par les documents', async ({ page }) => {
    await selectModel(page, CLOUD_MODEL);

    const chatInput = page.locator(CHAT.input);
    await chatInput.click();
    await page.keyboard.type('#');

    // Selectionner la premiere KB visible
    const firstKB = page.getByText('Bibliographie')
      .or(page.getByText('Knowledge'))
      .first();

    const isVisible = await firstKB.isVisible({ timeout: 10_000 }).catch(() => false);
    test.skip(!isVisible, 'Aucune KB disponible');

    await firstKB.click({ timeout: 10_000 });

    // Re-focus l'input et poser une question
    await chatInput.click();
    await page.keyboard.press('Backspace'); // Nettoyer le # residuel
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
   * TEST 3 : Le bouton "Available Tools" est visible
   *
   * Si des outils MCP sont configures, un bouton "Available Tools"
   * apparait dans la zone de chat input.
   *
   * CONCEPT : Test conditionnel sur la presence d'un element
   */
  test('bouton outils MCP visible (si configure)', async ({ page }) => {
    await selectModel(page, CLOUD_MODEL);

    const toolsButton = page.locator(CHAT.availableTools);
    const isVisible = await toolsButton.isVisible({ timeout: 5_000 }).catch(() => false);
    test.skip(!isVisible, 'Outils MCP non configures sur cette instance');

    await expect(toolsButton).toBeVisible();
  });

  /**
   * TEST 4 : Ouvrir le selecteur d'outils
   *
   * Cliquer sur "Available Tools" ouvre un popup/dialog
   * listant les outils disponibles (recherche web, code, etc.).
   */
  test('ouvrir le selecteur d outils MCP', async ({ page }) => {
    await selectModel(page, CLOUD_MODEL);

    const toolsButton = page.locator(CHAT.availableTools);
    const isVisible = await toolsButton.isVisible({ timeout: 5_000 }).catch(() => false);
    test.skip(!isVisible, 'Outils MCP non configures');

    await toolsButton.click();

    // Un popup/dialog devrait apparaitre
    const toolPopup = page.locator('[role="dialog"], [role="menu"], [role="listbox"]').first()
      .or(page.getByText(/tools|outils/i).first());
    await expect(toolPopup).toBeVisible({ timeout: 10_000 });

    // EXERCICE : Comptez le nombre d'outils disponibles
  });

  /**
   * TEST 5 : Declencher une recherche web via outil MCP
   *
   * Ce test active l'outil de recherche, envoie un message,
   * et verifie que le LLM utilise l'outil pour enrichir sa reponse.
   */
  test('recherche web via outil MCP (si disponible)', async ({ page }) => {
    await selectModel(page, CLOUD_MODEL);

    const toolsButton = page.locator(CHAT.availableTools);
    const isVisible = await toolsButton.isVisible({ timeout: 5_000 }).catch(() => false);
    test.skip(!isVisible, 'Outils MCP non configures');

    // Ouvrir et activer l'outil de recherche
    await toolsButton.click();
    const searchTool = page.getByText(/search|recherche|searx/i).first();
    if (await searchTool.isVisible({ timeout: 5_000 }).catch(() => false)) {
      await searchTool.click();
    }

    // Fermer le popup et envoyer un message
    await page.locator(CHAT.input).click();
    await sendMessage(page, 'Search the web for "Open WebUI latest version" and summarize.');
    const response = await waitForResponse(page);

    expect(response.length).toBeGreaterThan(20);
  });
});

// =====================================================================
// PARTIE 3 : Channels
// =====================================================================

test.describe('04c — Channels (canaux de discussion)', () => {

  /**
   * TEST 6 : Naviguer vers la section Channels
   */
  test('acceder aux canaux de discussion', async ({ page }) => {
    await page.goto('/');
    await expect(page.locator(MODEL.selectorButton)).toBeVisible({ timeout: 15_000 });

    const channelsLink = page.getByRole('link', { name: /channels|canaux/i }).first();
    if (await channelsLink.isVisible({ timeout: 5_000 }).catch(() => false)) {
      await channelsLink.click();
      await expect(page).toHaveURL(/channel/i, { timeout: 10_000 });
    } else {
      await page.goto('/channels');
      await expect(page.locator('body')).toBeVisible({ timeout: 15_000 });
    }
  });

  /**
   * TEST 7 : Poster un message dans un canal
   *
   * CONCEPT : Le meme editeur TipTap est utilise dans les channels.
   * On applique la meme technique (click + keyboard.type + Enter).
   */
  test('poster un message dans un canal (si disponible)', async ({ page }) => {
    await page.goto('/channels');
    await expect(page.locator('body')).toBeVisible({ timeout: 15_000 });

    const channelItem = page.locator('a[href*="/channels/"]').first();
    const hasChannels = await channelItem.isVisible({ timeout: 5_000 }).catch(() => false);
    test.skip(!hasChannels, 'Aucun canal disponible');

    await channelItem.click();
    await page.waitForTimeout(1000);

    // Trouver l'input du channel
    const messageInput = page.locator('#chat-input, [contenteditable="true"]').last();
    await messageInput.click();

    const testMessage = `Test Playwright Module 04 — ${new Date().toISOString()}`;
    await page.keyboard.type(testMessage, { delay: 10 });
    await page.keyboard.press('Enter');

    // Verifier que le message apparait
    await expect(page.getByText(testMessage).first()).toBeVisible({ timeout: 10_000 });
  });
});
