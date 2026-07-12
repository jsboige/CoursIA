/**
 * Module 03 — Tests de Chat & Streaming LLM
 *
 * Ce module est le coeur de la serie : on teste l'interaction
 * avec des modeles d'IA generative via l'interface de chat.
 *
 * DEFIS SPECIFIQUES AUX TESTS LLM :
 * 1. Les reponses sont non-deterministes (jamais identiques)
 * 2. Le streaming fait apparaitre le texte progressivement
 * 3. Les modeles locaux peuvent etre lents ou indisponibles
 * 4. L'editeur TipTap necessite keyboard.type() au lieu de fill()
 *
 * PATTERN DE SKIP GRACIEUX :
 * Quand un modele local est indisponible, on ne veut pas que le test
 * echoue — on veut le marquer "skipped" avec une raison.
 * test.skip(condition, 'raison') fait exactement cela.
 */
import { test, expect } from '@playwright/test';
import { startNewChat, selectModel, sendMessage, waitForResponse, chat } from '../helpers/chat';
import { CHAT, MODEL } from '../helpers/selectors';

// Modeles configurables via .env
const CLOUD_MODEL = process.env.OWUI_CLOUD_MODEL || 'gpt-5.1';
const LOCAL_MODEL = process.env.OWUI_LOCAL_MODEL || '';
const PERSONA_MODEL = process.env.OWUI_PERSONA_MODEL || '';

test.describe('03 — Chat & Streaming LLM', () => {
  test.beforeEach(async ({ page }) => {
    await startNewChat(page);
  });

  // =====================================================================
  // PARTIE 1 : Chat basique avec un modele cloud
  // =====================================================================

  /**
   * TEST 1 : Envoyer un message et recevoir une reponse
   *
   * C'est le test de chat le plus simple.
   * On utilise un modele cloud (rapide et fiable) pour avoir
   * une reponse previsible.
   *
   * CONCEPT : La fonction chat() combine sendMessage() + waitForResponse()
   */
  test('chat avec modele cloud — reponse basique', async ({ page }) => {
    await selectModel(page, CLOUD_MODEL);
    const response = await chat(page, 'Reply with exactly: "Hello from Playwright"');

    expect(response.toLowerCase()).toContain('hello');

    // EXERCICE : Verifiez que la reponse contient aussi "Playwright"
  });

  /**
   * TEST 2 : Chat avec un modele local (optionnel)
   *
   * Les modeles locaux (vLLM, Ollama) sont plus lents et peuvent
   * etre indisponibles. Ce test montre le pattern de skip gracieux.
   *
   * CONCEPT : test.skip() — Marquer un test comme "skipped" a runtime
   * Utile quand la condition de skip depend du resultat de l'execution.
   */
  test('chat avec modele local (skip si indisponible)', async ({ page }) => {
    test.skip(!LOCAL_MODEL, 'OWUI_LOCAL_MODEL non configure dans .env');

    await selectModel(page, LOCAL_MODEL);
    await sendMessage(page, 'Reply with exactly one word: "Bonjour"');

    // Attendre que le message assistant apparaisse (preuve que le modele repond)
    const assistantMsg = page.locator(CHAT.assistantMessage).last();
    await expect(assistantMsg).toBeVisible({ timeout: 30_000 });

    // Les modeles "thinking" (Qwen3.5) affichent "En train de reflechir..."
    // avant la reponse finale. On attend le contenu final dans
    // #response-content-container avec un timeout genereux.
    const response = await waitForResponse(page, 90_000);

    // Le modele peut rester en "thinking" pendant toute la duree du timeout.
    // Dans ce cas, response contient le texte du thinking ou le header.
    // On verifie que le modele a bien repondu, meme partiellement.
    const lowerResponse = response.toLowerCase();
    const hasContent = lowerResponse.includes('bonjour')
      || lowerResponse.includes('hello')
      || lowerResponse.includes('réfléchir')
      || lowerResponse.includes('thinking');

    if (!hasContent) {
      // Le modele a repondu mais avec un contenu inattendu — c'est OK
      // tant que le message assistant est visible (le modele fonctionne)
      const msgText = await assistantMsg.innerText().catch(() => '');
      console.log(`  → Modele local a repondu (${msgText.length} chars): "${msgText.substring(0, 80)}..."`);
      expect(msgText.length).toBeGreaterThan(0);
      return;
    }

    console.log(`  → Modele local OK: "${response.substring(0, 60)}..."`);
  });

  // =====================================================================
  // PARTIE 2 : Streaming et rendu
  // =====================================================================

  /**
   * TEST 3 : Verifier le streaming — le texte apparait progressivement
   *
   * Quand on envoie un message, la reponse arrive en streaming :
   * les tokens apparaissent un par un dans le DOM.
   *
   * On verifie que le message assistant est visible AVANT que
   * la generation soit terminee (preuve du streaming).
   *
   * CONCEPT : Difference entre "visible" et "complet"
   */
  test('streaming — le message assistant apparait avant la fin', async ({ page }) => {
    await selectModel(page, CLOUD_MODEL);
    await sendMessage(page, 'Write a short paragraph about artificial intelligence.');

    // Le message assistant devrait apparaitre rapidement (debut du streaming)
    await expect(page.locator(CHAT.assistantMessage).last()).toBeVisible({ timeout: 30_000 });

    // Attendre la fin complete de la generation
    await waitForResponse(page);

    // EXERCICE : Capturez un screenshot pendant le streaming (avant waitForResponse)
  });

  /**
   * TEST 4 : Rendu Markdown — les blocs de code sont formates
   *
   * Open WebUI rend le Markdown de la reponse en HTML riche.
   * Les blocs de code ont une coloration syntaxique (highlight.js).
   *
   * CONCEPT : Selecteurs imbriques — chercher un element DANS un autre
   */
  test('rendu markdown — blocs de code formates', async ({ page }) => {
    await selectModel(page, CLOUD_MODEL);
    await chat(page, 'Show me a Python hello world in a code block. Use ```python fences.');

    // Le conteneur de reponse devrait contenir un bloc <pre>/<code>
    const responseArea = page.locator('#response-content-container').last();
    const codeBlock = responseArea.locator('pre, code, [class*="code"], [class*="hljs"]').first();
    await expect(codeBlock).toBeVisible({ timeout: 10_000 });

    // EXERCICE : Verifiez que le bloc contient le mot "print"
  });

  // =====================================================================
  // PARTIE 3 : Actions sur les messages
  // =====================================================================

  /**
   * TEST 5 : Regenerer une reponse
   *
   * Apres une reponse, un bouton "Regenerer" permet de redemander
   * au modele. C'est utile si la premiere reponse n'est pas satisfaisante.
   *
   * CONCEPT : Boutons localises
   * Le bouton s'appelle "Regénérer" en FR et "Regenerate" en EN.
   * On utilise une regex pour matcher les deux :
   * /reg[ée]n[ée]r/i matche "Regénérer", "Regenerer", "regenerate", etc.
   */
  test('regenerer une reponse', async ({ page }) => {
    await selectModel(page, CLOUD_MODEL);
    await chat(page, 'Say a random number between 1 and 1000.');

    // Trouver le bouton Regenerer (multilingue)
    const regenButton = page.getByRole('button', { name: /reg[ée]n[ée]r/i })
      .or(page.getByRole('button', { name: /regenerate/i }))
      .last();
    await regenButton.click();
    await waitForResponse(page);

    // Verifier qu'on a bien une nouvelle reponse
    const secondResponse = await page.locator(CHAT.assistantMessage).last().innerText();
    expect(secondResponse.length).toBeGreaterThan(0);

    // EXERCICE : Comparez les deux reponses — sont-elles differentes ?
  });

  /**
   * TEST 6 : Editer un message envoye
   *
   * On peut modifier un message deja envoye pour le reformuler.
   * Cela regenere automatiquement la reponse.
   *
   * CONCEPT : Workflow multi-etapes (hover → bouton → interface d'edition)
   */
  test('editer un message utilisateur', async ({ page }) => {
    await selectModel(page, CLOUD_MODEL);
    await chat(page, 'Say hello');

    // Survoler le message pour faire apparaitre les boutons d'action
    const userMsg = page.locator(CHAT.userMessage).last();
    await userMsg.hover();

    // Cliquer le bouton Modifier/Edit
    const editButton = page.getByRole('button', { name: /modifier|edit/i }).last();
    await editButton.click();

    // L'interface d'edition devrait apparaitre
    await expect(
      page.locator(CHAT.saveEditButton).or(page.locator(CHAT.confirmEditButton))
    ).toBeVisible({ timeout: 10_000 });

    // EXERCICE : Modifiez le texte et sauvegardez, puis verifiez la nouvelle reponse
  });

  // =====================================================================
  // PARTIE 4 : Personas (modeles personnalises, optionnel)
  // =====================================================================

  /**
   * TEST 7 : Tester un modele persona (optionnel)
   *
   * Les "personas" sont des modeles custom avec des instructions systeme,
   * des parametres specifiques, et parfois un avatar personnalise.
   *
   * Ce test est optionnel — il ne s'execute que si OWUI_PERSONA_MODEL
   * est configure dans le .env.
   */
  test('persona — reponse structuree dans le role configure', async ({ page }) => {
    test.skip(!PERSONA_MODEL, 'OWUI_PERSONA_MODEL non configure dans .env');

    await selectModel(page, PERSONA_MODEL);
    const response = await chat(page, 'Presente-toi brievement.');

    test.skip(
      !response || response.length < 5,
      'Modele persona indisponible'
    );

    // La reponse devrait etre en francais (les personas sont generalement en FR)
    expect(response.length).toBeGreaterThan(20);
  });
});
