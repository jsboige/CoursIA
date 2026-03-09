/**
 * Fonctions utilitaires pour interagir avec le chat Open WebUI.
 *
 * POINTS CLES A RETENIR :
 * =======================
 * 1. TipTap Editor : OWUI utilise un editeur rich text TipTap/ProseMirror.
 *    On DOIT utiliser keyboard.type() au lieu de fill() pour declencher
 *    correctement les evenements de l'editeur.
 *
 * 2. Streaming : Les reponses LLM arrivent en streaming (token par token).
 *    Le contenu apparait progressivement dans #response-content-container.
 *    On doit attendre que la generation soit terminee avant d'asserter.
 *
 * 3. Timeouts : Les modeles LLM (surtout locaux) peuvent mettre 30s-2min
 *    pour repondre. Les timeouts sont donc genereux (120s par defaut).
 */
import { type Page, expect } from '@playwright/test';
import { CHAT, MODEL } from './selectors';

/**
 * Ferme les modales qui peuvent apparaitre au premier chargement.
 *
 * Open WebUI affiche souvent un dialogue "Quoi de neuf" (Changelog)
 * apres la premiere connexion ou une mise a jour. Ce modal bloque
 * tous les clics sur la page car il utilise un overlay plein ecran.
 *
 * STRATEGIE : On cherche le bouton de fermeture de la modale
 * et on le clique s'il est visible. Sinon, on passe.
 */
export async function dismissModals(page: Page): Promise<void> {
  // Attendre un court instant que les modales eventuelles apparaissent
  await page.waitForTimeout(1000);

  // Strategie 1 : Cliquer le bouton de fermeture du dialogue (croix ou bouton)
  const closeButtons = [
    // Bouton "Okay, Got it!" ou "Fermer" en bas du changelog
    page.getByRole('button', { name: /okay|got it|fermer|close|d'accord/i }),
    // Bouton croix (X) dans la modale
    page.locator('[role="dialog"] button').filter({ hasText: /×|✕/ }),
    // Bouton croix generique dans une modale
    page.locator('[role="dialog"] button[aria-label*="close" i], [role="dialog"] button[aria-label*="fermer" i]'),
    // Cliquer en dehors de la modale (sur l'overlay)
  ];

  for (const btn of closeButtons) {
    try {
      if (await btn.isVisible({ timeout: 2_000 })) {
        await btn.click({ timeout: 3_000 });
        // Attendre que la modale disparaisse
        await page.locator('[role="dialog"]').waitFor({ state: 'hidden', timeout: 5_000 }).catch(() => {});
        return;
      }
    } catch {
      // Continuer avec le prochain selecteur
    }
  }

  // Strategie 2 : Si aucun bouton trouve, essayer Escape
  const dialog = page.locator('[role="dialog"]');
  if (await dialog.isVisible({ timeout: 1_000 }).catch(() => false)) {
    await page.keyboard.press('Escape');
    await dialog.waitFor({ state: 'hidden', timeout: 5_000 }).catch(() => {});
  }
}

/**
 * Demarre un nouveau chat en naviguant vers la page d'accueil.
 * Plus fiable que de cliquer le bouton "New Chat" dans la sidebar
 * (qui peut etre masque quand la sidebar est repliee).
 *
 * Ferme automatiquement les modales (changelog, etc.) qui peuvent
 * bloquer les interactions.
 */
export async function startNewChat(page: Page): Promise<void> {
  await page.goto('/');
  await dismissModals(page);
  await expect(page.locator(MODEL.selectorButton)).toBeVisible({ timeout: 15_000 });
}

/**
 * Selectionne un modele via le selecteur dropdown.
 * Ouvre le dropdown, recherche le modele par nom, et clique dessus.
 */
export async function selectModel(page: Page, modelName: string): Promise<void> {
  await page.locator(MODEL.selectorButton).click();
  await expect(page.locator(MODEL.modelListbox)).toBeVisible({ timeout: 10_000 });

  // Rechercher dans le champ de recherche du dropdown
  const searchInput = page.locator(
    '[role="menu"] input[type="text"], [role="menu"] input[placeholder]'
  ).first();
  await searchInput.fill(modelName);

  // Cliquer le premier resultat
  await page.locator(MODEL.modelOption).first().click({ timeout: 10_000 });
  await expect(page.locator(MODEL.modelListbox)).not.toBeVisible({ timeout: 5_000 });
}

/**
 * Envoie un message dans le chat.
 *
 * ATTENTION : Utilise keyboard.type() et non fill() !
 * L'editeur TipTap ne reagit pas a fill() car il utilise
 * contentEditable avec des evenements personnalises.
 */
export async function sendMessage(page: Page, message: string): Promise<void> {
  const chatInput = page.locator(CHAT.input);
  await chatInput.click();
  await page.keyboard.type(message, { delay: 10 });
  // Enter envoie le message (Shift+Enter pour retour a la ligne)
  await page.keyboard.press('Enter');
  await expect(page.locator(CHAT.userMessage).last()).toBeVisible({ timeout: 15_000 });
}

/**
 * Attend la fin de la reponse de l'assistant.
 *
 * Strategie : On poll le contenu de #response-content-container
 * jusqu'a ce qu'il ait du texte significatif (> 2 caracteres).
 *
 * Pendant la phase "thinking" (Qwen, Claude) : le container peut
 * afficher du texte de reflexion. On attend que le vrai contenu arrive.
 */
export async function waitForResponse(page: Page, timeoutMs = 120_000): Promise<string> {
  // Attendre que le message assistant apparaisse
  await expect(page.locator(CHAT.assistantMessage).last()).toBeVisible({ timeout: 30_000 });

  // Attendre le contenu complet via polling
  await page.waitForFunction(
    () => {
      const containers = document.querySelectorAll('#response-content-container');
      const last = containers[containers.length - 1];
      return last && last.textContent && last.textContent.trim().length > 2;
    },
    undefined,
    { timeout: timeoutMs, polling: 1000 },
  ).catch(() => {});

  // Petit delai pour le rendu final Svelte
  await page.waitForTimeout(500);

  // Extraire le texte de la reponse
  const contentContainer = page.locator(CHAT.assistantMessage).last()
    .locator('#response-content-container');
  const content = await contentContainer.innerText({ timeout: 5_000 }).catch(() => '');
  if (content.trim()) return content.trim();

  // Fallback : texte complet du message assistant
  return await page.locator(CHAT.assistantMessage).last().innerText();
}

/**
 * Envoie un message et attend la reponse complete.
 * Combine sendMessage() + waitForResponse().
 */
export async function chat(page: Page, message: string, timeoutMs = 120_000): Promise<string> {
  await sendMessage(page, message);
  return await waitForResponse(page, timeoutMs);
}

/**
 * Verifie si un service est accessible (HEAD request).
 * Utile pour skip conditionnel quand un service externe est indisponible.
 */
export async function isServiceAvailable(page: Page, url: string): Promise<boolean> {
  try {
    const response = await page.request.get(url, { timeout: 5_000 });
    return response.ok();
  } catch {
    return false;
  }
}
