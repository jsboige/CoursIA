/**
 * Selecteurs CSS centralises pour les tests E2E Open WebUI.
 *
 * POURQUOI CENTRALISER LES SELECTEURS ?
 * ======================================
 * 1. Maintenance : Si OWUI change un ID ou une classe, on corrige a un seul endroit
 * 2. Lisibilite : Les tests utilisent des noms semantiques (CHAT.input vs '#chat-input')
 * 3. Documentation : Les commentaires expliquent les choix de selecteurs
 *
 * STRATEGIES DE SELECTION (par ordre de preference) :
 * - IDs : Les plus stables (#chat-input, #new-chat-button)
 * - Roles ARIA : Accessibles et resilients (button[aria-label="..."])
 * - Attributs data-* : Conçus pour les tests (rarement presents dans OWUI)
 * - Classes CSS : Fragiles, eviter si possible (.chat-user, .chat-assistant)
 *
 * NOTE : Open WebUI utilise des labels localises (francais quand locale=fr-FR).
 * Preferer les selecteurs independants de la langue (IDs, roles).
 * Pour les labels localises, utiliser des regex : page.getByRole('button', { name: /reg[ée]n/i })
 */

// --- Authentification ---
export const AUTH = {
  emailInput: 'input[autocomplete="email"]',
  passwordInput: 'input[type="password"]',
  submitButton: 'button[type="submit"]',
  authPage: '#auth-page',
} as const;

// --- Navigation ---
export const NAV = {
  chatSearch: '#chat-search',
  newChatButton: '#new-chat-button',
  chatContextMenu: '#chat-context-menu-button',
} as const;

// --- Selection de modele ---
export const MODEL = {
  // Matche "Select a model" (vide) et "Selected model: X" (avec defaut)
  selectorButton: 'button[aria-label^="Select"]',
  // Les modeles sont dans un listbox ARIA
  modelListbox: '[role="listbox"][aria-label="Available models"]',
  modelOption: '[role="option"]',
  addModelButton: 'button[aria-label="Add Model"]',
} as const;

// --- Chat ---
export const CHAT = {
  // L'editeur TipTap/ProseMirror (PAS un textarea standard !)
  input: '#chat-input',
  inputContainer: '#chat-input-container',
  submitButton: '#chat-input-container button[type="submit"]',
  // Messages dans le fil de conversation
  userMessage: '.chat-user',
  assistantMessage: '.chat-assistant',
  // Bouton de statut (apparait apres la generation)
  statusToggle: 'button[aria-label="Toggle status history"]',
  // Boutons d'edition
  saveEditButton: '#save-edit-message-button',
  closeEditButton: '#close-edit-message-button',
  confirmEditButton: '#confirm-edit-message-button',
  // Outils MCP
  availableTools: 'button[aria-label="Available Tools"]',
} as const;

// --- Partage ---
export const SHARE = {
  shareButton: '#chat-share-button',
  copyAndShareButton: '#copy-and-share-chat-button',
} as const;

// --- Barre laterale ---
export const SIDEBAR = {
  searchContainer: '#search-container',
} as const;
