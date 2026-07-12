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
  // Le bouton du selecteur de modele.
  // IMPORTANT (v0.10) : l'aria-label est localise ("Modele selectionne : X"
  // en fr-FR, "Selected model: X" en en). L'ancien selecteur
  // `button[aria-label^="Select"]` ne matchait donc plus en francais.
  // On privilegie l'ID (independant de la langue et de la version) et on
  // garde des variantes aria-label en repli pour les versions anterieures.
  selectorButton:
    'button[id^="model-selector-"], button[aria-label^="Select" i], button[aria-label^="Modèle" i], button[aria-label^="Sélection" i]',
  // Les modeles sont dans un listbox ARIA. IMPORTANT (v0.10) : l'aria-label
  // est localise ("Modeles disponibles" en fr, "Available models" en en) ;
  // quand le dropdown est ouvert c'est le seul listbox affiche, on cible
  // donc simplement le role, independamment de la langue.
  modelListbox: '[role="listbox"]',
  modelOption: '[role="option"]',
  // Champ de recherche du dropdown (v0.10 : id stable #model-search-input,
  // avec des replis sur le placeholder localise pour les versions anterieures)
  searchInput:
    '#model-search-input, [role="listbox"] input, input[placeholder*="odel" i], input[placeholder*="odèle" i]',
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
  // Outils MCP (v0.8.8+ : le bouton n'a plus d'aria-label stable,
  // utiliser le 2eme bouton du inputContainer — voir module 04)
  availableTools: 'button[aria-label="Available Tools"]',  // legacy, peut ne plus matcher
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

// --- Compte / menu utilisateur ---
// VERIFIE firsthand contre v0.10.2 fr-FR (2026-07, lors de la generation des
// captures du Tour). Le bouton avatar (bas de la sidebar) porte l'aria-label
// localise "Menu utilisateur" (fr) / "User menu" (en) et n'a pas d'ID stable.
// Les entrees du menu (Reglages, Conversations archivees, Deconnexion...) sont
// des <button> cibles par leur libelle via getByRole('button', { name }).
export const ACCOUNT = {
  // Bouton avatar ouvrant le menu utilisateur.
  menuButton:
    'button[aria-label="Menu utilisateur"], button[aria-label="User menu" i]',
  // ATTENTION v0.10.2 fr : l'entree des reglages s'appelle "Reglages"
  // (PAS "Parametres"). Regex tolerante pour les deux libelles fr + l'anglais.
  settingsEntry: /r[ée]glages|param[èe]tres|settings/i,
  // Autres entrees du menu (multilingue)
  logout: /d[ée]connexion|log ?out|sign ?out/i,
  archivedChats: /conversations archiv[ée]es|archived chats/i,
} as const;

// =====================================================================
// Nouveautes v0.10 (voir module 06)
// =====================================================================

// --- Raisonnement / reflexion (v0.10.2 : visualisation live) ---
// La v0.10.2 affiche EN DIRECT les etapes de raisonnement des modeles
// "thinking". Le bloc est generalement un <details> repliable, ou un
// conteneur dont le libelle contient "raisonnement"/"reflexion"/"thinking".
// VERIFIE firsthand contre v0.10.2 (2026-07-02) : avec un modele "thinking"
// (ex. OpenRouter.deepseek/deepseek-r1-0528), ces selecteurs detectent bien le
// bloc de raisonnement rendu en direct (test 06b "raisonnement", 7 passed).
// Restent volontairement larges (l'UI peut deriver d'une version a l'autre).
export const REASONING = {
  // Conteneur repliable du raisonnement
  block:
    'details[class*="reason" i], details[class*="think" i], [class*="reasoning" i], [class*="thinking" i]',
  // Libelle multilingue du bloc (pour getByText)
  label: /raisonnement|r[ée]flexion|r[ée]fl[ée]chi|reasoning|thinking|thought/i,
} as const;

// --- Dossiers (v0.10 : dossiers d'equipe partageables) ---
export const FOLDER = {
  // Bouton de creation d'un dossier dans la sidebar (libelle multilingue)
  newFolderButton: /nouveau dossier|new folder|cr[ée]er un dossier/i,
  // Entree de dossier dans la sidebar
  item: '[data-folder-id], [class*="folder" i]',
  // Option de partage dans le menu contextuel d'un dossier
  shareOption: /partager|share/i,
} as const;

// --- Memoire (v0.10 : refonte, sort de beta) ---
// Chemin VERIFIE firsthand contre v0.10.2 fr-FR (2026-07) :
//   ACCOUNT.menuButton -> ACCOUNT.settingsEntry ("Reglages")
//   -> personalizationTab ("Personnalisation") -> manageButton ("Gerer")
//   -> fenetre "Memoire N" (emptyState visible sur un compte neuf).
export const MEMORY = {
  // Onglet "Personnalisation" dans la fenetre Reglages
  personalizationTab: /personnalisation|personalization/i,
  // Bouton "Gerer" de la section Memoire (ouvre la fenetre de gestion)
  manageButton: /g[ée]rer|manage/i,
  // Etat vide (compte neuf) dans la fenetre de gestion de la memoire
  emptyState: /aucun|les souvenirs|no memories|seront affich/i,
  // Bouton d'ajout d'un souvenir
  addButton: /ajouter un souvenir|add memory/i,
  // (conserve) libelle multilingue de la section (compat module 06)
  settingsLabel: /m[ée]moire|memory|personnalisation|personalization/i,
} as const;
