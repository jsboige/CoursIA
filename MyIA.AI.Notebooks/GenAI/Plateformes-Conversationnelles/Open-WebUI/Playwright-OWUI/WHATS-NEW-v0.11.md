# Nouveautés Open WebUI v0.11 (août 2026)

[← Retour Playwright-OWUI](./README.md)

> **Pour qui ?** Étudiants qui suivent la série Playwright-OWUI sur une instance
> mise à jour en **v0.11.0**. Les 7 instances du cours (myia + EPF, EPF-GenAI,
> ECE, ESG, EPITA, Pauwels) y sont passées le **2026-08-07**. Ce document
> explique ce qui a changé depuis la v0.10.2, ce qui a cassé dans nos tests
> (spoiler : rien d'irréparable, et rien dans l'application), et ce que vous
> pouvez tester en bonus.

## Contexte de mise à jour

La **v0.11** refonde l'interface entière d'Open WebUI — chat, workspace, panneau
d'administration, fenêtre de réglages. C'est la plus grosse évolution *visuelle*
depuis la v0.8, mais l'API et les mécanismes que teste cette série sont restés
stables.

La campagne de revalidation est déjà faite : les modules 01-06 ont été rejoués
contre l'instance réelle v0.11.0 (**37 passed / 1 failed / 4 skipped en 6,7 min**,
PR #9854). Le seul rouge était un défaut de **test**, pas de l'application —
voir « Pièges mesurés » plus bas.

## Ce qui ne change PAS (rassurant pour vos tests existants)

- **Authentification** : même endpoint `/api/v1/auths/signin`, même rate limit
  (~2 min), même pattern `storageState`.
- **Éditeur de chat** : toujours TipTap/ProseMirror → `keyboard.type()` obligatoire
  (jamais `fill()`), `#chat-input` inchangé.
- **Sélecteur de modèles** : le bouton lui-même est inchangé (revérifié
  firsthand le 2026-08-07).
- **Streaming** : même mécanisme Server-Sent Events, même API
  `/api/chat/completions`.
- **Barres d'édition de message** : les identifiants (`#save-edit-message-button`,
  `#confirm-edit-message-button`) existent toujours — mais lisez le piège n°2,
  leur *sémantique* diffère selon le message.

## Changements BREAKING (ils ont cassé nos tests — ils casseront les vôtres)

### 1. Les réglages admin sont des onglets, plus un lien de navigation

Avant (v0.10) : un lien « Réglages » dans la navigation admin. Maintenant (v0.11) :
la fenêtre de réglages s'ouvre et expose **tout** en onglets — « Général »,
« Connexions », « Base de données », « Authentification », … — les réglages
utilisateur et admin vivent dans la même fenêtre.

Deux pièges mesurés (chronologie réelle, instance de cours, 2026-08-07) :

| t après `goto('/admin/settings')` | état |
|---|---|
| 4,3 s | page chargée, **0 correspondance** pour un lien « Réglages » |
| 7,5 s | un vestige `<a href="/admin/settings">Réglages</a>` **apparaît** |
| 10,7 s | redirection vers `/`, le lien **disparaît** |

- **La fenêtre transitoire de ~3 s** : asserter sur le lien vestige est une
  course perdue d'avance — le même test passe ou échoue selon l'humeur du
  réseau. Attendre l'état stabilisé (`waitForURL` hors de `/admin/settings`)
  avant d'asserter.
- **L'ambiguïté strict mode** : « Général » existe dans le groupe d'onglets
  *utilisateur* ET dans le groupe *admin* (2 correspondances → violation).
  Utiliser un onglet propre à la section visée (« Authentification » prouve
  qu'on est côté admin).

```typescript
// v0.11 — attendre la page stabilisée, puis asserter l'onglet admin
await page.waitForURL((url) => !url.pathname.startsWith('/admin/settings'),
  { timeout: 30_000 });
await expect(page.getByRole('tab', { name: /authentification|authentication/i }))
  .toBeVisible();
```

### 2. « Conversations archivées » n'est plus une entrée de menu

Le menu utilisateur a été réorganisé avec la refonte : l'entrée « Conversations
archivées » a disparu du menu (les archives restent accessibles, mais plus par
ce chemin). Les tests qui la cherchaient par `getByRole('menuitem')` échouent —
c'est un défaut de test, pas de l'application.

### 3. La fenêtre Réglages a changé de forme

Les réglages personnels sont désormais une fenêtre modale à onglets (même
fenêtre que l'admin, section différente). Si vos tests naviguent dans les
réglages par des liens, ils doivent passer par des `getByRole('tab')`.

## Nouveautés à tester en bonus (opportunités)

Toutes vérifiées dans les notes de version officielles v0.11.0 — liste
restreinte à ce qui se teste depuis l'interface de cours :

- **Pages de dossier** : ouvrir un dossier mène à sa propre page — chats
  paginés, tri par titre ou dernière mise-à-jour, nouveau chat directement
  depuis le dossier. Bonus voisin : les dossiers portent un **compteur de
  non-lus** et les chats non lus un point.
- **Fork d'une conversation** : chaque réponse a un bouton « forker » qui
  copie la conversation jusqu'à ce point dans un nouveau chat (souvenir de la
  branche inclus).
- **Panneau d'état du chat** : une commande d'état affiche l'utilisation du
  contexte, les messages en file, les tâches en cours et le chat ID — et le
  menu slash montre à quel point la fenêtre de contexte est pleine.
- **Compaction à la demande** : une commande compacte les tours anciennes
  immédiatement, sans attendre le seuil automatique (introduit en v0.10).
- **Aperçus au survol** : survoler un chat dans la sidebar montre un aperçu
  compact de ses derniers messages ; les horodatages apparaissent au survol
  au format local.
- **Raccourcis clavier personnalisables** : la plupart des raccourcis se
  re-bindent dans les réglages (sauvegardés sur le compte) — et un interrupteur
  les coupe tous.
- **Discuter d'une note** : une note ouvre maintenant une vraie expérience de
  chat (choix du modèle, outils, pièces jointes), avec insertion de la réponse
  dans la note.
- **Onglet Usage** : un tableau de bord personnel dans les réglages — activité
  de jetons, séries, modèles les plus utilisés.
- **Variables de chat et variables utilisateur** : un prompt système peut
  déclarer des champs (texte, liste) remplis par conversation, ou insérer des
  valeurs stockées dans votre compte.
- **Sous-agents** (si l'admin les active) : un modèle peut déléguer des
  morceaux de tâche à des agents d'arrière-plan qui rendent leurs résultats
  dans le chat.

## Pièges mesurés — les trois leçons de la revalidation

La campagne v0.11 (#9854) a sorti trois défauts de test. Aucun bug applicatif.
Chacun illustre une leçon que le parcours enseigne :

1. **Le faux vert** (module 02) : l'assertion « lien Réglages » passait
   *par intermittence* grâce au vestige transitoire de ~3 s. Un test qui passe
   sans rien vérifier ne signale rien — c'est pire qu'un rouge.
2. **Le locator non scopé** (module 03) : `.last()` sur toute la page prenait
   le bouton « Modifier » de l'assistant au lieu de celui du message
   utilisateur. Les deux barres d'édition ne sont pas interchangeables : sur le
   message utilisateur, `#confirm-edit-message-button` s'appelle « Envoyer » et
   **régénère** ; sur la réponse assistant, le même id s'appelle « Enregistrer »
   et ne régénère **pas**. Toujours partir du message (`userMsg.getByRole(...)`)
   et pas de `page`.
3. **Le timeout avalé** (`helpers/chat.ts`) : un `waitForFunction().catch(() => {})`
   laissait le fallback rendre le texte d'une bulle vide — le nom du modèle —
   et le test échouait trois lignes plus loin, sans rapport avec la cause.
   Échouer franchement, en nommant la cause.

Ces trois récits détaillés sont dans le body de la PR #9854 ; la méthode de
triage (régression applicative vs dérive de sélecteur vs panne d'infra) est le
sujet de [`TRIAGE-INFRA-VS-TEST.md`](./TRIAGE-INFRA-VS-TEST.md).

## Notes backend/admin (inutile pour les TP, utile pour comprendre la flotte)

- **Modèle d'ordre des modèles par variable** (`MODEL_ORDER_LIST`) : l'ordre
  survit au redémarrage sur les instances qui ne persistent pas la config —
  c'est le mécanisme que la flotte du cours utilise déjà.
- **Le formulaire de connexion se désactive pendant l'envoi** : plus de double
  soumission concurrente sur réponse lente (visible si vous testez le
  rate limit du module 02).
- **Notifications vers webhooks** (onglet dédié, choix d'événements), transferts
  de fichiers streamés, paramètres de compaction affinés (modèle dédié, plafond
  de jetons, part de messages retenus).

---

*WHATS-NEW-v0.11 — facts mesurés sur les instances du cours (campagne #9854,
2026-08-07) + notes de version officielles v0.11.0. 0 emoji, 0 secret. Suite du
chantier #12135.*
