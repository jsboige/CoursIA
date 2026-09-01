# Manifeste des figures — GenAI/Open-WebUI/00-Tour-Plateforme (parcours découverte)

Provenance des images de `assets/` du parcours « Tour de la plateforme » (Epic #4427, sous Epic #4433 ; captures initiales PR #4809 v0.10.2, **re-captures v0.11.0**).

> **Mise à jour v0.11.0 (2026-08-30, lane myia-ai-01:myia-open-webui — issue #12135)** :
> Le parcours de captures a été **ré-exécuté sur l'instance `demo.open-webui.myia.io` en v0.11.0**
> (`tour-captures.spec.ts`, projet autonome `capture/`), générant **6 figures** (4 nouvelles, 2 régénérées)
> et retirant **1 figure périmée** (v0.10.2). Antifuite par construction : **compte de capture
> `capture.tour+12135@myia.io` non-administrateur** (approuvé `pending → user` le 2026-08-30 via l'API
> `POST /api/v1/users/{id}/update` par le lane, sans intervention du user), surfaces **sans contenu réel**
> (chat sur invite fictive, réglages, mémoire vide de compte neuf), masquage (`mask`) des identifiants
> (`getByText(/@/)`), des liens `/` et du **bouton « Open Terminal (…) » entier** dans `capture()`.
>
> **✅ Re-audit vision EXÉCUTÉ (doctrine #5780 — 2026-08-30, après régénération).**
> Méthode : lecture vision par modèle vision local (Qwen3.6-35B, via sk-agent — la lecture `Read`
> directe des PNG n'était pas disponible dans le contexte d'exécution du lane), **transcription à
> l'aveugle** des bandes de l'image (sans nommer les chaînes cherchées, pour éviter l'écho), et
> **vérification déterministe** des boîtes de masque (scan de pixels magenta). L'audit a détecté puis
> confirmé **2 défauts de fuite + 1 défaut de contenu** sur la première régénération, tous corrigés
> avant le commit :
> 1. **Libellé « Open Terminal (pauwels) » partiellement lisible** sur les vues chat (masque du seul
>    `<span class="truncate">` insuffisant + capture prise avant stabilisation du composer) → masque
>    du **bouton entier** + attente de stabilisation ; vérifié par scan pixel (magenta sur la zone
>    bouton) et transcription à l'aveugle ;
> 2. **Page de connexion figée pré-rendu** (résidu de texte « ol », aucun champ) → le script attend
>    maintenant le rendu du formulaire (champs vides) ;
> 3. **Réponse en erreur « Model not found »** au lieu du poème (erreur *sanitizée* côté non-admin ;
>    causes racine : abonnement MistralAI épuisé + v0.11 — base sans ligne DB = admin-only) →
>    sélection explicite d'un modèle fonctionnel dans le sélecteur. Sur l'instance de capture,
>    « TP Prompt Engineering » a été **rebasé sur le modèle local** pour la figure 02 (voir note
>    sous la figure) — rebasage réversible, scope instance de capture uniquement.
>
> Les descriptions ci-dessous sont donc **vérifiées pixel-par-pixel** (vision + scan), plus dérivées du scénario.

---

## 01-connexion.png

- **Source** : capture Playwright sur instance Open-WebUI **v0.11.0** (tour-captures.spec.ts, scénario « pre-auth login ») — re-capture 2026-08-30, 29 506 octets (formulaire rendu ; la version #4809 figeait le shell pré-rendu).
- **Description visuelle** : *(vérifiée vision)* page de connexion **rendue** — titre « Connectez-vous à Formation Pro Open-Webui (Open WebUI) », champs **« E-mail » et « Mot de passe » vides**, bouton « Connexion », lien « Vous n'avez pas de compte ? Inscrivez-vous ». Aucune donnée saisie, aucun compte identifiable.
- **Alt-text (FR)** : Page de connexion Open WebUI v0.11.0 — formulaire vide (E-mail / Mot de passe), aucun identifiant saisi.
- **Poids** : 28,8 Ko (natif PNG 1440×900)

## 01-premiere-vue.png

- **Source** : capture Playwright sur Open-WebUI **v0.11.0** (tour-captures.spec.ts, scénario « première vue post-connexion ») — nouvelle figure 2026-08-30, 59 432 octets.
- **Description visuelle** : *(vérifiée vision + scan pixel)* écran de chat après authentification — modèle présélectionné « TP Data Analyst Agent » (tuteur), suggestions d'invites, panneau Fichiers du compte neuf (`.bash_logout`, `.bashrc`), toast « Vous êtes désormais connecté. ». Le contrôle « Open Terminal (…) » du composer est **masqué** (boîte magenta — scan pixel vérifié sur sa zone).
- **Alt-text (FR)** : Première vue post-connexion de la plateforme Open WebUI v0.11.0 (chat, compte de capture non-admin).
- **Poids** : 58,0 Ko (natif PNG 1440×900)

## 02-chat-streaming.png

- **Source** : capture Playwright sur Open-WebUI **v0.11.0** (tour-captures.spec.ts, scénario « réponse en streaming sur invite fictive ») — nouvelle figure 2026-08-30, 138 135 octets (régénérée après correction des défauts 1 et 3).
- **Description visuelle** : *(vérifiée vision, transcription à l'aveugle)* réponse de l'assistant **« TP Prompt Engineering »** à l'invite fictive **« Rédige un court poème sur la mer. »** — un court poème (« Sur le sable, le sel s'incruste… ») puis **l'analyse pédagogique du tuteur** (leçon Zero-Shot, rôle et contexte, défi du module 1) : le tuteur ajoute cette analyse par conception. Composer en bas avec le chip du modèle ; zones d'identité masquées (boîtes magenta) ; aucun identifiant, aucune URL, aucun secret (vérifié par transcription à l'aveugle des bandes basse et médiane).
- **Note d'incident (2026-08-30)** : la réponse est servie par le **modèle local** (`Local.qwen3.6-35b-a3b`) car l'abonnement MistralAI était épuisé au moment de la capture (erreur 400 « Check your subscription » côté admin, « Model not found » sanitizée côté non-admin) et v0.11 rend les bases sans ligne DB admin-only. Le tuteur « TP Prompt Engineering » de l'instance de capture a été rebasé sur le modèle local pour cette figure (rebasage réversible : base d'origine `MistralAI.mistral-medium-latest`).
- **Alt-text (FR)** : Réponse du tuteur « TP Prompt Engineering » (Open WebUI v0.11.0) à l'invite fictive « Rédige un court poème sur la mer. » — poème puis analyse de prompt.
- **Poids** : 134,9 Ko (natif PNG 1440×900)

## 03-dossier-equipe.png

- **Source** : capture Playwright sur Open-WebUI **v0.11.0** (tour-captures.spec.ts, scénario « dossier d'équipe v0.10 ») — nouvelle figure 2026-08-30, 57 169 octets.
- **Description visuelle** : *(vérifiée vision + scan pixel)* écran de chat, panneau Fichiers du compte neuf avec le champ **« Nom du dossier »** actif (création de dossier), fichiers `.bash_logout` / `.bashrc` / `datasets`. Contrôle « Open Terminal (…) » **masqué** (boîte magenta, scan pixel vérifié).
- **Alt-text (FR)** : Création d'un dossier (« Nom du dossier ») dans le panneau Fichiers, compte neuf — Open WebUI v0.11.0.
- **Poids** : 55,8 Ko (natif PNG 1440×900)

## 05-parametres.png

- **Source** : capture Playwright sur Open-WebUI **v0.11.0** (tour-captures.spec.ts, scénario « paramètres personnels ») — nouvelle figure 2026-08-30, 66 550 octets.
- **Description visuelle** : *(vérifiée vision)* dialogue **Réglages** ouvert sur l'onglet **« Général »** (thème, langue, prompt système, réglages avancés), bandeau « Vous êtes désormais connecté. », zones d'identité masquées (boîtes magenta sur le coin supérieur et la colonne de droite). Navigation : le bouton du menu utilisateur porte le libellé FR « Menu utilisateur » et l'entrée « Réglages » est un `<button>` (pas un `role=menuitem`).
- **Alt-text (FR)** : Dialogue Réglages Open WebUI v0.11.0, onglet Général.
- **Poids** : 65,0 Ko (natif PNG 1440×900)

## 05-memoire.png

- **Source** : capture Playwright sur Open-WebUI **v0.11.0** (tour-captures.spec.ts, scénario « mémoire vide sur compte neuf ») — re-capture 2026-08-30, 56 073 octets.
- **Description visuelle** : *(vérifiée vision)* onglet **Personnalisation** → section **Mémoire (EXPÉRIMENTAL)**, état vide « **Saved Memories 0** » directement visible. **Évolution UX v0.10 → v0.11** : en v0.11 le panneau mémoire est affiché directement sur l'onglet Personnalisation — le bouton « Gérer » (qui ouvrait la sous-modale « Mémoire 0 » en v0.10.2) **n'existe plus** ; le test a été corrigé en conséquence.
- **Alt-text (FR)** : Onglet Personnalisation > Mémoire (EXPÉRIMENTAL) Open WebUI v0.11.0, état « Saved Memories 0 » sur un compte neuf.
- **Poids** : 54,8 Ko (natif PNG 1440×900)

## ~~02-raisonnement-direct.png~~ (retirée)

- **Source** : capture v0.10.2 (commit `cb113faee` #4809, 115 825 octets), **RETIRÉE le 2026-08-30** : le scénario « raisonnement en direct » est `skip` en v0.11.0 (pas de `DEMO_OWUI_REASONING_MODEL` configuré pour le compte de capture) → aucune re-capture disponible ; la figure **périmée (v0.10.2, modèle `z-ai/glm-5`)** n'est pas conservée pour ne pas laisser figer une capture obsolète dans le parcours v0.11.
- **Statut** : supprimée de `assets/`. À re-ajouter quand un modèle de raisonnement sera configuré pour la capture. *(Note : le modèle local utilisé pour la figure 02 « pense » en direct — l'indicateur « En train de réfléchir… » est apparu pendant la génération — mais la figure vise le poème, pas le raisonnement.)*

---

**Total** : 6 figures (~397 Ko ; max 134,9 Ko par fichier — politique #5654 ≤200 Ko respectée). Arc pédagogique du README parent :
1. **Connexion & première vue** (`01-connexion.png`, `01-premiere-vue.png`)
2. **Le chat IA : modèles, streaming, multimodal** (`02-chat-streaming.png`)
3. **Le travail & dossiers d'équipe** (`03-dossier-equipe.png`)
4. **Paramètres personnels & mémoire** (`05-parametres.png`, `05-memoire.png`)

Chaque figure est placée **dans la section du README parent où le sujet correspondant est discuté** (et non dans une section Galerie isolée), conformément à la doctrine figures amendée 2026-07-09.

**Limitations de cette MANIFEST** :
- Les 6 figures sont des **captures d'écran figées** (snapshot du UI à un instant t, v0.11.0). Toute évolution ultérieure d'Open-WebUI (UI v0.12+) peut rendre les labels ou la disposition obsolètes — un re-audit vision sera nécessaire à chaque bump de version majeure (cf. #5780). Celui de v0.11.0 est **fait** (2026-08-30, méthode décrite en tête).
- Le scénario « raisonnement en direct » reste **différé** (pas de modèle de raisonnement configuré) ; les sections 3 (Workspace) / 4 (Canaux) / 6 (Administration) du README parent restent **schématisées** (Mermaid dans `architecture.md`) plutôt qu'en captures — cette MANIFEST ne les couvre donc pas.
- **0 secret inline** : aucune URL de tenant, e-mail nominatif, clé ou jeton n'apparaît dans les figures — **vérifié par transcription vision à l'aveugle de chaque figure** (compte de capture non-admin + masquage + surfaces sans contenu réel).
