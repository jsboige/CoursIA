# Manifeste des figures — GenAI/Open-WebUI/00-Tour-Plateforme (parcours découverte)

Provenance des images de `assets/` du parcours « Tour de la plateforme » (Epic #4427, sous Epic #4433 ; captures initiales PR #4809 v0.10.2, **re-captures v0.11.0**).

> **Mise à jour v0.11.0 (2026-08-30, lane myia-ai-01:myia-open-webui — issue #12135)** :
> Le parcours de captures a été **ré-exécuté sur l'instance `demo.open-webui.myia.io` en v0.11.0**
> (`tour-captures.spec.ts`, projet autonome `capture/`), générant **6 figures** (4 nouvelles, 2 régénérées)
> et retirant **1 figure périmée** (v0.10.2). Antifuite par construction : **compte de capture
> `capture.tour+12135@myia.io` non-administrateur** (approuvé `pending → user` le 2026-08-30 via l'API
> `POST /api/v1/users/{id}/update` par le lane, sans intervention du user), surfaces **sans contenu réel**
> (chat sur invite fictive, réglages, mémoire vide de compte neuf), masquage (`mask`) des identifiants
> (`getByText(/@/)`) et des liens `/` dans `capture()`, et revue image-par-image.
>
> **⚠️ Re-audit vision requis (doctrine #5780, "re-audit à chaque bump de version majeure")** :
> les descriptions ci-dessous sont **dérivées du scénario** (`tour-captures.spec.ts`) et des métadonnées
> (taille, source), **PAS d'une re-lecture vision pixel-par-pixel** cette fois (le rendu image n'était pas
> disponible dans le contexte d'exécution du lane). Un audit vision M3/MiniMax (lecture `Read` directe des
> PNG) est l'étape de suivi avant/à côté du merge — conformément à la note de limitation historique de cette
> MANIFEST. Les **tailles** et la **présence** des fichiers sont vérifiées.

---

## 01-connexion.png

- **Source** : capture Playwright sur instance Open-WebUI **v0.11.0** (tour-captures.spec.ts, scénario « pre-auth login ») — re-capture 2026-08-30, 8 095 octets (inchangé vs #4809).
- **Description visuelle** (dérivée du scénario) : page de connexion pré-authentification, capture du **shell avant saisie** (masquage anti-fuite intentionnel) — quasi-blanc, contenu réduit.
- **Alt-text (FR)** : Page de connexion Open WebUI v0.11.0 — capture pré-authentification (logo seul, aucun champ visible), masquage anti-fuite intentionnel.
- **Poids** : 7,9 Ko (natif PNG 1440×900)

## 01-premiere-vue.png

- **Source** : capture Playwright sur Open-WebUI **v0.11.0** (tour-captures.spec.ts, scénario « première vue post-connexion ») — nouvelle figure 2026-08-30, 61 389 octets.
- **Description visuelle** (dérivée du scénario) : écran de chat après authentification du compte de capture (non-admin, frais) — vue d'accueil de la conversation, aucune donnée d'établissement.
- **Alt-text (FR)** : Première vue post-connexion de la plateforme Open WebUI v0.11.0 (chat, compte de capture non-admin).
- **Poids** : 59,9 Ko (natif PNG 1440×900)

## 02-chat-streaming.png

- **Source** : capture Playwright sur Open-WebUI **v0.11.0** (tour-captures.spec.ts, scénario « réponse en streaming sur invite fictive ») — nouvelle figure 2026-08-30, 37 707 octets.
- **Description visuelle** (dérivée du scénario) : réponse de l'assistant en cours de streaming ; invite **FICTIVE** (`Rédige un court poème sur la mer.`), aucun contenu propriétaire d'établissement.
- **Alt-text (FR)** : Réponse de l'assistant Open WebUI v0.11.0 en streaming sur une invite fictive.
- **Poids** : 36,8 Ko (natif PNG 1440×900)

## 03-dossier-equipe.png

- **Source** : capture Playwright sur Open-WebUI **v0.11.0** (tour-captures.spec.ts, scénario « dossier d'équipe v0.10 ») — nouvelle figure 2026-08-30, 59 250 octets.
- **Description visuelle** (dérivée du scénario) : création d'un dossier d'équipe dans la sidebar sur un compte neuf (aucun dossier réel visible).
- **Alt-text (FR)** : Dossier d'équipe dans la sidebar Open WebUI v0.11.0 (compte neuf).
- **Poids** : 57,9 Ko (natif PNG 1440×900)

## 05-parametres.png

- **Source** : capture Playwright sur Open-WebUI **v0.11.0** (tour-captures.spec.ts, scénario « paramètres personnels ») — nouvelle figure 2026-08-30, 66 515 octets.
- **Description visuelle** (dérivée du scénario) : dialogue **Réglages** ouvert (Menu utilisateur → Réglages), onglet par défaut ; navigation réparée ce tir (le bouton du menu utilisateur porte le libellé FR « Menu utilisateur » et l'entrée « Réglages » est un `<button>`, pas un `role=menuitem`).
- **Alt-text (FR)** : Dialogue Réglages Open WebUI v0.11.0.
- **Poids** : 65,0 Ko (natif PNG 1440×900)

## 05-memoire.png

- **Source** : capture Playwright sur Open-WebUI **v0.11.0** (tour-captures.spec.ts, scénario « mémoire vide sur compte neuf ») — re-capture 2026-08-30, 56 039 octets.
- **Description visuelle** (dérivée du scénario) : onglet **Personnalisation** → section **Mémoire (EXPÉRIMENTAL)**, état vide « **Saved Memories 0** » directement visible. **Évolution UX v0.10 → v0.11** : en v0.11 le panneau mémoire est affiché directement sur l'onglet Personnalisation — le bouton « Gérer » (qui ouvrait la sous-modale « Mémoire 0 » en v0.10.2) **n'existe plus** ; le test a été corrigé en conséquence (on ne clique plus « Gérer », on attend le texte d'état vide).
- **Alt-text (FR)** : Onglet Personnalisation > Mémoire (EXPÉRIMENTAL) Open WebUI v0.11.0, état « Saved Memories 0 » sur un compte neuf.
- **Poids** : 54,7 Ko (natif PNG 1440×900)

## ~~02-raisonnement-direct.png~~ (retirée)

- **Source** : capture v0.10.2 (commit `cb113faee` #4809, 115 825 octets), **RETIRÉE le 2026-08-30** : le scénario « raisonnement en direct » est `skip` en v0.11.0 (pas de `DEMO_OWUI_REASONING_MODEL` configuré pour le compte de capture) → aucune re-capture disponible ; la figure **périmée (v0.10.2, modèle `z-ai/glm-5`)** n'est pas conservée pour ne pas laisser figer une capture obsolète dans le parcours v0.11.
- **Statut** : supprimée de `assets/`. À re-ajouter quand un modèle de raisonnement sera configuré pour la capture.

---

**Total** : 6 figures (~282 Ko). **Politique** (#5654) : ≤200 KB/fichier, downscale ≤1200 px max. Arc pédagogique du README parent :
1. **Connexion & première vue** (`01-connexion.png`, `01-premiere-vue.png`)
2. **Le chat IA : modèles, streaming, multimodal** (`02-chat-streaming.png`)
3. **Le travail & dossiers d'équipe** (`03-dossier-equipe.png`)
4. **Paramètres personnels & mémoire** (`05-parametres.png`, `05-memoire.png`)

Chaque figure est placée **dans la section du README parent où le sujet correspondant est discuté** (et non dans une section Galerie isolée), conformément à la doctrine figures amendée 2026-07-09.

**⚠️ Limitations de cette MANIFEST** :
- Les 6 figures sont des **captures d'écran figées** (snapshot du UI à un instant t, v0.11.0). Toute évolution ultérieure d'Open-WebUI (UI v0.12+) peut rendre les labels ou la disposition obsolètes — un re-audit vision sera nécessaire à chaque bump de version majeure (cf. #5780).
- Le scénario « raisonnement en direct » reste **différé** (pas de modèle de raisonnement configuré) ; les sections 3 (Workspace) / 4 (Canaux) / 6 (Administration) du README parent restent **schématisées** (Mermaid dans `architecture.md`) plutôt qu'en captures — cette MANIFEST ne les couvre donc pas.
- Les descriptions visuelles sont **dérivées du scénario** du spec, pas d'une re-lecture vision pixel-par-pixel (cf. avertissement en tête) ; le re-audit vision est l'étape de suivi.
- **0 secret inline** : aucune URL de tenant, e-mail nominatif, clé ou jeton n'apparaît dans les figures (compte de capture non-admin + masquage + surfaces sans contenu réel ; revue anti-fuite appliquée).
