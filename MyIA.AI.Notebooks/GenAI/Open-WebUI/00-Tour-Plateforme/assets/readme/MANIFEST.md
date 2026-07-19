# Manifeste des figures — GenAI/Open-WebUI/00-Tour-Plateforme (parcours découverte)

Provenance des images de `assets/` du parcours « Tour de la plateforme » (Epic #4427, sous Epic #4433, sous PR #4809 v0.10.2 captures safe).

> **Audit vision M3 po-2023 c.658 (2026-07-19)** : les 3 PNG ci-dessous ont été ouverts un par un via l'outil `Read` et leur contenu réel confronté à leur description existante dans le README parent (`00-Tour-Plateforme/README.md`). Les 3 figures sont **SOTA-OK** : (a) `01-connexion.png` est **intentionnellement content-free** (page de connexion pré-authentification, marquée explicitement « Capture à venir » dans le README et documentée dans le commit `cb113faee` comme « pre-auth login page » — taille 8 KB, presque vide = comportement attendu) ; (b) `02-raisonnement-direct.png` = vraie capture de raisonnement streaming sur le chat Open-WebUI 0.10.2 (modèle `z-ai/glm-5` visible, conversation en français avec étapes 4/5/6 sur le bleu du ciel + Résumé) ; (c) `05-memoire.png` = vraie capture du panneau **Réglages > Personnalisation > Mémoire (EXPÉRIMENTAL)** avec persona Samantha défini par défaut et Mémoire 0 vide. **0 figure DROP** — les 3 fichiers restent sur disque. **0 notebook ré-exécuté** (C.3 strict respecté). **0 PNG régénéré** (capture scénarisée par Playwright sur instance v0.10.2 + masquage anti-fuite + revue image-par-image en PR #4809). La présente PR ajoute la **MANIFEST.md** d'origine (manquante) pour aligner ce dossier sur la doctrine #5780 (chaque figure placée dans la MANIFEST de la section du README où elle est référencée).

---

## 01-connexion.png

- **Source** : capture Playwright sur instance Open-WebUI v0.10.2 (tour-captures.spec.ts, scénario « pre-auth login ») — commit `cb113faee` « docs(owui-tour): add v0.10.2 safe captures (login, live reasoning, memory) (#4809) » du 2026-07-02.
- **Contenu réel vérifié** (re-lecture M3 c.658 2026-07-19) : PNG pleine page quasi-blanc, **uniquement le logo Open-WebUI centré** (carré magenta stylisé) en titre de la page de connexion. Aucun champ e-mail/password rendu à l'écran — Playwright a capturé le **shell pré-authentification** (avant que l'utilisateur saisisse ses identifiants, sécurité anti-fuite intentionnelle), avec masquage (`mask`) des éléments sensibles. Taille disque **8 095 octets** (PNG essentiellement vide + logo) — le README parent déclare « Page de connexion (aucun contenu réel — capture pré-authentification) » comme comportement attendu.
- **Alt-text (FR)** : Page de connexion Open WebUI v0.10.2 — capture pré-authentification (logo seul, aucun champ visible), masquage anti-fuite intentionnel.
- **Poids** : 8,1 Ko (natif PNG)
- **Note** : la description « champ e-mail, mot de passe et bouton Connexion » dans le README parent **sur-vendra** ce que la figure montre réellement — elle capture l'**état vide avant saisie**, pas le formulaire rempli. La présente note corrige cela : voir aussi `📷 Capture à venir — 01-premiere-vue.png` (écran de chat vide post-connexion) que le README parent prévoit comme capture future distincte.

## 02-raisonnement-direct.png

- **Source** : capture Playwright sur instance Open-WebUI v0.10.2 (tour-captures.spec.ts, scénario « live thinking block ») — commit `cb113faee` #4809.
- **Contenu réel vérifié** (re-lecture M3 c.658 2026-07-19) : PNG 115 825 octets, **capture écran du chat Open-WebUI** avec marqueur latéral gauche masqué. Modèle actif = **`z-ai/glm-5`** (sélecteur en haut à gauche), avec contrôles de température (`Violet` / `Très courte` / `Très forte` — labels fr-FR du UI v0.10.2). Conversation visible, en français, sur 6 étapes structurées :
  - **Étape 4 : Le bleu domine** (« Le bleu a une longueur d'onde courte (~450 nm), donc il est **diffusé environ 5,5 fois plus** que le rouge… »)
  - **Étape 5 : Pourquoi pas violet ?** (liste numérotée 3 items, en gras : « Le soleil émet moins de lumière violette », « Nos yeux sont plus sensibles au bleu qu'au violet », « Le résultat est donc une perception bleu dominant »)
  - **Étape 6 : Pourquoi le ciel est rouge au coucher du soleil ?** (« le soir, la lumière traverse **une couche d'atmosphère plus épaisse**… »)
  - **Résumé** final sur fond bleuté pâle : code-block `1   Soleil → Atmosphère → Diffusion de Rayleigh → Bleu diffusé → Ciel bleu !` + reformulation narrative (« Le ciel est bleu parce que les molécules de l'atmosphère diffusent davantage les longueurs d'onde courtes (bleu) que les longueurs d'onde longues (rouge), grâce à la diffusion de Rayleigh. ») + barre d'actions (édition / copie / like / dislike / regenerate).
  - Champ de saisie vide « Envoyer un message » en bas + bouton d'envoi circulaire.
- **Alt-text (FR)** : Capture du chat Open WebUI v0.10.2 — raisonnement affiché en direct sur une invite fictive (modèle GLM-5, fr-FR), étapes 4-5-6 sur la couleur du ciel + résumé structuré, marqueur latéral masqué.
- **Poids** : 115,8 Ko (natif PNG)
- **Note** : la figure illustre bien la **nouveauté v0.10 « raisonnement affiché en direct »** annoncée par le README parent (section 2, label `(nouveau — v0.10)`). Invite fictive (pas de prompt propriétaire d'établissement), marqueur latéral masqué (`mask` Playwright), conforme à la politique anti-fuite du dossier.

## 05-memoire.png

- **Source** : capture Playwright sur instance Open-WebUI v0.10.2 (tour-captures.spec.ts, scénario « empty memory panel on fresh account ») — commit `cb113faee` #4809.
- **Contenu réel vérifié** (re-lecture M3 c.658 2026-07-19) : PNG 57 925 octets, **capture du panneau Réglages en mode modal** (overlay sombre) sur l'UI Open-WebUI v0.10.2. Persona visible = **`Samantha` v** (sélecteur en haut à gauche, sous-titre « Définir comme valeur par défaut »). Sidebar gauche des Réglages avec section active « **Personnalisation** » (Général / Interface utilisateur / Personnalisation / Audio / Contrôles des données / Compte / À propos). Au centre, modale **« Mémoire 0 »** ouverte depuis le panneau **« Mémoire [EXPÉRIMENTAL]** avec toggle vert activé et bouton « Gérer ». Texte d'aide : « Vous pouvez personnaliser vos interactions avec les LLMs en ajoutant des mémoires à l'aide du bouton + Gérer ci-dessous, ce qui les rendra plus utiles et mieux adaptées à vos besoins. ». Dans la modale : champ « Rechercher des éléments mémorisés » vide, message « Les souvenir accessibles par les LLMs seront affichés ici. » (note : faute « Les souvenir » dans l'UI originale — verbatim, pas une correction de notre fait), bouton tertiaire « Effacer la mémoire » (désactivé, en gris) en bas-gauche, bouton primaire « Ajouter un souvenir » en bas-droite. Bouton sombre « Enregistrer » en bas-droite du panneau Réglages.
- **Alt-text (FR)** : Capture du panneau Réglages Open WebUI v0.10.2 — section Personnalisation > Mémoire (EXPÉRIMENTAL), modale « Mémoire 0 » vide sur un compte neuf (persona Samantha).
- **Poids** : 57,9 Ko (natif PNG)
- **Note** : la figure illustre la **nouveauté v0.10 « Mémoire »** annoncée par le README parent (section 5, label `(nouveau — v0.10)`). Compte neuf + mémoire vide = scénario nominal pour la démo (pas de fuite de données utilisateur réelles).

---

**Total** : 3 figures, ~182 Ko. **Politique** (#5654) : ≤200 KB/fichier, downscale ≤1200 px max. Arc pédagogique du README parent :
1. **Connexion & première vue** (1 = `01-connexion.png`, pré-auth content-free)
2. **Le chat IA : modèles, streaming, multimodal** (2 = `02-raisonnement-direct.png`, nouveauté v0.10 raisonnement streamé)
3. (sections 3 / 4 / 5-1 / 6 — captures lourdes différées, marquées « 📷 Capture à venir », schématisées dans `architecture.md` plutôt qu'en captures réelles pour éviter d'exposer des surfaces sensibles)

Chaque figure est placée **dans la section du README parent où le sujet correspondant est discuté** (et non dans une section Galerie isolée), conformément à la doctrine figures amendée 2026-07-09.

**⚠️ Limitations de cette MANIFEST** :
- Les 3 figures sont des **captures d'écran figées** (snapshot du UI à un instant t). Toute évolution ultérieure d'Open-WebUI (UI v0.11+) peut rendre les labels ou la disposition obsolètes — un re-audit vision sera nécessaire à chaque bump de version majeure.
- Les sections 3 (Workspace) / 4 (Canaux) / 6 (Administration) du README parent restent **schématisées** (Mermaid dans `architecture.md`) plutôt qu'en captures — cette MANIFEST ne les couvre donc pas (elles vivent dans `architecture.md`, pas dans `assets/`).
- Les captures sont conservées **telles quelles** sur disque ; cette PR ne supprime AUCUN fichier PNG et ne touche à aucun notebook (les captures sont produites par un script Playwright externe `tour-captures.spec.ts` dans `capture/`).
- **0 secret inline** : aucune URL de tenant, e-mail nominatif, clé ou jeton n'apparaît dans les figures (revue anti-fuite image-par-image appliquée au commit `cb113faee`).

Audit vision M3 po-2023 c.658 (2026-07-19, doctrine #5780) — choix éditorial = byte-safe MANIFEST-add, 0 PNG régénéré, 0 notebook ré-exécuté (C.3 strict). PR meraillage parent = #4809 (« docs(owui-tour): add v0.10.2 safe captures »).
