# ICT — Matrice de dissociations (notebook × claim × proxy × contrôle × seeds × verdict × portée)

> **Statut.** Document de synthèse transversal, grade **C-documentaire** (consolidation, pas de nouveau dispatch). Ossaturé par la **factorisation 4-objets** dégagée par l'audit #4 (tour 523) — remplace « la variable latente miraculeuse » comme cadre de lecture des claims.
> **Objet.** Construire la matrice canonique `notebook × claim × proxy × contrôle × seeds × verdict × portée` qui rend l'état scientifique de la série ICT lisible d'un coup d'œil et discipline la montée en généralité.
> **Discipline.** Une entrée par (notebook, claim). Colonne `verdict` sobre (`Établi` / `Fortement soutenu` / `Spéculatif`), colonne `portée` explicite (régime où le claim tient). Le document **ne « monte » jamais** un fait de dissociation en obstruction cohomologique sans les prérequis (cf #7733 rectification A2 : `H¹ ≠ 0` est *candidat* à obstruction, pas érigé en impossibilité sauf Kochen-Specker et Arrow). See [#4588](https://github.com/jsboige/CoursIA/issues/4588). Issue-source : [#7734](https://github.com/jsboige/CoursIA/issues/7734).

## Pourquoi cette ossature 4-objets

L'audit #4 a fait apparaître quatre grandeurs que les notebooks ICT mesurent en pratique, sans toujours les nommer explicitement. Plutôt que de continuer à les superposer sous une « variable latente » générique, on les pose comme **ossature** de la matrice : chaque claim se lit comme un pattern de présence/absence dans cet espace, et les **dissociations** entre claims deviennent des **patterns** lisibles.

| Objet | Symbole | Définition opérationnelle | Notebook-ancrage |
|---|---|---|---|
| **Saillance** | `s_t` | Ce qui est perceptiblement présent (forme, objet, token, feature activée). Grandeur *présente* à l'instant `t`, indépendamment de sa valeur. | ICT-1 (Φ sur système-jouet), ICT-8 (bifurcation), ICT-21 (features SAE) |
| **Représentation prédictive** | `q_t(z)` | Ce que le système croit de la cause/du futur. Cas simple `p̂` : croyance réduite à un point (moyenne). Cas général : distribution sur l'espace des causes. | ICT-10 (p̂ mesuré sur fronce), ICT-12 (animats), ICT-14 (free energy) |
| **Prégnance / valence** | `π_t(z)` | Ce qui donne de l'importance : attraction, répulsion, urgence, valeur biologique/normative. À distinguer de la saillance (qui est présence sans valeur). | ICT-12 (champ de valence), ICT-19 (enjeu/stake) |
| **Opérateur de workspace** | `W_t` | Ce qui rend des composantes disponibles à d'autres mécanismes (décision, raisonnement, rapport, contrôle). Critère opérationnel = influence retardée sur le décours du système. | ICT-24 (ignition workspace), ICT-SAE-JLens |

**Pourquoi cette ossature discipline la montée en généralité.** La série a cherché un scalaire unique — elle a falsifié cette recherche (Φ/F covarient, K diverge, ICT-synthèse cross-substrat). La factorisation 4-objets dit *pourquoi* un scalaire unique ne peut pas exister en général : les quatre objets ne sont pas superposables. Quand un claim affirme une superposition, il faut indiquer **où** dans l'espace 4D elle opère et **où** elle casse — c'est précisément ce que la matrice rend lisible.

## Dissociations canoniques que cette ossature rend visibles

Cinq patterns structurels qui se répètent dans la série, chacun dans son régime propre :

| Pattern | Forme | Lecture |
|---|---|---|
| **Saillant sans importance** | `s_t ≠ 0, π_t = 0` | Présence perceptive sans valeur — base de la publicité, des leurres. (ICT-14 contraste `s` forte / `π` nulle sur signal sinusoidal non-prédictif.) |
| **Important mais mal prédit** | `π_t` haut, `q_t` loin de la cible | Récompense élevée, représentation interne à côté. (ICT-10 verdict régime-dépendant de `p̂` : illusoire sur dérive et créneau.) |
| **Bien représenté non globalement accessible** | `q_t` bon, `W_t` sélectif | Information disponible localement, pas au workspace. (ICT-24 verdict dissociation : pics emergence_gain et ignitions workspace ne co-localisent pas sur S4.) |
| **Globalement diffusé tout en étant faux** | `W_t` large, `q_t` faux | Bruit propagé comme s'il était signal. (ICT-13 verdict honnête Gate 3 : la réciprocité active TFT est le point de rupture sous bruit.) |
| **Fortement compressé non causalement utilisé** | `K` basse, effet causal nul | Pattern mémorisé, jamais mobilisé. (ICT-17b verdict dissociatif : 2/5 proxys co-localisent avec la généralisation, 3/5 dissocient.) |

Chaque ligne de la matrice situe un claim de notebook dans cet espace, avec son contrôle, ses seeds, son verdict, sa portée.

## Matrice

Conventions :
- **Objet 4-tuple** = `(s, q, π, W)` couverts par le claim. `✓` = proxy direct, `○` = proxy indirect ou partiel, `—` = non couvert.
- **Verdict** = `Établi` (multi-seed ≥ 3, contre contrôle négatif, Gates falsifiables passés) · `Fortement soutenu` (≥ 2 seeds, Gates partiels, contrôle présent) · `Spéculatif` (≤ 2 seeds ou Gates non falsifiables, ou contrefactuel non exécuté).
- **Portée** = régime de validité explicite. Si vide, le claim est **non-régime-dépendant** dans le périmètre du notebook (rare).

### Strate 1 — tri auto-organisé

| Notebook | Claim | Objet 4-tuple | Proxy | Contrôle | Seeds | Verdict | Portée |
|---|---|---|---|---|---|---|---|
| **ICT-1** | La trajectoire de Φ oscille sans asymptote unique sur l'attracteur | `s` ✓, `q` —, `π` —, `W` — | Φ calculé par vrai PyPhi | Système-jouet AND/OR, 4 départs distincts | 4 départs | **Établi** | Réseau de petite taille (≤ 8 nœuds), trajectoire sur 6 pas |
| **ICT-2** | Le tri auto-organisé exhibe une *compétence for free* (auto-réparation, délai de gratification) | `s` ✓, `q` —, `π` —, `W` — | sortedness + inversions | Réseau uni-directionnel vs bi-directionnel | Multi-pas (220+) | **Établi** | Tableaux uni/bi-directionnels ; agrégation « kin » **non** reproduite (cf ICT-4) |
| **ICT-3** | La dégradation gracieuse et le délai de gratification sont quantifiables | `s` ✓ | Distributions de récupération | Cellules défectueuses injectées à fréquences variables | ≥ 5 fréquences | **Établi** | Robustesse linéaire jusqu'à ~30 % de défauts ; effondrement au-delà |
| **ICT-4** | L'agrégation « kin » positive émerge **seulement** avec degrés de liberté | `s` ✓, `W` ○ | Affinité par algotype | Sans degrés de liberté (agrégation disparaît) | Multi-règles | **Établi** | Variétés répétées ; ségrégation à la Schelling si signature imposée |
| **ICT-5** | L'émergence causale (Hoel) est discriminante entre échelles | `s` ✓, `W` ○ | Information effective Φ_eff | Baselines micro/macro explicites | Multi-coarse-grainings | **Établi** | Au-delà de la borne de taille PyPhi (couverture par CE 2.0) |
| **ICT-6** | La TPM estimée depuis les trajectoires de tri permet l'émergence causale multi-échelles | `s` ✓ | TPM empirique → CE 2.0 | Markov-naïf, persist | Multi-chaînes | **Établi** | Tri auto-organisé stable ; ne transfère **pas** tel quel aux régimes non-stationnaires |
| **ICT-7** | Le tri *paraît* scale-free mais possède une taille caractéristique | `s` ✓ | MLE de Hill + KS (Clauset) | Branchement critique (exposant 3/2) | ≥ 10 tirages | **Établi** | Détection robuste quand `x_min` correctement choisi (sinon faux positif scale-free) |

### Strate 2 — morphogenèse dynamique

| Notebook | Claim | Objet 4-tuple | Proxy | Contrôle | Seeds | Verdict | Portée |
|---|---|---|---|---|---|---|---|
| **ICT-8** | Les *early-warning signals* (Scheffer 2009) précèdent la bifurcation pli | `s` ✓, `W` ○ | Valeur propre → 0, variance ↑, autocorrélation ↑, τ de Kendall | Potentiel effectif, détrendage | Multi-paramètres | **Établi** | Modèle de pâturage de May ; leçon *sans complaisance* : EWS = signal local, pas déterminisme |
| **ICT-9** | L'agence est mesurable comme *gain de réparation* (RD − diffusion) après `do(·)` | `s` ✓, `π` ○, `W` ○ | `repair_gain`, `recovery_score` | Mondes contrefactuels Pearl : RD vs diffusion pure | Multi-ablation, multi-seed | **Établi** | Mesures naïves (pixel, cosinus spectral) **produisent des fantômes** ; seule la structure restaurée contrastée au contrôle passif tient |
| **ICT-10** | Le métathéorème (comptage d'équilibres ne change qu'aux plis) clôt la strate 2 | `s` ✓, `π` ○ | Squelette catastrophique + comptage d'équilibres | Chemin générique, modèle jouet | Théorique + mesuré | **Établi** | Fronce canonique ; barrière basse → haute dimension non franchie par cette mesure |
| **ICT-10** (bis) | `p̂` *gagne* en anticipation sur trajectoire lisse, *perd* sur dérive/créneau | `s` ✓, `q` ✓, `π` ○ | `p̂` vs persistance, moyenne mobile, AR(1) in-sample | 3 familles × 3 baselines adverses | 5/5 graines sur lisse | **Fortement soutenu** | Régime-dépendant (lisse seulement) ; **non** un avantage universel du modèle interne |
| **ICT-10** (ter) | La correspondance sémiophysique (Ch.2 Thom) : pivots ↔ transitions, verbe SVO ↔ lacet, anticipation ↔ `p̂` | `s` ✓, `q` ✓, `π` ✓ | Correspondance nommée | — | — | **Spéculatif** | Caveat de non-prédictivité (Thom lui-même) ; pont basse → haute dim via neurosymbolique/Lean/EML #4653 |

### Strate 3 — trajectoires intégrées (régime-dépendance)

| Notebook | Claim | Objet 4-tuple | Proxy | Contrôle | Seeds | Verdict | Portée |
|---|---|---|---|---|---|---|---|
| **ICT-11** | L'échelle méso-émergente est l'échelle privilégiée pour l'agence | `s` ✓, `W` ○ | `repair_gain` + `basin_return_probability` + Hoel info effective | Multi-résolutions (b ∈ {4, 8, 16, 32}) | Multi-seed | **Spéculatif** | Les deux mesures d'agence **se contredisent** : `repair_gain` pic méso (artefact-contaminé, > 1), `basin_return` strictement décroissante ; verdict honnête = pas d'échelle privilégiée confirmée |
| **ICT-12** | `p̂` est régime-dépendant (capture x4 sur balistique rapide, perd sur erratique) | `s` ✓, `q` ✓, `π` ✓ | Taux de capture, évasion, irréversibilité, switching | Animat réactif (gradient instantané) vs anticipateur (`p̂`) ; marche aléatoire comme contrôle négatif | Multi-régimes | **Établi** | Le modèle interne paie son coût là où la source échappe au réactif **et** reste prévisible — *ni* universellement avantageux *ni* ruineux |
| **ICT-13** Gate 1 | TFT et Grim co-domident le tournoi Axelrod | `s` ✓, `π` ○ | Score de tournoi round-robin | 6 stratégies (AllC, AllD, TFT, gTFT, Pavlov, Grim) | Multi-tournois | **Établi** | Paiements canoniques T=5, R=3, P=1, S=0 |
| **ICT-13** Gate 2 | Le seuil de coopération soutenable colle au Folk theorem | `s` ✓, `π` ○ | δ* analytique vs numérique | (T-R)/(T-P) = 0.500 | Mesure numérique = 0.550 | **Établi** | Écart ~10 % explicable par discrétisation et stochasticité du tournoi |
| **ICT-13** Gate 3 | Sous bruit d'exécution, la réciprocité active (TFT) est le point de rupture | `s` ✓, `W` ○ | Score de tournoi vs bruit ε ∈ [0, 0.40] | 6 stratégies | Multi-ε | **Établi** | Contredit la prédiction Nowak-Sigmund sur ces paiements ; Grim paradoxalement le plus robuste |
| **ICT-13** Gate 4 | Les bassins d'invasion dépendent de la fraction initiale | `s` ✓, `W` ○ | Bassin d'invasion contre AllD résident | Fraction initiale ∈ [0, 1] | Multi-fractions | **Établi** | TFT/Grim dès 2 %, gTFT à 34 %, Pavlov/AllC jamais (1.0) |
| **ICT-13** (verdict global) | La robustesse stratégique est **fonction du régime**, pas intrinsèque | `s` ✓, `π` ○ | 4 Gates falsifiables combinés | — | 4 Gates × multi-seed | **Établi** | Bruit + structure de paiements → la « forme stable » n'existe qu'au sein d'un environnement donné |

### Strate 4 — énergie libre et représentationnel

| Notebook | Claim | Objet 4-tuple | Proxy | Contrôle | Seeds | Verdict | Portée |
|---|---|---|---|---|---|---|---|
| **ICT-14** | La *free energy* articule anticipation (`p̂`) et trajectoire Φ | `s` ✓, `q` ✓, `π` ○ | Free energy + expected free energy | Persistance, AR(1) | Multi-seed | **Fortement soutenu** | Banc sinusoidal bruité, 300 pas ; free energy formelle tracée seulement en partie (figure rendue = cas d'application de `p̂`, pas la F proprement dite — honnêteté disclosure dans README) |

### Strate 5 — réalisation de la théorie fondatrice

| Notebook | Claim | Objet 4-tuple | Proxy | Contrôle | Seeds | Verdict | Portée |
|---|---|---|---|---|---|---|---|
| **ICT-15** | Φ/F/K convergent sur le banc cross-substrat | `s` ✓, `q` ○, `W` ○ | Φ, F, K mesurés indépendamment | Substrats témoins (random, persistance) | Multi-substrat (4-5) | **Spéculatif** | **Verdict honnête : Φ et F covarient, K diverge** ; le triplet **ne converge pas** universellement ; ICT-15b (sensitivity) et ICT-15c (meta-proxy obstruction) creusent |
| **ICT-16** | `F` = partie résiduelle de `K` + bosse complexité-entropie | `s` ✓ | MDL two-part code | Modèles témoins sans bosse | Multi-source | **Établi** | Bosse Crutchfield-Feldman 1998 mesurée à H* ≈ 1.99 bits/symbole ; cave emptor : **un seul couple (modèle, famille de sources)** dans la figure rendue |
| **ICT-17** | L'ε-machine (Crutchfield) ≠ Hoel : deux lectures de l'émergence causale | `s` ✓, `W` ○ | États causaux + complexité statistique + entropie d'excès | Hoel info effective, CE 2.0 | Multi-substrat | **Fortement soutenu** | Dissociation reconnue mais pas hiérarchisée |
| **ICT-17b** | 2/5 proxys dissocient du progrès de généralisation pendant le grokking | `s` ✓, `q` ○ | ‖w‖², Fisher-MDL, 1-test_acc, trace de Fisher, pred-zlib | Baseline avant-grokking | 5 proxys | **Établi** | 3 co-localisent (‖w‖², Fisher-MDL, 1-test_acc) ; 2 dissocient (trace Fisher, pred-zlib). Verdict honnête dissociatif (#7268) |
| **ICT-18** | Forcer une trajectoire ICT à devenir réversible *mesure* sa production d'entropie | `s` ✓, `q` ○, `π` ○ | Distribution stationnaire, inversion temporelle, σ de Schnakenberg | Détailed balance (σ = 0) | 4 substrats testés | **Établi** | GPU-free ; ancré ICT-3 *competency for free* |
| **ICT-18b** P1 | Le budget `B_state` s'épuise au pli de bifurcation | `s` ✓, `q` ○ | `B_state` (Monte-Carlo primaire) | `B_work` (témoin) | Multi-substrat (S2/S4/S3) | **Établi** | Co-varie avec les EWS d'ICT-8 ; `B_state` ≪ `B_work` en pré-pli |
| **ICT-18b** P2 | Dissiper plus (↑ σ) ne régénère pas plus (B_state stable) | `s` ✓, `q` ○ | σ vs `B_state` | Substrat témoin (dissipation sans structure) | S4 (Gray-Scott) | **Établi** | **Verdict dissociation** : la réversibilité se dissocie en un moyen (σ) et une fin (compétence de régénération) ; on mesurait son coût, pas sa finalité |
| **ICT-18b** P3 | La monoculture stratégique (Axelrod 6 stratégies) porte une dette d'irréversibilité culturelle | `s` ✓, `q` ○, `W` ○ | `B_state` sur Axelrod | Axelrod multi-stratégies vs tournoi homogène | S3 | **Établi** | Dette détectable, magnitude dépendante de la distribution initiale |
| **ICT-19** | L'enjeu `I_stake` (récupérabilité Levin) est mesurablement distinct du moyen `I_thermo` (σ) | `s` ✓, `π` ✓, `W` ○ | `{I_thermo, I_stake}` (jamais agrégé) | S5 = pur dissipateur (contrôle négatif obligatoire) | S1-S5 | **Établi** | ICT-19b raffinement : `repair_gain` +0.82 ± 0.27 sur S4 (espace de champ) |
| **ICT-20** | Changepoints, EWS et hystérésis sont détectables en *feature-space* | `s` ✓, `q` ○ | Changepoint + EWS | Calibration baseline | Multi-seed | **Fortement soutenu** | Calibration = proxy direct sans commit sur la nature de la transition |
| **ICT-21** | Les features SAE Qwen-Scope (jalon 9B) tracent une trajectoire d'états discrets | `s` ✓, `q` ○ | Top-k features SAE (W64K-L0_50) | Modèle non-finetuné | 9B-Base | **Établi (jalon)** | Scope = 9B ; **panneau cross-échelle** (gamme Qwen3/Qwen3.5 700M → 120B) = chantier #5105 / #7396 à part, non livré ici (cf #7733 rectification A4) |
| **ICT-22** | Le transformer (4ᵉ substrat) s'intègre au banc cross-substrat | `s` ✓, `q` ✓, `W` ✓ | Double contrôle passif/actif | Tri, Gray-Scott, Axelrod (3 substrats témoins) | LLM 9B | **Établi** | GPU-required ; intégration cross-substrat effectivement négative (LLM = le plus faible sur Φ/F/K) |
| **ICT-23** | Le désalignement émergent est modélisable par fronce (V(p; a, b)) | `s` ✓, `q` ✓, `π` ✓ | Pli `a = -(transgression cumulée) × (charge sémantique)` | Inoculation (P0) — protocole arXiv:2511.18397 | Mesure in-context | **Fortement soutenu** | Jouet + mesure in-context ; l'inoculation aplatit le potentiel (a ≥ 0 → monostable) |
| **ICT-Argumentation** (Phase B) | 5 classes de drift Argumentum portent des dissociations croyances/structure causale mesurables | `s` ✓, `q` ✓, `W` ○ | Φ-trajectoire sur graphes d'arguments | Classes : IN_SYNC / SRC_DRIFT / TRAD_DRIFT / MISSING_LANG / ORPHAN_ROW | Multi-classe, multilingue | **Fortement soutenu** | Banc T2 Argumentum ; sub-grain Phase B du zoo ICT |
| **ICT-24** Gates 22-23 | L'ignition workspace (Baars) et l'emergence_gain (Hoel) **ne co-localisent pas** sur S4 | `s` ✓, `W` ✓ | Séries Gini + événements d'ignition persistants + fan-out + `emergence_gain` event-triggered | Contraste synthétique (+0.44) | Multi-seed | **Établi** | **Verdict dissociation** : les deux lectures IIT↔GWT capturent des choses différentes sur S4 |
| **ICT-24** Gate 24 | Le clamp sélectif d'une feature workspace modifie causalement l'ignition | `s` ✓, `W` ✓ | Ablation sélective | Substrat non-clampé | GPU phase 2 | **OPEN** | Coordonnateur GPU2 ; verdict en attente |
| **ICT-SAE-JLens** | SAE Qwen-Scope ≠ jacobien J-Lens neuronpedia sur le même modèle | `s` ✓, `W` ○ | Features différentielles (K_DIFF = 64), séries de concentration, matrices de séparation, dégradation top-k | 4 fixtures pré-extraites | 9B-Base, couche 16 | **Établi** | GPU-free ; banc numpy-only confrontant deux lentilles du même workspace |
| **ICT-25** | L'inoculation (permission) vs inoculation (interdit) : impact sur persona features | `s` ✓, `q` ✓, `π` ✓, `W` ✓ | GRPO × récompense hackable × 3 bras N/I/P | Bras pénalité-contraste | PR1 CPU livrée | **OPEN (phase 2 GPU)** | Réalignement 3 bras nécessaire (#5105) : le bras livré réprime (pénalité + interdit) au lieu de *permettre* (protocole Anthropic) |

### Capstones transverses

| Notebook | Claim | Objet 4-tuple | Proxy | Contrôle | Seeds | Verdict | Portée |
|---|---|---|---|---|---|---|---|
| **ICT-Synthèse** Gate 4 | Φ/F/K ordonnent les substrats différemment (Φ-F covarient, K diverge) | `s` ✓, `q` ○ | Φ/F/K mesurés sur 4-5 substrats | Substrats random / persistants | Multi-substrat | **Établi** | Φ-F τ de Kendall = +1.00 ; K disjoint — l'*invariant* est dans la *méthode*, pas dans le nombre |
| **ICT-Synthèse** Gate 5 | La réversibilisation (σ, distance à P_rev) discrimine orthogonalement aux jambes Φ/F/K | `s` ✓ | σ_real + distance à P_rev (échelle symlog) | Substrats réversibles (bistable ≈ 0) | Multi-substrat | **Établi** | Bistable quasi-nul ; tri fortement irréversible ; **l'asymétrie temporelle** est la jambe manquante du triplet |

## Repères vérifiables

- Issue-source [#7734](https://github.com/jsboige/CoursIA/issues/7734) — critères d'acceptation (une entrée par (notebook, claim), verdict sobre, portée explicite, pas de montée en obstruction cohomologique).
- Synthèse conceptuelle complémentaire (3-régimes : invariants / dissociations / obstructions) : [`docs/ict/synthese-invariants-dissociations-obstructions.md`](synthese-invariants-dissociations-obstructions.md) (See #7399). Les deux documents sont **complémentaires, non redondants** : la grille 3-régimes est conceptuelle et transversale ; cette matrice est opérationnelle et par-claim.
- Doc companion obstruction/recollement : [`docs/grothendieckian-lens.md`](../grothendieckian-lens.md) — la lecture cohomologique ICT est **candidate** (grade C), érigée en impossibilité seulement pour Kochen-Specker (#7290) et Arrow (`social_choice_lean`) ; cf rectification A2 du cadrage 2026-07-20 (#7733).
- Epic umbrella : [#4588](https://github.com/jsboige/CoursIA/issues/4588) — registre des livrables ICT.
- Dette de rigueur audit #4 : [#7733](https://github.com/jsboige/CoursIA/issues/7733) — 5 corrections A1-A5 propagées en PR #7889 (c.728y+33).

## Ce que cette matrice n'est pas

- **Pas un score de maturité.** Les verdicts sont `Établi` / `Fortement soutenu` / `Spéculatif`, **pas** une note. Un verdict `Spéculatif` n'est pas un échec — c'est l'état honnête d'un claim qui demande plus de seeds ou de contrefactuels avant de monter en généralité (cf ICT-11).
- **Pas une unification forcée.** Les 4 objets ne sont pas réductibles à un scalaire unique ; cette matrice le *montre* (chaque ligne situe le claim dans l'espace 4D), elle ne le *cache* pas.
- **Pas une montée en obstruction cohomologique.** Une dissociation est *décrite* ici (régime 2 du document companion) ; elle n'est jamais *élevée* en obstruction (régime 3) sans les prérequis (Kochen-Specker, Arrow, falsification cross-substrat déjà acquise). La discipline de la grille 3-régimes prévaut.
- **Pas un nouveau dispatch.** Aucune nouvelle dépendance expérimentale n'est créée ici. Les sous-issues (sensitivity ICT-15b, meta-proxy obstruction ICT-15c, argumentation Phase B, ICT-24c dérivée temporelle, ICT-25 3 bras) existent par ailleurs ; cette matrice les **référence**, ne les **déclenche** pas.
