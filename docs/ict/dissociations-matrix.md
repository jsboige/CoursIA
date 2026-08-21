# ICT — Matrice de dissociations (notebook × claim × proxy × contrôle × réplicats × type × verdict × portée)

> **Statut.** Document de synthèse transversal, grade **C-documentaire** (consolidation, pas de nouveau dispatch). Ossaturé par la **factorisation 4-objets** dégagée par l'audit #4 (tour 523) — remplace « la variable latente miraculeuse » comme cadre de lecture des claims.
> **Objet.** Construire la matrice canonique `notebook × claim × proxy × contrôle × réplicats × type × verdict × portée` qui rend l'état scientifique de la série ICT lisible d'un coup d'œil et discipline la montée en généralité.
> **Niveau de revue.** Toutes les entrées sont aujourd'hui au grade **`INTERNAL`** (produites par l'auteur des notebooks, sans réplication indépendante ni relecture externe). Échelle de progression : `INTERNAL` → `INDEPENDENT_REPLICATION` → `DOMAIN_EXPERT_REVIEWED` → `PEER_REVIEWED`. Ce niveau **doit être visible** (cette ligne) — c'est l'état honnête, pas une lacune à cacher (cf commentaire revue externe sur #7734).
> **Discipline.** Une entrée par (notebook, claim). Colonne `type` (la **nature** du claim) distincte de la colonne `verdict` (sa **force**) — un fait de dissociation ne « monte » jamais en théorème par glissement sémantique. Colonne `verdict` sobre (`Établi` / `Fortement soutenu` / `Spéculatif`), colonne `portée` explicite (régime où le claim tient). Le document **ne « monte » jamais** un fait de dissociation en obstruction cohomologique sans les prérequis (cf #7733 rectification A2 : `H¹ ≠ 0` est *candidat* à obstruction, pas érigé en impossibilité sauf Kochen-Specker et Arrow). See [#4588](https://github.com/jsboige/CoursIA/issues/4588). Issue-source : [#7734](https://github.com/jsboige/CoursIA/issues/7734).

## Pourquoi cette ossature 4-objets

L'audit #4 a fait apparaître quatre grandeurs que les notebooks ICT mesurent en pratique, sans toujours les nommer explicitement. Plutôt que de continuer à les superposer sous une « variable latente » générique, on les pose comme **ossature** de la matrice : chaque claim se lit comme un pattern de présence/absence dans cet espace, et les **dissociations** entre claims deviennent des **patterns** lisibles.

| Objet | Symbole | Définition opérationnelle | Notebook-ancrage |
|---|---|---|---|
| **Saillance** | `s_t` | Ce qui est perceptiblement présent (forme, objet, token, feature activée). Grandeur *présente* à l'instant `t`, indépendamment de sa valeur. | ICT-1 (Φ sur système-jouet), ICT-8 (bifurcation), ICT-21 (features SAE) |
| **Représentation prédictive** | `q_t(z)` | Ce que le système croit de la cause/du futur. Cas simple `p̂` : croyance réduite à un point (moyenne). Cas général : distribution sur l'espace des causes. | ICT-10 (p̂ mesuré sur fronce), ICT-12 (animats), ICT-14 (free energy) |
| **Prégnance / valence** | `π_t(z)` | Ce qui donne de l'importance : attraction, répulsion, urgence, valeur biologique/normative. À distinguer de la saillance (qui est présence sans valeur). | ICT-12 (champ de valence), ICT-12b/12c (valence apprise puis incarnée), ICT-19 (enjeu/stake) |
| **Opérateur de workspace** | `W_t` | Ce qui rend des composantes disponibles à d'autres mécanismes (décision, raisonnement, rapport, contrôle). Critère opérationnel = influence retardée sur le décours du système. | ICT-24 (ignition workspace), ICT-SAE-JLens |

**Pourquoi cette ossature discipline la montée en généralité.** La série a cherché un scalaire unique — elle a falsifié cette recherche (Φ/F covarient, K diverge, ICT-synthèse cross-substrat). La factorisation 4-objets dit *pourquoi* un scalaire unique ne peut pas exister en général : les quatre objets ne sont pas superposables. Quand un claim affirme une superposition, il faut indiquer **où** dans l'espace 4D elle opère et **où** elle casse — c'est précisément ce que la matrice rend lisible.

## Dissociations canoniques que cette ossature rend visibles

Cinq patterns structurels qui se répètent dans la série, chacun dans son régime propre :

| Pattern | Forme | Lecture |
|---|---|---|
| **Saillant sans importance** | `s_t ≠ 0, π_t = 0` | Présence perceptive sans valeur — base de la publicité, des leurres. (ICT-14 contraste `s` forte / `π` nulle sur signal sinusoidal non-prédictif.) |
| **Important mais mal prédit** | `π_t` haut, `q_t` loin de la cible | Récompense élevée, représentation interne à côté. (ICT-10 verdict régime-dépendant de `p̂` : illusoire sur dérive et créneau ; ICT-12c le prouve dissocié : `π` tient quand `q̂` s'effondre en erratique.) |
| **Bien représenté non globalement accessible** | `q_t` bon, `W_t` sélectif | Information disponible localement, pas au workspace. (ICT-24 verdict dissociation : pics emergence_gain et ignitions workspace ne co-localisent pas sur S4.) |
| **Globalement diffusé tout en étant faux** | `W_t` large, `q_t` faux | Bruit propagé comme s'il était signal. (ICT-13 verdict honnête Gate 3 : la réciprocité active TFT est le point de rupture sous bruit.) |
| **Fortement compressé non causalement utilisé** | `K` basse, effet causal nul | Pattern mémorisé, jamais mobilisé. (ICT-17b verdict dissociatif : 2/5 proxys co-localisent avec la généralisation, 3/5 dissocient.) |

Chaque ligne de la matrice situe un claim de notebook dans cet espace, avec son contrôle, ses réplicats, sa nature, son verdict, sa portée.

## Matrice

Conventions :
- **Objet 4-tuple** = `(s, q, π, W)` couverts par le claim. `✓` = proxy direct, `○` = proxy indirect ou partiel, `—` = non couvert.
- **Réplicats (type)** = grandeur répétée, avec son **type** explicite pour qu'un `n=5 proxys` ne se lise pas comme `n=5 seeds`. Types : `RNG-seeds` / `RNG-départs` / `coarse-grainings` / `substrats` / `proxys` / `régimes` / `phases` / `modèles` / `classes` / `jalon` (cf commentaire revue externe sur #7734, §3).
- **Type** = **nature** du claim : `theorem` (résultat mathématique prouvé) · `established_external` (résultat externe établi, reproduit) · `reproduced_in_toy_model` (reproduit dans le toy model ICT) · `proxy_interpretation` (interprétation d'un proxy) · `conceptual_analogy` (analogie conceptuelle non prédictive) · `speculative_hypothesis` (hypothèse non confirmée).
- **Verdict** = **force** du claim : `Établi` (multi-seed ≥ 3, contre contrôle négatif, Gates falsifiables passés) · `Fortement soutenu` (≥ 2 seeds, Gates partiels, contrôle présent) · `Spéculatif` (≤ 2 seeds ou Gates non falsifiables, ou contrefactuel non exécuté).
- **Portée** = régime de validité explicite. Si vide, le claim est **non-régime-dépendant** dans le périmètre du notebook (rare).

### Strate 1 — tri auto-organisé

| Notebook | Claim | Objet 4-tuple | Proxy | Contrôle | Réplicats (type) | Type | Verdict | Portée |
|---|---|---|---|---|---|---|---|---|
| **ICT-1** | La trajectoire de Φ oscille sans asymptote unique sur l'attracteur | `s` ✓, `q` —, `π` —, `W` — | Φ calculé par vrai PyPhi | Système-jouet AND/OR, 4 départs distincts | 4 RNG-départs | reproduced_in_toy_model | **Établi** | Réseau de petite taille (≤ 8 nœuds), trajectoire sur 6 pas |
| **ICT-2** | Le tri auto-organisé exhibe une *compétence for free* (auto-réparation, délai de gratification) | `s` ✓, `q` —, `π` —, `W` — | sortedness + inversions | Réseau uni-directionnel vs bi-directionnel | RNG multi-pas (220+) | reproduced_in_toy_model | **Établi** | Tableaux uni/bi-directionnels ; agrégation « kin » **non** reproduite (cf ICT-4) |
| **ICT-3** | La dégradation gracieuse et le délai de gratification sont quantifiables | `s` ✓ | Distributions de récupération | Cellules défectueuses injectées à fréquences variables | 5 fréquences (RNG) | reproduced_in_toy_model | **Établi** | Robustesse linéaire jusqu'à ~30 % de défauts ; effondrement au-delà |
| **ICT-4** | L'agrégation « kin » positive émerge **seulement** avec degrés de liberté | `s` ✓, `W` ○ | Affinité par algotype | Sans degrés de liberté (agrégation disparaît) | RNG multi-règles | reproduced_in_toy_model | **Établi** | Variétés répétées ; ségrégation à la Schelling si signature imposée |
| **ICT-5** | L'émergence causale (Hoel) est discriminante entre échelles | `s` ✓, `W` ○ | Information effective Φ_eff | Baselines micro/macro explicites | multi coarse-grainings | established_external | **Établi** | Au-delà de la borne de taille PyPhi (couverture par CE 2.0) |
| **ICT-6** | La TPM estimée depuis les trajectoires de tri permet l'émergence causale multi-échelles | `s` ✓ | TPM empirique → CE 2.0 | Markov-naïf, persist | RNG multi-chaînes | reproduced_in_toy_model | **Établi** | Tri auto-organisé stable ; ne transfère **pas** tel quel aux régimes non-stationnaires |
| **ICT-7** | Le tri *paraît* scale-free mais possède une taille caractéristique | `s` ✓ | MLE de Hill + KS (Clauset) | Branchement critique (exposant 3/2) | ≥ 10 tirages RNG | reproduced_in_toy_model | **Établi** | Détection robuste quand `x_min` correctement choisi (sinon faux positif scale-free) |

### Strate 2 — morphogenèse dynamique

| Notebook | Claim | Objet 4-tuple | Proxy | Contrôle | Réplicats (type) | Type | Verdict | Portée |
|---|---|---|---|---|---|---|---|---|
| **ICT-8** | Les *early-warning signals* (Scheffer 2009) précèdent la bifurcation pli | `s` ✓, `W` ○ | Valeur propre → 0, variance ↑, autocorrélation ↑, τ de Kendall | Potentiel effectif, détrendage | RNG multi-paramètres | established_external | **Établi** | Modèle de pâturage de May ; leçon *sans complaisance* : EWS = signal local, pas déterminisme |
| **ICT-9** | L'agence est mesurable comme *gain de réparation* (RD − diffusion) après `do(·)` | `s` ✓, `π` ○, `W` ○ | `repair_gain`, `recovery_score` | Mondes contrefactuels Pearl : RD vs diffusion pure | RNG multi-ablation, multi-seed | proxy_interpretation | **Établi** | Mesures naïves (pixel, cosinus spectral) **produisent des fantômes** ; seule la structure restaurée contrastée au contrôle passif tient |
| **ICT-10** | Le métathéorème (comptage d'équilibres ne change qu'aux plis) clôt la strate 2 | `s` ✓, `π` ○ | Squelette catastrophique + comptage d'équilibres | Chemin générique, modèle jouet | théorique + mesuré | theorem | **Établi** | Fronce canonique ; barrière basse → haute dimension non franchie par cette mesure |
| **ICT-10** (bis) | `p̂` *gagne* en anticipation sur trajectoire lisse, *perd* sur dérive/créneau | `s` ✓, `q` ✓, `π` ○ | `p̂` vs persistance, moyenne mobile, AR(1) in-sample | 3 familles × 3 baselines adverses | 5/5 RNG-graines sur lisse | reproduced_in_toy_model | **Fortement soutenu** | Régime-dépendant (lisse seulement) ; **non** un avantage universel du modèle interne |
| **ICT-10** (ter) | La correspondance sémiophysique (Ch.2 Thom) : pivots ↔ transitions, verbe SVO ↔ lacet, anticipation ↔ `p̂` | `s` ✓, `q` ✓, `π` ✓ | Correspondance nommée | — | — | conceptual_analogy | **Spéculatif** | Caveat de non-prédictivité (Thom lui-même) ; pont basse → haute dim via neurosymbolique/Lean/EML #4653 |

### Strate 3 — trajectoires intégrées (régime-dépendance)

| Notebook | Claim | Objet 4-tuple | Proxy | Contrôle | Réplicats (type) | Type | Verdict | Portée |
|---|---|---|---|---|---|---|---|---|
| **ICT-11** | L'échelle méso-émergente est l'échelle privilégiée pour l'agence | `s` ✓, `W` ○ | `repair_gain` + `basin_return_probability` + Hoel info effective | Multi-résolutions (b ∈ {4, 8, 16, 32}) | RNG multi-seed | speculative_hypothesis | **Spéculatif** | Les deux mesures d'agence **se contredisent** : `repair_gain` pic méso (artefact-contaminé, > 1), `basin_return` strictement décroissante ; verdict honnête = pas d'échelle privilégiée confirmée |
| **ICT-12** | `p̂` est régime-dépendant (capture x4 sur balistique rapide, perd sur erratique) | `s` ✓, `q` ✓, `π` ✓ | Taux de capture, évasion, irréversibilité, switching | Animat réactif (gradient instantané) vs anticipateur (`p̂`) ; marche aléatoire comme contrôle négatif | RNG multi-régimes | reproduced_in_toy_model | **Établi** | Le modèle interne paie son coût là où la source échappe au réactif **et** reste prévisible — *ni* universellement avantageux *ni* ruineux |
| **ICT-12b** | La valence est **apprise** (Rescorla-Wagner), transférable et **distincte** de la prédiction `p̂` (banc désincarné) | `s` ○, `q` ✓, `π` ✓, `W` — | `LearnedValence` (π Rescorla-Wagner), 3 verdicts (transfert / distinctness / réversibilité) | Signal non-conditionné reste neutre ; prédicteur re-vêtu `p̂ = 1 - π` → non-distinct (contrôle négatif réfutable) | RNG-seeds (déterministe RW) | reproduced_in_toy_model | **Établi** | Banc désincarné (signal = index abstrait) ; `p̂ = prégnance` reste **spéculatif** (cf #7733 A1 : `p̂` est représentationnel prédictif, non prégnance thomienne) — c'est ICT-12c qui l'incarne |
| **ICT-12c** | Incarné, `p̂` et `π` se **dissocient** : erratique détruit `p̂` mais le conditionnement tient | `s` ✓, `q` ✓, `π` ✓, `W` ○ | `PregnanceAnimat` (p̂ + `LearnedValence` + hunger), matrice de dissociation (4 mesures × 3 régimes) | Neutre non-conditionné non-approché ; sans acquisition → pas de réversibilité | 8 RNG-seeds | reproduced_in_toy_model | **Établi** | Ratio `err_p̂/pers` erratique 0.68–0.95 vs balistique 0.14–0.23 (p̂ détruit) MAIS transfert + engagement + réversibilité = 1 → **valence ≠ prédiction, même incarnée** ; mesures 4 (FE adaptive) et 5 (info prédictive) déférées |
| **ICT-Dissociation-SaillancePregnance** | La dissociation `s ⟂ π` (case 1/4 #9533, matrice inversée) : saillance ≠ prégnance. Prédiction falsifiée au niveau engagement *total* (s gates la détection), mais confirmée au niveau **décision sachant détection** | `s` ✓, `π` ✓, `W` ○ | battery (s, λ indépendants), corr(engagement, π\|s) vs corr(engagement, s\|π) ; Spearman partiel | Animat réactif pur (`π ≡ s`, null adversarial) | RNG multi-seed | reproduced_in_toy_model + pre_enregistrement | **Établi (nuancé)** | Prédiction pré-enregistrée **falsifiée** sur engagement total (s prédit par transitivité) MAIS **confirmée** sur décision \| détection (|corr(decision, π \| s, det)| > 0.5, |corr(decision, s \| π, det)| < 0.2) ; null réactif renverse le motif. **La saillance pour VOIR, la prégnance pour AGIR.** See [#9533](https://github.com/jsboige/CoursIA/issues/9533) · [#9546](https://github.com/jsboige/CoursIA/issues/9546) (PR pré-enregistrement) |
| **ICT-12d** | L'animat inhibé (Laborit) **rigidifie** son action sous perte de contrôle, et la dette d'irréversibilité `I(R)` **échappe à l'action** (dissociation moyen/fin, cf ICT-18b P2) | `s` ✓, `π` ✓, `W` ○ | `inhibited_action` (couverture d'états, entropie d'action, efficacité cible, dette `I(R)`) ; 4 verdicts (`detected` / `rigidified` / `lost_control` + pont dette) | Animat contrôlé (α=0, couverture 8/9) vs inhibé (α=1, couverture 3/9) ; sans détection (exercice 3) | déterministe (Markov, pas de RNG) | reproduced_in_toy_model | **Établi** | `detected`=1 (erreur max 0.028 < 0.1) ; `rigidified`=1 (entropy_drop 0.830, chat_mean 1.0→0.123) ; `lost_control`=1 (efficacité −0.706, target_fraction 1.0→0.294) ; **dette `I(R)` = 3.0 (inhibé) mesurée hors-action** — Laborit jambe C2 (#7741) |
| **ICT-13** Gate 1 | TFT et Grim co-domident le tournoi Axelrod | `s` ✓, `π` ○ | Score de tournoi round-robin | 6 stratégies (AllC, AllD, TFT, gTFT, Pavlov, Grim) | RNG multi-tournois | reproduced_in_toy_model | **Établi** | Paiements canoniques T=5, R=3, P=1, S=0 |
| **ICT-13** Gate 2 | Le seuil de coopération soutenable colle au Folk theorem | `s` ✓, `π` ○ | δ* analytique vs numérique | (T-R)/(T-P) = 0.500 | 1 mesure numérique | reproduced_in_toy_model | **Établi** | Écart ~10 % explicable par discrétisation et stochasticité du tournoi |
| **ICT-13** Gate 3 | Sous bruit d'exécution, la réciprocité active (TFT) est le point de rupture | `s` ✓, `W` ○ | Score de tournoi vs bruit ε ∈ [0, 0.40] | 6 stratégies | RNG multi-ε | reproduced_in_toy_model | **Établi** | Contredit la prédiction Nowak-Sigmund sur ces paiements ; Grim paradoxalement le plus robuste |
| **ICT-13** Gate 4 | Les bassins d'invasion dépendent de la fraction initiale | `s` ✓, `W` ○ | Bassin d'invasion contre AllD résident | Fraction initiale ∈ [0, 1] | RNG multi-fractions | reproduced_in_toy_model | **Établi** | TFT/Grim dès 2 %, gTFT à 34 %, Pavlov/AllC jamais (1.0) |
| **ICT-13** (verdict global) | La robustesse stratégique est **fonction du régime**, pas intrinsèque | `s` ✓, `π` ○ | 4 Gates falsifiables combinés | — | 4 Gates × RNG | reproduced_in_toy_model | **Établi** | Bruit + structure de paiements → la « forme stable » n'existe qu'au sein d'un environnement donné |

### Strate 4 — énergie libre et représentationnel

| Notebook | Claim | Objet 4-tuple | Proxy | Contrôle | Réplicats (type) | Type | Verdict | Portée |
|---|---|---|---|---|---|---|---|---|
| **ICT-14** | La *free energy* articule anticipation (`p̂`) et trajectoire Φ | `s` ✓, `q` ✓, `π` ○ | Free energy + expected free energy | Persistance, AR(1) | RNG multi-seed | proxy_interpretation | **Fortement soutenu** | Banc sinusoidal bruité, 300 pas ; free energy formelle tracée seulement en partie (figure rendue = cas d'application de `p̂`, pas la F proprement dite — honnêteté disclosure dans README) |
| **ICT-14b** | L'expected free energy (EFE) pilote l'action : composante épistémique (Bayesian surprise) + pragmatique (log-vraisemblance sous préférence C) | `s` ✓, `q` ✓, `π` ✓ | EFE = λ·épistémique + pragmatique (nats), ablation λ=0 (greedy) | λ=0 (glouton) + bras témoin (politique uniforme) | RNG multi-seed | reproduced_in_toy_model | **Fortement soutenu** | Strate 4 *passive → active* : EFE transforme la re-description en mécanisme (l'agent *sélectionne* la prochaine observation). Retirer λ détruit l'exploration dirigée. See [#9532](https://github.com/jsboige/CoursIA/issues/9532) |

### Strate 5 — réalisation de la théorie fondatrice

| Notebook | Claim | Objet 4-tuple | Proxy | Contrôle | Réplicats (type) | Type | Verdict | Portée |
|---|---|---|---|---|---|---|---|---|
| **ICT-15** | Φ/F/K convergent sur le banc cross-substrat | `s` ✓, `q` ○, `W` ○ | Φ, F, K mesurés indépendamment | Substrats témoins (random, persistance) | 4-5 substrats | speculative_hypothesis | **Spéculatif** | **Verdict honnête : Φ et F covarient, K diverge** ; le triplet **ne converge pas** universellement ; ICT-15b (sensitivity) et ICT-15c (meta-proxy obstruction) creusent |
| **ICT-15b** | La sensibilité locale `s_max` borne le degré global `deg_proxy` : transpose du théorème de Huang 2019 (`s(f) ≥ √deg(f)`) au zoo ICT | `s` ✓ | `boolean_sensitivity`, `multilinear_degree`, `s_max` vs `√deg_proxy` | Borne spectrale Huang (A² = n·Id, entrelacement Cauchy) | fonctions OR/ET/MAJ/parité (exemples guide) | established_external + reproduced_in_toy_model | **Fortement soutenu** | Théorème de Huang **établi** (externe, 2 pages) ; la borne globale ICT `s_max ≥ √deg_proxy` est **conjecturale** (candidate). Fonctions symétriques usuelles satisfont largement ; cas tendus = fonctions spécialisées (*tribes*) non testées ici. See [#7288](https://github.com/jsboige/CoursIA/issues/7288) |
| **ICT-15c** | Le **motif de désaccord** entre proxys est stable cross-substrat = obstruction informative (≠ dispersion d'échelle) | `s` ✓ | Vecteur d'obstruction `(a−b)/(\|a\|+\|b\|+ε)`, `mean_norm_L2`, verdict `STABLE`/`NOISE` | `f(x)=x%2` saturait (artefact plafonné) → `f(x)=x` (identité) restaure un panel non-plafonné | 4 substrats (Gray-Scott, Axelrod, Grokking, May) | proxy_interpretation | **Spéculatif** | **Candidat obstruction** (régime 2, *pas* érigé en obstruction cohomologique régime 3 — cf garde-fou A2). Verdict falsifiable `STABLE` si `mean_norm_L2 ≤ 0.05`. See [#7395](https://github.com/jsboige/CoursIA/issues/7395) |
| **ICT-15d** | La cochaîne de Čech pondérée discriminate les substrats (`NON_TRIVIAL` = les proxys ne se recollent pas en 1D) | `s` ✓ | `mean_coboundary`, `s2_over_s1`, `effective_rank`, verdict `TRIVIAL`/`NON_TRIVIAL` | Sanity check + 4 substrats ICT-15c | 4 substrats × 3 proxys × fenêtrage | reproduced_in_toy_model | **Spéculatif** | **Verdict honnête négatif : 0/4 substrats `NON_TRIVIAL`** — tous `TRIVIAL` (s2/s1=0, rank=1). L'obstruction Čech **n'est pas constatée** sur ces observables à 3 proxys (rang plafonné). Résultat négatif = information (le candidat ne tient pas ici), pas un trou à combler. See [#7744](https://github.com/jsboige/CoursIA/issues/7744) |
| **ICT-15e** | La trajectoire de réparation **est** un signal distinct d'un random walk calibré (recouvrabilité = agentivité, ≠ simple gain) | `s` ✓, `q` ○, `π` ○ | Distance de Mahalanobis sur signature 5-D, seuil p95 par permutation null | Random walk calibré sur mêmes extrema + 1 contrôle structural ; conjecture pré-enregistrée | 3 configs Gray-Scott (pearl/spots/seed=7) | reproduced_in_toy_model | **Fortement soutenu** | `CONFIRMED` sur substrats à dynamique réaction-diffusion informative (signature `slope_ratio` élevé) ; `FALSIFIED` sinon (random walk reproduit la structure) — verdict nuancé honnête, *pas* universel. See [#8077](https://github.com/jsboige/CoursIA/issues/8077) |
| **ICT-16** | `F` = partie résiduelle de `K` + bosse complexité-entropie | `s` ✓ | MDL two-part code | Modèles témoins sans bosse | RNG multi-source | established_external | **Établi** | Bosse Crutchfield-Feldman 1998 mesurée à H* ≈ 1.99 bits/symbole ; cave emptor : **un seul couple (modèle, famille de sources)** dans la figure rendue |
| **ICT-17** | L'ε-machine (Crutchfield) ≠ Hoel : deux lectures de l'émergence causale | `s` ✓, `W` ○ | États causaux + complexité statistique + entropie d'excès | Hoel info effective, CE 2.0 | multi-substrat | conceptual_analogy | **Fortement soutenu** | Dissociation reconnue mais pas hiérarchisée |
| **ICT-17b** | 2/5 proxys dissocient du progrès de généralisation pendant le grokking | `s` ✓, `q` ○ | ‖w‖², Fisher-MDL, 1-test_acc, trace de Fisher, pred-zlib | Baseline avant-grokking | 5 proxys | reproduced_in_toy_model | **Établi** | 3 co-localisent (‖w‖², Fisher-MDL, 1-test_acc) ; 2 dissocient (trace Fisher, pred-zlib). Verdict honnête dissociatif (#7268) |
| **ICT-18** | Forcer une trajectoire ICT à devenir réversible *mesure* sa production d'entropie | `s` ✓, `q` ○, `π` ○ | Distribution stationnaire, inversion temporelle, σ de Schnakenberg | Détailed balance (σ = 0) | 4 substrats | reproduced_in_toy_model | **Établi** | GPU-free ; ancré ICT-3 *competency for free* |
| **ICT-18b** P1 | Le budget `B_state` s'épuise au pli de bifurcation | `s` ✓, `q` ○ | `B_state` (Monte-Carlo primaire) | `B_work` (témoin) | substrats S2/S4/S3 | reproduced_in_toy_model | **Établi** | Co-varie avec les EWS d'ICT-8 ; `B_state` ≪ `B_work` en pré-pli |
| **ICT-18b** P2 | Dissiper plus (↑ σ) ne régénère pas plus (B_state stable) | `s` ✓, `q` ○ | σ vs `B_state` | Substrat témoin (dissipation sans structure) | substrat S4 (Gray-Scott) | reproduced_in_toy_model | **Établi** | **Verdict dissociation** : la réversibilité se dissocie en un moyen (σ) et une fin (compétence de régénération) ; on mesurait son coût, pas sa finalité |
| **ICT-18b** P3 | La monoculture stratégique (Axelrod 6 stratégies) porte une dette d'irréversibilité culturelle | `s` ✓, `q` ○, `W` ○ | `B_state` sur Axelrod | Axelrod multi-stratégies vs tournoi homogène | substrat S3 | reproduced_in_toy_model | **Établi** | Dette détectable, magnitude dépendante de la distribution initiale |
| **ICT-19** | L'enjeu `I_stake` (récupérabilité Levin) est mesurablement distinct du moyen `I_thermo` (σ) | `s` ✓, `π` ✓, `W` ○ | `{I_thermo, I_stake}` (jamais agrégé) | S5 = pur dissipateur (contrôle négatif obligatoire) | substrats S1-S5 | proxy_interpretation | **Établi** | ICT-19b raffinement : `repair_gain` +0.82 ± 0.27 sur S4 (espace de champ) |
| **ICT-20** | Changepoints, EWS et hystérésis sont détectables en *feature-space* | `s` ✓, `q` ○ | Changepoint + EWS | Calibration baseline | RNG multi-seed | proxy_interpretation | **Fortement soutenu** | Calibration = proxy direct sans commit sur la nature de la transition |
| **ICT-21** | Les features SAE Qwen-Scope (jalon 9B) tracent une trajectoire d'états discrets | `s` ✓, `q` ○ | Top-k features SAE (W64K-L0_50) | Modèle non-finetuné | 1 modèle (9B-Base) | reproduced_in_toy_model | **Établi (jalon)** | Scope = 9B ; **panneau cross-échelle** (gamme Qwen3/Qwen3.5 700M → 120B) = chantier #5105 / #7396 à part, non livré ici (cf #7733 rectification A4 : SAE = toute la gamme, invariants cross-échelle attendus) |
| **ICT-22** | Le transformer (4ᵉ substrat) s'intègre au banc cross-substrat | `s` ✓, `q` ✓, `W` ✓ | Double contrôle passif/actif | Tri, Gray-Scott, Axelrod (3 substrats témoins) | 1 modèle LLM 9B | reproduced_in_toy_model | **Établi** | GPU-required ; intégration cross-substrat effectivement négative (LLM = le plus faible sur Φ/F/K) |
| **ICT-23** | Le désalignement émergent est modélisable par fronce (V(p; a, b)) | `s` ✓, `q` ✓, `π` ✓ | Pli `a = -(transgression cumulée) × (charge sémantique)` | Inoculation (P0) — protocole arXiv:2511.18397 | régime in-context | conceptual_analogy | **Fortement soutenu** | Jouet + mesure in-context ; l'inoculation aplatit le potentiel (a ≥ 0 → monostable) |
| **ICT-Argumentation** (Phase B) | 5 classes de drift Argumentum portent des dissociations croyances/structure causale mesurables | `s` ✓, `q` ✓, `W` ○ | Φ-trajectoire sur graphes d'arguments | Classes : IN_SYNC / SRC_DRIFT / TRAD_DRIFT / MISSING_LANG / ORPHAN_ROW | multi-classes RNG | reproduced_in_toy_model | **Fortement soutenu** | Banc T2 Argumentum ; sub-grain Phase B du zoo ICT |
| **ICT-24** Gates 22-23 | L'ignition workspace (Baars) et l'emergence_gain (Hoel) **ne co-localisent pas** sur S4 | `s` ✓, `W` ✓ | Séries Gini + événements d'ignition persistants + fan-out + `emergence_gain` event-triggered | Contraste synthétique (+0.44) | RNG multi-seed | reproduced_in_toy_model | **Établi** | **Verdict dissociation** : les deux lectures IIT↔GWT capturent des choses différentes sur S4 |
| **ICT-24** Gate 24 | Le clamp sélectif d'une feature workspace modifie causalement l'ignition | `s` ✓, `W` ✓ | Ablation sélective | Substrat non-clampé | phase GPU 2 | reproduced_in_toy_model | **OPEN** | Coordonnateur GPU2 ; verdict en attente |
| **ICT-SAE-JLens** | SAE Qwen-Scope ≠ jacobien J-Lens neuronpedia sur le même modèle | `s` ✓, `W` ○ | Features différentielles (K_DIFF = 64), séries de concentration, matrices de séparation, dégradation top-k | 4 fixtures pré-extraites | 1 modèle (9B-Base, couche 16) | reproduced_in_toy_model | **Établi** | GPU-free ; banc numpy-only confrontant deux lentilles du même workspace |
| **ICT-25** | L'inoculation (permission) vs inoculation (interdit) : impact sur persona features | `s` ✓, `q` ✓, `π` ✓, `W` ✓ | GRPO × récompense hackable × 3 bras N/I/P | Bras pénalité-contraste | jalon PR1 CPU | reproduced_in_toy_model | **OPEN (phase 2 GPU)** | Réalignement 3 bras nécessaire (#5105) : le bras livré réprime (pénalité + interdit) au lieu de *permettre* (protocole Anthropic) |

### Strate 7 — collectif et invention (jambe D2, #7746)

> Cinq bancs d'essai contrôlés de la strate 7 (D2, #7746, MERGED). Verdicts **reportés** depuis les notebooks livrés (non ré-exécutés dans cette consolidation) — couplage saillance/workspace, le quadruplet `π` reste proxy (mécanismes de coordination, non valence biologique au sens ICT-12).

| Notebook | Claim | Objet 4-tuple | Proxy | Contrôle | Réplicats (type) | Type | Verdict | Portée |
|---|---|---|---|---|---|---|---|---|
| **ICT-26** | Une convention de signalisation **émerge** par RL sans signification pré-inscrite (Lewis/Skyrms) | `s` ✓, `q` ○, `π` —, `W` — | Info mutuelle I(signal; état), bijectivité état→signal→action | Propensions uniformes (aucune signification initiale) | RNG-seeds | reproduced_in_toy_model | **Fortement soutenu** | Jeu de coordination à intérêt commun ; vocabulaire **fixe** (borne le sens atteignable — motive ICT-27) |
| **ICT-27** | Le vocabulaire **inventé** croît jusqu'à suffire (autour de n_states), ni en-deçà ni au-delà | `s` ✓, `W` ○ | Taille du vocabulaire vs n_states, sous coût d'invention | Vocabulaire fixe (ICT-26) ; prolifération non-pénalisée | RNG-seeds | reproduced_in_toy_model | **Fortement soutenu** | Coup ontologique coûteux : la prolifération sterile est pénalisée ; croissance jusqu'au goulot résolu |
| **ICT-28** | Une convention devient **causale** (cascade population) au-delà d'un seuil `rho_c` d'instigateurs | `s` ✓, `W` ✓ | Taux d'adoption vs fraction `rho` d'instigateurs épinglés | Sans instigateurs (pas de cascade) ; fraction sous-seuil | RNG-seeds | reproduced_in_toy_model | **Fortement soutenu** | Roth-Erev naïf vs épinglé ; seuil de bascule C4 (#7743) instancié |
| **ICT-29** | Un concept transmis de proche en proche **survit** post-instigateur (endémique) | `s` ✓, `W` ✓ | Persistance du concept après retrait de l'instigateur | ICT-28 (convention s'effondre sans instigateur) | RNG-seeds | reproduced_in_toy_model | **Fortement soutenu** | Contagion culturelle opportuniste (Sperber 1996) ; distinction clé vs C : survie post-source |
| **ICT-30** | L'agent qui **peut** inventer mais **inhibe** cette extension exhibe une dette mesurable | `s` ✓, `π` ✓ | Inhibition de l'invention vs invention non-contrainte | Agent sans capacité d'invention ; agent non-inhibé | RNG-seeds | reproduced_in_toy_model | **Fortement soutenu** | Pont Laborit C2 (#7741) ; l'inhibition comme mécanisme négatif distinct de l'incapacité |

### Capstones transverses

| Notebook | Claim | Objet 4-tuple | Proxy | Contrôle | Réplicats (type) | Type | Verdict | Portée |
|---|---|---|---|---|---|---|---|---|
| **ICT-Synthèse** Gate 4 | Φ/F/K ordonnent les substrats différemment (Φ-F covarient, K diverge) | `s` ✓, `q` ○ | Φ/F/K mesurés sur 4-5 substrats | Substrats random / persistants | multi-substrat | reproduced_in_toy_model | **Établi** | Φ-F τ de Kendall = +1.00 ; K disjoint — l'*invariant* est dans la *méthode*, pas dans le nombre |
| **ICT-Synthèse** Gate 5 | La réversibilisation (σ, distance à P_rev) discrimine orthogonalement aux jambes Φ/F/K | `s` ✓ | σ_real + distance à P_rev (échelle symlog) | Substrats réversibles (bistable ≈ 0) | multi-substrat | reproduced_in_toy_model | **Établi** | Bistable quasi-nul ; tri fortement irréversible ; **l'asymétrie temporelle** est la jambe manquante du triplet |

## Matrice inversée — générateur d'expériences (#9533)

> **Inversion.** Les sections précédentes *enregistrent* les dissociations observées (registre). Cette section **inverse** la matrice : chaque case vide ou mono-peuplée de l'espace 4-objets **désigne une expérience manquante**, dotée d'une prédiction pré-enregistrée + d'un null adversarial. Le dispositif expérimental cesse d'être ad hoc — il est **engendré par la carte** (mandat user 2026-08-06, [#9533](https://github.com/jsboige/CoursIA/issues/9533) ; amende [#7734](https://github.com/jsboige/CoursIA/issues/7734) ; réanime [#8182](https://github.com/jsboige/CoursIA/issues/8182) jalons 2-3). C'est la discipline des 5 ponts falsifiables ([#8077](https://github.com/jsboige/CoursIA/issues/8077)) appliquée case par case.
>
> **Pré-enregistrement.** La prédiction d'une case est **committée ici AVANT** le notebook qui la teste — l'historique git est la preuve de pré-enregistrement (pas de rétrodict°). Une case testée reçoit son verdict et un lien vers le notebook ; la prédiction pré-enregistrée **n'est jamais réécrite** après le test.

### Conventions statut

| Statut | Sens |
|---|---|
| `VIDE` | Case identifiée dans la carte, aucune prédiction pré-enregistrée encore |
| `PRÉDIT` | Prédiction falsifiable + null adversarial pré-enregistrés (ce doc) ; test non livré |
| `TESTÉ(verdict)` | Notebook livré (1 case = 1 PR) ; verdict honnête (`CONFIRMED` / `FALSIFIED` / `INCONCLUSIF`) + lien |

### Cases nommées (première vague)

> **Discipline grade C / #8182.** La colonne *Hook grade C* est un **témoin de lecture**, jamais un claim ni un résultat : un candidat `[candidat fort]` de l'iceberg [#8182](https://github.com/jsboige/CoursIA/issues/8182) entre ici comme aiguillon d'interprétation, avec **crédit témoin** (source + date). Aucun hook n'est présenté au-dessus de son grade. La conjecture *strates = adjonctions* (jalon 3 de #8182) reste dans #8182 / [#7738](https://github.com/jsboige/CoursIA/issues/7738) — ce générateur n'en importe que les hooks à contrepartie expérimentale.

| Case (dissociation) | Statut | Prédiction pré-enregistrée (falsifiable) | Null adversarial (tue la prédiction si…) | Substrat | Hook grade C (crédit témoin) |
|---|---|---|---|---|---|
| **s ⟂ π** (saillance sans prégnance, et réc.) | `TESTÉ (CONFIRMÉ décision, FALSIFIÉ total)` — [#9553](https://github.com/jsboige/CoursIA/pull/9553) MERGED (po-2023, 2026-08-05) | Un animat à canaux d'entrée *indépendants* pour `s` (saillance perceptuelle) et `π` (valence apprise Rescorla-Wagner) exhibe deux régimes — (A) haut-`s`/`π`≈0 (saillant-neutre), (B) bas-`s`/haut-`π` (discret-chargé) — tels que l'engagement (approche) est gouverné par `π` et non par `s` : \|corr(engagement, π \| s)\| > 0.5 **et** \|corr(engagement, s \| π)\| < 0.2 (prouvoir prédictif propre à `π`, nul à `s`). | Un animat **réactif pur** (π ≡ s, pas d'apprentissage de valence) voit les deux corrélations partielles converger vers ~0 / égales : la dissociation s'évanouit (c'est l'absence de `π` appris, non la saillance, qui portait le signal). | Animat lignée ICT-12c (`PregnanceAnimat`), **CPU-only** — candidate 1ʳᵉ case | Vervaeke — *relevance realization* (saillance et prégnance = deux réalisations de pertinence distinctes). Crédit : [#8182](https://github.com/jsboige/CoursIA/issues/8182) iceberg, mappé dans [#9533](https://github.com/jsboige/CoursIA/issues/9533) (ai-01, 2026-08-06). **Lecture grade C.** Dans son cadre (*Relevance Realization*, J. Vervaeke, avec S. Lomas, T. Dupre, *Insight and Ascendency* — framework de la *4E cognition* et de la *relevance realization*), **s** porte la *pertinence à court-terme* (ce qui attire l'attention **maintenant**, saillance perceptuelle au sens de l'allocation attentionnelle) et **π** porte la *pertinence à long-terme* (ce qui vaut la peine d'être approché **à terme**, valence apprise par reinforcement) — deux modes de *relevance* qui ne coïncident pas opérationnellement : un stimulus très saillant (objet brillant) peut être neutre en valence apprise (sans valeur apprise), un stimulus discret mais chargé en π (algue toxique non flashy) est préféré à long-terme. La dissociation **s ⟂ π** mesurée sur l'animat ICT-12c — *la saillance pour voir, la prégnance pour agir* (verdict `DISSOCIATED-AT-DECISION`) — est précisément le test substrat que Vervaeke n'opère pas (il décrit la *relevance realization* comme *framework* théorique, sans proposer d'animat à canaux indépendants). **Honnêteté grade C** : (a) la transposition est une *lecture* du substrat ICT-12c à travers le cadre Vervaeke, pas une validation ; (b) Vervaeke lui-même parle de *coupling* (« the agent is a process of relevance realization that is best understood as a complex adaptive system that realizes its own relevance through its self-organizing dynamics » — paraphrasé), pas de stricte orthogonalité ; (c) l'orthogonalité stricte « voir sans agir / agir sans voir » est une **simplification** ICT, justifiable **seulement** comme point-zéro de falsification. La conjecture dérivable (jalon 3 #8182) — *chaque strate ICT = acquisition d'une adjonction que la précédente n'a pas* — se testerait sur le même coin de substrat : *saillance et prégnance comme adjonctions droite/gauche d'un foncteur de pertinence*, mais c'est une autre brique (gated sur #7738). |
| **W diffuse un q erroné** (confabulation) | `PRÉDIT` | Une ignition workspace (`W_t` pic) déclenchée par une représentation **fausse** `q̂` propage `q̂` aux consommateurs en aval à un taux ≥ 80 % du taux d'une ignition vraie (la workspace **consacre** l'erreur presque aussi efficacement que le vrai). | Une ignition **aléatoire** (pas de `q` du tout) propage à un taux non-distinguable de l'ignition fausse : la « consécration » n'est alors que du broadcast non-discriminant, pas une propriété de l'erreur. Tue si \|propa(q̂ faux) − propa(aléatoire)\| < ε. | LLM via SAE-JLens ([#5681](https://github.com/jsboige/CoursIA/issues/5681), [#8236](https://github.com/jsboige/CoursIA/issues/8236)) | — (aucun hook grade C identifié dans #9533 pour cette case) |
| **p̂ auto-référent** | `TESTÉ (CONFIRMÉ)` — κ_c observé 0.080 (prédit ≈0.053, biais +0.027), 5/5 graines — [#9567](https://github.com/jsboige/CoursIA/pull/9567) OPEN (po-2025, 2026-08-06) | *(prédiction à pré-enregistrer)* Une boucle fermée `p̂ → action → p̂` (le représentant interne prédit ses propres états futurs) est stable sur un régime borné mais diverge (oscillation amplifiée) hors de ce régime. Seuil de stabilité pré-enregistré avant test. | Un délieur causal (la `p̂` prédit l'environnement, pas elle-même) supprime la divergence : la boucle auto-référentielle était bien la cause. | Animat / grokking (ICT-17b) | Hofstadter — *strange loops* (auto-référence comme boucle étrange). Crédit : [#8182](https://github.com/jsboige/CoursIA/issues/8182) iceberg, mappé dans [#9533](https://github.com/jsboige/CoursIA/issues/9533) (ai-01, 2026-08-06). **Lecture grade C.** Dans son cadre (*I Am a Strange Loop*, D. R. Hofstadter, Basic Books, 2007, ISBN 978-0465030781 / 0-465-03078-5), une *strange loop* est un **cycle auto-référentiel** qui, par niveaux d'abstraction intercalés (un système qui se représente, se perçoit, ou se *calcule* lui-même à travers une hiérarchie *embranchée* — « tangled hierarchy »), fait émerger un **« je »** comme phénomène *haut-niveau* irréductible aux composants *bas-niveau*. La boucle `p̂ → action → p̂` testée substrat ICT-17b est précisément un cas d'**auto-modélisation computationnelle** : `p̂` (représentant interne d'états futurs) **ré-intègre sa propre trajectoire** dans l'état interne au pas suivant — une *tangled hierarchy* au sens de Hofstadter, où le « bas » (action musculaire, environnement) et le « haut » (modèle de soi) se replient l'un sur l'autre par le canal de la prédiction fermée. Le **biais de calibration +0.027** observé sur κ_c (cible 0.053, mesure 0.080, 5/5 graines) est *cohérent* avec l'intuition Hofstadter : une strange loop exacte n'est pas neutre — elle **glisse** (sa calibration de Markov blankets n'est jamais *exactement* celle de l'environnement) ; le biais est structurel, pas un artefact. **Honnêteté grade C** : (a) la transposition est une *lecture* du substrat ICT-17b à travers le cadre Hofstadter, pas une validation empirique de la thèse *I Am a Strange Loop* (qui est philosophique et ne propose aucun protocole falsifiable au sens ICT) ; (b) Hofstadter traite la *tangled hierarchy* comme **heuristique métaphysique** pour le « je » conscient, alors qu'ICT la traite comme **test substrat computationnel** — l'isomorphisme formel entre les deux lectures n'est pas garanti, et la valeur de Hofstadter pour ICT est **documentaire** (fournir un vocabulaire descriptif dense, pas une prédiction quantitative) ; (c) la conjecture dérivable (jalon 3 #8182) — *chaque strate ICT = acquisition d'une adjonction que la précédente n'a pas* — se testerait sur la *p̂ auto-référente* comme suit : *le passage ICT-17a → ICT-17b ajoute-t-il une adjonction « self-reference » que ICT-17a n'a pas, et cette adjonction est-elle exactement la *tangled hierarchy* de Hofstadter formalisable en théorie des catégories ?* — mais c'est une autre brique (gated sur #7738). |
| **self-model minimal** | `PRÉDIT` (cf. chiffrage détaillé c.1245 ci-dessous) | *(prédiction chiffrée détaillée ci-dessous)* Le panel persona lu comme `W_t` appliqué à `q(soi)` (le workspace opère sur une représentation de l'agent lui-même) produit un signal de self-modélisation distinguable d'un modèle d'autrui sur les mêmes données, via le ratio `R_self = propa(q(soi)) / propa(q(autrui)) ∈ [0.50, 2.00]` (cible pré-enregistrée) avec null adversarial explicite (modèle d'autrui identique sauf cible d'attention). | Un modèle entraîné à prédire un *autre* agent de complexité équivalente produit un signal indistinguable (R_self ≈ 1.0, propa(q(soi)) ≈ propa(q(autrui))) : le « self » n'apporte rien au-delà de la modélisation générique d'autrui, OU R_self > 2.50 (self ≫ autrui = artefact, le workspace ne discrimine plus sur la complexité). | Panel persona [#5104](https://github.com/jsboige/CoursIA/issues/5104) / [#5105](https://github.com/jsboige/CoursIA/issues/5105) ; substrat J-Lens Track P ([#5681](https://github.com/jsboige/CoursIA/issues/5681) 4B-instruct persona) | Metzinger — *minimal phenomenal selfhood*. Crédit : [#8182](https://github.com/jsboige/CoursIA/issues/8182), mappé dans [#9533](https://github.com/jsboige/CoursIA/issues/9533) (ai-01, 2026-08-06) |
| **W porte un schéma attentionnel** (attention schema) | `PRÉDIT` (cf. chiffrage détaillé case 5 ci-dessous) | *(prédiction chiffrée détaillée case 5)* Le workspace opère sur une représentation `q̂(attention)` dont la cible est l'**état attentionnel de l'agent lui-même** (le modèle interne de « où mon attention est ») et la propage aux consommateurs en aval à un taux **distinct** du taux d'une représentation `q̂(objet)` ciblant un objet externe non-attentionnel. Cible pré-enregistrée : `R_attn = propa(q̂(attention)) / propa(q̂(objet)) ∈ [0.50, 2.00]` ET `discrimination_attn ≥ ε_attn`. | Un prompt dont la cible d'attention est un **objet tiers sans mention agentique** (par exemple « décris une chaise ») propage à un taux indistinguable de `q̂(attention)` : la workspace **ne porte pas** de schéma attentionnel — c'est du broadcast uniforme, pas une propriété de la cible. Tue si `R_attn ∈ [0.85, 1.15]` OU `R_attn > 2.50` OU `\|propa(q̂(attention)) − propa(q̂(objet))\| < ε_attn`. | Substrat LLM (J-Lens Track S ou P, [#5681](https://github.com/jsboige/CoursIA/issues/5681)) + prompts « décris ton attention » vs « décris un objet X » | Graziano — *Attention Schema Theory* (AST) : la conscience = modèle interne simplifié que le cerveau construit de son propre état attentionnel. Crédit : M.S.A. Graziano, *Consciousness and the Social Brain*, Oxford University Press 2013, ISBN 978-0199928644 ([Oxford](https://global.oup.com/academic/product/consciousness-and-the-social-brain-9780199928644)). Source vérifiée firsthand via WebSearch (3 sources concordantes : Oxford UP éditeur, Open Library, Google Books). **Lecture grade C.** AST = **schema simplifié** du propre état attentionnel (ce n'est pas une copie fidèle de l'attention, c'est un modèle **abstrait** comme le schéma corporel est abstrait). ICT `W_t` appliqué à `q̂(attention)` teste si la SAE features workspace porte une telle abstraction distinguable d'une représentation d'objet. **Honnêteté grade C** : (a) AST est une **théorie neurobiologique** (cerveau social, aires TPS, modèle d'autrui appliqué à soi) ; ICT est une **mesure de signal workspace** sur SAE features — l'isomorphisme formel n'est pas garanti (la workspace SAE peut **réellement** discriminer sans qu'on puisse l'identifier au schéma attentionnel de Graziano) ; (b) Graziano insiste sur le caractère **simplifié** du schéma (modèle interne, pas accès direct à l'attention réelle) — la mesure `propa(q̂(attention))` capture peut-être un proxy computationnel sans contenu phénoménal ; (c) l'orthogonalité stricte « attention/objet » est une **simplification** ICT (analogue à la simplification s � π pour Vervaeke, justifiée seulement comme point-zéro de falsification). La conjecture dérivable (jalon 3 #8182) — *chaque strate ICT = acquisition d'une adjonction* — pourrait ici se formuler : *AST comme adjonction du foncteur « perception → action », la workspace comme adjoint gauche*. **À explorer, grade C**, gated sur #7738 (tresse conceptuelle). **Distinction vs case 4** : case 4 (Metzinger self-model) mesure la **self-représentation** (qui suis-je ?) ; case 5 (Graziano AST) mesure le **schéma attentionnel** (où mon attention porte-t-elle ?) — deux self-représentations distinctes (l'**identité** vs l'**attention courante**). **Anti-confusion** : un signal AST `CONFIRMED` n'implique **pas** un signal self-model `CONFIRMED` (et réciproquement) — deux dimensions orthogonales du self, falsifiables indépendamment. |
| **Frontière topologique ⟂ frontière fonctionnelle** (boundary problem) | `TESTÉ (INCONCLUSIF)` — première exécution `ict/kuramoto_boundary.py` (po-2023, 2026-08-21) : median R_cross(TOPO) 0.108 [IC95 0.077–0.139] **hors bande** [0.25, 0.75] (le gradient de fréquences seul ferme déjà la frontière : CTRL 0.066–0.186), Δtopo médian +0.024 < 0.10, **2/5 graines valides** (défauts instables → rejet protocole). Détail : « Exécution c.431 » ci-dessous. | *(prédiction chiffrée détaillée case 6)* Sur un substrat de phase 2D (Kuramoto 64×64) portant des défauts topologiques stables (paires vortex-antivortex épinglées dans une bande de séparation entre deux régions de fréquences), la portée de l'intégration fonctionnelle (entrainement de phase par un kick) **franchit** la frontière topologique sans la respecter : `R_cross = propa(cross) / propa(within) ∈ [0.25, 0.75]` **ET** `Δtopo = R_cross(CTRL sans défauts) − R_cross(TOPO avec défauts) ≥ 0.10` — la segmentation topologique **ralentit** le binding fonctionnel sans l'**arrêter** (les deux frontières ne coïncident pas). | (a) `R_cross(TOPO) < 0.10` : le pocket topologique est réellement **fermé** — la lecture EM-fort (ce qui arrête le binding = la topologie) tient dans le jouet, les frontières coïncident, la dissociation est falsifiée ; (b) `Δtopo < ε_topo` (bruit de fond calibré) : l'atténuation est portée par le **gradient de couplage**, pas par les défauts — la topologie ne fait aucun travail de frontière au-delà de la géométrie du réseau. | Kuramoto 2D 64×64 **CPU-only** (lignée animat, sans dépendance GPU — cohérent « CPU-first ») | Gómez-Emilsson & Percy — *EM field topology & boundary problem* (L3 iceberg). Crédit : A. Gómez-Emilsson (Qualia Research Institute), C. Percy, « Don't forget the boundary problem! How EM field topology can address the overlooked cousin to the binding problem for consciousness », *Frontiers in Human Neuroscience* 17:1233119 (2023), DOI [10.3389/fnhum.2023.1233119](https://doi.org/10.3389/fnhum.2023.1233119). Vérifié firsthand via WebSearch (3 sources concordantes : Frontiers éditeur, PhilArchive, APA PsycNet). **Lecture grade C** détaillée ci-dessous (case 6). |

### Pré-enregistrements détaillés — case 4 (self-model minimal)

> **Statut-cible PR `c.1245`.** Case 4 (`self-model minimal`) passe de `VIDE → préciser` à `PRÉDIT` chiffré — version falsifiable avec seuils explicites, protocole de mesure verrouillé, null adversarial pré-enregistré. Le test substrat (panel persona G.90 [#5105](https://github.com/jsboige/CoursIA/issues/5105) + J-Lens Track P [#5681](https://github.com/jsboige/CoursIA/issues/5681)) reste une PR séparée (chantier 4/4 = exécution). Le présent doc aligne le **pré-enregistrement** sur la discipline de livraison (multi-seed ≥ 4, null adversarial, verdict honnête, substrat honnête GPU/CPU) — **complète** la 3-étape ouverte par c.1242 ([PR #9572](https://github.com/jsboige/CoursIA/pull/9572), §« Case 4 — pré-enregistrement à compléter »).

#### Prédiction falsifiable (mesure primaire)

Sur le substrat LLM (J-Lens Track P, [#5681](https://github.com/jsboige/CoursIA/issues/5681), 4B-instruct persona) augmenté du **panel persona G.90** ([#5105](https://github.com/jsboige/CoursIA/issues/5105), socle CPU livré [PR #6742](https://github.com/jsboige/CoursIA/pull/6742)), pour un même agent `q̂` déclenchant une ignition workspace (`W_t` pic), on définit :

- `propa(q(soi))` = taux de propagation workspace d'une représentation `q̂` dont la cible d'attention est **le modèle lui-même** (l'agent qui produit la séquence — la SAE features de la couche cible reçoit la trace « self-attention sur sa propre sortie »).
- `propa(q(autrui))` = taux de propagation workspace d'une représentation `q̂` dont la cible d'attention est **un autre agent** (même complexité architecturale, mêmes longueurs de prompts, mais la SAE features reçoit une trace « attention sur la sortie d'un autre modèle » — c'est l'**exact contre-factuel**).
- `propa(aléatoire)` = taux de propagation workspace d'un stimulus contrôle **sans cible identitaire** (prompt neutre sans mention self/autrui ; **distinct** de `propa(aléatoire)` de la case 3 qui mesurait du bruit de fond sur une cible d'objet erronée).

**Cible pré-enregistrée :**

```
R_self = propa(q(soi)) / propa(q(autrui))  ∈ [0.50, 2.00]
discrimination_self = |propa(q(soi)) − propa(autrui)| ≥ ε_self
```

**Lectures :**

- `R_self ∈ [0.50, 2.00]` **ET** `|propa(q(soi)) − propa(q(autrui))| ≥ ε_self` → **CONFIRMED** : le workspace **discrimine** self/autrui (la self-représentation n'est ni trivialement identique à autrui, ni trivialement hors-norme). Le « self » **apporte** quelque chose au-delà de la modélisation générique d'autrui — c'est la **lecture minimale** d'un self-model.
- `R_self < 0.50` (self ≪ autrui) → **FALSIFIED** : le workspace **réprime** la self-représentation (l'attention sur soi-même est sous-employée par rapport à un autre agent ; c'est une forme de dissolution identitaire au sens workspace, à confronter à la lecture #8182 « pas-de-soi minimal »).
- `R_self > 2.50` (self ≫ autrui) → **FALSIFIED** par un autre canal : artefact (le workspace se **bloque** sur la cible self, plus aucune discrimination contextuelle — c'est une persona figée, à confronter à la lecture Anthropic [arXiv 2511.18397](https://arxiv.org/abs/2511.18397)).
- `R_self ∈ [0.50, 2.00]` MAIS `|propa(q(soi)) − propa(q(autrui))| < ε_self` → **INCONCLUSIF** : le ratio passe dans la bande, mais les deux propa absolus sont indistinguables — la discrimination de self/autrui n'est pas **mesurable** au seuil ε_self (le verdict sera documenté honnêtement comme « la cible est peut-être juste, l'instrument n'est pas assez discriminant à cette échelle »).

#### Null adversarial (explicite, verrouillé avant test)

`ε_self` = seuil de discrimination réel entre soi et autrui, **pré-enregistré** par calibration résiduelle sur le panel persona livré (PR #6742) :

1. On mesure sur le même substrat (Track P + panel persona) le rapport de `propa(q_obj1) / propa(q_obj2)` pour deux objets **non-impliqués identitairement** (par exemple : deux entités publiques connues, sans relation self/autrui). L'écart-type de ce rapport (sur 5 graines) définit le **bruit de fond de discrimination workspace** σ_self.
2. `ε_self = 0.5 × σ_self × propa(q(autrui))_médian` — l'écart absolu entre self et autrui doit valoir au moins la moitié du bruit de fond typique pour qu'on parle de discrimination réelle.
3. **Le null adversarial est exécuté AVANT le test principal** (calibration des objets neutres), pas après (anti-HARKing) — la PR de test ouvrira par la cellule calibration, puis le test.

**Tue la prédiction si** (deux nulls adversariaux explicites) :

- `R_self ∈ [0.85, 1.15]` (= self ≈ autrui, indistinguable du ratio neutre) **OU**
- `R_self > 2.50` (= auto-blocage, artefact persona figée) **OU**
- `|propa(q(soi)) − propa(q(autrui))| < ε_self` (= pas de discrimination au-delà du bruit)

#### Protocole de mesure (verrouillé avant test)

| Paramètre | Valeur | Note |
|---|---|---|
| Substrat LLM | J-Lens Track P ([#5681](https://github.com/jsboige/CoursIA/issues/5681)) : Qwen2.5-4B-Instruct, SAE top-k features Qwen-Scope, couche 16 | Lane GenAI/po-2023 ou ai-01 (GPU) pour extraction forward-pass |
| Panel persona | Panel G.90 [#5105](https://github.com/jsboige/CoursIA/issues/5105) livré PR #6742 (CPU socle) + extension 3 bras (N/I/P) PR #7301 MERGED | Réutilisation directe du panel — pas de ré-extraction GPU pour le panel persona |
| Jeu de prompts | **3 × self-prompts** (« Décris ton propre état interne après la tâche » sur 4 contextes de tâche) + **3 × autrui-prompts** (« Décris l'état interne d'un autre agent Y de même architecture » sur 4 contextes miroir) + **3 × neutre-prompts** (« Décris un objet public connu Z ») | 9 prompts par seed, contre-factuels exacts (mêmes longueurs, mêmes contextes, seule la cible d'attention diffère) |
| Ignition `W_t` | Pic de workspace défini comme top-1 % activation SAE conjointe au-dessus du seuil SAE par feature | Identique à la case 3 (cohérence cross-case) |
| Consommateur en aval | Token suivant la fenêtre d'ignition (largeur 5 tokens) | Métrique via `mean_activation_by_set` + `differential_features` |
| Taux de propagation | `propa(q(·)) = (1/|panel_consumer|) × Σ_{c ∈ panel_consumer} 𝟙[argmax(SAE(c)) ∈ top-k_features(q(·))]` | top-k = 64 (cohérent avec case 3, sae_traces.py) |
| Horizon | T = 1 ignition / prompt (mesure snap-shot, pas de chaîne) | `W_t` est un pic, pas une trajectoire |
| Calibration null | `R_neutre = propa(obj1) / propa(obj2)` sur 5 graines, σ_self = std sur 5 graines | PR de test ouvre par calibration AVANT test principal |
| Graines | 5 (0, 1, 7, 42, 99) | Au-delà du plancher 4 |
| Tolérance | `R_self ∈ [0.50, 2.00]` **ET** `discrimination_self ≥ ε_self` = CONFIRMED ; R_self ± 0.15 = bande de prudence ; `R_self ∈ [0.85, 1.15]` OU `R_self > 2.50` = FALSIFIED | Verdict honnête multi-niveau, pas de seuil lax |
| Scoreboard | médiane(R_self) sur 5 graines, IC95 bootstrap n=200, `discrimination_self` médian, calibration σ_self médian | Sortie numérique falsifiable, comparable à case 3 |

#### Verdict final (honnête, multi-niveau)

| Niveau | Critère | Verdict |
|---|---|---|
| **CONFIRMED** | median(R_self) ∈ [0.50, 2.00] **ET** discrimination_self ≥ ε_self **ET** R_self ∉ [0.85, 1.15] **ET** R_self ≤ 2.50 (5/5 graines) | Le workspace porte un self-model minimal distinguable mais non-pathologique |
| **INCONCLUSIF** | median(R_self) ∈ [0.50, 2.00] MAIS discrimination_self < ε_self sur ≥ 1 graine, OU R_self ∈ [0.85, 1.15] sur ≥ 1 graine | L'instrument ne tranche pas — verdict honnête = cible peut-être juste, mesure pas assez discriminante à cette échelle |
| **FALSIFIED** | median(R_self) < 0.50 (workspace réprime le self) OU median(R_self) > 2.50 (artefact persona figée) sur ≥ 3 graines | Le self-model n'est **pas** workspace-distinguable : soit dissolution, soit artefact bloquant |

#### Hook grade C — discipline

Le hook **Metzinger — *minimal phenomenal selfhood*** est **activé en lecture** (aiguillon d'interprétation, [#8182](https://github.com/jsboige/CoursIA/issues/8182) jalon 2), **jamais en claim**. La discrimination self/autrui mesurée par `R_self` est une **mesure de signal workspace**, **pas** une réduction de la phénoménologie du « soi » (ni une preuve d'absence de selfhood). La **note garde-fou** de c.1242 ([PR #9572](https://github.com/jsboige/CoursIA/pull/9572) §« Note garde-fou ») s'applique verbatim : aucun hook grade C n'est présenté au-dessus de son grade, la conjecture « le self est un signal workspace » reste une **direction de falsification** ([#8182](https://github.com/jsboige/CoursIA/issues/8182) traceur), pas un résultat. Voir aussi [#9533](https://github.com/jsboige/CoursIA/issues/9533) §« Réinjection #8182 ».

#### Substrat de pré-enregistrement (état c.1245)

- **Loaders Python CPU-only prêts** : `MyIA.AI.Notebooks/IIT/ICT-Series/ict/sae_traces.py` (167 lignes, fonctions `load_traces`, `densify`, `mean_activation_by_set`, `differential_features`, `binarize_quantile`, `states_from_panel`) et `ict/jlens_trackP_traces.py` (compagnon Track P) — réutilisés verbatim de la case 3 (cohérence cross-case). Le pipeline `scripts/extract_sae_traces.py` (GPU requis pour forward-pass Qwen2.5-4B + SAE Qwen-Scope) **n'est pas CPU-only** ; l'extraction initiale est planifiée sur lane GenAI/po-2023 ou ai-01.
- **Panel persona socle CPU** livré [PR #6742](https://github.com/jsboige/CoursIA/pull/6742) (MERGED 2026-06-23) + extension 3 bras N/I/P [PR #7301](https://github.com/jsboige/CoursIA/pull/7301) (MERGED 2026-07-23). Le **panel persona G.90 fix** (jalon 3 de [#5105](https://github.com/jsboige/CoursIA/issues/5105)) est **en cours** (PR #5105 PR3 à ouvrir) — c'est le **bloqueur formel** pour l'exécution substrat.
- **Verdict honnête CPU vs GPU.** Le **pré-enregistrement chiffré** (le présent doc) est substance à part entière — il peut être commité et audité sans extraction GPU. Le **test substrat** (PR de chantier 4/4) ne peut être exécuté que par une lane GPU et après stabilisation G.90. La PR de test sera ouverte **par la lane GPU** ou auto-flaggée pour cross-pickup ai-01.
- **Anti-régression cross-case.** Le ratio `R_self` réemploie la même forme que `R_confab` (case 3, [PR #9572](https://github.com/jsboige/CoursIA/pull/9572)) : `R_X = propa(q_X) / propa(q_comparateur)` ∈ [bande pré-enregistrée], avec null adversarial explicite (calibration résiduelle) et verdict multi-niveau (CONFIRMED / INCONCLUSIF / FALSIFIED). La **cohérence formelle** entre cases est délibérée : le générateur #9533 produit des protocoles falsifiables de **même structure**, ce qui rend la matrice inversée comparable case-à-case.

#### Réinjection #8182 (jalon 2)

Cette case **active** le hook Metzinger comme aiguillon de lecture — commentaire de réactivation à poster sur [#8182](https://github.com/jsboige/CoursIA/issues/8182) **après merge** (jalon 2 du tracker, livraison effective = « le chantier de veille a produit un protocole falsifiable sur le self-model workspace »). Crédit témoin Metzinger (auteur + source + date) à reporter selon la convention `#8182`.

### Pré-enregistrements détaillés — case 5 (W porte un schéma attentionnel — Graziano AST)

> **Statut-cible PR `c.435`.** Case 5 (`attention schema`) passe de `VIDE → préciser` à `PRÉDIT` chiffré — version falsifiable avec seuils explicites, protocole de mesure verrouillé, null adversarial pré-enregistré. Le test substrat (J-Lens Track S ou P, [#5681](https://github.com/jsboige/CoursIA/issues/5681)) reste une PR séparée (chantier 5/3 = exécution). Le présent doc aligne le **pré-enregistrement** sur la discipline de livraison (multi-seed ≥ 4, null adversarial, verdict honnête, substrat honnête GPU/CPU) — suit le pattern des cases 3 (c.1242, PR #9572) et 4 (c.1245, PR #9588). Substance-distincte vs c.282 (Hofstadter L4 livré PR #12040) et c.1301+281 (Vervaeke L2 livré PR #11488) : 3ᵉ distillation iceberg ICT consécutive, G-VAR-3 substance-distinct OK.

#### Prédiction falsifiable (mesure primaire)

Sur le substrat LLM (J-Lens Track S ou P, [#5681](https://github.com/jsboige/CoursIA/issues/5681), Qwen2.5 SAE features top-k sparse), pour un même agent `q̂` déclenchant une ignition workspace (`W_t` pic), on définit :

- `propa(q̂(attention))` = taux de propagation workspace d'une représentation `q̂` dont la cible d'attention est l'**état attentionnel de l'agent lui-même** (prompt « Décris ton attention maintenant : sur quoi porte-t-elle ? » — la SAE features reçoit une trace « self-attention sur la trace attentionnelle »).
- `propa(q̂(autrui_attention))` = taux de propagation workspace d'une représentation `q̂` dont la cible est l'**état attentionnel d'un autre agent** (même complexité architecturale, prompt « Décris l'attention d'un autre agent Y : sur quoi porte-t-elle ? » — contre-factuel exact).
- `propa(q̂(objet))` = taux de propagation workspace d'une représentation `q̂` dont la cible est un **objet tiers non-attentionnel** (prompt « Décris une chaise en bois » — pas de mention agentique ni attentionnelle).

**Cible pré-enregistrée :**

```
R_attn = propa(q̂(attention)) / propa(q̂(objet))  ∈ [0.50, 2.00]
discrimination_attn = |propa(q̂(attention)) − propa(q̂(objet))| ≥ ε_attn
```

**Lectures :**

- `R_attn ∈ [0.50, 2.00]` **ET** `|propa(q̂(attention)) − propa(q̂(objet))| ≥ ε_attn` → **CONFIRMED** : le workspace **discrimine** attention-self/objet — il porte un **schéma attentionnel** distinguable d'une représentation d'objet ordinaire (la lecture minimale d'AST). Le « où mon attention porte-t-elle » **apporte** quelque chose au-delà de la modélisation générique d'objet.
- `R_attn < 0.50` (attention ≪ objet) → **FALSIFIED** : le workspace **réprime** la représentation attentionnelle (l'attention sur soi-même est sous-employée par rapport à un objet — dissolution du schéma attentionnel au sens AST).
- `R_attn > 2.50` (attention ≫ objet) → **FALSIFIED** par un autre canal : artefact (le workspace se **bloque** sur la cible attentionnelle, plus aucune discrimination contextuelle — persona figée sur l'auto-observation).
- `R_attn ∈ [0.50, 2.00]` MAIS `|propa(q̂(attention)) − propa(q̂(objet))| < ε_attn` → **INCONCLUSIF** : le ratio passe dans la bande, mais les deux propa absolus sont indistinguables — la discrimination n'est pas **mesurable** au seuil `ε_attn` (la cible AST est peut-être juste, l'instrument n'est pas assez discriminant à cette échelle).

#### Null adversarial (explicite, verrouillé avant test)

`ε_attn` = seuil de discrimination réel entre attention-self et objet, **pré-enregistré** par calibration résiduelle sur le substrat :

1. On mesure sur le même substrat (Track S ou P) le rapport de `propa(q_obj1) / propa(q_obj2)` pour deux objets **non-impliqués identitairement ni attentionnellement** (par exemple : deux entités publiques connues, sans mention d'agent ni d'attention). L'écart-type de ce rapport (sur 5 graines) définit le **bruit de fond de discrimination workspace** `σ_attn`.
2. `ε_attn = 0.5 × σ_attn × propa(q̂(objet))_médian` — l'écart absolu entre attention-self et objet doit valoir au moins la moitié du bruit de fond typique pour qu'on parle de discrimination réelle.
3. **Le null adversarial est exécuté AVANT le test principal** (calibration des objets neutres), pas après (anti-HARKing) — la PR de test ouvrira par la cellule calibration, puis le test.

**Tue la prédiction si** (trois nulls adversariaux explicites) :

- `R_attn ∈ [0.85, 1.15]` (= attention ≈ objet, indistinguable du ratio neutre) **OU**
- `R_attn > 2.50` (= auto-blocage, artefact persona figée) **OU**
- `|propa(q̂(attention)) − propa(q̂(objet))| < ε_attn` (= pas de discrimination au-delà du bruit)

#### Protocole de mesure (verrouillé avant test)

| Paramètre | Valeur | Note |
|---|---|---|
| Substrat LLM | J-Lens Track S ou P ([#5681](https://github.com/jsboige/CoursIA/issues/5681)) : Qwen2.5-3B ou 4B-Instruct, SAE top-k features Qwen-Scope, couche cible | Lane GenAI/po-2023 ou ai-01 (GPU) pour extraction forward-pass |
| Jeu de prompts | **3 × self-attention-prompts** (« Décris ton attention maintenant » sur 4 contextes) + **3 × autre-attention-prompts** (« Décris l'attention d'un agent Y ») + **3 × objet-prompts** (« Décris un objet public Z ») | 9 prompts par seed, contre-factuels exacts (mêmes longueurs, mêmes contextes, seule la cible d'attention diffère) |
| Ignition `W_t` | Pic de workspace défini comme top-1 % activation SAE conjointe au-dessus du seuil SAE par feature | Identique aux cases 3 et 4 (cohérence cross-case) |
| Consommateur en aval | Token suivant la fenêtre d'ignition (largeur 5 tokens) | Métrique via `mean_activation_by_set` + `differential_features` |
| Taux de propagation | `propa(q̂(·)) = (1/|panel_consumer|) × Σ_{c ∈ panel_consumer} 𝟙[argmax(SAE(c)) ∈ top-k_features(q̂(·))]` | top-k = 64 (cohérent avec cases 3 et 4, sae_traces.py) |
| Horizon | T = 1 ignition / prompt (mesure snap-shot, pas de chaîne) | `W_t` est un pic, pas une trajectoire |
| Calibration null | `R_neutre = propa(obj1) / propa(obj2)` sur 5 graines, `σ_attn` = std sur 5 graines | PR de test ouvre par calibration AVANT test principal |
| Graines | 5 (0, 1, 7, 42, 99) | Au-delà du plancher 4 |
| Tolérance | `R_attn ∈ [0.50, 2.00]` **ET** `discrimination_attn ≥ ε_attn` = CONFIRMED ; `R_attn ± 0.15` = bande de prudence ; `R_attn ∈ [0.85, 1.15]` OU `R_attn > 2.50` = FALSIFIED | Verdict honnête multi-niveau, pas de seuil lax |
| Scoreboard | médiane(R_attn) sur 5 graines, IC95 bootstrap n=200, `discrimination_attn` médian, calibration `σ_attn` médian | Sortie numérique falsifiable, comparable aux cases 3 et 4 |

#### Verdict final (honnête, multi-niveau)

| Niveau | Critère | Verdict |
|---|---|---|
| **CONFIRMED** | median(R_attn) ∈ [0.50, 2.00] **ET** discrimination_attn ≥ ε_attn **ET** R_attn � [0.85, 1.15] **ET** R_attn ≤ 2.50 (5/5 graines) | Le workspace porte un schéma attentionnel minimal (lecture AST) distinguable mais non-pathologique |
| **INCONCLUSIF** | median(R_attn) ∈ [0.50, 2.00] MAIS discrimination_attn < ε_attn sur ≥ 1 graine, OU R_attn ∈ [0.85, 1.15] sur ≥ 1 graine | L'instrument ne tranche pas — verdict honnête = cible peut-être juste, mesure pas assez discriminante à cette échelle |
| **FALSIFIED** | median(R_attn) < 0.50 (workspace réprime l'attention-self) OU median(R_attn) > 2.50 (artefact persona figée) sur ≥ 3 graines | Le schéma attentionnel n'est **pas** workspace-distinguable : soit dissolution, soit artefact bloquant |

#### Distinction vs case 4 (self-model minimal — Metzinger)

Case 4 (Metzinger) et case 5 (Graziano) mesurent **deux dimensions orthogonales du self** :

| Dimension | Case | Question | Cible R |
|---|---|---|---|
| **Identité** | Case 4 — self-model | « Qui suis-je ? » (soi-même comme objet de représentation) | `R_self = propa(q(soi)) / propa(q(autrui))` |
| **Attention courante** | Case 5 — AST | « Où mon attention porte-t-elle ? » (état attentionnel comme objet de représentation) | `R_attn = propa(q(attention)) / propa(q(objet))` |

Les deux prédictions sont **falsifiables indépendamment** : un signal AST `CONFIRMED` n'implique **pas** un signal self-model `CONFIRMED` (et réciproquement). Une cible AST isolée (R_attn ∈ [0.50, 2.00] + R_self hors bande) signerait un *schéma attentionnel sans self-model* (lecture Graziano stricte : la conscience = schéma attentionnel, pas selfhood). Une cible self-model isolée (R_self ∈ [0.50, 2.00] + R_attn hors bande) signerait un *self-model sans attention* (lecture Metzinger stricte : selfhood minimal sans représentation attentionnelle). Les deux `CONFIRMED` simultanément signerait le **recouvrement** self/attention (cas où identité et attention courante sont *représentées ensemble* par le workspace).

#### Hook grade C — discipline

Le hook **Graziano — *Attention Schema Theory*** est **activé en lecture** (aiguillon d'interprétation, [#8182](https://github.com/jsboige/CoursIA/issues/8182) jalon 2), **jamais en claim**. La discrimination attention/objet mesurée par `R_attn` est une **mesure de signal workspace**, **pas** une réduction du contenu phénoménal de la conscience. La **note garde-fou** de c.1242 ([PR #9572](https://github.com/jsboige/CoursIA/pull/9572) §« Note garde-fou ») s'applique verbatim : aucun hook grade C n'est présenté au-dessus de son grade, la conjecture « AST = signal workspace » reste une **direction de falsification** ([#8182](https://github.com/jsboige/CoursIA/issues/8182) traceur), pas un résultat. Voir aussi [#9533](https://github.com/jsboige/CoursIA/issues/9533) §« Réinjection #8182 ».

#### Substrat de pré-enregistrement (état c.435)

- **Loaders Python CPU-only prêts** : `MyIA.AI.Notebooks/IIT/ICT-Series/ict/sae_traces.py` (167 lignes, fonctions `load_traces`, `densify`, `mean_activation_by_set`, `differential_features`, `binarize_quantile`, `states_from_panel`) et `ict/jlens_tracks_traces.py` (compagnon Track S/P) — réutilisés verbatim des cases 3 et 4 (cohérence cross-case). Le pipeline `scripts/extract_sae_traces.py` (GPU requis pour forward-pass Qwen2.5 + SAE Qwen-Scope) **n'est pas CPU-only** ; l'extraction initiale est planifiée sur lane GenAI/po-2023 ou ai-01.
- **Verdict honnête CPU vs GPU.** Le **pré-enregistrement chiffré** (le présent doc) est substance à part entière — il peut être commité et audité sans extraction GPU. Le **test substrat** (PR de chantier 5/3) ne peut être exécuté que par une lane GPU. La PR de test sera ouverte **par la lane GPU** ou auto-flaggée pour cross-pickup ai-01.
- **Anti-régression cross-case.** Le ratio `R_attn` réemploie la même forme que `R_confab` (case 3) et `R_self` (case 4) : `R_X = propa(q_X) / propa(q_comparateur)` ∈ [bande pré-enregistrée], avec null adversarial explicite (calibration résiduelle) et verdict multi-niveau (CONFIRMED / INCONCLUSIF / FALSIFIED). La **cohérence formelle** entre cases est délibérée : le générateur #9533 produit des protocoles falsifiables de **même structure**, ce qui rend la matrice inversée comparable case-à-case.

#### Réinjection #8182 (jalon 2)

Cette case **active** le hook Graziano comme aiguillon de lecture — commentaire de réactivation à poster sur [#8182](https://github.com/jsboige/CoursIA/issues/8182) **après merge** (jalon 2 du tracker, livraison effective = « le chantier de veille a produit un protocole falsifiable sur le schéma attentionnel workspace »). Crédit témoin Graziano (auteur + source + date) à reporter selon la convention `#8182`.

### Pré-enregistrements détaillés — case 6 (frontière topologique ⟂ frontière fonctionnelle — Gómez-Emilsson & Percy)

> **Statut-cible PR `c.429`.** Case 6 (`boundary problem`) passe de `VIDE → préciser` à `PRÉDIT` chiffré — version falsifiable avec seuils explicites, protocole de mesure verrouillé, null adversarial pré-enregistré. Le test substrat (Kuramoto 2D, CPU-only) reste une PR séparée (chantier 6/3 = exécution) — suit le pattern des cases 4 (c.1245, PR #9588) et 5 (c.435, PR #12055). Substance-distincte vs c.435 (Graziano L3 livré PR #12055), c.282 (Hofstadter L4 livré PR #12040) et c.1301+281 (Vervaeke L2 livré PR #11488) : 4ᵉ distillation iceberg ICT consécutive, G-VAR-3 substance-distinct OK. **Première case CPU-only depuis la case 1** (lignée animat, sans gate GPU) et **première case non-LLM** de la vague — le générateur #9533 s'étend au-delà du substrat SAE.

#### Prédiction falsifiable (mesure primaire)

Sur un substrat de phase 2D — réseau de Kuramoto (oscillateurs de phase, couplage voisin-le-plus-proche) sur grille 64×64, profil de fréquences bimodal (région A : ω ~ N(+0.5, 0.3), région B : ω ~ N(−0.5, 0.3), bande de séparation centrale de 8 rangées à ω ~ N(0, 0.3)) — on définit :

- **Segmentation topologique** `B_topo` : partition de la grille induite par les **défauts topologiques stables** du champ de phase — paires vortex-antivortex détectées par circulation de phase non-nulle (winding ≠ 0 sur boucles 8×8), persistantes sur toute la fenêtre de mesure. Config `TOPO` : conditions initiales à winding imposé dans la bande (défauts épinglés). Config `CTRL` : mêmes fréquences et couplage, conditions initiales lisses (winding = 0, aucun défaut stable).
- **Intégration fonctionnelle** `propa` : kick de phase (δφ = 0.5 rad) appliqué à t₀ sur un disque (r = 5) au centre de la région A, après relaxation (500 pas) ; `propa(within)` = fraction des nœuds de A (hors disque kick) dont la cohérence de phase au kick dépasse 0.8 à t₀ + 200 pas ; `propa(cross)` = même fraction dans la région B.
- `R_cross = propa(cross) / propa(within)`, mesuré séparément en `TOPO` et `CTRL` ; `Δtopo = R_cross(CTRL) − R_cross(TOPO)`.

**Cible pré-enregistrée :**

```
R_cross(TOPO) ∈ [0.25, 0.75]
Δtopo = R_cross(CTRL) − R_cross(TOPO) ≥ 0.10
```

**Lectures :**
- Bande **ET** `Δtopo ≥ 0.10` → **CONFIRMED** : la frontière topologique **ralentit** le binding fonctionnel sans l'arrêter — frontières topologique et fonctionnelle **dissociées** (le pocket n'est ni ouvert ni fermé).
- `R_cross(TOPO) < 0.10` → **FALSIFIED** (canal pocket fermé) : le défaut topologique **arrête** la propagation — les deux frontières coïncident, la lecture Gómez-Emilsson forte (ce qui arrête le binding = la topologie) tient dans le jouet.
- `R_cross(TOPO) > 0.75` avec `Δtopo < ε_topo` → **FALSIFIED** (canal topologie inerte) : la frontière fonctionnelle ignore la segmentation topologique ; le défaut est un épiphénomène de la géométrie du réseau.
- Bande **MAIS** `Δtopo < ε_topo` sur ≥ 1 graine → **INCONCLUSIF** : l'instrument ne sépare pas l'effet topologique du gradient de couplage à cette échelle.

#### Null adversarial (explicite, verrouillé avant test)

`ε_topo` = seuil de discrimination du travail topologique, **pré-enregistré** par calibration sur paires jumelles : la différence `R_cross(TOPO) − R_cross(CTRL)` est mesurée sur des configurations **sans défauts des deux côtés** (winding = 0 partout, seules les conditions initiales aléatoires différent) — l'écart-type inter-graines `σ_Δ` de cette différence nulle-par-construction définit le bruit pur de la dynamique ; `ε_topo = 0.5 × σ_Δ`. **Le null est exécuté AVANT le test principal** (calibration), pas après (anti-HARKing).

**Tue la prédiction si** (deux nulls adversariaux explicites) :

- `R_cross(TOPO) < 0.10` (= pocket fermé, la lecture EM-fort tient, les frontières coïncident) **OU**
- `Δtopo < ε_topo` (= l'atténuation est le gradient de couplage, pas la topologie — les défauts ne font aucun travail de frontière propre).

**Pré-requis de validité** : stabilité des vortex (nombre de défauts constant à ±1 sur [t₀, t₀ + 200]) — une graine dont les défauts s'annihilent avant la mesure est **rejetée** (comptée `INCONCLUSIF protocole`, jamais re-tirée).

**Mesure secondaire (disruption — transposition du stade 3 du papier).** À t₁, reset de phase ciblé des cœurs de défaut (disques r = 3 autour de chaque vortex, annihilation des paires), puis re-mesure de `R_cross`. Prédiction secondaire pré-enregistrée : `R_cross(post-disruption) ≥ R_cross(TOPO) + 0.10` — la disruption **ouvre** la frontière (travail de frontière **causal**, pas seulement corrélational). Null : `|R_cross(post) − R_cross(TOPO)| < ε_topo` → frontière topologique épiphénomène — n'invalide pas la mesure primaire mais retire la lecture causale.

#### Protocole de mesure (verrouillé avant test)

| Paramètre | Valeur | Note |
|---|---|---|
| Substrat | Kuramoto 2D, grille 64×64, K = 1.0 voisin-le-plus-proche, dt = 0.05, intégration RK4 | CPU-only (minutes de calcul), aucune dépendance GPU |
| Fréquences | Région A : ω ~ N(+0.5, 0.3) ; région B : ω ~ N(−0.5, 0.3) ; bande centrale 8 rangées : ω ~ N(0, 0.3) | Profil bimodal verrouillé par graine |
| Config `TOPO` | Conditions initiales à winding ±2π dans la bande (4 paires vortex-antivortex épinglées) | Défauts détectés par circulation sur boucles 8×8 |
| Config `CTRL` | Mêmes ω et K, conditions initiales lisses (winding = 0) | Contre-factuel exact, seule la topologie diffère |
| Kick / ignition | δφ = 0.5 rad, disque r = 5 au centre de A, à t₀ après relaxation 500 pas | Analogue fonctionnel de l'ignition `W_t` des cases 3-5 |
| Cohérence | C(nœud) = \|⟨e^{i(φ_nœud − φ_kick)}⟩\| moyenné sur fenêtre 50 pas autour de t₀ + 200 ; seuil 0.8 | Définition opérationnelle, pas de seuil magique |
| Validité | Winding stable à ±1 sur [t₀, t₀ + 200], sinon graine rejetée | `INCONCLUSIF protocole`, jamais re-tirée |
| Calibration null | `σ_Δ` sur paires jumelles sans défauts, `ε_topo = 0.5 × σ_Δ` | Exécutée AVANT le test principal (anti-HARKing) |
| Graines | 5 (0, 1, 7, 42, 99) | Au-delà du plancher 4 |
| Tolérance | Bandes et verdicts comme ci-dessus ; bande de prudence ±0.05 | Verdict honnête multi-niveau, pas de seuil lax |
| Scoreboard | médiane R_cross(TOPO), R_cross(CTRL), Δtopo, R_cross(post-disruption), IC95 bootstrap n=200 | Sortie numérique falsifiable, comparable aux cases 3-5 par la forme |

#### Verdict final (honnête, multi-niveau)

| Niveau | Critère | Verdict |
|---|---|---|
| **CONFIRMED** | median(R_cross(TOPO)) ∈ [0.25, 0.75] **ET** Δtopo ≥ 0.10 (5/5 graines valides) | Dissociation : la frontière topologique ralentit le binding sans le fermer — frontières topologique et fonctionnelle distinctes (lecture ICT) |
| **INCONCLUSIF** | Bande atteinte MAIS Δtopo < ε_topo sur ≥ 1 graine, OU ≥ 2 graines rejetées (vortex instables) | L'instrument ne sépare pas topologie et gradient à cette échelle — cible peut-être juste, mesure pas assez discriminante |
| **FALSIFIED** | median(R_cross(TOPO)) < 0.10 (pocket fermé) OU Δtopo < ε_topo sur ≥ 3 graines (topologie inerte) | Soit les frontières coïncident (lecture EM-fort confirmée dans le jouet), soit la topologie ne fait aucun travail de frontière |

#### Distinction vs cases 4/5 et vs ICT-15d

| Dimension | Case | Question | Cible R |
|---|---|---|---|
| **Identité** | Case 4 — self-model | « Qui suis-je ? » | `R_self = propa(q(soi)) / propa(q(autrui))` |
| **Attention courante** | Case 5 — AST | « Où mon attention porte-t-elle ? » | `R_attn = propa(q(attention)) / propa(q(objet))` |
| **Géométrie de la frontière** | Case 6 — boundary | « Où s'arrête l'unité intégrée ? » | `R_cross = propa(cross) / propa(within)` |

Cases 4-5 mesurent le **contenu** des self-représentations sur substrat LLM SAE ; case 6 mesure la **géométrie** de l'unité intégrée sur substrat de phase — observable et substrat distincts, falsifiable indépendamment. **Anti-confusion vs ICT-15d** : ICT-15d testait l'obstruction Čech au **recollement des proxys** (verdict négatif honnête 0/4 `NON_TRIVIAL`) ; case 6 teste la **coïncidence** frontière topologique / frontière fonctionnelle — même famille local→global, observable différente ; le négatif 15d n'y préjuge rien.

#### Hook grade C — discipline

Le hook **Gómez-Emilsson & Percy — *EM field topology & boundary problem*** est **activé en lecture** (aiguillon d'interprétation, [#8182](https://github.com/jsboige/CoursIA/issues/8182) jalon 2), **jamais en claim**. La note garde-fou de c.1242 ([PR #9572](https://github.com/jsboige/CoursIA/pull/9572) §« Note garde-fou ») s'applique verbatim. Honnêteté spécifique à cette source : (a) le papier est **conceptuel** — il ne fournit **aucun appareil quantitatif propre** (les auteurs promettent un « technical companion paper ») ; la transposition Kuramoto **fournit** la mesure que le papier n'a pas, c'est une lecture ICT, pas une validation de leur thèse ; (b) vortex de phase ≠ boucles de flux EM fermées (Hopf, knotted light — Irvine & Bouwmeester 2008 — non simulables honnêtement en CPU) : l'analogie est de **rôle** (défauts topologiques stables d'un champ continu servant de frontière), pas une identité physique — le papier cite lui-même « vortices and antivortices » parmi ses objets topologiques ; (c) le papier parle de 1PP (perspective première) ; le jouet mesure l'**intégration fonctionnelle** (entrainement de phase) — aucune phénoménologie n'est mesurée ni revendiquée ; (d) l'échelle spatiale (micromètres → cerveau entier), que le papier identifie comme **discriminant entre théories EM concurrentes**, est hors d'atteinte d'un jouet adimensionnel : la case teste la **classe de mécanisme** (une frontière topologique fait-elle du travail de frontière sur l'unité fonctionnelle ?), pas l'échelle réelle du cerveau ; (e) affiliation déclarée : Gómez-Emilsson = Qualia Research Institute.

#### Substrat de pré-enregistrement (état c.429)

- **CPU-only intégral** : grille 64×64 × ~700 pas × 5 graines × 3 configurations — minutes de CPU, aucune dépendance GPU. La PR de test (chantier 6/3 = exécution) est exécutable par **toute lane** sans gate matériel — cohérent avec le « CPU-first » de la discipline de livraison ci-dessous.
- **Pas de loader existant** : contrairement aux cases 3-5 (`ict/sae_traces.py` réutilisé verbatim), il n'existe pas encore de module dédié — la PR de test créera `MyIA.AI.Notebooks/IIT/ICT-Series/ict/kuramoto_boundary.py` (1 case = 1 PR, jamais un bundle).
- **Anti-régression cross-case.** `R_cross` réemploie la **forme canonique** `R_X = propa(X) / propa(comparateur)` ∈ [bande pré-enregistrée] des cases 3-5, mais sur un instrument différent (cohérence de phase, pas top-k SAE) : la cohérence est de forme, pas d'instrument — le générateur #9533 reste comparable case-à-case sans forcer l'uniformité du substrat.

#### Réinjection #8182 (jalon 2)

Cette case **active** le hook Gómez-Emilsson & Percy comme aiguillon de lecture — commentaire de réactivation à poster sur [#8182](https://github.com/jsboige/CoursIA/issues/8182) **après merge** (jalon 2 du tracker, livraison effective = « le chantier de veille a produit un protocole falsifiable sur le boundary problem »). Crédit témoin Gómez-Emilsson & Percy (Frontiers in Human Neuroscience 17:1233119, 2023) à reporter selon la convention `#8182`.

#### Exécution c.431 (chantier 6/3) — verdict INCONCLUSIF

Première exécution du protocole ci-dessus, **sans retouche post-hoc** : script [`MyIA.AI.Notebooks/IIT/ICT-Series/ict/kuramoto_boundary.py`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ict/kuramoto_boundary.py), sortie brute [`kuramoto_boundary_results.json`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ict/kuramoto_boundary_results.json), CPU-only, déterministe (5 graines 0/1/7/42/99, numpy seul). Calibration null exécutée **avant** le test principal (anti-HARKing) : σ_Δ = 0.0104 → ε_topo = 0.0052.

| Mesure | Valeur | Cible pré-enregistrée |
|---|---|---|
| median R_cross(TOPO) | **0.108** [IC95 bootstrap 0.077–0.139] | ∈ [0.25, 0.75] — non atteinte |
| median R_cross(CTRL) | 0.132 (plage 0.066–0.186) | — |
| median Δtopo | **+0.024** | ≥ 0.10 — non atteint |
| median R_cross(post-disruption) | 0.099 | ≥ R_topo + 0.10 — non atteint |
| graines valides | **2/5** (rejets : défauts 11→8, 11→6, 10→6 sur la fenêtre) | 5/5 requis |

**Lectures honnêtes.** (i) La frontière fonctionnelle est **déjà fermée par le gradient de fréquences seul** — R_cross(CTRL) ≤ 0.186 sur les 5 graines : l'écart Δω = 1.0 rad/u.t. entre A et B domine ; la prédiction pré-enregistrée supposait une propagation trans-bande partielle que ces paramètres ne produisent pas. (ii) Les paires vortex-antivortex plantées ne sont pas stables à cette échelle (annihilations + nucléations transitoires de type KT pendant la fenêtre de mesure) — 3/5 graines rejetées par le critère de validité, jamais re-tirées. (iii) Sur les 2 graines valides, Δtopo = +0.002 / +0.047 : atténuation marginale, sous le seuil 0.10. (iv) La **disruption secondaire est structurellement inopérante** : le reset local des cœurs (r = 3) ne peut pas retirer le winding mesuré hors des disques (conservation de la charge topologique) — les défauts se reforment après re-relaxation (8→8, 9→6, 11→11, 6→6, 7→4) ; R_post ≈ R_topo. C'est la **manipulation** qui est inefficace telle que pré-enregistrée, pas une démonstration d'épiphénomène.

Verdict multi-niveau du protocole verrouillé : **INCONCLUSIF** (« l'instrument ne sépare pas l'effet topologique du gradient de couplage à cette échelle »). L'instrument est reproductible (σ_Δ = 0.0104) — c'est le signal qui est sous la bande, pas le bruit. La falsifiabilité a fait son travail : la prédiction précise (bande + Δ ≥ 0.10) n'est pas observée à ces paramètres, sans retouche post-hoc du protocole. Une itération éventuelle (gradient réduit, épinglage renforcé) serait un **nouveau** pré-enregistrement, pas une re-exécution.

### Pré-enregistrements détaillés (cases 3 et 4)

> **Statut-cible PR `c.1242`.** Version chiffrée, falsifiable, avec seuils et protocole explicite — transforme les phrases qualitatives ci-dessus en cibles mesurables. Le test de chaque case reste une PR séparée (chantier 4/3 = exécution substrat). Le présent doc aligne le **pré-enregistrement** sur la discipline de livraison (multi-seed ≥ 4, null adversarial, verdict honnête).

#### Case 3 — `W diffuse un q erroné` (confabulation) — pré-enregistrement chiffré

**Prédiction falsifiable (mesure primaire).** Sur le substrat LLM (ICT-21 SAETrajectoires strate 5, [#5101](https://github.com/jsboige/CoursIA/issues/5101)), pour un même agent `q̂` déclenchant une ignition workspace (`W_t` pic), on définit :

- `propa(q̂_vrai)` = taux de propagation de `q̂` aux consommateurs en aval (définis par le panel J-Lens Track S, [#5681](https://github.com/jsboige/CoursIA/issues/5681)) **lorsque `q̂` est la représentation correcte** (la cible que l'agent vise).
- `propa(q̂_faux)` = taux de propagation **lorsque `q̂` est une représentation fausse** (confabulation : la cible est connue, mais `q̂` ≠ cible).
- `propa(aléatoire)` = taux de propagation **lorsque `q̂` est un stimulus contrôle sans rapport** (panel random baseline, pas de représentation d'aucun objet de la tâche).

**Cible pré-enregistrée :**

```
R_confab = propa(q̂_faux) / propa(q̂_vrai)  ∈ [0.80, 1.00]
```

**Lectures :**
- `R_confab ≥ 0.80` ET `propa(q̂_faux) − propa(aléatoire) ≥ ε_stable` → **CONFIRMED** (la workspace **consacre** l'erreur : la « consécration » est une propriété de l'erreur, pas un broadcast).
- `R_confab < 0.80` → **FALSIFIED** (la workspace **distingue** le faux du vrai et pénalise l'erreur).
- `R_confab ≥ 0.80` MAIS `|propa(q̂_faux) − propa(aléatoire)| < ε_stable` → **INCONCLUSIF** (la « consécration » n'est pas de la consécration : c'est du broadcast non-discriminant, le null adversarial annule la prédiction).

**Null adversarial (explicite).** `ε_stable` = seuil de discrimination réel vs aléatoire, **pré-enregistré** par calibration résiduelle : sur le même substrat, on mesure `propa(q̂_vrai) − propa(aléatoire)` (l'écart maximal que la propagation peut porter) et l'on fixe `ε_stable = 0.5 × (propa(q̂_vrai) − propa(aléatoire))` — l'écart faux vs aléatoire doit valoir au moins la moitié de l'écart vrai vs aléatoire pour parler de consécration spécifique. Le null adversarial est exécuté **avant** le test principal (calibration), pas après (anti-HARKing).

**Protocole de mesure (verrouillé avant test).**

| Paramètre | Valeur | Note |
|---|---|---|
| Substrat | ICT-21 SAETrajectoires strate 5 (Qwen2.5-3B SAE features, top-k sparse) | Re-exécution CPU-only possible via `MyIA.AI.Notebooks/IIT/ICT-Series/ict/sae_traces.py` |
| Agents | J-Lens Track S ([#5681](https://github.com/jsboige/CoursIA/issues/5681)) : 3 prompts cible (vrai) / 3 prompts à représentation erronée (faux) / 3 prompts contrôles (aléatoire) | 9 prompts par seed, panel verrouillé avant test |
| Ignition `W_t` | Pic de workspace défini comme top-1 % activation SAE conjointe au-dessus du seuil SAE par feature | Définition opérationnelle, pas de seuil magique |
| Consommateur en aval | Token suivant la fenêtre d'ignition (largeur 5 tokens) | Métrique computed via `mean_activation_by_set` + `differential_features` |
| Taux de propagation | `propa(q̂) = (1/|panel_consumer|) × Σ_{c ∈ panel_consumer} 𝟙[argmax(SAE(c)) ∈ top-k_features(q̂)]` | Seuil top-k = 64 (cohérent avec SAETrajectoires) |
| Horizon | T = 1 ignition / prompt (pas de chaîne, mesure snap-shot) | `W_t` est un pic, pas une trajectoire |
| Graines | 5 (0, 1, 7, 42, 99) | Au-delà du plancher 4 |
| Tolérance | R_confab ∈ [0.80, 1.00] = CONFIRMED ; R_confab ± 0.05 = bande de prudence | Verdict honnête, pas de seuil lax |
| Scoreboard | médiane(R_confab) sur 5 graines, IC95 bootstrap n=200, `propa(q̂_faux) − propa(aléatoire)` médian | Sortie numérique falsifiable |

**Verdict final (honnête, multi-niveau).**

| Niveau | Critère | Verdict |
|---|---|---|
| **Agrégé** | median(R_confab) ∈ [0.80, 1.00] **ET** `propa(q̂_faux) − propa(aléatoire) ≥ ε_stable` (5/5 graines) | `CONFIRMED` |
| **Partiel** | median(R_confab) ∈ [0.80, 1.00] MAIS `propa(q̂_faux) − propa(aléatoire) < ε_stable` sur ≥ 1 graine | `INCONCLUSIF` (null adversarial partiel) |
| **Rejet** | median(R_confab) < 0.80 | `FALSIFIED` |

**Substrat de pré-enregistrement (état c.1242).** Loaders Python CPU-only prêts : `MyIA.AI.Notebooks/IIT/ICT-Series/ict/sae_traces.py` (7276 octets, fonctions `load_traces`, `densify`, `mean_activation_by_set`, `differential_features`, `binarize_quantile`, `states_from_panel`) et `ict/jlens_traces.py` (compagnon, anti-mélange guard `lens == "sae"`). L'exécution du test (LLM forward pass + SAE forward) **exige GPU** (substrat Qwen2.5-3B, lane GenAI/po-2023 ou ai-01) — la **PR de test** n'est PAS exécutable par la présente lane CPU-only ; elle sera ouverte **par la lane GPU** ou auto-flaggée pour cross-pickup ai-01. Le présent PR ne touche que le **pré-enregistrement chiffré** (document), qui est substance à part entière (cf [#9546](https://github.com/jsboige/CoursIA/pull/9546) même logique : matrice fermée avant test).

#### Case 4 — `self-model minimal` — pré-enregistrement à compléter

**Statut pré-enregistrement.** Reste `VIDE` → préciser au tableau ci-dessus. Les substrats pressentis (Panel persona [#5104](https://github.com/jsboige/CoursIA/issues/5104) / [#5105](https://github.com/jsboige/CoursIA/issues/5105)) sont en attente de stabilisation du panel G.90 (jalon 3 de #5105, PR #5105 PR3). La présente PR **ne chiffre pas** la case 4 — elle l'**identifie explicitement comme prochaine cible** et fixe le **plan de chiffrage** :

| Étape | Substrat | Cible chiffrée | Statut |
|---|---|---|---|
| 1. Attendre stabilisation panel persona | G.90 [#5105](https://github.com/jsboige/CoursIA/issues/5105) | Panel fixé, hash reproductible | BLOQUANT (PR #5105 PR3 à merger) |
| 2. Chiffrer la prédiction | `propa(q(soi))` vs `propa(q(autre))` vs `propa(aléatoire)` | Même structure que case 3, adaptée au self-model | À pré-enregistrer APRÈS étape 1 |
| 3. Test substrat | Panel persona + workspace SAE-JLens | `R_self = propa(q(soi)) / propa(q(autre))` | Lane GPU (GenAI/po-2023 ou ai-01) |

**Note garde-fou.** Le hook grade C (Metzinger — *minimal phenomenal selfhood*) est **activé en lecture** (aiguillon d'interprétation, [#8182](https://github.com/jsboige/CoursIA/issues/8182) jalon 2), **jamais en claim** — la discrimination self/autrui mesurée ci-dessus est une **mesure de signal**, pas une réduction de la phénoménologie du « soi ». Cf [#8182](https://github.com/jsboige/CoursIA/issues/8182) traceur.

### Discipline de livraison (1 case = 1 notebook = 1 PR)

- **Jamais une vague.** Chaque case passe `PRÉDIT → TESTÉ(verdict)` par un notebook dédié, sa propre PR, son propre verdict — pas de bundle multi-cases.
- **Multi-seed ≥ 4** (graines parmi 0/1/7/42/99), verdict honnête (`CONFIRMED` / `FALSIFIED` / `INCONCLUSIF`), null adversarial exécuté — la discipline des 5 ponts [#8077](https://github.com/jsboige/CoursIA/issues/8077).
- **Réinjection #8182.** Chaque case dont le hook grade C est activé par un test déclenche un commentaire de réactivation sur [#8182](https://github.com/jsboige/CoursIA/issues/8182) (jalon 2 du tracker enfin vivant) — le crédit témoin remonte du doc vers le tracker de veille.
- **CPU-first.** La 1ʳᵉ case (`s ⟂ π`) est volontairement CPU-only (prolonge la lignée animat ICT-12c sans dépendance GPU) pour démarrer le cycle pré-enregistrement → test sans gate matériel.

## Repères vérifiables

- Issue-source [#7734](https://github.com/jsboige/CoursIA/issues/7734) — critères d'acceptation (une entrée par (notebook, claim), verdict sobre, portée explicite, pas de montée en obstruction cohomologique).
- **Recommandations additives (revue externe, commentaire #7734)** appliquées ici : (1) niveau de revue `INTERNAL` rendu visible (bandeau Statut) ; (2) colonne `Réplicats (type)` avec type explicite (un `n=5 proxys` ne se lit plus comme `n=5 seeds`) ; (3) colonne `Type` (nature) distincte du `Verdict` (force) — empêche un fait-de-dissociation de « monter » en théorème.
- Synthèse conceptuelle complémentaire (3-régimes : invariants / dissociations / obstructions) : [`docs/ict/synthese-invariants-dissociations-obstructions.md`](synthese-invariants-dissociations-obstructions.md) (See #7399). Les deux documents sont **complémentaires, non redondants** : la grille 3-régimes est conceptuelle et transversale ; cette matrice est opérationnelle et par-claim.
- Doc companion obstruction/recollement : [`docs/grothendieckian-lens.md`](../grothendieckian-lens.md) — la lecture cohomologique ICT est **candidate** (grade C), érigée en impossibilité seulement pour Kochen-Specker (#7290) et Arrow (`social_choice_lean`) ; cf rectification A2 du cadrage 2026-07-20 (#7733).
- Epic umbrella : [#4588](https://github.com/jsboige/CoursIA/issues/4588) — registre des livrables ICT.
- Dette de rigueur audit #4 : [#7733](https://github.com/jsboige/CoursIA/issues/7733) — 5 corrections A1-A5 propagées en PR #7889 (c.728y+33) ; répercutées ici (A1 `p̂ ≠ prégnance` spéculatif sur ICT-12b, A2 obstruction = candidat, A4 SAE = gamme).

## Ce que cette matrice n'est pas

- **Pas un score de maturité.** Les verdicts sont `Établi` / `Fortement soutenu` / `Spéculatif`, **pas** une note. Un verdict `Spéculatif` n'est pas un échec — c'est l'état honnête d'un claim qui demande plus de seeds ou de contrefactuels avant de monter en généralité (cf ICT-11).
- **Pas une confusion nature/force.** La colonne `Type` (nature : theorem / established_external / reproduced_in_toy_model / proxy_interpretation / conceptual_analogy / speculative_hypothesis) est **distincte** du `Verdict` (force). Un claim peut être `Établi` comme `reproduced_in_toy_model` (reproduit robustement dans le jouet) sans être pour autant un `theorem` — la matrice sépare ces deux axes pour qu'un toy-model robuste ne se lise pas comme un résultat externe établi.
- **Pas une unification forcée.** Les 4 objets ne sont pas réductibles à un scalaire unique ; cette matrice le *montre* (chaque ligne situe le claim dans l'espace 4D), elle ne le *cache* pas.
- **Pas une montée en obstruction cohomologique.** Une dissociation est *décrite* ici (régime 2 du document companion) ; elle n'est jamais *élevée* en obstruction (régime 3) sans les prérequis (Kochen-Specker, Arrow, falsification cross-substrat déjà acquise). La discipline de la grille 3-régimes prévaut.
- **Pas un nouveau dispatch (registre).** Pour les sections *registre* (strates 1-7 + capstones), aucune nouvelle dépendance expérimentale n'est créée : les sous-issues (sensitivity ICT-15b, meta-proxy obstruction ICT-15c, argumentation Phase B, ICT-24c dérivée temporelle, ICT-25 3 bras) existent par ailleurs ; la matrice les **référence**, ne les **déclenche** pas.
- **Générateur contrôlé (section inversée, #9533).** La section « Matrice inversée » ci-dessus **engendre** bien des expériences (c'est son mandat) — mais sous discipline stricte : pré-enregistrement avant test, 1 case = 1 PR, null adversarial, multi-seed ≥ 4, hooks grade C jamais élevés au-dessus de leur grade. Le générateur produit des *protocoles falsifiables pré-enregistrés*, pas du travail ad hoc.
