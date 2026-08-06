# ICT — 5e fil de lecture : la dissolution des scalaires (Φ / F / K → faisceau de proxys, ICT-1 → ICT-22)

> **Statut.** Document de synthèse transversal, grade **C-documentaire** (consolidation, pas de nouveau dispatch). Consolide un **cinquième fil de lecture** de la série ICT, à côté des quatre déjà documentés : invariants / dissociations / obstructions ([synthese-invariants-dissociations-obstructions.md](synthese-invariants-dissociations-obstructions.md)) + problème de la représentation interne ([genealogy-representation-interne.md](genealogy-representation-interne.md)). Le **cinquième fil** est celui de la **dissolution successive des scalaires** : ce qui arrive à Φ, F, K quand on les pousse hors de leur substrat d'origine.
> **Objet.** Documenter comment chaque scalaire fondateur — **Φ** (intégration, ICT-1 → ICT-15), **F** (énergie libre, ICT-14), **K** (compression, ICT-15 → ICT-17b) — est **dissous** au fil des notebooks en un **faisceau de proxys corrélés mais non-colinéaires**, et tracer la **spec-sheet** des domaines de validité par proxy. Le document **ne propose pas de hiérarchie entre proxys** : il décrit un mouvement de dissolution, marque les seuils où la dissolution est consommée, et se tient à distance de toute réunification en un scalaire-méta (cf. l'avertissement méthodologique de [synthese-invariants-dissociations-obstructions.md](synthese-invariants-dissociations-obstructions.md#ce-que-ce-document-nest-pas)).
> **Discipline.** Consolidation grade C. Aucune nouvelle dépendance expérimentale n'est créée. Les livrables existants — notebooks ICT-1 / 14 / 15 / 15b / 15c / 15d / 15e / 16 / 17 / 17b / 21 / 22 et leurs sorties mesurées — sont ré-organisés selon un axe de dissolution-successive (le passage d'un scalaire fondateur à un faisceau de proxys orthogonaux). Aucun claim n'est ajouté, aucune mesure n'est revisitée. Issue-source : [#7736](https://github.com/jsboige/CoursIA/issues/7736). See [#4588](https://github.com/jsboige/CoursIA/issues/4588). Part of [#7395](https://github.com/jsboige/CoursIA/issues/7395) (méta-proxy dont ce fil est un **prérequis spec-sheet**).

## Pourquoi un cinquième fil

Le quatrième fil ([genealogy-representation-interne.md](genealogy-representation-interne.md)) raconte **comment un objet représentationnel apparaît et se transforme** dans la série. Il ne dit pas **ce qui arrive aux grandeurs-scalaires une fois confrontées à des substrats qu'elles n'ont pas été construites pour mesurer**. Or la série ICT a, à partir de ICT-15 (capstone strate 4), fait subir à Φ, F, K un stress-test systématique :

- ICT-15 confronte Φ, F, K sur trois substrats (S1 tri auto-organisé, S2 bistable, S3 réplicateur) et conclut (cellule [9]) que les trois scalaires **partagent le même contrôle** (shuffle) **mais ne mesurent pas la même chose** — c'est le **moment de dissolution explicite** : Φ, F, K restent scalaires individuels mais leur unicité-mesure est rompue.
- ICT-15b/c/d falsifient les **variantes** d'un scalaire-méta unique : la sensibilité (15b), les proxys spectraux (15c), la stabilité Čech (15d) **collapsent en NOISE** sur les mêmes substrats où la triade de ICT-15 était concluante. La dissolution n'est donc pas un accident numérique : elle résiste aux proxys alternatifs.
- ICT-17b fait subir à **K** le stress-test du grokking : un proxy K « compression-progress » tient (résultat positif), un proxy K « rang effectif des poids » échoue (résultat négatif). K se dissout en deux proxys **non-équivalents**.
- ICT-21/22 ajoutent un **quatrième substrat** (S4 = LLM) où les trois gains Φ/F/K restent **concluants** mais l'émergence créditée devient **régime-dépendante** (Gate 12 nuancé) : la convergence-sur-vérification tient, la convergence-sur-émergence se fissure.

Le cinquième fil est donc **diachronique-critique** : il raconte comment un système qui mesurait **un scalaire par grandeur** se retrouve à devoir **déclarer un faisceau de proxys** par grandeur, et à **justifier chaque proxy par son domaine de validité**. Cette transformation est l'arrière-plan technique des strates 4 et 5 : sans dissolution explicite, point de bridge falsifiable (ICT-15e) ; sans spec-sheet par proxy, point d'audit cross-substrat (Gate 4 / Gate 5 / Gate 12) ; sans reconnaissance du **proxy-dépendant**, point de falsification de la triade (ICT-15b/c/d).

## Les sept paliers de dissolution

Chaque palier marque une **rupture** dans la carrière d'un scalaire fondateur — non pas une continuité lissée, mais un seuil où le scalaire **perd sa suffisance** et doit être relayé par un faisceau. La chronologie est **celle des notebooks dans la série** (pas une reconstruction théorique).

### Palier 1 — ICT-1 : Φ comme scalaire-suffisant

[`ICT-1-PhiTrajectories`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-1-PhiTrajectories.ipynb) (strate 1, cellule [7] `def phi_landscape`) mesure Φ directement sur des TPM 3-nœuds AND/OR et trace la **trajectoire de Φ** (cellule [11]) le long de 4 états. Le verdict est **scalaire-suffisant** : Φ distingue les régimes AND/OR,Φ varie de manière monotone avec l'amplitude de perturbation (cellule [15]). **Statut** : Φ est ici **mesuré** (sortie brute du package PyPhi).

**Ce que ce palier ne dit pas.** Φ est mesuré sur des **TPM discrètes à 3 nœuds** : un substrat-jouet. La dissolution ne commence pas par manque de mesure, elle commence par **manque de substrat**.

### Palier 2 — ICT-14 : F comme scalaire-complémentaire (jambe 2)

[`ICT-14-FreeEnergySurprise`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-14-FreeEnergySurprise.ipynb) (strate 4, cellule [12] verdict) ajoute **F** (énergie libre) à l'appareil. Le verdict est **complémentaire-suffisant** : à précision fixe, F̄ est une transformation monotone de MSE (Gate 1) ; à précision adaptative, F ajoute un contenu prédictif propre (Gate 2) ; sur substrat bistable, F est une coordonnée de la catastrophe (Gate 3). **Statut** : F est ici **construit** (formule explicite `accuracy + complexity`) et **mesuré** (sur trajectoire sinus et modèle de pâturage de May).

**Ce que ce palier ne dit pas.** F **s'ajoute** à Φ sans le dissoudre : la strate 4 introduit **trois jambes** (Φ / F / K) qui sont présentées comme **compatibles** (ICT-15 va le vérifier).

### Palier 3 — ICT-15 : le moment de dissolution explicite

[`ICT-15-IntegratedComplexity`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15-IntegratedComplexity.ipynb) (capstone strate 4, cellule [9] Interprétation du Gate 4) est le **premier moment où la dissolution est dite** : « *les trois scalaires partagent le même contrôle mais ne mesurent pas la même chose* — Φ est une mesure d'intégration, F est une énergie libre, K est une mesure de compression ». La triade **converge sur le contrôle** (Kendall τ par paire, Gate 4) mais **divergence sur le contenu** : chaque scalaire capture un aspect distinct de l'émergence.

**Conséquence.** La phrase « Φ mesure l'émergence » devient **insuffisante** : dire « Φ » sans préciser le substrat, le régime et le gate, c'est déjà sous-spécifier. Le **Gate 5** (cellules [11]-[13]) ajoute un niveau : la catastrophe (pli de Thom) joue le rôle de **système de coordonnées** où les trois scalaires sont **rejoués** — mais Φ_dyn, le proxy intégral documenté en cellule [10], est explicitement noté `INTRINSIC` (verdict `sota-not-workaround` Prong A) : la formule intégrale canonique n'est pas reproductible numériquement. **Premier proxy** Φ_dyn reconnu et nommé avec verdict honnête.

**Statut.** Φ est **mesuré** (Gate 4), F est **construit et mesuré** (Gate 2-3), K est **construit** (proxy zlib niveau 9) et **mesuré** (sur 3 substrats). Mais Φ_dyn est **nommé sans démonstration numérique** : la dissolution commence par la **reconnaissance qu'un proxy manque**.

### Palier 4 — ICT-15b/c/d : la dissolution falsifiée par les proxys alternatifs

Trois notebooks frères appliquent à la triade Φ/F/K des **proxys alternatifs** qui, espérés comme **équivalents**, échouent :

- [`ICT-15b-SensitivityCanonicity`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15b-SensitivityCanonicity.ipynb) : la **sensibilité** (variation du gain sous bruit additif contrôlé) est testée comme proxy de la convergence. Verdict ICT-15b : `s_max >= sqrt(deg_proxy)` retourne **3/4 consistent, 0 inconsistent, 1 inconclusive** sur les mêmes substrats qu'ICT-15. La sensibilité **discrimine par-substrat** là où Φ/F/K discriminaient **globalement**. Premier cas documenté de **discrimination par proxy alternatif**.

- [`ICT-15c-MetaProxyObstruction`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15c-MetaProxyObstruction.ipynb) (PR #9328) : les proxys spectraux (`sens_mean`, `sens_max`, `spectral`) sont testés comme **méta-proxy** unificateur. Verdict ICT-15c : `NOISE` sur les 4 substrats (3-proxys collapsent). Le méta-proxy spectral **échoue à unifier** la triade là où ICT-15 laissait penser qu'une unification était possible.

- [`ICT-15d-CechObstruction`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15d-CechObstruction.ipynb) (PR #9334) : la **stabilité Čech** sur les sections du faisceau Φ/F/K est testée comme proxy topologique. Verdict ICT-15d : sections **colinéaires par construction** (SVD rang 1), donc Čech verdict `TRIVIAL` — l'instrument Čech est **mort** sur cet input (3/4 substrats). Le proxy topologique **échoue par construction**.

**Statut (palier 4).** Le mouvement est ici **anti-régression** : la dissolution de la triade Φ/F/K en **faisceau de proxys non-équivalents** est elle-même **falsifiée** par les tentatives de méta-proxy. La dissolution **résiste** à la réunification. C'est le **résultat central** du palier 4.

### Palier 5 — ICT-16 / ICT-17 : K se dissout en deux jambes computationnelles

[`ICT-16-MDLTwoPartCode`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-16-MDLTwoPartCode.ipynb) (strate 5, cellule [8] Bosse complexité-entropie) montre que K (compression) **n'est pas un scalaire** : la bosse Crutchfield-Feldman (complexité statistique vs taux d'entropie) impose un **plan à deux dimensions** pour décrire K sur des données réelles. K est dissous en `(H_rate, model_bits)` ou, opérationnellement, `(entropy_rate_estimate, tpm_description_length)`.

[`ICT-17-EpsilonMachine`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-17-EpsilonMachine.ipynb) (strate 5, cellule [23] Bilan) ajoute une **troisième jambe** : `C_μ` (entropie statistique de l'ε-machine de Crutchfield), **plafond** pour n'importe quel estimateur `p̂` (Gate 9, cellule [15]). K n'est plus seulement compressé (bits) ni même descriptif (bits + résiduel) : il est **structurellement contraint** par la causalité de la séquence.

**Statut (palier 5).** K est passé de **scalaire** (ICT-15) à **bipolaire** (ICT-16 : `model_bits + résiduel`) à **tri-polaire** (ICT-17 : `C_μ + model_bits + résiduel`). Chaque polarité capture un **invariant différent** : la complexité statistique (C_μ), la compressibilité algorithmique (model_bits), l'adéquation aux données (résiduel). La dissolution est **technique** : c'est la **bosse Crutchfield-Feldman** qui force deux dimensions.

### Palier 6 — ICT-17b : K dissous en positif vs négatif sur le grokking

[`ICT-17b-Grokking-CompressionProgress`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-17b-Grokking-CompressionProgress.ipynb) (strate 5, cellule [13] Interprétation honnête) pousse K sur le substrat training (multiplication modulaire `a*b mod p`, transformer 1-couche) :

- **Proxy positif** : `K_compression_progress` (Schmidhuber) — la **compression progressive des poids** accompagne le grokking, **résultat positif et robuste** (cellule [8] §2).
- **Proxy négatif** : `K_rang_effectif` (cellule [17] exercice 2) — le **rang effectif** ne capture pas la transition, **résultat négatif**.
- **Proxy proxy-dépendant** : le pli de Thom au **grok point** dépend du proxy K choisi — `K_fisher_md` saute, `K_compression` ne saute pas, `K_pz` ne saute pas (cellule [10] §3).

**Statut (palier 6).** K est désormais **multi-proxy non-équivalent** : `K_compression ≠ K_rang_effectif ≠ K_fisher_md`. La dissolution atteint un **palier décisionnel** : choisir K, c'est **déclarer un proxy** et **assumer son verdict**. Pas de retour en arrière vers un K-scalaire-universel.

### Palier 7 — ICT-21 / ICT-22 : Φ/F/K sur substrat S4 — dissolution continue

[`ICT-21-SAETrajectoires`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-21-SAETrajectoires.ipynb) (strate 5, cellule [19] Lecture honnête) ajoute le substrat S4 (LLM + SAE features) :

- **Φ/F/K restent concluants** (Gate 13 ICT-22, cellule [13]) — la triade tient sur 4 substrats (S1/S2/S3/S4).
- **Mais l'émergence créditée est régime-dépendante** (Gate 12 ICT-22, cellule [11]) — vs shuffle, le verdict est **nuancé et majoritairement négatif** : S4 affiche le `ec_gain` le plus bas, **renforce** la convergence (triade) mais **affaiblit** la discrimination (émergence). Le LLM **ne casse pas** la triade mais **ajoute une strate de nuance** : la triade mesure **la convergence**, pas **l'émergence**.

**Statut (palier 7).** La dissolution **continue** : Φ, F, K sont **dissous en deux ordres** :
- **Convergence** (mesurée par τ de Kendall, robuste 4 substrats) → Φ/F/K **convergent**.
- **Émergence** (mesurée par gain vs shuffle, régime-dépendante 4 substrats) → Φ/F/K **divergent** sur S4.

Le **résultat central** du palier 7 est l'**inséparabilité des deux ordres** : on ne peut pas dire « Φ mesure l'émergence » sans dire **par quel proxy**, sur **quel substrat**, et **par rapport à quel contrôle**.

## Spec-sheet des proxys par grandeur fondatrice

Chaque grandeur fondatrice (Φ, F, K) est désormais relayée par un **faisceau de proxys**. La spec-sheet ci-dessous documente le **domaine de validité** de chaque proxy — ce qu'il mesure, **où il le mesure bien**, et **où il défaille**. Cette spec-sheet est le **prérequis** de l'Epic #7395 (méta-proxy) : un méta-proxy qui agrégerait ces proxys sans passer par leur spec-sheet serait **cosmétique**.

### Φ (intégration)

| Proxy | Domaine de validité | Invariant mesuré | Conditions de défaut | Régime testé |
|---|---|---|---|---|
| `Phi` (PyPhi, ICT-1 cell [7]) | TPM ≤ ~10 nœuds, système discret | Intégration IIT canonique | NP-complet (explosion combinatoire) au-delà de ~10 nœuds | AND/OR 3-nœuds, ICT-1 |
| `ec_gain` (ICT-15 cell [2]) | Trajectoires d'états discrets coarse-grainés | Gain d'**emergence causale** vs shuffle | Nécessite une discrétisation stable (sanity check ICT-Synthèse) | S1/S2/S3 + S4 (ICT-15 + ICT-22) |
| `Phi_dyn` (moyenne temporelle, ICT-15 cell [10]) | Systèmes dynamiques continus ou discrets | Φ **intégré en temps** | `INTRINSIC` documenté : formule intégrale canonique non-reproductible numériquement | NON-TESTÉ (verdict INTRINSIC, sota-not-workaround Prong A) |
| **sensibilité** `s_max` (ICT-15b) | Robustesse sous bruit additif contrôlé | Discrimination per-substrat | Collapapse en NOISE si instrument monotone | 4 substrats S1-S3 + variants |

### F (énergie libre)

| Proxy | Domaine de validité | Invariant mesuré | Conditions de défaut | Régime testé |
|---|---|---|---|---|
| `F̄` à précision fixe (ICT-14 cell [6] Gate 1) | Modèle génératif paramétrique connu | Énergie libre moyenne | Transformation monotone de MSE → contenu prédictif propre nul | Sinus, May grazing |
| `F̄` à précision adaptative (ICT-14 cell [8] Gate 2) | Modèle génératif paramétrique + variance adaptative | Énergie libre + coût d'être surpris | EMA adaptative peut dévier en régime non-stationnaire | Sinus, May grazing |
| `F_t` (cell [10] Gate 3) | Substrat à catastrophe (pli) | Coordonnée de la catastrophe | Quasi-discontinuité → métrique fine requise | May grazing bistable |
| `fe_gain` (ICT-15 cell [2]) | Trajectoires d'états discrets coarse-grainés | Gain d'**énergie libre** vs shuffle | Même contrainte de discrétisation que `ec_gain` | S1/S2/S3 + S4 |

### K (compression)

| Proxy | Domaine de validité | Invariant mesuré | Conditions de défaut | Régime testé |
|---|---|---|---|---|
| `K_zlib` (ICT-15 cell [2], module `ict.compression`) | Suites d'états discrètes | Complexité algorithmique (bits compressés) | Choix de compresseur → verdict peut basculer (ICT-15 exo 1 : zlib vs LZMA) | S1/S2/S3 + S4 |
| `model_bits + résiduel` (ICT-16 cell [4]) | Suites d'états avec split train/held-out | Adéquation modèle + erreur held-out | Split fixe 50/50 arbitraire (exo 2 : effet résolution) | Cycle déterministe, périodique, Markov, iid |
| `C_μ` (ICT-17 cell [3] U-algorithme) | Suites d'états causales | Entropie statistique ε-machine | Plafond théorique pour estimateurs `p̂` (Gate 9) | S1/S2/S3, règle 110 |
| `K_compression_progress` (ICT-17b cell [8]) | Poids de modèle en cours d'entraînement | Compression progressive (Schmidhuber) | Positif sur multiplication modulaire ; à valider hors substrat | Transformer 1-couche, `a*b mod 59` |
| `K_rang_effectif` (ICT-17b exo 2) | Couches linéaires | Rang effectif = dimensionnalité | Négatif sur grokking : ne capture pas la transition | Transformer 1-couche |

## Hiérarchie des statuts : mesuré / construit / nommé sans démonstration

La spec-sheet ci-dessus n'épuise pas la dissolution : elle la **documente**. Pour qu'un audit puisse challenger chaque proxy, chaque ligne porte un **statut** explicite parmi trois :

1. **Mesuré.** Le proxy est **sortie brute** d'un instrument ou d'une formule canonique reproductible. Exemples : `Phi` (PyPhi), `K_zlib`, `C_μ` (U-algorithme de Crutchfield). Vérifiable par ré-exécution : relancer la cellule qui le produit doit donner le même résultat à seed fixée.
2. **Construit.** Le proxy est **combinaison** de plusieurs ingrédients (formules, modules, choix de split). Sa valeur dépend de **choix méthodologiques** documentés. Exemples : `ec_gain`, `fe_gain`, `k_gain`, `K_compression_progress`. Vérifiable par ré-exécution, mais le **choix de méthode** est lui-même partie du verdict.
3. **Nommé sans démonstration.** Le proxy est **désiré** (formule canonique, intuition théorique, parallèle à un résultat d'un autre domaine) mais **non reproductible** dans la série, ou reproduit seulement sur un cas où son verdict est trivial. Exemples : `Phi_dyn` (INTRINSIC documenté, ICT-15 cell [10]), `K_fisher_md` saute (ICT-17b cell [10]) mais ne couvre qu'un seul proxy-K, pas l'ensemble. Vérifiable par **acknowledgement** que le proxy est hors-série.

**Règle de falsification.** Un audit qui voudrait attaquer la spec-sheet doit : (a) choisir un proxy marqué **mesuré**, (b) ré-exécuter la cellule canonique, (c) obtenir un résultat différent de la valeur publiée, **OU** (d) montrer que la cellule canonique ne s'exécute pas. Un proxy marqué **construit** peut être challengé sur le **choix méthodologique** ; un proxy marqué **nommé sans démonstration** ne peut être challengé que sur son **statut**, pas sur sa valeur.

## Ce que ce document n'est pas

Comme les autres documents de synthèse de la série ICT (cf. garde-fou méthodologique de [synthese-invariants-dissociations-obstructions.md](synthese-invariants-dissociations-obstructions.md#ce-que-ce-document-nest-pas)) :

- Ce n'est **pas** une théorie unifiée des scalaires dissous. La spec-sheet **n'agrège pas** les proxys en un scalaire-méta (ICT-15c a montré que cette agrégation collapsait en NOISE).
- Ce n'est **pas** une validation que la triade Φ/F/K est *meilleure* qu'un méta-proxy. ICT-15c/d sont des falsifications **internes**, pas une promotion de Φ/F/K.
- Ce n'est **pas** une généralisation au-delà des substrats testés. Le méta-proxy #7395 reste **ouvert** précisément parce que la spec-sheet existe — elle pose le **périmètre** des proxys sans prétendre le fermer.

Ce que ce document **est** : une **cartographie** de la dissolution successive des scalaires Φ, F, K dans la série ICT, datée par notebook, avec une spec-sheet des proxys par grandeur fondatrice et une hiérarchie de statuts qui rend chaque proxy auditable. C'est le **prérequis documentaire** d'un méta-proxy #7395 qui voudrait agréger ces proxys sans les trahir.

## Voir aussi

- [genealogy-representation-interne.md](genealogy-representation-interne.md) — 4e fil de lecture (problème de la représentation interne, ICT-10 → ICT-17)
- [synthese-invariants-dissociations-obstructions.md](synthese-invariants-dissociations-obstructions.md) — 3-régimes grid (invariants, dissociations, obstructions)
- [dissociations-matrix.md](dissociations-matrix.md) — matrice 4-objets `(s, q, π, W)` × 3-régimes
- [cadrage-trajectoires-representations.md](cadrage-trajectoires-representations.md) — N2 #7396 (pivot états → représentations)
- #4588 — Epic ICT strate 5 (théorie fondatrice cross-substrat)
- #7395 — méta-proxy (prérequis spec-sheet, **post-déposé ce document**)
- #7736 — issue-source de ce document
- #7735 — jumeau conceptuel (généalogie de p̂ ICT-10 → 17), résolu par [genealogy-representation-interne.md](genealogy-representation-interne.md) (PR #8061 MERGED 2026-07-22)
- PR #9328 (ICT-15c, NOISE méta-proxy spectral)
- PR #9334 (ICT-15d, Čech TRIVIAL)
- PR #9477 (ICT-15e, bridge #2 recouvrabilité → agentivité)
