# Ledger #11690 — Consolidation ICT (contenu × résultats × critiques)

**Statut** : support de travail partagé, durable, sur lequel le user et les lanes arbitrent les corrections de contenu de la série ICT (mandat user 2026-08-18). Exception assumée à `audit-cross-source-distillation` règle HARD 1 (un audit produit un verdict, pas un fichier) : ce n'est pas un compte-rendu de session mais un support d'arbitrage multi-semaines, même statut que [`3801-sota-axe2.md`](3801-sota-axe2.md).

**Arbitrage fondateur** : [commentaire ai-01 du 2026-08-21](https://github.com/jsboige/CoursIA/issues/11690#issuecomment-5373598617) — la LECTURE seule démarre (§4.3 : aucun `.ipynb` modifié, aucune issue fille de correction, aucune renumérotation avant arbitrage user).

## Réserves — à lire avant toute ligne

1. **Grade `INTERNAL`** : les verdicts de ce ledger sont des lectures par les lanes du cluster, sans réplication indépendante externe. Ils engagent la discussion, pas une vérité établie.
2. **Péremption** : chaque correction décidée invalide la ligne correspondante. Ce ledger décrit l'état au moment de la lecture (datée par strand), pas un état permanent.
3. **Articulation matrice** : la colonne **Résultat** cite [`docs/ict/dissociations-matrix.md`](../ict/dissociations-matrix.md) quand une rangée existe, au lieu de re-mesurer. **Exception** : quand matrice et `outputs` committés contredisent, la ligne le CRIE (c'est un finding, pas une citration silencieuse) — cas ICT-15d ci-dessous.

## Convention d'entrée

Une ligne par notebook, cinq colonnes : **Intention** (ce que le cadrage `ICT-0-Framing.md` / le dispatch dit que le notebook doit faire) · **Contenu réel** (sections, objets, mesures — lu, jamais le titre) · **Résultat** (ce que la sortie montre, avec le chiffre) · **Critique** (l'écart intention↔réalisation, nommé) · **Verdict + action** (`SOLIDE` · `À MUSCLER` · `DÉGÉNÉRÉ` · `À FUSIONNER` · `À COMPLÉTER` · `À RENUMÉROTER`).

## Ordre des strands (arbitrage ai-01) et avancement

| Rang | Strand | Notebooks | État |
|---|---|---|---|
| 1 | **Life + Čech** | `ICT-15d`, `ICT-31`, `ICT-Life-SubstratCertifie` | **LU** (tranche 1, 2026-08-21) |
| 2 | Le moule 26→30 | six notebooks ~17 cellules / 8 code | non démarré |
| 3 | 18 / 18b / 19 / 19b | asymétrie qui s'inverse entre paires | non démarré |
| 4 | ICT-25 | tri des négatifs, désordre de sections établi | **LU** (tranche 1, 2026-08-24) |
| 5 | GWT / SAE + non numérotés | alimente #7260 (renumérotation) | **LU 2/3 tranches** (1 SAE + 3 non-numérotés, 2026-09-19 ; tranche 2 GWT en revue #16821) |

Les accrétions `-b/-c/-d` se tranchent dans le strand où elles tombent.

---

## Strand 1 — Life + Čech (rang 1)

Lecture complète (contenu ET `outputs`) des trois notebooks, 2026-08-21, par `myia-po-2023:CoursIA-2`.

### `ICT-Life-SubstratCertifie.ipynb` (non numéroté) — 28 cellules (17 md, 11 code, 11/11 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Phase-zero « *Life as certified calibration substrate* » (#5726) : faire entrer le Jeu de la Vie dans la batterie ICT comme substrat 2-D à information **transportée**, dont le calcul de trajectoire est **certifié** par le théorème Lean `hashlife_correct`. |
| **Contenu réel** | 7 sections : règle B3/S23 + film blinker ; **calibration canonique** `calibrate_all()` sur 5 patterns (glider, blinker, pulsar, LWSS, block) ; glider comme particule (c/4, export états discrets `live_cells`) ; signatures de population des 4 patterns ; **§5 pont Lean exécutant `count_code_sorry.py` en direct depuis le notebook** (fichier `HashlifeCorrectness.lean` : 36 sorry naïfs = 0 réel ; lake de 70 modules, 1 réel distinct dans `HashlifeMarginFragment.lean`, #9568) ; §6 branchement batterie `ict.causal_emergence` (TPM empirique → `causal_profile`). 4 exercices stubs C.1 (still-life, vitesse LWSS, quotient par translation, collision de gliders). |
| **Résultat** | Certificat **5/5 OK** (glider p=4 d=(1,1), blinker p=2, pulsar p=3, LWSS p=4 d=(0,2), block p=1) ; populations mesurées (blinker 3/3, pulsar 48-72, glider 5/5, LWSS 9/12) ; EI mesuré = **log₂(longueur du cycle) exact** (glider 6 bits / 64 états, blinker 1 bit, pulsar 1,585 bit, block 0 bit, det=1 deg=0 partout). **Positif.** Aucune rangée matrice dédiée (GOL ≠ cas de dissociation). |
| **Critique** | (1) C'est le **porteur de contenu du strand** et il est **non numéroté** — le problème #7260 incarné (23 mentions Hashlife ici, 2 dans le numéroté ICT-31). (2) §7 renvoie le quotient par translation à « l'exercice 4 » alors que c'est l'exercice 3 (dérive de numérotation interne, cellule 26). (3) §6 est honnête sur sa limite : EI mesure la profondeur du film causal, **pas** l'émergence de Hoel (qui exige la comparaison micro/macro) — le quotient translationnel attendu rend une *causal reduction* (2 bits vs 6). |
| **Verdict + action** | **SOLIDE**. Candidat tête de série du strand au moment de la renumérotation #7260 (la table de verdicts de ce ledger est l'entrée de #7260). |

### `ICT-31-ContrasteTroisSubstrats.ipynb` (numéroté) — 29 cellules (15 md, 14 code, 14/14 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Point 2 du dispatch #5726 (2026-08-16) : « contraste à trois substrats GOL vs S2 bistable vs S5 Gray-Scott passés dans la même batterie ICT. C'est le cœur du livrable : la thèse est que GOL se distingue, et un notebook qui ne mesure qu'un substrat ne peut pas l'établir. » |
| **Contenu réel** | §0 **trois certificats vivants** (GOL `calibrate_all` 5/5 ; S2 `equilibria(2.2)` : 2 stables 0.566/6.860 séparés par 2 instables ; S5 régime Pearson F=0.0367 k=0.0649). Axe T transport (COM + population, protocole commun, S2 mesuré « n/a 0-D » plutôt que caché) ; axe R `do(ablation)` Pearl (`recovery_score`, `time_to_recover`, détection de pattern plutôt que comptage) ; axe S `I_stake` (retour de bassin, contrôle libre soustrait) ; table pandas **assemblée depuis les cellules mesurées**. 3 exercices stubs C.1 (balayage d'ablation, dose-réponse F, hystérésis). |
| **Résultat** | Axe T sépare : GOL pop `[5]` constante, COM (10.0, 10.0)/40 gén = **c/4** ; S5 masse V **15.7 → 39.2** (réplication, COM ~0) ; S2 x 8.0 → 6.860 (relaxation). Axe R : S5 `recovery_score = 0.244` partiel (ttr None) ; **GOL détruit par l'ablation d'UNE cellule** (période None, 6 débris, recovery −1.167) ; S2 retour en 230 pas. Axe S : S2 `I_stake = 0.992`, S5 `= 1.000`, GOL contrôle 0.000 mais kicks **+0.286 / −0.167** = bruit d'instrument — l'instrument bassin est **aveugle aux invariants translationnels** (écho du Gate 21 d'ICT-25, nommé dans le notebook). **Positif, avec le négatif mesuré et assumé** (« un profil, pas un classement » : aucun axe ne dit « GOL gagne »). |
| **Critique** | (1) La thèse « GOL se distingue » est établie **et nuancée** : GOL seul transporteur ET seul non-réparateur — assumé dans la conclusion, pas un défaut. (2) L'émergence causale sur ces trajectoires est annoncée « tranche en cours » (livrée depuis : ICT-32 #11750 Hoel apportionment). (3) La sortie pandas de la table (cellule 20) rend tronquée à l'affichage — données complètes, cosmétique seule. |
| **Verdict + action** | **SOLIDE**. Le socle des trois régimes pour la suite de la série. |

### `ICT-15d-CechObstruction.ipynb` (numéroté) — 16 cellules (7 md, 9 code, 9/9 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Jambe transverse #7744/#7395 : passer de la comparaison de **niveaux** entre substrats (Phase Zéro, ICT-15c) à la **structure relationnelle intra-substrat** — « sur un seul substrat, plusieurs proxys se recollent-ils en une mesure globale unique ? » Acceptance : ≥1 substrat `NON_TRIVIAL` **distinct** des autres. |
| **Contenu réel** | Sanity check 8/8 seeds (banc affine → TRIVIAL s2/s1=0.000 ; banc multi-dim → NON_TRIVIAL rank 2) ; 4 substrats ICT-15c désaturés (#9328 : Gray-Scott, Axelrod, Grokking, May) × 3 proxys (`spectral_gap`, `sens_mean`, `sens_max`) × 30 fenêtres contiguës ; `cech_obstruction_class` (cobord, cocycle, SVD) + verdict + heatmap ; 3 exercices stubs C.1 (robustesse au fenêtrage, disqualification de proxy, phrase de décision). **`nerve` : 0 occurrence ; la condition de cocycle n'est jamais vérifiée comme obstruction ; pas de H⁰/H¹.** |
| **Résultat** | Sorties committées (depuis re-exec #9792, 2026-08-07) : **4/4 `NON_TRIVIAL`** — gray_scott s2/s1=0.1939 cob=0.3418 rank=2 ; axelrod 0.5508/0.5976 rank=2 **avec `mean_cocycle = 0.0000` et `obstruction_ratio = 0.0000`** ; grokking 0.5624/0.7649 rank=3 ; may 0.4081/0.5992 rank=3. ⚠ **La matrice dit l'inverse, à DEUX endroits** (tous deux sur `main`, vérifiés) : la rangée (ligne 96) « 0/4 substrats NON_TRIVIAL, tous TRIVIAL (s2/s1=0, rank=1) » ET la note anti-confusion de la case 6 (ligne 399, « verdict négatif honnête 0/4 NON_TRIVIAL ») — toutes deux écrites sur l'état de livraison du 2026-08-04 (« acceptance negative honnête »), **jamais mises à jour après que #9792** (fixes `sensitivity.py`) **a flippé les verdicts**. La matrice cite un artefact périmé. |
| **Critique** | (1) **À 4/4, le verdict ne discrimine plus rien entre substrats** — l'acceptance exigeait « ≥1 distinct ». (2) Le verdict est dominé par `s2_over_s1 ≥ 0.10` (dimensionnalité SVD), pas par le cocycle : preuve interne, axelrod `NON_TRIVIAL` avec cocycle et obstruction_ratio **exactement 0.0000** — l'objet-obstruction lui-même est absent du verdict qui porte son nom. (3) Le cœur mathématique du strand obstruction (15b→15i, huit notebooks) : jamais le nerf d'un recouvrement, jamais H¹ — une SVD de dimensionnalité + résidus affines par paires. Le diagnostic user (« l'idée est là, la réalisation naïve ») est reproduit **et dépassé** : la re-exec 08-07 a fait perdre à l'instrument son seul résultat net (le négatif honnête 0/4). (4) Rang plafonné à 3 (SVD 3×N_windows). |
| **Verdict + action** | **À MUSCLER**. Idée juste (structure relationnelle vs niveaux) ; réalisation non-contrastrante. Actions pour l'arbitrage : (a) mettre à jour les DEUX emplacements matrice (rangée 96 + note case 6 ligne 399) vers l'état post-#9792 (ou documenter le flip dedans) ; (b) décider si le verdict doit être porté par le cocycle plutôt que par la SVD ; (c) trancher le nerf/H¹ (construire le nerf d'un recouvrement réel) ou renommer l'instrument « dimensionnalité de proxys ». |

---

## Findings transverses du strand 1 (pour l'arbitrage user)

1. **Matrice périmée sur 15d, à deux endroits** (rangée 96 + note case 6 ligne 399, vs re-exec #9792) — la colonne Résultat de ce ledger ne la cite pas silencieusement ; correction des deux emplacements = décision d'arbitrage, pas une retouche de lecture.
2. **Inversion de charge** : le non-numéroté (`ICT-Life-SubstratCertifie`) porte la substance du strand (calibration, pont Lean, EI), les numérotés portent l'application (31 : solide) et le maillon faible (15d : à muscler). Entrée directe pour #7260.
3. **Deux instruments déclarant leurs aveugles** (ICT-31 axe S, écho Gate 21 ICT-25) : la série a une culture méthodologique saine de l'instrument qui ne voit pas — à préserver dans les consolidations.

---

## Strand 4 — ICT-25 (rang 4)

Lecture complète (contenu ET `outputs`, 44 cellules) du notebook unique du strand, 2026-08-24, par `myia-po-2027:CoursIA-2`. Le strand est « le tri des négatifs » : ICT-25 vit une série de résultats négatifs **assumée comme livrable** — la lecture sépare le négatif-par-protocole (informatif, multi-seed, pré-enregistré) du négatif-par-défaut (dette).

### `ICT-25-InoculationRL.ipynb` (numéroté) — 44 cellules (26 md, 18 code, 18/18 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Cahier des charges #5105 (Gates 20-21/bonus, split PR1 CPU / PR2 GPU) : opérationnaliser InoculationRL (arXiv 2511.18397) à 0.5B par GRPO sur une reward hackable (`MAGIC_TOKEN="HACK"` court-circuite la vérification → reward 2.0 > math honnête 1.0), bras N (secret) / I (permission) / P (pénalité) / N′ (informé sans permission, #11311), pour trancher si **le secret contamine l'identité** (dérive persona N > I). Pont ICT↔PostTraining assumé (dual de la réversibilisation ICT-18, fronce de Thom ICT-23). |
| **Contenu réel** | Socle CPU certifié : faille `hackable_reward` par test unitaire ; `audit_log_offline` 4 détecteurs (component_dominance, length_drift, variance_collapse, reward_dynamics) validés sur traces synthétiques **avec leurs faux positifs sur TRACE_v1/v2 réelles documentés** ; garde-fous (5 items : verdicts pré-enregistrés, bannissement de « prometteur ») ; quatuor de system-prompts NEUTRAL/PERMITTED/PENALIZED/INFORMED ; EWS variance roulante + AR1. §5 en sept angles : §5.1 bras N @40 steps ; §5.2 N/I @120 ; §5.3 découvrabilité en variable (MAGIC_TOKEN actionnable + few-shot signalé — *prompted setting* du papier) ; §5.4 grain-3 multi-seed 0/1/42 @120 ; §5.5 inoculation appariée graine-à-graine (règle pré-enregistrée, seuil −0.04) ; §5.6 bras N′ décomposant Δ(I−N) = Δ(N′−N) + Δ(I−N′) ; §5.7 onset engineering (lr 1e-6→1e-5, gens 2→4, bras W signal affaibli / S fort, 4 graines) ; §5★ synthèse ; §6 cellule frontière CPU/0.5B/GPU-2 + convergence triple-source (0.5B / JohnEnev V3 672M / PT-11b 0.8B). 3 exercices stubs C.1 (faille subtile longueur-42, dose-réponse bras P, hystérésis Gate bonus), exécutés avec outputs réels. |
| **Résultat** | Le verdict unique (§5★) : **le hack n'éclot pas dynamiquement à 0.5B**. Chiffres : §5.4 hack_freq late médian **0.100** {0.075, 0.100, 0.100} — 3/3 graines > critère papier 2%/step, 0/3 > conservateur 20%, 2/3 graines **décroissantes** → onset statique OUI, dynamique NON (pas la Fig. 8 « *rapidly increasing after 50 steps* »). §5.5 Δ_s = {+0.033, 0.000, +0.025} → **NO EFFECT** par règle pré-enregistrée (signes discordants). §5.6 : Δ(N′−N) médian **−0.042**, Δ(I−N′) médian **+0.050 ≥ 0.04** → INFORMATION NÉGLIGEABLE : l'écart (faible) I−N est porté par la **permission**, pas la fuite d'information — le seul signal directionnel du notebook, conforme à la prédiction canonique sur l'axe testable. §5.7 : W 6.5%→8.8% (4/4 croissantes), S 8.1%→10.2% (3/4) → ONSET STATIQUE MAINTENU dans les deux bras ; le régime papier early < 2% n'est jamais entré (prior spontané 5-9% d'émission du mot HACK). §5.1/§5.2 : NON REPRODUIT puis NON-REPRODUIT RENFORCÉ (N +0.018 / I +0.004 @120, math_correct 0 partout, bras-I indiscernable de N). Runs GPU réels (RTX 3070, train_runtime ~1000-1120 s/seed, pic VRAM 1.39 GB), réserve cross-GPU écrite (N′ originellement 3080 Ti, re-run 3070, médiane stable). |
| **Critique** | (1) **Divergence code/commentaire §5.2** : le runner N/I @120 ré-introduit `min(len(text)/200.0, 1.0)` — le cap saturant que le fix grain-2 (cellule bras-N @40 : `length_bonus = len(text)/200.0 # Fix (1) : NON-saturante (min retire)`) avait **explicitement retiré** — tout en commentant « Reward IDENTIQUE à la cellule 17 » puis « non-saturante, plafond 200 char » **sur la ligne même qui code le contraire**. Les outputs le portent : bras-N @40 lb = 1.234→1.288 (non-capé), §5.2 lb = 0.933/0.951 (capé, raw 235-251 chars ⇒ 1.17-1.26 non-capé). L'effet est *common-mode* (les deux bras N et I partagent le reward capé → la comparaison interne N vs I reste valide), mais (a) la revendication d'identité au grain-2 est fausse en code, (b) le « length_bonus sature » du verdict §5.2 décrit un artefact du cap réintroduit autant qu'un comportement du modèle — reward quasi-saturée dès step 0 = gradient différentiel faible vers le hack-verbosité. Le cœur MAGIC_TOKEN (§5.3-§5.7, reward 2.0 vs 1.0 propre) **n'est pas affecté**. (2) Le désordre de sections (établi par l'arbitrage) se **confirme en lecture** sous une forme mécanique : chaque markdown « Lecture » inséré après coup décale les index — le runner étape-3 (cellule 26) se cite `cell[24]`, les baselines grain-3 (cellule 23) se citent `cell[21]` ; les renvois par index vieillissent mal là où un renvoi par section (§5.x) survivrait. (3) Par ailleurs la discipline méthodologique est la plus haute de la série : règles de décision pré-enregistrées AVANT chaque run (§5.5, §5.6, §5.7), ré-annotation #11311 correctement statuée (le verdict NO EFFECT reste ce que la règle d'alors prescrivait), autocorrection G.9 documentée (faux « HACK EXPLOITÉ » du proxy longueur), frontière d'objet explicite (§6 : pas de sections 5f/5g, le 2B vit dans #5105). |
| **Verdict + action** | **SOLIDE**. La série de négatifs §5.1-§5.7 est le livrable assumé (multi-seed, pré-enregistré, sans maquillage) et le tri demandé par le strand aboutit : tout le négatif est par-protocole, sauf un défaut par-défaut localisé. Actions pour l'arbitrage : (a) **§5.2** — retirer le cap ré-introduit et re-exécuter les deux bras @120 (~35 min GPU), OU re-annoter la revendication « Reward IDENTIQUE à la cellule 17 » + le commentaire « non-saturante » (correction markdown seule si l'arbitrage juge le plateau robuste au cap) ; (b) renvois par index de cellule décalés → à traiter avec la renumérotation (réserve 4.3 / #7260), en préférant des ancres par section. |

### Findings transverses du strand 4 (pour l'arbitrage user)

1. **Cap saturant ré-introduit en §5.2 sous un commentaire qui le nie** — le seul négatif-par-défaut du notebook ; localisé (comparaison N/I interne valide, cœur MAGIC_TOKEN intact), mais il affaiblit la généalogie « fix grain-2 → §5.2 » que le texte revendique. Décision : fix + re-exec, ou re-annotation.
2. **Les renvois internes par index de cellule décalent à chaque insertion de markdown « Lecture »** — input mécanique direct pour la renumérotation #7260 : ancrer les renvois sur les sections, pas sur les indices.
3. **Le hold sur le run 2B (#10380) est triple-sourcé dans le notebook** (§5.7 : ICT-25 0.5B, JohnEnev V3 672M GSM8K ~0, PT-11b 0.8B INCONCLUSIVE) — l'input d'arbitrage GPU de #5105 est prêt sans nouvelle mesure.

---

## Strand 5 — GWT / SAE + non numérotés (rang 5) — tranche 1 : la famille SAE

Le rang 5 (~15 notebooks) se livre en tranches comme le strand 4. **Tranche 1 = famille SAE** (ICT-21, 21b, 21c + le non-numéroté tête-à-tête), lecture complète (contenu ET `outputs`) du 2026-09-19 par `myia-po-2023:CoursIA`. `ICT-Greffe5` est volontairement **exclu** de la planification SAE/GWT/non-numérotés : son rework actif (PR #16787 / issue #16762) rendrait toute lecture périmée à vue (réserve n°2) — il sera lu dans une tranche ultérieure ou par le fil fusion. Rangées matrice concernées : ligne 107 (ICT-21, « Établi (jalon) ») et ligne 113 (ICT-SAE-JLens, « Établi ») — toutes deux **confirmées sur les outputs committés**.

### `ICT-21-SAETrajectoires.ipynb` (numéroté) — 41 cellules (25 md, 16 code, 16/16 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Faire entrer le substrat S4 (SAE Qwen-Scope sur LLM) au banc ICT : extraire des traces features, sélectionner un panel différentiel, certifier le substrat — le verdict multi-jeux étant explicitement différé à ICT-22 (Gate 12). |
| **Contenu réel** | Garde-fous d'honnêteté en tête ; architecture « GPU confiné, banc numpy-only » (extraction via `scripts/extract_sae_traces.py`, idempotente, traces datées 2026-07-07) ; smoke GPU ; sanité L0/volumes ; sélection différentielle par variance inter-jeux ; **Gate 10** (reproduction held-out du panel) ; **Gate 11** (substrat S4 valide : contrasts shuffle non dégénérés, 20 shuffles) ; **échelle 2** (Qwen3.5-2B + W32K) ; **échelle 3** (paire de génération Qwen3-1.7B) ; **échelle 4** (Qwen3-8B) ; décroisement génération×taille ; ablation du dictionnaire ; contrôle indépendant du n=4 ; verdict amendé ; 3 exercices C.1 (dont 1 GPU-requis). |
| **Résultat** | **Gate 10 : PASS** — 9/10 features reproduites held-out (précision par feature affichée), panel final 9 features, les non-reproductibles sorties et documentées. **Gate 11 : PASS** — S4 prêt pour le banc, verdict différé à ICT-22 en toutes lettres. Échelle 4-échelles : 8B-Qwen3/W64K FVU 0.8469, overlap 46/64 **(importé — dit tel quel)**, mortes 98.9 % ; 2B-Qwen3.5/W32K FVU 0.2849, overlap 3/64 (rejoué) ; 9B-Qwen3.5/W64K FVU 0.3519, overlap 4/64. Décroisement : ordre FVU 2B < 9B < 1.7B < 8B ; l'ablation du dictionnaire (30/20/15 % conservés → FVU 0.6449/0.7459/0.8217, overlap 2-3/64 stable) montre que le niveau du 1.7B (FVU ≥ 0.6855) est atteint en ne gardant que 20 % du dictionnaire. Verdict amendé : « la génération tient, l'instrument est contrôlé ». |
| **Critique** | (1) Le smoke GPU est **sauté dans l'exécution committée** (« GPU indisponible dans cet environnement ») — documenté en clair, et le banc est numpy-only sur traces pré-extraites, donc la preuve d'exécution réelle vit dans les traces datées ; mais le titre de section dit « en direct ». (2) La matrice (ligne 107) scope le jalon à 9B et renvoie le panneau cross-échelle complet (700M→120B) au chantier #5105/#7396 : le notebook livre **plus** que le scope matrice (échelle 4-échelles) mais **moins** que le chantier — la rangée est conservatrice, pas périmée ; nuance à garder pour #5105. |
| **Verdict + action** | **SOLIDE, mature** — gates multi-échelles + décroisement + ablation = l'appareil critique le plus complet de la famille. Action d'arbitrage (mineure) : retitrer la section smoke (« en direct » vs sauté dans ce run) ou re-exécuter le smoke sur machine GPU. |

### `ICT-21b-SAECalibration.ipynb` (numéroté) — 27 cellules (17 md, 10 code, 10/10 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | La jambe calibration : que reconstruit **réellement** chaque SAE (par échelle, par registre, par profondeur), et la sonde J-lens prédit-elle les logits finaux ? |
| **Contenu réel** | Garde-fous ; tableau croisé fidélité×échelle ; loi d'usage des activations ; axe profondeur ; axe J-lens par taille ; couverture de la collection ; 4 exercices C.1. Convention de stub notable : la partie mécanique est **calculée réellement** (étendues, meilleurs/pires) et l'interprétation laissée à l'étudiant (`Interpretation : None`). |
| **Résultat** | Qwen3-1.7B FVU 0.6855 (variance expliquée 31.4 %) vs Qwen3.5-2B FVU 0.2849 (71.5 %) ; par registre : math le mieux reconstruit aux deux échelles, étendue 0.0120 (1.7B) vs 0.0655 (2B) ; axe profondeur et sondes J-lens mesurés ; l'exercice 1 rend honnêtement (« traces frac 0.75 absentes ») ; couverture : 30B/27B/35B **GPU-gated, ni exécutées ni simulées** — dit en toutes lettres. |
| **Critique** | (1) L'axe J-lens (sondes par taille) vit en partie dans des cellules dont la sortie committée est le stub (`J-lens : None` × 4) : la partie mécanique du tableau croisé est réelle, mais la comparaison sondes-vs-SDA des classements attend l'exercice 4 — le titre de section promet « la sonde prédit-elle les logits » alors que la réponse chiffrée n'est pas dans les outputs committés. (2) Aucune rangée matrice dédiée (lignes 107/113 couvrent 21 et JLens, pas 21b) — la calibration alimente la lecture des deux autres sans son propre verdict. |
| **Verdict + action** | **À COMPLÉTER (léger)** — le socle est sain (garde-fous, couverture honnête, stubs bien conçus), mais l'axe J-lens titre une question que les outputs ne répondent pas. Action : exécuter la partie sonde (traces déjà présentes, CPU) ou retitrer la section vers l'exercice. |

### `ICT-21c-SAECatastrophes.ipynb` (numéroté) — 28 cellules (17 md, 11 code, 11/11 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Forme et dynamique des perturbations du dictionnaire : que se passe-t-il quand on détruit (une partie de) le dictionnaire SAE — catastrophes, entropies, inoculation ? |
| **Contenu réel** | Garde-fous ; contrastes trained/control sur 3 échelles (1.7B L14, 2B L12, 9B L16) — features actives, gini, entropies par registre ; cascade d'ablation frac_gardee ∈ {1.0, 0.5, 0.3, 0.2, 0.15} sur le 2B (témoin control_seed=42, mask_seed=42) ; lectures interprétées sous chaque résultat ; 3 exercices C.1 (dont 1 « GPU locale : RTX 3070 suffit pour 2B »). |
| **Résultat** | Trained vs control (3 échelles) : features actives 14966/16636/20786 (trained) vs 8191/6589/6925 (control) ; gini trained 0.847/0.687/0.684 vs control 0.921/0.866/0.873 ; entropies par registre trained 0.27-0.51 vs control 0.74-0.86 — le SAE entraîné active plus de features, moins inégalitairement, plus spécifiquement par registre. Cascade d'ablation : FVU 0.2849 (100 %) → 0.4692 (50 %) → 0.6449 (30 %) → 0.7459 (20 %) → 0.8217 (15 %) tandis que **overlap_diff64 reste 2-3/64 à tous les niveaux** : la signature différentielle survit à la destruction du dictionnaire — « **l'inoculation est absente** » : le signal n'est pas porté par les features conservées. |
| **Critique** | (1) Les chiffres d'ablation 30/20/15 % sont **identiques au millième** à ceux d'ICT-21 (0.6449/0.7459/0.8217) : cohérence inter-notebooks réelle, mais c'est le **même jeu de mesures** partagé, pas une réplique indépendante — à dire pour ne pas créditer deux fois la même preuve. (2) La lecture « contraste d'échelle qui ne concerne que le trained » mériterait son entrée matrice (dissociation scale-dépendante) — pas de rangée dédiée pour 21c non plus. |
| **Verdict + action** | **SOLIDE** — le négatif « inoculation absente » est un résultat propre, mesuré à trois échelles avec témoin. Action d'arbitrage : une rangée matrice 21c (le signal différentiel survit à l'ablation — charge du panneau vs charge du dictionnaire). |

### `ICT-SAE-JLens-TeteATete.ipynb` (non numéroté) — 31 cellules (20 md, 11 code, 11/11 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Confronter les **deux lentilles** du workspace global sur le même modèle (Qwen3.5-9B-Base, couche 16) : features SAE vs jacobien J-Lens — rangée matrice dédiée (ligne 113) sur l'opérateur `W_t` (ligne 17). |
| **Contenu réel** | Garde-fous ; 4 traces pré-extraites (sae/jlens × trained/control), vérification des métadonnées (jacobienne 248320 dims, couche 16) ; **alignement token-à-token vérifié True sur les 20 prompts** ; activation moyenne par jeu + 64 features différentielles par lentille ; lecture qualitative ; comparaison croisée dans l'espace partagé (positions/token) ; séparation des jeux ; ablation contrôle ; **discussion honnête de la divergence sémantique** ; 3 exercices C.1. |
| **Résultat** | Concentration différentielle : SAE trained mean 0.2739 (±0.0567) vs J-Lens trained 0.0526 (±0.0147) ; **Pearson(SAE, J-Lens) trained = +0.0846, control = +0.0164** — les deux lentilles, parfaitement alignées token-à-token, voient des concentrations quasi **non corrélées** ; matrices de séparation : Pearson +0.3273 (faible) ; ablation contrôle mesurée (les deux lentilles se dégradent différemment). La divergence est le livrable assumé : reconstruire le résidu (SAE) et prédire les logits (J-Lens) capturent des propriétés différentes du même workspace. |
| **Critique** | C'est un **non-numéroté porteur de substance** — même pattern que `ICT-Life-SubstratCertifie` au strand 1 : il porte une rangée matrice dédiée (l. 113) sur l'opérateur `W_t`, une discussion de divergence que les numérotés 21/21b/21c n'ont pas, et 31 cellules bien tenu. Le problème #7260 incarné une fois de plus. |
| **Verdict + action** | **SOLIDE, mature**. Action d'arbitrage (#7260) : candidat de tête à la renumérotation — le tête-à-tête est le complément naturel d'ICT-21 (même substrat 9B, l'un sélectionne le panel, l'autre le confronte à la lentille jacobienne). |

### Findings transverses de la tranche 1 (pour l'arbitrage user)

1. **Une famille, un substrat, une discipline** : les quatre notebooks partagent le même appareil (garde-fous d'honnêteté en tête, GPU confiné / banc numpy-only sur traces datées et témoins `control_seed`) — la culture méthodologique relevée aux strands 1, 3 et 4 est ici **institutionnalisée** (c'est la seule sous-famille où le garde-fou est une section titrée dans chaque notebook).
2. **Preuve partagée ≠ preuve répliquée** : l'ablation du dictionnaire (30/20/15 %) porte des chiffres identiques au millième dans ICT-21 et ICT-21c — un seul jeu de mesures cité deux fois. Cohérent, mais l'arbitrage ne doit pas le créditer comme réplication indépendante (le dire une fois, ici).
3. **Le tête-à-tête JLens est le finding d'instrument du strand** : deux lentilles parfaitement alignées token-à-token (vérifié True) voient des concentrations quasi orthogonales (+0.08) — c'est la *divergence sémantique des instruments* démontrée sur le même objet, réponse directe au programme « déclarer ses aveugles » des strands 1/4.
4. **Négatif propre à préserver** : « l'inoculation est absente » (21c) — la signature différentielle survit à l'ablation de 85 % du dictionnaire (overlap 2-3/64 stable, FVU 0.28→0.82). Action proposée : rangée matrice dédiée (le signal vit dans la charge du panneau, pas dans le dictionnaire).
5. **Entrées pour #7260 (renumérotation)** : (a) le non-numéroté tête-à-tête porte une rangée matrice `W_t` et 31 cellules — candidat de tête à numéroter, naturellement adjacent à ICT-21 ; (b) l'ordre 21→21b→21c est correct (substrat → calibration → perturbations) ; (c) ICT-21b est le seul de la famille avec un titre de section (axe J-lens) que ses outputs committés ne répondent pas — complété ou retitré à l'arbitrage.
6. **Tranches restantes du rang 5** : GWT (ICT-22, 22b, 23, 24), puis les non-numérotés restants (Annexe-ProxyContextuality, Argumentation-BeliefTrajectories, Dissociation-PhatSelfReference, Dissociation-SaillancePregnance, Greffe2, Greffe4, Synthese-CrossSubstrat ; Greffe5 après son rework #16762).

## Strand 5 — GWT / SAE + non numérotés (rang 5) — tranche 2 : la famille GWT (Global Workspace)

Lecture complète (contenu ET `outputs`) des quatre notebooks GWT, 2026-09-19, par `myia-po-2023:CoursIA`. La famille reçoit le Gate 12 qu'ICT-21 lui défère explicitement, le moteur d'intervention causal (22b), la fronce de Thom appliquée au désalignement (23) et le gate de réconciliation IIT↔GWT (24). Rangées matrice concernées (ICT-22, ICT-23, ICT-24 Gates 22-23, ICT-24 Gate 24) : **toutes cohérentes avec les outputs committés** — la matrice énonce déjà le négatif de 22 (« intégration cross-substrat effectivement négative ») et la non-co-localisation de 24 comme thèses.

### `ICT-22-LLMSubstrat.ipynb` (numéroté) — 26 cellules (17 md, 9 code, 9/9 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Intégrer le transformer comme quatrième substrat du banc cross-substrat et y créditer l'émergence (Gate 12, double contrôle) puis re-tester la convergence à quatre substrats (Gate 13). |
| **Contenu réel** | Mêmes traces S4 qu'ICT-21 (2699 tokens, W64K, 5 jeux de prompts) ; sélection différentielle ; discrétisation grossière ; Gate 12 par jeu vs shuffle ET vs modèle contrôle ; Gate 13 : tableau des gains des 4 substrats + τ de Kendall par paire ; 3 exercices C.1 ; conclusion. |
| **Résultat** | **Gate 12 : 2/5 jeux crédités** (code_python ec_gain 0.634 ✓, dialogue 1.677 ✓ ; math 0.819 ✗, narrative_en −0.019 ✗, prose_fr −1.066 ✗) ; `fe_gain` positive sur 5/5 (0.226-0.532) ; la différence trained-vs-contrôle **change de signe selon le jeu** (−1.225 à +0.356). **Gate 13 : S4 = le substrat le plus faible** (ec_gain 0.684 vs S1 3.438 / S2 2.097 / S3 2.009) ; τ(ec,fe) = +0.667, τ(ec,k) = +0.000, τ(fe,k) = +0.333 — **consistent = False partout**. La lecture honnête titrée dans le notebook : « **nuancé et majoritairement négatif, et c'est un résultat en soi** ». |
| **Critique** | Aucune : le négatif est livré avec ses deux contrôles, multi-jeux, sans maquillage — et la matrice l'avait déjà énoncé comme tel (« effectivement négative »). La régularité transitionnelle (`fe_gain` 5/5) vs l'émergence causale multi-échelles (2/5) est une dissociation proprement établie à l'intérieur même du notebook. |
| **Verdict + action** | **SOLIDE** — négatif-par-protocole assumé (même famille que le tri des négatifs d'ICT-25, strand 4). Aucune action de contenu. |

### `ICT-22b-CausalInterventionEngine.ipynb` (numéroté) — 41 cellules (27 md, 14 code, 14/14 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Le moteur d'intervention causal : opérer, contrôler, mesurer — sur un banc où la vérité terrain est connue **par construction** (format Gate 24, #5635). |
| **Contenu réel** | Banc synthétique float64 (avec garde de cwd expliquée) où la causalité est un choix expérimental ; 5 opérations sur le panneau d'entrée (canal ÉTAT) ; canaux séparés état/readout/comportement dans un même run ; **contrôles obligatoires** (cible aléatoire APPARIÉE, sham, doses symétriques) ; famille trois bras cible/aléatoire-apparié/intact ; courbe dose-réponse ; interchange contre-factuel par protocole capture-puis-écriture ; **verdict falsifiable à critères fixés AVANT la lecture** ; récapitulatif « sept contrôles, aucun relâché » ; « Portée du verdict : ce que SUPPORTED ne dit pas » ; 3 exercices C.1. |
| **Résultat** | Ablation : sélectivité `selective` (la tranche cible seule bouge) ; famille trois bras : « effet massif et sélectif à la fois » ; dose-réponse « monotone et quasi antisymétrique » ; interchange features causales (3, 17) : **bascule causale OUI + contrôle stable OUI** (pred(a′)=0, pred(b′)=1) ; **VERDICT : SUPPORTED**. |
| **Critique** | Aucune — c'est la discipline instrumentale la plus haute de la série ICT : vérité terrain par construction, sept contrôles nommés un à un, critères de verdict écrits avant la lecture des résultats, portée du verdict explicitement bornée (« ce que SUPPORTED ne dit pas »). C'est l'instrument que les cases matrice 4/5/15 (confabulation, self-model, AST) réutilisent en aval. |
| **Verdict + action** | **SOLIDE, mature** — le référentiel méthodologique de la série. Aucune action. |

### `ICT-23-PersonaCatastrophe.ipynb` (numéroté) — 20 cellules (13 md, 7 code, 7/7 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Modéliser le désalignement émergent par la fronce de Thom : V(p; a, b) avec a = −T·s (transgression × charge sémantique) et b = r (récompense) — prédiction P1 d'#5104 (hystérésis + signature d'inoculation monotone), prédiction P2 (EWS Wissel/Scheffer). |
| **Contenu réel** | Trois jambes explicatives ; paramétrage sémantique du potentiel fronce ; bistabilité par balayage de s ; **Gates 16-17** : boucle d'hystérésis + signature d'inoculation N_catastrophes(s) ; EWS variance + AR1 sur trajectoires SDE bistable vs inoculée ; exercice 1 (potentiel V-linéaire), 2 (balayage continu), 3 (permission vague) ; cellule frontière ; continuité ICT-13 (grim trigger). |
| **Résultat** | Bistabilité : s=0 **False**, s=0.3 **True**, s=1.0 **True** — la charge sémantique ouvre bien le pli. Sweep de charge : **N_catastrophes = 0 / 4 / 2 / 2** pour s = 0 / 0.3 / 0.6 / 0.9. EWS : bistable variance 0.0001 / AR1 0.1391 vs inoculée 0.0000 / 0.1175 — direction conforme, amplitude faible. |
| **Critique** | (1) La signature d'inoculation prédite (cellule §3 : « **monotone non-croissante** : maximale sous forte charge sémantique, nulle sous inoculation totale ») n'est **pas réalisée dans le sweep committé** : le pic est à s=0.3 (4 catastrophes) puis DÉCROÎT (2, 2) — maximale à charge moyenne, pas forte ; seul le point s=0 (inoculation → N=0) tient. Aucune cellule « lecture » ne relit ce sweep (c'est le seul notebook de la famille sans lecture dédiée par résultat). (2) L'écart EWS (AR1 0.139 vs 0.118, +18 %) va dans le bon sens mais n'est pas confronté à un seuil. |
| **Verdict + action** | **SOLIDE sur le cœur** (la fronce modélise le phénomène, l'inoculation aplatit — matrice cohérente) **/ À COMPLÉTER sur la signature P1**. Action d'arbitrage : une cellule lecture du sweep N(s) (non-monotonie assumée ? grain de balayage trop grossier ? effets de taille finie ?) + un seuil sur l'EWS — une demi-heure de travail. |

### `ICT-24-WorkspaceIgnition.ipynb` (numéroté) — 23 cellules (14 md, 9 code, 9/9 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | L'axe Global Workspace sur S4 et le **gate de réconciliation IIT↔GWT** : les ignitions (lecture Dehaene, seuil quantile 0.85, persistance ≥ 3) portent-elles les pics de complexité créditée (emergence_gain, Hoel) ? |
| **Contenu réel** | Garde-fous ; mêmes traces S4 ; sanité sur un panel synthétique où hub et ignition sont **plantés** ; **Gate 22** (structure : fan-out d'influence, 3 variantes trained/control/time-shuffled) ; **Gate 23** (co-localisation ignition×crédit, double contrôle, 5 jeux = multi-graines, n_shuffles=10) ; **Gate 24** (ablation sélective par clamp = phase 2 GPU, explicitement déléguée à une PR distincte) ; note « écart de nommage assumé » sur la numérotation des gates (#56xx) ; 3 exercices C.1. |
| **Résultat** | **Gate 22 : partiel** — fan-out concentré (Gini 0.485-0.659) mais **non spécifique au modèle entraîné** (max fan-out : control 18 > trained 10) ; `concentrated=True` y compris temps mélangés → « seuil trop permissif », auto-diagnostiqué (« déjà marqué empirique faible, à recalibrer, ligne 411 du module »). **Gate 23 : la co-localisation N'A PAS LIEU** — 36 événements, 6 crédités (17 %), contraste moyen **−0.2320** (signe négatif = anti-co-localisation) — c'est la **dissociation IIT↔GWT**, énoncée comme thèse par la matrice. Gate 24 : non exécuté ici (phase 2 GPU), matrice « verdict en attente » — cohérent. |
| **Critique** | Aucune — les trois gates sont livrés avec leur statut exact : partiel auto-diagnostiqué (avec la ligne de code à recalibrer), négatif-thèse confirmée, causal différé explicitement. Le clamp sélectif (Gate 24) reste **la seule mesure interventionnelle** de l'axe workspace : c'est la dette GPU documentée du strand, pas un manque de rigueur. |
| **Verdict + action** | **SOLIDE**. Actions d'arbitrage : (a) exécuter Gate 24 phase 2 (extraction GPU2, déjà cadrée dans le notebook et la matrice) ; (b) recalibrage du seuil Gini ligne 411 (entré aussi par la lecture de Gate 22). |

### Findings transverses de la tranche 2 (pour l'arbitrage user)

1. **La famille GWT livre des négatifs assumés comme résultats** — c'est sa signature : Gate 12 « majoritairement négatif et c'est un résultat en soi » (22), non-co-localisation = la thèse même (24, contraste moyen −0.23), Gate 22 partiel auto-diagnostiqué avec la ligne de code fautive (24). La matrice est **cohérente sur les 5 rangées** (elle avait déjà énoncé le négatif de 22 et la dissociation de 24 comme claims) — rien à crier, contrairement au strand 1.
2. **ICT-22b est le référentiel méthodologique de la série** : vérité terrain par construction, sept contrôles nominés, critères de verdict fixés avant lecture, portée de SUPPORTED bornée — l'instrument que les cases matrice 4/5/15 réutilisent. À préserver tel quel dans toute consolidation.
3. **Un seul point de charge de la famille : ICT-23** — le plus court (20 cellules), sans cellules lecture par résultat, avec une sous-prédiction (signature d'inoculation monotone) **partiellement violée dans le sweep committé** (N = 0/4/2/2, pic à charge moyenne) et non relue dans le notebook. Une cellule lecture + un seuil EWS suffisent.
4. **La chaîne 21→22→24 est tenue au fil des notebooks** : 21 certifie S4 et défère Gate 12 à 22 « en toutes lettres » ; 22 l'exécute et livre le négatif ; 24 prend le relais workspace avec la même primitive `emergence_gain` réutilisée (« la même primitive que le reste de la série »). La continuité SAE→GWT est réelle, pas seulement éditoriale.
5. **Entrées pour #7260 (renumérotation)** : ordre 22→22b→23→24 correct (substrat → moteur causal → fronce → workspace) ; aucun candidat à la fusion ; le Gate 24 phase 2 = dette GPU documentée (déjà tracée matrice), pas un motif de renumérotation ; l'« écart de nommage assumé » des gates (#56xx) est une entrée supplémentaire pour l'ancrage par section plutôt que par numéro (même leçon que le strand 4, renvois décalés).
6. **Tranche 3 restante du rang 5** : les non-numérotés (Annexe-ProxyContextuality, Argumentation-BeliefTrajectories, Dissociation-PhatSelfReference, Dissociation-SaillancePregnance, Greffe2, Greffe4, Synthese-CrossSubstrat ; Greffe5 après son rework #16762).

## Strand 5 — GWT / SAE + non numérotés (rang 5) — tranche 3 : les non numérotés

Lecture complète (contenu ET `outputs`) des sept non-numérotés restants, 2026-09-19, par `myia-po-2023:CoursIA`. **Avec cette tranche, le rang 5 est complet et le ledger couvre 100 % des strands** — toutes les lectures du chemin critique user (arbitrage 19/09) sont consignées. Trois des sept ont une rangée matrice dédiée (SaillancePregnance l. 74, Argumentation l. 110, p̂ auto-référent l. 208) — **toutes cohérentes avec les outputs** ; quatre n'en ont pas (Annexe, Greffe2, Greffe4, Synthese).

### `ICT-Annexe-ProxyContextuality.ipynb` (non numéroté) — 21 cellules (13 md, 8 code, 8/8 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Formaliser la contextualité du zoo de proxys ICT comme un **CSP** (SAT/CP-SAT réel, pas une analogie) : un proxy est contextuel si aucune assignation cohérente ne couvre ses contextes d'usage. |
| **Contenu réel** | Dictionnaire ; **trois crans** démontrés (boîte PR `strongly_contextual` 8/8, logique `logically_contextual` 1/5(9), non contextuel 16/0(16)) ; garde-fou « trois manières d'être vide » ; la mesure appliquée au zoo ICT ; « où l'analogie meurt — quatre points de rupture » ; 3 exercices C.1. |
| **Résultat** | Zoo ICT (seuils = médianes du corpus) : 3 contextes, **1 seul recouvrement distinct**, les 3 proxys (`spectral_gap`, `sensitivity_mean`, `sensitivity_max`) **partagés partout** → `satisfiable: False`... et le CP-SAT tranche : `INFEASIBLE`, verdict **`degenerate_single_cover`** — le zoo n'est **pas contextuel** au sens du CSP. La lecture titrée : « l'écart entre les deux dernières lignes **est** le résultat ». |
| **Critique** | Aucune — négatif outillé : le vrai solveur CP-SAT est appelé (outil SOTA, pas une réimplémentation), le garde-fou distingue les trois façons d'être vide avant de conclure, et la section « où l'analogie meurt » borne elle-même la portée. |
| **Verdict + action** | **SOLIDE**. Pas de rangée matrice — candidate naturelle (dissociation contextuel/non-contextuel du zoo). |

### `ICT-Argumentation-BeliefTrajectories.ipynb` (non numéroté) — 45 cellules (23 md, 22 code, 22/22 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Phase B Argumentum (matrice l. 110) : trajectoire de croyance d'un débat (AF de Dung) et dette d'irréversibilité du discours, avec prédictions pré-enregistrées AVANT tout test. |
| **Contenu réel** | Le plus riche de la tranche : setup ; substrat trajectoire ; **§3 prédictions pré-enregistrées** ; régimes discursifs structurels ; P-disc-1 à P-disc-4 (dont contrôle null à degré conservé) ; **trois spécimens littéraires codés arête par arête** (Loup et l'Agneau, Loup et le Chien — grammaire de l'englobement) ; **témoins Chaplin #7742 pré-enregistrés** ; récapitulatif ; 3 exercices C.1. |
| **Résultat** | P-disc-1 **PARTIEL** (« une seule dimension tient : K ») ; P-disc-2 **PASS** (le spectre laplacien distingue les régimes) ; P-disc-3 **PARTIEL** (le régime populiste épuise la diversité) ; P-disc-4 contrôle **PARTIEL** (une dimension persiste vs null, l'autre expliquée par le degré). Témoins : barbier **0 extinction observée = 0 attendue** (« l'instrument sur sa première lame où l'échec était possible ») ; Hynkel **REFUS: CANAUX_CONTRADICTOIRES** — « refus ≠ zéro : le premier lève une exception codée, le second est un résultat ». |
| **Critique** | Aucune majeure. Le geste « refus codé ≠ résultat nul » est une distinction méthodologique rare et précieuse (un instrument qui sait dire *je ne peux pas mesurer ça*). Les PARTIEL sont comptés comme PARTIEL, pas arrondis vers le haut. |
| **Verdict + action** | **SOLIDE, mature** — candidat de tête #7260 avec la Synthese. |

### `ICT-Dissociation-PhatSelfReference.ipynb` (non numéroté) — 30 cellules (19 md, 11 code, 11/11 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Case 2 / Epic #9533 : la boucle auto-référentielle `p_hat → action → p_hat` diverge-t-elle là où le délieur causal reste borné ? (rangée matrice l. 208.) |
| **Contenu réel** | Sanity check (2 régimes, **39 ordres de grandeur d'écart**) ; mécanique de la boucle ; 4 substrats (scan de stabilité κ, délieur causal vs bouclée 5 graines, frontière observée vs prédite, sensibilité à l'horizon T) ; verdict honnête à 2 niveaux ; **verdict agrégé 5 graines** ; crédit témoin Hofstadter (grade C) ; 3 exercices C.1. |
| **Résultat** | Frontière observée **κ_c = 0.080** vs prédite ≈ 0.053 — biais **+0.027 dans la tolérance pré-enregistrée** ; dissociation bouclée/délieur True ; sensibilité à T = preuve de non-trivialité ; **VERDICT : CONFIRMED** (5/5 graines, protocole complet). |
| **Critique** | Aucune. La matrice (l. 208, TESTÉ CONFIRMÉ, mêmes chiffres κ 0.080 / biais +0.027 / 5 graines) est **exactement** ce que les outputs portent — cohérence parfaite rangée↔notebook. |
| **Verdict + action** | **SOLIDE, mature**. Aucune action. |

### `ICT-Dissociation-SaillancePregnance.ipynb` (non numéroté) — 35 cellules (22 md, 13 code, 13/13 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Case `s ⟂ π` (matrice l. 74) : saillance (être vu) ≠ prégnance (compter pour agir) — prédiction falsifiée au niveau engagement total, sauvée au niveau décision. |
| **Contenu réel** | Batterie de stimuli **décorrélation par construction** (corr(s, λ) = −0.216 ≈ 0) ; apprentissage Rescorla-Wagner (V apprend λ, pas s) ; deux animats (valence cible vs réactif null adversarial) ; mesure à 2 niveaux (engagement total vs décision|détection) ; corrélation partielle Spearman avec démonstration FWL ; null adversarial « inversion miroir » ; **robustesse multi-seed ≥ 4** ; **analyse de puissance** (Prong B SOTA, #3801) ; 3 exercices C.1. |
| **Résultat** | **VERDICT : DISSOCIATED-AT-DECISION** (« une falsification qui localise, pas qui invalide ») ; multi-seed : 4 verdicts dont 1 affaibli (`DISSOCIATED-DECISION-NULL-WEAK`), **aucun renversement** ; puissance : ≥ 120 stimuli suffisent à résoudre la dissociation décision sur toute seed ; le null réactif inverse le motif (« sans apprentissage de la valence, la saillance reprend le contrôle de la décision »). |
| **Critique** | Aucune — c'est le modèle du « verdict à deux niveaux » : le niveau où la prédiction meurt est nommé, le niveau où elle tient est mesuré, et l'analyse de puissance chiffre le prix statistique de la dissociation (la non-trivialité Prong B exigée par #3801 est satisfaite par construction). |
| **Verdict + action** | **SOLIDE, mature**. Aucune action. |

### `ICT-Greffe2-EspaceAtteignable.ipynb` (non numéroté) — 32 cellules (21 md, 11 code, 11/11 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Le quadruplet (A, F, r, π) : rendre « élargir son espace » **testable** (critères #13568) — la greffe ICT sur le bras planification. |
| **Contenu réel** | Socle STRIPS **« copie de Planners-5c », garanties du lake non re-dérivées** (la sortie organ-first #16778 utilisée à la lettre : la copie est déclarée, l'organe natif nommé) ; domaine deux rives/gouffre/radeau ; A différentiel système ; **contrôle négatif de la primitive stérile** ; F et r à budget ; le noyau (ce que la primitive rend inatteignable) ; cas 3 navigation (bras Planners-10b) ; synthèse ; limites ; 3 exercices C.1. |
| **Résultat** | A_t : 54 états, **1/3 buts** → +raft : 60 états, **3/3 buts** → +discard : 78 états (Δ|A| décore, **Δ(buts) discrimine**) ; l'élargissement non contrôlé **contracte** la liberté résiduelle ; noyau non vide à budget fixe ; cas 3 : trois politiques π, **A et F inchangés par construction**, h* inchangé (39/33/8) — seul π bouge, l'espace ne triche pas. |
| **Critique** | Aucune — les 4 critères de #13568 sont démontrés un à un avec leur contrôle, et la déclaration de copie pédagogique du socle STRIPS est exactement le pattern que la règle organ-first (merge #16778) exige. |
| **Verdict + action** | **SOLIDE**. Pas de rangée matrice — candidate (élargissement utile vs contractant). |

### `ICT-Greffe4-VoteOnChain.ipynb` (non numéroté) — 27 cellules (17 md, 10 code, 10/10 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Fermer la boucle Argumentation → Choix social → SmartContracts : le vote argumenté exécuté et audité **sur chaîne** (critères #13570). |
| **Contenu réel** | Trois organes nommés avec ce que chacun apporte ; AF de Dung sur 3 propositions (positions issues du graphe) ; règle Borda **nommée et justifiée** ; la manipulation (bulletin contredisant sa position) ; exécution SC-13 : **tests forge** + **fuzzing des invariants** ; « ce que la chaîne ajoute — et ce qu'elle ne résout pas » ; 3 exercices C.1. |
| **Résultat** | Manipulation : sincere C1 gagne → vote-balle de V3 : **C0 gagne (écart strict 8-7-6)** (« enterrage, vote-balle, et le mensonge épistémique ») ; forge : **5 tests passed, 0 failed** (gas rapporté, ex. 13046) ; fuzzer BrokenInvariants : **1 failing décodé** — le contre-exemple est lu et interprété (« la borne tient sous attaque aléatoire »), pas masqué. |
| **Critique** | Aucune — la chaîne est **réellement exécutée** (forge test + fuzz), le contre-exemple du fuzzer est décodé comme donnée pédagogique, et la section finale borne honnêtement ce que la chaîne ne résout pas. |
| **Verdict + action** | **SOLIDE**. Pas de rangée matrice — candidate (la manipulation bascule l'issue, l'audit tient). |

### `ICT-Synthese-CrossSubstrat.ipynb` (non numéroté) — 40 cellules (26 md, 14 code, 14/14 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | **Le capstone** : un seul appareil de mesure, trois (puis quatre) substrats, six gates qui rejouent le fil ENTIER de la série — et un « verdict sans complaisance ». |
| **Contenu réel** | Tableau récapitulatif du fil ; S1 tri / S2 bistable / S3 réplicateur mesurés au même appareil ; **Gate 1** (émergence vs contrôle dégénéré, 100 shuffles) ; **Gate 2** (transfert du scalaire d'intégration) ; **Gate 3** (robustesse au régime, 5 graines) ; **Gate 4** (la convergence Φ/F/K survit-elle au 4ᵉ substrat — capstone strate 5) ; **Gate 5** (irréversibilité, jambe ICT-18) ; **Gate 6** (enjeu, jambe ICT-19) ; verdict sans complaisance ; 3 exercices C.1. |
| **Résultat** | Gate 1 : **3/3 substrats créditent** (z > 1 ; gains EC +1.0 à +2.7). Gate 2 : τ(EI, EC_gain) = −0.333 (consistent **False**) mais τ(EI, EC_réel) = **+1.000 True** — le scalaire transfère sur la grandeur réelle, pas sur le gain. Gate 3 : la graine 99 **échoue** (−0.33, False) — τ observés [−0.33, 0.33, 1.0], la robustesse au régime est **partielle et dite telle**. Gate 4 : τ(ec, fe) = +1.000 **CONSISTENT**, k divergent. Gate 5 : S2 0.0000, S3 0.0196/0.0205, **S4 0.0889/1.1774**. Gate 6 : stake_index crédite S1 +1.00, S2 +1.00, S3 +0.68 « **MAIS il ÉCHOUE sur le substrat champ Gray-Scott (I_stake = −0.51 = sous le drift)** ». |
| **Critique** | Aucune — c'est le livre de compte de la série : chaque gate cite son origine (ICT-15, ICT-18, ICT-19), les échecs (graine 99, champ Gray-Scott) sont affichés en clair, et l'échec Gate 6 sur champ rejoint **exactement** l'artefact d'instrument documenté par ICT-19b (le scalaire sur champ 2D) — la synthèse confirme le strand 3 indépendamment. |
| **Verdict + action** | **SOLIDE, mature — le fil de la série**. Action d'arbitrage (#7260) : candidat de tête à la renumérotation (le capstone mérite un numéro, pas un statut d'annexe). |

### Findings transverses de la tranche 3 (pour l'arbitrage user)

1. **Les non-numérotés portent la profondeur de la série** — le pattern du strand 1 (Life-SubstratCertifie) est la règle, pas l'exception : les deux plus gros notebooks de la tranche (Argumentation 45 cellules, Synthese 40) sont non numérotés, et la Synthese est littéralement le capstone (Gates 1-6 rejouant toute la série). Entrée majeure #7260 : **Synthese et Argumentation en tête des candidats à la renumérotation**, avec le tête-à-tête JLens (tranche 1).
2. **La négativité assumée reste la culture dominante** : zoo non contextuel (Annexe, CP-SAT INFEASIBLE sur le vrai solveur), graine 99 qui échoue (Synthese Gate 3), stake_index qui échoue sur champ (Synthese Gate 6 — confirmation indépendante de l'artefact d'ICT-19b relevé au strand 3), refus codé ≠ résultat nul (Argumentation Hynkel).
3. **Greffe2 est l'exemplaire organ-first** (#16778) : le socle STRIPS est déclaré « copie de Planners-5c » avec les garanties du lake non re-dérivées — exactement la sortie « copie pédagogique déclarée » que la règle exige. Greffe4 exécute la vraie chaîne (forge 5/5 + fuzzer décodé).
4. **Matrice : 3 rangées dédiées, toutes cohérentes** (SaillancePregnance, Argumentation, p̂ — cette dernière au chiffre près : κ 0.080 / biais +0.027 / 5 graines) ; **4 notebooks sans rangée** (Annexe, Greffe2, Greffe4, Synthese) — la Synthese re-mesure le banc des rangées existantes plutôt que de claimer la sienne ; trois candidats d'ajout mineurs (contextualité du zoo, élargissement contractant, manipulation basculante).
5. **Entrées #7260 complètes pour le rang 5** : renumeroter en priorité Synthese + Argumentation + JLens ; statuer le régime des Dissociations/Greffes/Annexe (noms fonctionnels stables vs numérotation — leur nature annexale est assumée dans les titres) ; Greffe5 reste post-rework (#16762).
6. **Le ledger est COMPLET** : rangs 1-4 + rang 5 en 3 tranches = tous les strands du chemin critique user (arbitrage 19/09) consignés. Les inputs d'arbitrage sont prêts : chaque strand porte ses findings transverses, le tableau d'avancement est fermé.
