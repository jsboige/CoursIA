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
| 3 | 18 / 18b / 19 / 19b | asymétrie qui s'inverse entre paires | **LU** (strand 3, 2026-09-19) |
| 4 | ICT-25 | tri des négatifs, désordre de sections établi | **LU** (tranche 1, 2026-08-24) |
| 5 | GWT / SAE + non numérotés | alimente #7260 (renumérotation) | non démarré |

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

## Strand 3 — 18 / 18b / 19 / 19b (rang 3)

Lecture complète (contenu ET `outputs`) des quatre notebooks, 2026-09-19, par `myia-po-2023:CoursIA`. Le strand porte l'hypothèse « asymétrie qui s'inverse entre paires » : la lecture la vérifie sur **deux axes** (rôle du principal dans chaque paire ; statut des substrats S2/S4 entre paires).

### `ICT-18-ArrowOfTimeReversibilization.ipynb` (numéroté) — 33 cellules (19 md, 14 code, 14/14 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Strate 5, Epic #4588 : forcer une trajectoire ICT à devenir réversible pour **mesurer** sa production d'entropie (σ de Schnakenberg), sur 5 substrats dont un contrôle faux-positif dédié. |
| **Contenu réel** | 9 sections : primitives (gate 1 detailed balance) ; S1 tri auto-organisé (ICT-2, « *competency for free* ») ; S2 bistable May (ICT-8) ; S3 Axelrod (ICT-13) ; S4 Gray-Scott (ICT-9) ; **S5 contrôle faux-positif** (S5a marche linéaire vs S5b oscillateur pilote) ; visualisation comparative ; 3 exemples guidés + 3 exercices (C.1, stubs propres). |
| **Résultat** | Sorties committées : Gate 1 OK (dist real↔reversibilized 0.0263, real↔reversed 0.0526) ; S1 Gate 3 **OK** (ratio σ/iid = 150.57) ; **S2 Gate 4 : KO** (ratio 0.00, dist 0.0000) ; S3 Gate 5 **AMBIGU** (coopération émergente, dist 14.0149) ; S4 Gate 6 **OK** (ratio 4285.72) ; Gate 7 **FAUX-POSITIF CONFIRMÉ** (S5b σ=4.6227 allume l'indice, S5a σ=0.0014 non). |
| **Critique** | (1) Le KO de S2 n'est **pas relié** au PASS de 18b P1 sur le même substrat : un lecteur de 18 seul retient « le bistable n'a pas de flèche », verdict que 18b nuance (le budget s'épuise au pli). Le pont n'est écrit nulle part. (2) Le Gate 5 AMBIGU assume son ambigüité mais sans renvoi vers la dette P3 de 18b qui donne au S3 sa lecture culturelle. |
| **Verdict + action** | **SOLIDE** — l'instrument discriminate ET attrape son propre faux-positif (S5b) : c'est la culture méthodologique saine relevée au strand 1. Action d'arbitrage : un pont d'une phrase 18↔18b sur S2 (le KO du Gate 4 et le PASS P1 mesurent deux choses différentes — la flèche vs l'épuisement au pli). |

### `ICT-18b-ReversibilityBudget.ipynb` (numéroté) — 25 cellules (17 md, 8 code, 8/8 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | La jambe « fin » de la réversibilisation : définir un budget B(t) et pré-enregistrer trois prédictions (P1/P2/P3) AVANT tout test (§3 explicite). |
| **Contenu réel** | §2 définitions (`B_state` primaire, `B_work` témoin) ; §3 pré-enregistrement ; P1 sur S2 au pli ; P2 sur S4 σ vs B_state ; P3 sur S3 monoculture Axelrod ; récapitulatif des verdicts ; 3 exercices (C.1). |
| **Résultat** | P1 **PASS** (tau_Kendall(c,budget) = −0.917, p=0.001, co-varie avec les EWS d'ICT-8 ; témoin `B_work` = 0.0000 sur chaîne réversible) ; P2 **DISSOCIATION** (dissipateur σ=0.0909, B_state=0.950 — dissiper plus ne régénère pas plus : « cadre ressource affaibli sur S4 ») ; P3 **PASS** (monoculture = état absorbant, dette d'irréversibilité culturelle mesurée). Matrice : les trois rangées **Établi**. |
| **Critique** | Aucune majeure. Le pré-enregistrement §3 est exemplaire (le même geste que ICT-25 §5★). P2 porte le verdict de dissociation moyen/fin que la matrice cite mot pour mot. |
| **Verdict + action** | **SOLIDE, mature**. Aucune action de contenu — candidat tel quel pour la consolidation finale de la paire. |

### `ICT-19-EnjeuBattery.ipynb` (numéroté) — 33 cellules (22 md, 11 code, 11/11 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | La triade *moyen / fin / enjeu* : pourquoi ICT-18 ne suffit pas (§1 explicite) — introduire `I_stake` (récupérabilité Levin) distinct du moyen `I_thermo` (σ), jamais agrégés. |
| **Contenu réel** | Théorie ; smoke test discriminant ; application S2/S4/S5 avec Lectures 1-4 ; paire (I_thermo, I_stake) ; gates falsifiables ENJEU-1/2 ; 3 exercices stubs C.1 (S1/S3 renvoyés aux exercices). |
| **Résultat** | Smoke test : I_stake(marche biaisée) = −1.0000, Δ = +1.9894 (la batterie discrimine) ; S2 revient à 0.9999 (Lecture 2) ; **Gate ENJEU-1 : FAIL** (I_stake(S4) = −0.5083 vs I_stake(S5) = −0.4651, delta −0.0431 — indiscernables, alors que I_thermo(S4) = +5.6249 vs 0.0000) ; **Gate ENJEU-2 : FAIL**. Verdict nul assumé (« un verdict nul honnête », Lecture 6). |
| **Critique** | Le verdict nul est un **artefact d'instrument démontré par 19b** : `stake_index` scalaire appliqué à un champ 2D. Le notebook l'affiche comme FAIL sans le drapeau « instrument-mismatch » — l'annexe de 19b le documente rétroactivement, mais le lecteur de 19 seul retient « gates FAIL ». C'est le défaut de charge du strand : le principal porte le négatif, le raffinement porte la preuve. |
| **Verdict + action** | **STRUCTURELLEMENT SAIN, localement PÉRIMÉ PAR CONSTRUCTION**. Action d'arbitrage (unique, documentée par 19b §13 « incrément de consolidation ultérieur ») : ré-exprimer le Gate ENJEU-1 sur l'instrument de champ (`repair_gain`) pour la ligne S4, en gardant le FAIL scalaire comme note pédagogique d'instrument. Rien d'autre à toucher. |

### `ICT-19b-EnjeuBattery-Raffinement.ipynb` (numéroté) — 24 cellules (15 md, 9 code, 9/9 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Tranche 3 : raffiner (§8 `repair_gain` champ, `time_to_recover`), résoudre les stubs S1/S3 de 19, calibrer sur substrat-jouet, réconcilier les tranches 2 et 3. |
| **Contenu réel** | §8 deux observables + exercices ; §9-§11 résolutions S1/S3/custom ; §12 verdict final avec **récapitulatif de l'enjeu mesuré** (tableau à valeurs) ; §13 annexe limites et suites (rédigée en « résolu / limites restantes / suites »). |
| **Résultat** | S1 stake_index **+1.0000** ; S3 **+0.6780** (ESS asymptotique oscillante) ; S4 `repair_gain` champ **+0.82 ± 0.27**, reconstruction locale 313–489 pas ; Custom A (ressort+bruit) **+0.9940** vs Custom B (marche biaisée ≈S5) **−1.0000**. Le verdict nul de 19 est **réparé** : artefact d'instrument (scalaire sur champ 2D) + câblage (`ablated` vs champ relaxé) + régime de Pearson (F=0.0367, k=0.0649, n=64). |
| **Critique** | Les exercices 1–3 restent à compléter (C.1, stubs propres — conforme). La note d'instrument du §12 (S4 mesuré en espace de champ, pas scalaire) est exactement le drapeau qui manque au gate de 19. |
| **Verdict + action** | **SOLIDE** — c'est le réparateur du strand. Action : aucune propre ; porte la correction à reporter sur 19 (cf. ci-dessus). |

### Findings transverses du strand 3 (pour l'arbitrage user)

1. **L'asymétrie s'inverse, vérifiée sur deux axes.** Axe rôle : dans la paire 18/18b le **principal porte la démonstration** (gates discriminants + faux-positif attrapé) et le `-b` affine (3/3 verdicts) ; dans la paire 19/19b le **principal porte le verdict nul** et le `-b` porte la preuve (gate réparé par changement d'instrument). Axe substrat : **S2 est KO dans 18 (pas de flèche) mais PASS dans 18b** (budget épuisé au pli) ; **S4 est OK dans 18 (σ×4285) mais dissocié dans 18b** (dissiper ≠ régénérer). Ces croisements ne sont pas des contradictions : ils SONT la thèse moyen/fin — mais aucun des quatre notebooks n'écrit le croisement, chacun ne voit que sa paire.
2. **Un seul point de consolidation de contenu** (le reste est sain) : le Gate ENJEU-1 d'ICT-19 exprimé sur le mauvais instrument pour S4, FAIL affiché, alors que 19b démontre l'artefact et documente lui-même la correction comme « incrément de consolidation ultérieur ». Chirurgie d'une cellule, pas une refonte.
3. **Contrôles négatifs : trois témoins, zéro redondance.** S5a/S5b (18, faux-positif), S5 (19), Custom B (19b, ≈S5) : chaque notebook porte son propre témoin, calibrated à son instrument — à préserver tel quel dans toute consolidation.
4. **Entrées pour #7260 (renumérotation)** : l'ordre 18→18b→19→19b est pédagogiquement correct (instrument → fin → enjeu → réparation) ; aucun notebook du strand n'est candidat à la fusion — 19 et 19b restent distincts par conception (verdict nul pédagogique vs réparation), mais leur **artificial split de charge** justifie que 19b soit lu immédiatement après 19 dans toute navigation.

---


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
