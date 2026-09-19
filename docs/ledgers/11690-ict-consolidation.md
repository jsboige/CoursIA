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
| 2 | Le moule 26→30 | cinq notebooks (26-30), 8 code chacun, 18-25 cellules | **LU** (strand 2, 2026-09-19) |
| 3 | 18 / 18b / 19 / 19b | asymétrie qui s'inverse entre paires | non démarré |
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

## Strand 2 — Le moule 26→30 (rang 2)

Lecture complète (contenu ET `outputs`) des cinq notebooks, 2026-09-19, par `myia-po-2023:CoursIA`. Correction factuelle d'entrée : la table annonçait « six notebooks ~17 cellules » — le disque en porte **cinq** (`ICT-26` à `ICT-30`, 18-25 cellules chacun). Le moule réel = **8 cellules code par notebook, 8/8 exécutées partout**, sur un squelette constant : 4 sections d'expérience (chacune verdict multi-graines + lecture) → synthèse → 3 exercices stubs C.1. Les cinq rangées matrice correspondantes (lignes 173-177) disent « **Fortement soutenu** » — la lecture le **confirme sur les outputs committés, aucune contradiction à crier**.

### `ICT-26-SignalingConvention.ipynb` (numéroté) — 22 cellules (14 md, 8 code, 8/8 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Expérience A, strate 7 (Lewis/Skyrms) : une convention de signalisation **émerge** par RL sans signification pré-inscrite — et ses limites. |
| **Contenu réel** | 4 sections : §1 émergence multi-graines ; §2 le goulot du vocabulaire FIXE ; §3 succès ≠ signification (contrôle à état dominant) ; §4 stabilité sous chocs ; synthèse ; 3 exercices C.1. Module `ict.signaling_convention` importé en direct. |
| **Résultat** | Émergence **4/5 graines** ; goulot **5/5** (le verdict le plus robuste du notebook) : MI plein vocabulaire 1.861 ± 0.297 vs limité 0.483 ± 0.017, ratio 0.266 ± 0.053 (plafonds analytiques log2(4)=2 / log2(2)=1) ; signification **5/5** avec la nuance affichée — le contrôle à état dominant réussit (succès ≈ 1.000) avec MI basse (0.627-1.145), et la graine 7 est la seule non-convergence totale (0.714 / 1.233) ; stabilité **4/5** : choc modéré résisté avec récupération, choc brutal détruit la convention. |
| **Critique** | (1) §1 et §4 partagent leur graine manquante (« même racine », dit le titre lui-même) — redondance documentée, pas cachée. (2) La nuance graine 7 (§3) est mesurée mais pas discutée : pourquoi cette graine cale-t-elle à 0.714 alors que les autres atteignent 1.000 ? Une phrase de lecture suffirait. |
| **Verdict + action** | **SOLIDE**. Le goulot 5/5 est la motivation écrite d'ICT-27 — la chaîne A→B est explicite. Action d'arbitrage (mineure) : une phrase de lecture sur la graine 7 en §3. |

### `ICT-27-SymbolInvention.ipynb` (numéroté) — 18 cellules (10 md, 8 code, 8/8 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Expérience B : lever le goulot d'ICT-26 — le vocabulaire **s'invente** et croît jusqu'à suffire, ni en-deçà ni au-delà, sous coût d'invention. |
| **Contenu réel** | 4 sections : §1 baseline figée (invention interdite) ; §2 verdict CROISSANCE ; §3 verdict COUT (gate de rentabilité) ; §4 verdict DIVERSITÉ ; synthèse ; 3 exercices C.1 (plafond explicite, asymétrie des états, invention ciblée). |
| **Résultat** | Baseline figée : succès **0.256 ≈ plafond théorique 1/4 = 0.250** (« aucun renforcement ne lève le plafond : le goulot est structurel ») ; CROISSANCE : vocabulaire final **[3, 4, 5, 6] pour attendu [3, 4, 5, 6]** — inventé à la mesure exacte du problème ; COUT : [6, 6, 6, 5.75, 4.25] — l'invention ralentit quand elle coûte, sans s'effondrer ; DIVERSITÉ : **5/6 conventions distinctes**, chacune une bijection de [0..3], parmi 24 valides (4!) — la graine sélectionne, elle n'impose pas. |
| **Critique** | Aucune majeure. Le plus dense du moule (18 cellules) et le seul où chaque section porte un verdict quantitatif à guichet fermé (attendu affiché avant la mesure). La réponse chiffrée au goulot d'ICT-26 (0.266 → [3,4,5,6]) est la chaîne la plus propre de la strate. |
| **Verdict + action** | **SOLIDE, mature**. Aucune action de contenu. |

### `ICT-28-CollectiveAdoption.ipynb` (numéroté) — 25 cellules (17 md, 8 code, 8/8 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Expérience C : la convention devient **causale** au niveau population — cascade d'adoption au-delà d'un seuil `rho_c` d'instigateurs épinglés (seuil de bascule C4, #7743). |
| **Contenu réel** | 4 sections + lectures chiffrées : §1 la courbe en S ; §2 sous le seuil la convention meurt ; §3 au-dessus, la cascade ; §4 contrôle négatif sans instigateur ; synthèse ; 3 exercices C.1 dont un sweep N (taille de population) et un sweep force d'engagement. |
| **Résultat** | Seuil : `threshold_exists = True`, **rho_c = 0.425**, saut maximal 0.472, adoption 0.000 @rho=0.05 → 1.000 @rho=0.95 ; sous le seuil : 0.011 (contre 0.333 au hasard — elle meurt) ; au-dessus : **0.850** ; contrôle négatif : **0.000 sans instigateur** (jamais de cascade spontanée). Exercice sweep N : rho_c = 0.300 (N=12), **0.575 (N=24)**, 0.425 (N=48) ; sweep force : 0.333 (s=2) puis plateau 0.556 (s=5/10/20). |
| **Critique** | (1) Le sweep N (exercice 1) montre un rho_c **non-monotone en taille de population** (0.300 → 0.575 → 0.425) — mesuré, affiché, mais sans phrase de lecture : effets de taille finie ? variance ? C'est le seul verdict du moule qui ne se stabilise pas et il vit dans un exercice. (2) Le plateau de force d'engagement (0.556 dès s=5) mérite sa phrase : l'engagement sature, il ne remplace pas la masse. |
| **Verdict + action** | **SOLIDE** (les 4 gates + contrôle négatif sont au niveau). Action d'arbitrage (mineure) : phrase de lecture sur la non-monotonie du sweep N — soit l'expliquer, soit la marquer comme variation de taille finie assumée. |

### `ICT-29-ConceptInoculation.ipynb` (numéroté) — 25 cellules (17 md, 8 code, 8/8 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Expérience D (Sperber 1996, contagion culturelle) : un concept transmis de proche en proche **survit** au retrait de l'instigateur — la distinction clé vs ICT-28, dont la convention s'effondre sans source. |
| **Contenu réel** | 4 sections à double étage (expérience + « lecture du verdict avec son chiffre » 1b/2a/3a) : transmission au-delà des graines ; biais de confirmation ; survie post-instigateur ; contrôle négatif sans transmission ; synthèse ; 3 exercices C.1 **avec caveats mesurés pré-écrits** (5a saturation de la transition de phase, 5b la baseline du stub mesure une adoption toutes précoces, 5c l'assortativité dégénère à saturation). |
| **Résultat** | Transmission réelle mais **partielle** (le concept dépasse les graines) ; biais de confirmation : fraction finale 1.000 (bias=0) → **0.335** (bias=0.9) — un frein, pas une extinction ; survie post-instigateur : 1.000 (persistant) → **0.725** (retiré), déclin mesuré 0.275 — endémie réelle mais érodée ; contrôle : **0.0 converti au-delà de la graine** sans transmission. |
| **Critique** | Aucune. Le double étage (verdict + lecture chiffrée sous chaque section) est le meilleur format de lecture du moule — et les exercices portent leurs propres caveats MESURÉS (5a/5b/5c) au lieu d'un énoncé naïf : culture méthodologique exemplaire, même geste que ICT-31/ICT-25 (strand 1/4). |
| **Verdict + action** | **SOLIDE, mature**. Candidat de référence pour le format « verdict + lecture chiffrée » si le user veut l'étendre au reste de la série (arbitrage). |

### `ICT-30-InhibitedInvention.ipynb` (numéroté) — 22 cellules (14 md, 8 code, 8/8 exécutées)

| Colonne | Contenu |
|---|---|
| **Intention** | Expérience E (pont Laborit C2, #7741) : l'agent qui **peut** inventer mais **inhibe** cette extension exhibe une dette mesurable — l'inhibition comme mécanisme négatif distinct de l'incapacité. |
| **Contenu réel** | 4 sections : §1 rigidification (l'inhibition fige le vocabulaire) ; §2 impuissance apprise (plafond et piège) ; §3 le piège est permanent (pas un manque de calcul) ; §4 contrôle négatif sans inhibition ; synthèse ; 3 exercices C.1 dont sweeps decay et growth (dose-réponse). |
| **Résultat** | Rigidification : vocabulaire 4.00 (inhibition 0) → **1.00** (inhibition max) ; impuissance apprise : inhibition **1.000 au plafond de renoncement**, vocabulaire final 2.00 (sous-optimal vs n_states=4) ; piège **STRUCTUREL** : persiste sous budget de calcul accru (l'inhibition supprime le mécanisme de sortie) ; contrôle : sans inhibition vocabulaire **4.00 = n_states** et coordination 1.000 — c'est bien l'inhibition qui piège. Exercices dose-réponse propres : decay 0.000→2.00, 0.030→4.00 ; growth 0.010→4.00, 0.060→2.00. |
| **Critique** | Aucune. Le contrôle négatif (§4) est exactement le monde d'ICT-26/27 sans inhibition — la réponse croisée est au chiffre (4.00 vs le 1 signal figé de 27 §1). |
| **Verdict + action** | **SOLIDE, mature**. Aucune action de contenu. |

### Findings transverses du strand 2 (pour l'arbitrage user)

1. **Le moule est réel, tenu et homogène** — la série la plus propre du ledger : 5 notebooks, même squelette (4 sections d'expérience + synthèse + 3 exercices C.1), même batterie `ict.*`, **8/8 cellules exécutées partout**, chaque notebook porte ses gates multi-graines + son contrôle négatif + ses sweeps en exercice. Aucune action de contenu majeure sur le strand : trois phrases de lecture mineures (26 graine 7, 28 sweep N, 28 plateau force) constituent tout le résiduel.
2. **L'arc narratif A→E est chaîné explicitement ET au chiffre** : A mesure le goulot du vocabulaire fixe (ratio MI 0.266) → B le lève par invention ([3,4,5,6] = attendu exact) → C fait passer la convention à la population (rho_c = 0.425, s'effondre sans instigateur : 0.011) → D inocule le concept qui SURVIT au retrait (0.725) — la distinction C/D est le point Sperber et elle est démontrée par contraste des deux contrôles → E montre le revers individuel (l'inhibition piège : 2.00 vs 4.00). Les renvois inter-notebooks sont écrits dans les prose, pas seulement dans la matrice.
3. **Cohérence matrice ↔ outputs vérifiée sur les cinq rangées** (173-177) : « Fortement soutenu » correspond aux verdicts mesurés — contrairement au strand 1 (15d, matrice périmée à deux endroits), rien à crier ici. La mise à jour matrice de 15d reste le seul finding matrice ouvert.
4. **Format gagnant identifié pour la série** : ICT-29 (verdict + « lecture du verdict avec son chiffre » sous chaque section + caveats mesurés pré-écrits dans les exercices) est le meilleur format de lecture du strand — candidat de référence si le user veut harmoniser le style des strates (arbitrage, pas une action de lane).
5. **Entrées pour #7260 (renumérotation)** : l'ordre 26→27→28→29→30 est porteur de sens narratif (individu → invention → population → culture → pathologie), à préserver tel quel ; aucun candidat à la fusion ni à la renumérotation dans le strand ; les cinq sont numérotés proprement.

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
