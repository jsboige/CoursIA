# Pré-enregistrement — Kastrup, dissociation cosmique (case 18 : alters privés ⟂ environnement commun)

> **Grade C explicite.** Ce document **scelle** le protocole de la tranche Kastrup de la veille [#8182](https://github.com/jsboige/CoursIA/issues/8182) (TOE ↔ conscience, carrefour Jaimungal — iceberg L5, « Kastrup (idéalisme analytique) », dernier candidat fort non servi : Vervaeke/Emilsson/Hofstadter/Metzinger/Graziano ont chacun leur tranche) **AVANT toute écriture du banc de mesure** — héritage des tranches Owen/Cruse ([#13426](https://github.com/jsboige/CoursIA/pull/13426)), Schurger ([#13459](https://github.com/jsboige/CoursIA/pull/13459)) et de la famille des cases 14-17 : source primaire lue et archivée, pré-enregistrement commité avant l'implémentation et la mesure, verdict borné. Le banc (`ict/kastrup_dissociation.py`) vient dans un commit fils — la relation de parenté des commits porte l'antériorité (leçon case 8c).
>
> **Cycle du 2026-09-29**, lane `myia-po-2024:CoursIA`. Claim : `[CLAIMED]` sur [#8182](https://github.com/jsboige/CoursIA/issues/8182), paths scoping les cinq fichiers de la tranche.

## 1. Source primaire et archivage

**Source** : Bernardo Kastrup, *Analytic Idealism: A consciousness-only ontology*, doctoral dissertation, Radboud University Nijmegen, 2019. Open access via PhilArchive ([KASAIA-3](https://philarchive.org/archive/KASAIA-3)). Le chapitre 3 (« The Universe in Consciousness ») porte l'argument de dissociation testé ici.

**Archivage gisement** ([bibliography-hygiene](../../.claude/rules/bibliography-hygiene.md)) : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\2019 - Kastrup - Analytic Idealism - thesis OA.pdf` — 3 296 268 octets, SHA256 `63ED6581…`, identité vérifiée sur la première page (auteur, titre, « Doctoral Dissertation Radboud University Nijmegen », « Processed on 18-2-2019 »), recherche par auteur ET titre avant dépôt (aucun Kastrup préexistant au rayon), une seule copie au rayon `Consciousness`.

**Méthode de lecture** : texte intégral extrait (148 pages, pypdf) et lu en sessions ciblées sur les sections porteuses (§3.2 résumé de l'ontologie, §3.9 excitations, §3.10 decombination, §3.11 boundary, §3.13 cœxistence des alters) ; les citations pivots ci-dessous sont des **spot-checks firsthand** — chaque citation a été relue dans le passage source extrait, pas propagée depuis un résumé (G.1).

## 2. Le cadre en deux phrases

Il n'existe que la conscience cosmique ; « nous sommes des alters dissociés de la conscience cosmique, entourés de ses pensées » (« We, as well as all other living organisms, are but dissociated alters of cosmic consciousness, surrounded by its thoughts »). La **décombinaison** — comment des champs phénoménaux privés se forment dans le champ unitaire — est résolue par la **dissociation**, dont le Trouble Dissociatif de l'Identité est l'ancre empirique (« dissociation is a sufficiently powerful potential solution to the decombination problem », p. 48).

**La formalisation propre de la source** — c'est elle qui arme le jouet, pas une métaphore importée : « ordinarily, these phenomenal contents are internally integrated through cognitive associations: a feeling evokes an abstract idea, which triggers a memory, which inspires a thought, etc. […] **Ordinary phenomenal activity in cosmic consciousness can thus be modeled as a connected directed graph** » (§3.10) ; et « **Dissociation entails that some phenomenal contents cease to be able to evoke others** » — « Dissociation can be visualized as what happens when the graph in Figure 3.1a becomes disconnected » (§3.10). Le graphe d'évocation, sa déconnexion en composantes (les alters), et la figure 3.5 (« Alters are immersed in a common phenomenal environment ») sont **dans le texte** : nœuds = contenus phénoménaux, arêtes = évocation, dissociation = partition du graphe, environnement phénoménal commun = canal exogène partagé.

## 3. La question falsifiable

Le passage qui porte l'opérationnalisation (§3.8, question b) : « **The decombination problem: How do private phenomenal fields form within cosmic consciousness? Why can I not read your thoughts by simply shifting the focus of my attention?** » — et la réponse structurelle : la vie privée des alters n'est PAS l'isolement (figure 3.5 : immersion dans un environnement commun), c'est la **cessation de l'évocation directe** entre segments.

**Dissociation à tester** : la triple structure de la source — (i) chaque composante reste **intégrée intérieurement** (« discrete centers of self-awareness », Braude 1995: 67, cité), (ii) l'évocation directe inter-composantes **cesse** (vie privée), (iii) le canal d'**environnement commun survit** à la même séparation (les alters restent immergés dans les pensées du champ) — est-elle **réalisable et séparable** sur substrat, et la structure **clusterisée** fait-elle un travail qu'un dommage aléatoire de même masse ne fait pas ? C'est la plus petite paire de propriétés structurales du chapitre 3 qui se laisse opposer sur un jouet : *la dissociation privatise sans isoler*.

**Relation aux cases existantes** (anti-duplication) : la case 13 (combination, `ict/combination_subjects.py`) teste la direction **montante** (des micro-sujets composent-ils un macro-sujet ?) ; la présente case teste la direction **descendante** (un champ unifié se décombine-t-il en centres privés ?) — le mot « decombination » est celui de la source. La case 14 (boundary, `ict/boundary_recollement.py`) demandait si la **connectivité est séparable d'une cause commune** pour la détection de frontière ; la case 18 réutilise la machinerie de corrélation partielle mais avec une **variable manipulée différente** (un calendrier de dissociation, pas une géométrie de frontière) et un **verdict différent** (réalisabilité du triple de Kastrup, pas séparabilité d'observables). Même famille d'outil, claim distinct, falsifiable indépendamment.

## 4. Prédiction chiffrée scellée (case 18)

### Substrat

Jouet **CPU-only**, numpy pur — le graphe d'évocation de la source, littéralement :

- **N = 120 contenus phénoménaux**, k = 3 alters de 40 nœuds.
- **Graphe d'évocation pondéré** `W` : arêtes intra-alter avec probabilité `p_in = 0.10`, arêtes inter-alters avec probabilité `p_out` **calibrée** (infra), poids `U[0.5, 1.5]`, puis `W` rendue row-stochastique et multipliée par `α = 0.85` (rayon spectral < 1, stabilité). À `d = 0`, le graphe est **connexe** (contrôle mécanique : composante géante = N).
- **Dynamique d'évocation** VAR(1) : `x(t+1) = α·W·x(t) + β_i·e(t) + η_i(t)` — `η` bruit privé iid `N(0, 1)` ; `e(t)` **environnement phénoménal commun** AR(1) scalaire (φ = 0.9, variance stationnaire 1), chargé sur chaque nœud par `β_i ~ U[0.5, 1.0]` (même loi dans chaque alter — l'immersion est uniforme, figure 3.5).
- **Calendrier de dissociation** : les entrées inter-blocs de `W` sont multipliées par `(1 − d)`, `d ∈ {0.0, 0.5, 0.8, 1.0}`. `d = 1.0` : évocation directe inter-alters **nulle** — la figure 3.1b de la source.
- **Trajectoires** : T = 20 000 pas après burn-in 2 000, observables sur l'état stationnaire.

### Calibration (gelée sur graines disjointes AVANT le run principal)

Sur les graines de calibration `11, 22, 33` — **jamais sur les graines de test**, et **sans jamais lire les observables à `d > 0`** : `p_out` et l'échelle de `β` visent, à `d = 0` seulement, `ρ_intra(0) ∈ [0.5, 0.7]` (graphe intégré) et `ρ_direct(0 | env) ∈ [0.2, 0.4]` (couplage direct inter-alters visible mais sous-dominant). Ces deux paramètres gelés, le run principal s'exécute.

### Observables (par graine, sur l'état stationnaire)

- `ρ_intra(d)` : corrélation de Pearson moyenne (moyenne Fisher-z) entre activations de nœuds d'un **même** alter.
- `ρ_direct(d | env)` : corrélation partielle moyenne entre nœuds d'alters **différents**, contrôlant `e(t)` (le facteur environnemental exact, connu de la simulation) — l'évocation directe une fois la cause commune partielleisée.
- `ρ_env` : corrélation marginale inter-alters à `d = 1.0` — tout le couplage restant est environnemental par construction ; c'est le canal de la figure 3.5.

### Prédictions (scellées — aucune bande ne sera recalibrée après mesure)

| # | Prédiction | Bande / critère |
|---|---|---|
| **P1** (vie intérieure — « discrete centers ») | La dissociation ne détruit pas l'intégration intérieure des alters : `ρ_intra(1.0) / ρ_intra(0.0)` | ≥ **0.80** sur ≥ 4/5 graines |
| **P2** (vie privée — « why can I not read your thoughts ») | L'évocation directe inter-alters cesse à dissociation complète : `\|ρ_direct(1.0 \| env)\|` | ≤ **0.10** sur ≥ 4/5 graines |
| **P3** (immersion commune — figure 3.5) | Le canal d'environnement survit à la séparation que le canal direct ne survit pas : `ρ_env` | ≥ **0.30** **ET** `ρ_env ≥ 3·\|ρ_direct(1.0 \| env)\|` sur ≥ 4/5 graines |
| **Null (a)** — vue de l'instrument | L'instrument **voit** le couplage direct avant dissociation, une fois la cause commune partielleisée : `\|ρ_direct(0.0 \| env)\|` | ≥ **0.15** sur ≥ 4/5 graines — sinon `NON CONCLUSIF_INSTRUMENT` |
| **Null (b)** — travail de la structure | Dommage aléatoire de **même masse totale** d'arêtes (intra+inter confondus, uniforme) : le bras aléatoire **échoue** P1 (`ρ_intra(1.0)/ρ_intra(0.0) < 0.80`) | sur ≥ 4/5 graines — si le bras aléatoire **passe** P1+P2, la structure clusterisée ne fait aucun travail → `NON CONCLUSIF` |

**Porte instrumentale** (leçon des cases 8b/8c/17) : si `ρ_intra(0.0) < 0.30` sur ≥ 3/5 graines (le graphe de base n'est jamais intégré — plancher), les prédictions ne s'évaluent pas : `NON CONCLUSIF_INSTRUMENT`.

### Verdicts bornés

- **SUPPORTED** : P1 ∧ P2 ∧ P3 tenues **ET** Null (a) dans bande **ET** Null (b) confirmé (la dissociation clusterisée privatise sans isoler, et la structure porte ce que le dommage aléatoire ne porte pas).
- **NOT SUPPORTED** : P1 échoue (la décombinaison détruit ce qu'elle doit préserver — les alters ne sont pas des centres) ; ou P2 échoue (le canal direct survit à la séparation complète — contradiction mécanique, signal d'un bug soulevé comme tel) ; ou P3 échoue (le canal d'environnement meurt avec le direct — la triple structure de la figure 3.5 n'est pas réalisable sur ce substrat).
- **NON CONCLUSIF** : Null (a) hors bande (instrument aveugle — la cause commune avale le signal direct, la leçon mesurée de la case 14) ; ou Null (b) passe P1+P2 (structure sans travail) ; ou porte instrumentale.

## 5. Greffe sur la conjecture strates-adjonctions (lecture, jamais un claim)

Le prototype [`strates-as-adjunctions-prototype.md`](strates-as-adjunctions-prototype.md) lit chaque strate ICT comme l'acquisition d'une adjonction ; la Cohesion `∮ ⊣ ♭ ⊣ ♯` de Schreiber code la localité/partition. La dissociation de Kastrup offre le point de contact **documentaire** dual de la case 16 : où la case 16 plaçait l'espace épistémique « as-yet-unpartitioned » **avant** l'adjonction de partition, la case 18 place la décombinaison **dans** l'acquisition même de la partition — « why can I not read your thoughts » se lit comme l'échec du recollement (gluing) à travers la partition dissociative, et le canal d'environnement commun comme ce qui subsiste du champ à toute trivialisation locale (une lecture en faisceau : les sections locales ne se recollent plus, mais vivent encore sur la même base). Si la case 18 tient, elle fournit le témoin substrat de cette lecture ; si elle échoue, la lecture perd son témoin, pas sa cohérence documentaire. Cette greffe n'est **pas** testée par la case 18 : elle en est l'horizon d'interprétation.

## 6. Honnêteté grade C (limites)

1. **Aucune phénoménologie n'est mesurée.** Le jouet teste la réalisabilité d'une triple structure de corrélations ; l'identification des composantes à des « alters » et du canal exogène aux « pensées de la conscience cosmique » est une **lecture** du design par le cadre Kastrup, pas une validation de la thèse. Kastrup ne spécifie aucun jouet, aucune bande, aucun ratio — les bandes sont calibrées à la classe des cases existantes (ratios de dissociation 0.8-3.0, conventions 14/15/16), assumé comme tel.
2. **P2 est vraie par construction à `d = 1.0`** (les entrées inter-blocs de `W` sont nulles : la corrélation partielle résiduelle n'est que du bruit d'échantillonnage, ~1/√T ≈ 0.007) — comme la P2 de la case 16, sa force ne vient pas de sa surprise mais de sa **conjonction** avec P3 (l'autre canal survit) et avec les nulls (l'instrument voyait le canal direct avant, le dommage aléatoire ne reproduit pas le profil). Le verdict le dira explicitement.
3. **P1 est partiellement vraie par construction** (les arêtes intra ne sont pas touchées par le calendrier ; `ρ_intra` peut même monter à `d = 1` par arrêt des fuites) — même traitement : c'est la conjonction qui porte.
4. **L'environnement est exogène et scalaire** : la source ne formalise pas la dynamique des « pensées » environnantes ; AR(1) scalaire est la plus petite structure qui donne au canal commun une variance mesurable. Une version où l'environnement répondrait à l'activité des alters (réciprocité) serait un autre jouet.
5. **Symétrisation** : l'évocation de la source est dirigée (« a feeling evokes an idea ») ; les observables sont symétriques (corrélations). Simplification déclarée, cohérente avec la famille.
6. **Le DID empirique n'est pas modélisé** : l'ancre clinique (l'alter aveugle de Strasburger & Waldvogel, p. 47-48 — « the brain activity normally associated with sight wasn't present while a blind alter was in control ») est citée comme motivation, pas comme donnée du jouet.
7. **Une case 18 SUPPORTED dirait** : *la plus petite triple structure du chapitre 3 de la thèse — centres intérieurement intégrés, évocation directe cessée, immersion commune préservée — se laisse réaliser et séparer sur substrat, et la structure clusterisée est load-bearing* — rien de plus. L'idéalisme analytique lui-même (l'ontologie moniste) est hors portée d'un jouet, par construction.

## 6bis. Amendement v1 → v2 (pré-exécution, 2026-09-29) : estimateur de cause commune dynamique

**Motivation mesurée sur le jouet, AVANT toute mesure du run principal.** En développant le banc (commit fils), le contrôle d'intégration court a exposé un défaut d'instrument : à `d = 1.0`, la corrélation partielle inter-alters contrôlant **le seul `e(t)`** mesurait `ρ_direct(1.0 | e(t)) ≈ 0.41` — très au-dessus de la bande P2 (≤ 0.10) alors que la valeur mécanique est **exactement 0** (les entrées inter-blocs de `W` sont nulles à `d = 1`).

**Diagnostic** : l'environnement est une **cause commune dynamique**. L'AR(1) `e` pénètre chaque nœud à `β·e(t-1)`, puis se propage dans le graphe d'évocation : `W·β·e(t-2)`, `W²·β·e(t-3)`, … Deux nœuds d'alters différents partagent ces composantes **décalées** de l'environnement ; contrôler le seul `e(t)` contemporain les laisse intégralement dans le résidu. C'est le piège cause-commune de la case 14 **généralisé aux séries temporelles** : la cause commune n'est pas un scalaire instantané, c'une trajectoire.

**Réparation (v2)** — `partial_corr_given(x, controls)` contrôle désormais la matrice `[e(t), e(t-1), …, e(t-L)]`, `L = ENV_LAGS = 60` : `α^60 ≈ 3×10⁻⁵ ≪ 1/√T ≈ 0.007`, la fenêtre couvre la relaxation complète de l'évocation. Toute corrélation inter-alters qui survit est soit de l'évocation directe (`W`), soit du bruit d'échantillonnage. Un test de régression dédié (`test_partial_corr_removes_lagged_env_coupling`) verrouille le piège : un couplage porté uniquement par `e(t-3)` survit au contrôle v1 (≈ 0.5) et meurt sous le contrôle v2 (< 0.05).

**Inchangé** : les bandes P1/P2/P3, les nulls, la porte, les graines, le substrat — aucune bande n'est recalibrée par cet amendement ; il répare l'**instrument** (ce que « contrôler l'environnement » veut dire quand la cause commune a une mémoire), pas la prédiction. Le test d'intégration court confirme v2 : `ρ_direct(1.0 | env, lags) ≈ 0.003`, dans la bande P2 avec la marge attendue d'un bruit ~1/√T.

## 6ter. Amendement v3 (pré-exécution, 2026-09-29) : observables inter-alters au niveau alter + calibration gelée

**Motivation mesurée pendant la calibration** (graines 11/22/33, lectures à `d = 0` uniquement, conformément au §4). La corrélation partielle inter-alters **par paires de nœuds** est structurellement aveugle sur ce substrat : à `β = 0` (canal η seul), même la corrélation **intra**-alter par paires tombe à ~0.03, et `ρ_direct(0 | env)` reste à ~0.02 pour tout `p_out ∈ [0.02, 0.9]` et tout `β_scale ∈ [0.2, 1.0]` — plat, insensible au couplage qu'il est censé voir. Cause : le mélange row-stochastique sur N = 120 nœuds donne des corrélations par paires O(1/N) — chaque nœud est dominé par son bruit privé, l'évocation est diffuse par construction. Ce n'est pas un défaut du graphe, c'est la mauvaise échelle de mesure : la théorie elle-même parle d'**alters** (« why can I not read **your** thoughts »), pas de paires de contenus pris isolément.

**Réparation (v3)** — les observables **inter-alters** passent au niveau alter : `x̄_a(t)` = moyenne des 40 activations de l'alter `a` ; `ρ_direct(d | env)` = corrélation partielle des `x̄_a` contrôlant `[e(t), …, e(t-60)]` ; `ρ_env` = corrélation marginale des `x̄_a` à `d = 1`. **Inchangés** : `ρ_intra` (P1), la porte instrumentale et le null (b) restent au niveau nœuds ; les bandes, les nulls, la porte, les graines de test — aucune valeur scellée ne bouge. Contrôles de sensibilité sur le jouet : l'agrégat discrimine `p_out` (0.36 à `p_out = 0.02`, 0.44 à `p_out = 0.05`) et est invariant à `β_scale` — exactement les deux degrés de liberté que la calibration doit séparer. La valeur par paires reste consignée dans les résultats (`rho_direct_node_pairs`) comme témoin de l'aveuglement.

**Calibration gelée (exécution du §4)** : `p_out = 0.02`, `β_scale = 0.3`. Sur les graines 11/22/33 à `d = 0` : `ρ_intra(0) = 0.541` ∈ [0.5, 0.7] ✓ ; `ρ_direct(0 | env) = 0.358` ∈ [0.2, 0.4] ✓. Ces deux valeurs sont gelées pour le run principal ; les graines de calibration ne servent à rien d'autre.

## 6quater. Amendement v4 (pré-exécution, 2026-09-29) : le calendrier préserve le budget d'évocation des alters

**Motivation mesurée sur une graine de diagnostic** (`555` — ni graine de calibration ni graine de test, pour ne lire `d > 0` sur aucune des deux familles). Après le gel v3 (`p_out = 0.02`, `β_scale = 0.3`), le contrôle d'intégration court donnait un ratio P1 de **0.42** — la « dissociation » détruisait plus de moitié de la corrélation intra-alter. Diagnostic : `W_at(1.0)` multiplie les entrées inter-blocs par 0 **sans renormaliser les lignes** — chaque nœud perd ~29 % de sa masse d'évocation totale. L'intervention v1 confondait **couper l'évocation inter-alters** avec **assombrir chaque alter**, ce que la source ne dit pas : « Dissociation entails that some phenomenal contents cease to be able to evoke **others** » — les autres, pas l'évocation en général ; la figure 3.1b montre les sous-graphes d'alters intacts et vivants.

**Réparation (v4)** — `W_at(d)` renormalise chaque ligne à sa masse d'origine : le budget d'évocation de chaque nœud est préservé et redirigé vers l'intérieur de l'alter. Mesure graine 555 : ratio P1 **0.42 → 0.99** (l'intégration intérieure est intacte), `ρ_direct(1.0 | env)` reste ≤ bande (0.012), le canal d'environnement reste haut (0.92). Le null (b) reçoit **la même renormalisation** : la comparaison porte sur le **placement** de la masse (structurée inter vs aléatoire uniforme), pas sur la masse elle-même — sinon le bras aléatoire échouerait P1 pour le même artefact d'assombrissement, et le null ne testerait rien.

**Inchangés** : bandes, nulls, porte, graines, paramètres gelés v3, observables v3. Le test `test_row_mass_preserved_across_dissociation` verrouille l'invariant.



## 7. Ce qui suit

1. **Ce document, commité, est le scellé.** Toute modification ultérieure des bandes P1/P2/P3/nulls/portes se fait par amendement **pré-exécution** horodaté dans ce fichier (pattern des cases 14/15/17 : `v1 → v2 AVANT re-run`), jamais silencieusement.
2. Le banc `MyIA.AI.Notebooks/IIT/ICT-Series/ict/kastrup_dissociation.py` + tests `ict/tests/test_kastrup_dissociation.py` + mesures `ict/results/kastrup_dissociation_results.json` vivront dans un commit fils, avec la ligne matrice case 18 mise à jour au statut `TESTÉ (...)` dans la même PR.
3. Verdict rapporté sur [#8182](https://github.com/jsboige/CoursIA/issues/8182) avec les mesures brutes par graine. La veille ne se clôt pas sur une tranche.

---

**Statut : SCELLÉ (v4 — §6bis estimateur à décalages · §6ter observables au niveau alter + calibration gelée p_out=0.02 β_scale=0.3 · §6quater budget d'évocation préservé ; bandes v1 inchangées) — 2026-09-29, en attente du run principal.**
