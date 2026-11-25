# Pré-enregistrement — Lahav & Neemeh, conscience relativiste (case 23 : la privacité phénoménale est perspectivelle, pas informationnelle)

> **Grade C explicite.** Ce document **scelle** le protocole de la tranche Lahav de la veille [#8182](https://github.com/jsboige/CoursIA/issues/8182) (TOE ↔ conscience, carrefour Jaimungal — iceberg **L3** : « Heidegger/Dasein, Graziano, Emilsson, Bach, Hoffman (interface), **Lahav** ») **AVANT toute écriture du banc de mesure** — héritage des tranches Kastrup (case 18), Butlin (case 19) et Khovanov (cases 21-22) : source primaire lue et archivée, pré-enregistrement commité avant l'implémentation et la mesure, verdict borné. Le banc (`ict/lahav_relativistic.py`) vient dans un commit fils — la relation de parenté des commits porte l'antériorité (leçon case 8c).
>
> **Cycle du 2026-11-20**, lane `myia-po-2028:CoursIA`. Claim : `[CLAIMED]` sur [#8182](https://github.com/jsboige/CoursIA/issues/8182) (c.7028404885), amendé aux chemins complets (c.7029424705) : `ict/lahav_relativistic.py`, `ict/tests/test_lahav_relativistic.py`, `ict/results/lahav_relativistic_results.json`, `docs/ict/lahav-relativistic-pre-enregistrement.md`.

## 1. Source primaire et archivage

**Source** : Nir Lahav & Zachariah A. Neemeh, *A Relativistic Theory of Consciousness*, Frontiers in Psychology **12**:704270, publié 12 mai 2022, doi [10.3389/fpsyg.2021.704270](https://doi.org/10.3389/fpsyg.2021.704270) (HYPOTHESIS AND THEORY, OA CC-BY).

**Archivage gisement** ([bibliography-hygiene](../../.claude/rules/bibliography-hygiene.md)) : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\Lahav_Neemeh_2021_A_Relativistic_Theory_of_Consciousness.pdf` — 25 pages, identité vérifiée sur la première page (auteurs, titre, doi, « Frontiers in Psychology | Volume 12 | Article 704270 »), recherche par auteur ET titre avant dépôt (aucun Lahav préexistant au rayon), une seule copie au rayon `Consciousness`.

**Méthode de lecture** : texte intégral extrait (pypdf, 25 pages) et **lu en entier** contre la copie archivée — introduction, argument conceptuel, section mathématique complète (éqs 1-51), discussion, conclusion. Les citations pivots ci-dessous sont des **spot-checks firsthand** — chaque citation a été relue dans le passage source extrait, pas propagée depuis un résumé (G.1).

## 2. Le cadre en deux phrases

La conscience phénoménale n'est ni privée ni illusoire : elle est **relativiste** — « a system either has or doesn't have phenomenal consciousness **with respect to some observer** » (résumé). Dans le cadre cognitif de référence du système lui-même (1re personne), le quale est observable et **identique** au jugement phénoménal (éq 35 : `c^µ_xt = Q^µ_xt`) ; depuis tout autre cadre (3e personne), les sous-systèmes supérieurs rendent **∅** sur cette représentation (éqs 36-38) et seule la sensation mesure ses **propriétés physiques** (éq 39 : `T(Q^ν)_µ = t^i_µ(Σ α_m ê_m)`).

**La formalisation propre de la source** — c'est elle qui arme le jouet, pas une métaphore importée : le modèle à trois niveaux `S = (T, P, C)` (éq 2, sensation/perception/conscience fonctionnelle, modules E, W, M, A, I, L — éqs 3-10), le principe d'équivalence Alice/ALICE (éqs 11-18 : mêmes mesures → même cadre → fonction delta → le « zombie » mesure des qualia), la condition 1re personne = `C` mesure directement le jugement (éq 42), la condition 3e personne = la sensation mesure les propriétés physiques (éq 43), et la **transformation entre cadres** `Ξνµ` (éq 46) à deux conditions — la fonction d'appartenance `m_C` (l'entrée est-elle un état de l'espace de C de l'observateur) **et** le delta de position spatiale `δ_r` — dont le scénario de **symétrie brisée** (éqs 49-50 : mêmes dynamiques, positions différentes → mutuellement 3e personne) montre que les deux conditions sont nécessaires.

## 3. La question falsifiable

Le passage qui porte l'opérationnalisation (discussion) : « **phenomenal properties are not truly private** […] it is non-trivial to do the transformation to the appropriate cognitive frame of reference. Nevertheless, this kind of transformation is nomologically possible » — et la symétrie du non-observateur privilégié : « Alice and Bob […] will not agree on who has phenomenal consciousness », chacun se mesure des qualia et ne mesure chez l'autre que des patterns physiques.

**Relativisme à tester** : la triple structure de la source — (i) **mesure directe** : dans son propre cadre et à sa propre position, `C` reconnaît directement ses propres jugements (voie 1re personne, éq 42, identité éq 35) ; (ii) **∅ direct inter-cadres** : les jugements d'un système appris indépendamment ne sont reconnus par **aucun** sous-système supérieur d'un autre cadre (éqs 36-38) — la voie directe est close ; (iii) **voie physique intacte** : la sensation de l'autre cadre mesure les **propriétés physiques** du pattern (coordonnées, éq 39) et celles-ci portent **toute l'information d'identité** du quale — l'identification indirecte réussit bien au-dessus du hasard. La privacité est **perspectivelle** (quel canal), pas **informationnelle** (quelle information) : c'est la plus petite paire de propriétés du formalisme qui oppose « relativiste » à « privé » sur un substrat. S'y ajoute le **travail de la condition spatiale** : la transformation `Ξνµ` (éq 46, `m_C` ∧ `δ_r`) contredit un routage « appartenance seule » (sans `δ_r`) sur le cas symétrie brisée — même dynamique, position différente → quand même indirect.

**Relation aux cases existantes** (anti-duplication) : la case 13 (combination) et la case 18 (Kastrup, décombinaison) testent la **structure du champ** (que des sujets composent/se décomposent) ; la case 23 teste la **structure de l'accès** (quels canaux mesurent quoi) — variable manipulée différente (l'apprentissage séparé des codebooks + la position), observable différente (prédicats de routage et taux de reconnaissance, pas des corrélations dynamiques). La case 5ter (Graziano contrôle) testait le bénéfice d'un schéma pour le contrôle ; ici le schéma n'est pas en cause, la **géométrie d'accès** l'est. Aucune case existante ne touche `Ξνµ`, `m_C` ou `δ_r`.

## 4. Prédiction chiffrée scellée (case 23)

### Substrat

Jouet **CPU-only**, numpy pur — le modèle à trois niveaux de la source, littéralement :

- **K = 8 entrées** `x_t` (objets physiques à propriétés `y ∈ R^6`). Espace de codage **D = 64** (« every degree of freedom of the dynamic of the system is represented as an axis of a multidimensional space »).
- **Systèmes** : par graine `s`, **Alice** (graine `s`) et **Bob** (graine `s + 10 000`) apprennent **séparément** — codebooks `P` et `C` de K vecteurs unitaires gaussiens tirés par leur propre graine (« two cognitive systems developed separately […] Alice and Bob have no states in common and the set of states is disjoint »). **ALICE** = réplique d'Alice (même graine, donc mêmes dynamiques/représentations) **à une position spatiale différente** — le scénario symétrie brisée.
- **Mesure directe** (éq 42) : l'état de C participant à la dynamique est `c_k + ε`, `ε ~ N(0, σ_ε² I)`, `σ_ε = 0.05` ; reconnaissance = cosinus max contre son propre codebook C **≥ τ = 0.80** (constantes gelées a priori ; marge : cos propre attendu ≈ 0.93, cos croisé attendu ≤ ~0.35).
- **∅ direct inter-cadres** (éqs 36-38) : l'état `c^Alice_k + ε` soumis au codebook C de Bob : si cosinus max < τ, sortie **∅** — P, C, L de Bob ne reconnaissent pas (dans le jouet, les trois partagent le prédicat d'appartenance au codebook).
- **Voie physique** (éqs 39-40) : la sensation T mesure les **coordonnées** du pattern (l'état lui-même dans la base partagée — les propriétés physiques `y_j = Σ α_m ê_m` sont indépendantes du cadre) avec bruit `N(0, σ_T² I)`. Session de labo : M = 40 observations bruitées par pattern, prototypes = moyennes ; test : N_test = 200 observations fraîches, étiquetage au plus proche prototype. Précision vs hasard 1/8.
- **Transformation `Ξνµ`** (éq 46) : routage direct vers `C_ν` ssi `m_C^ν(x) ≠ ∅` **∧** `δ_r(x, S_ν) = 1` ; sinon voie `S_ν` (indirecte, par T). Variantes : **appartenance seule** (sans `δ_r`) et **approximation éq 51** (sans `m_C`).

### Calibration (gelée sur graines disjointes AVANT le run principal)

Sur les graines de calibration `11, 22, 33` — **jamais sur les graines de test** `0, 1, 7, 42, 99` (convention de la famille) — un seul paramètre est calibré : `σ_T`, sur la grille `{0.05, 0.10, 0.15, 0.20, 0.30}`, pris comme la plus petite valeur donnant une précision du canal physique ∈ **[0.80, 0.95]** à l'état repos. `σ_ε = 0.05`, `τ = 0.80`, D, K, M, N_test gelés a priori (ci-dessus). Ces valeurs gelées, le run principal s'exécute.

### Observables (par graine de test)

- `R_direct_own` : taux de reconnaissance directe (≥ τ) des **propres** K jugements par C — les deux sens (Alice/Alice, Bob/Bob), symétrie attendue.
- `R_direct_foreign` : taux de reconnaissance directe (faux positifs) des K jugements d'**autrui** (∅ attendu) — les deux sens ; témoin : cosinus croisé max consigné.
- `Acc_indirect` : précision d'identification par la voie physique seule (lequel des K jugements autrui avait), prototypes labo vs observations fraîches.
- **Fidélité de dispatch** : la table des 6 cas (3 cas de mesure × 2 scénarios de position) routée par `Ξνµ` vs la table attendue du texte ; et le nombre de cas où le routage **appartenance seule** contredit `Ξνµ`.

### Prédictions (scellées — aucune bande ne sera recalibrée après mesure)

| # | Prédiction | Bande / critère |
|---|---|---|
| **P1** (mesure directe — éq 42) | Dans son cadre, C reconnaît ses propres jugements : `R_direct_own` (moyenne des deux sens) | ≥ **0.95** sur ≥ 4/5 graines |
| **P2** (∅ direct inter-cadres — éqs 36-38) | La voie directe est close pour autrui : `R_direct_foreign` (les deux sens) | ≤ **0.05** sur ≥ 4/5 graines |
| **P3** (voie physique intacte — éqs 39-40) | Les propriétés physiques portent l'identité du quale : `Acc_indirect` | ≥ **0.75** sur ≥ 4/5 graines **ET** ≥ 3× le hasard (0.375) |
| **Null (a)** — vue de l'instrument | Le canal physique a une fidélité mesurable au repos (graines de calibration) : `Acc_cal` | ∈ **[0.70, 0.98]** — sinon `NON_CONCLUSIF_INSTRUMENT` |
| **Null (b)** — travail de la condition spatiale | Le routage « appartenance seule » contredit `Ξνµ` sur **au moins un** cas (attendu : propre quale, symétrie brisée — même codebook, position différente → indirect) | sur **5/5** graines — s'il coïncide partout, `δ_r` ne fait aucun travail → `NON_CONCLUSIF` |
| **Porte de séparabilité** | La marge direct/tiers est massive à l'état repos (graines de calibration) : `R_direct_own − R_direct_foreign` | ≥ **0.80** — sinon `NON_CONCLUSIF_INSTRUMENT` |

**Verdict borné** (convention de la famille) : `SUPPORTED` si P1 ∧ P2 ∧ P3 tenues et les deux nulls dans leurs bandes ; `REFUTED` si une prédiction échoue **dans le sens de la non-réalisabilité** (voie directe fermée chez soi, ou ∅ chez soi / ouverte vers autrui, ou canal physique sous le hasard) ; `NON_CONCLUSIF` sinon (instrument ou null b).

## 5. Greffe sur la lentille (lecture, jamais un claim)

Le troisième mouvement de la lentille grothendieckienne (changement de représentation vers le contrôlable) lit l'éq 44 comme un **changement de carte** : quale et pattern physique sont deux trivialisations locales du même objet, la transformation `Ξνµ` le morphisme qui les recolle — la « privacité » est l'échec de recollement **tant que la carte de l'autre n'est pas chargée**, pas une propriété ontologique. Cette greffe n'est **pas** testée par la case 23 : elle en est l'horizon d'interprétation.

## 6. Honnêteté grade C (limites)

1. **Aucune phénoménologie n'est mesurée.** Le jouet teste la réalisabilité et la séparabilité d'une triple structure **d'accès** (canaux direct/tiers/physique) ; l'identification des codebooks à des « qualia » et des prédicats à des « mesures » est une lecture du design par le cadre de la source, pas une validation de la thèse relativiste. La source ne spécifie aucune bande, aucun jouet — les bandes sont calibrées à la classe des cases 14-22, assumé comme tel.
2. **L'identité éq 35 est vraie par construction** (`Q := c` dans le jouet) — sa force ne vient pas de sa surprise mais de sa **conjonction** avec le routage : la même représentation est directe dans son cadre et ∅ dans l'autre. Le verdict le dira explicitement.
3. **P2 est attendue quasi-mécaniquement** (codebooks aléatoires en D = 64 : cosinus croisés ≤ ~0.35 ≪ τ = 0.80) — c'est une **mesure de disjointness** de l'apprentissage séparé, pas un exploit ; ce qui la rend informative est qu'elle échouerait si l'apprentissage séparé ne séparait pas (D petit, τ bas), et qu'elle est la moitié du contraste perspectivelle.
4. **Le prototype labo est un oracle partiel** : la session de catalogage (M = 40 observations) donne à l'observateur tiers la correspondance pattern→étiquette que la source appelle « transformation nomologiquement possible mais technologiquement infaisable » ; le jouet la réalisabilité de la correspondance **par les seules propriétés physiques**, pas sa faisabilité neuronale.
5. **La position spatiale est un index, pas une géométrie** : `δ_r` compare des identifiants de position, fidèle à l'usage de la source (éq 46) ; aucune métrique spatiale n'est modélisée.
6. **Les éqs 3-10 sont réduites** : T, P, C, L deviennent des prédicats d'appartenance à des codebooks ; les modules E, W, M, A, I de la source ne sont pas instanciés (le jouet n'a pas besoin d'eux pour la question d'accès). Réduction déclarée, cohérente avec la famille.
7. **Une case 23 SUPPORTED dirait** : *la plus petite triple structure d'accès du formalisme de Lahav & Neemeh — mesure directe chez soi, ∅ direct chez autrui, information d'identité intégralement portée par la voie physique, condition spatiale load-bearing — se laisse réaliser et séparer sur substrat* — rien de plus. La dissolution du problème difficile (le claim philosophique du papier) est hors portée d'un jouet, par construction.

## 7. Ce qui suit

1. **Ce document, commité, est le scellé.** Toute modification ultérieure des bandes P1/P2/P3/nulls/portes se fait par amendement **pré-exécution** horodaté dans ce fichier (pattern des cases 14/15/17/18 : `v1 → v2 AVANT re-run`), jamais silencieusement.
2. Le banc `MyIA.AI.Notebooks/IIT/ICT-Series/ict/lahav_relativistic.py` + tests `ict/tests/test_lahav_relativistic.py` + mesures `ict/results/lahav_relativistic_results.json` vivront dans un commit fils, avec la ligne matrice case 23 et la ligne du tableau README ajoutées dans la même PR.
3. Verdict rapporté sur [#8182](https://github.com/jsboige/CoursIA/issues/8182) avec les mesures brutes par graine. La veille ne se clôt pas sur une tranche.

***

**Statut : TESTÉ (SUPPORTED) — exécution 2026-11-20 (po-2028), scellé v1 sans amendement. P1 1.000 (5/5) · P2 0.000 (5/5, croisés ≤ 0.373 ≪ τ) · P3 0.895–0.940 (5/5) · null a 0.845–0.945 (3/3) · null b 5/5 · porte dormante (marge 1.0) · dispatch 6/6 × 5. Banc et mesures committés en commits fils.**
