# Strates ICT comme adjonctions — prototype grade C

> **Grade C explicite.** Ce document est un **prototype** de la conjecture posée en jalon 3 de [#8182](https://github.com/jsboige/CoursIA/issues/8182) (TOE ↔ conscience, carrefour Jaimungal) : *chaque strate ICT = acquisition d'une adjonction que la précédente n'a pas*. **Gated sur [#7738](https://github.com/jsboige/CoursIA/issues/7738) (tresse conceptuelle, CLOSED 2026-08-06)** — c'est-à-dire que la tresse a livré son cadrage (Thom/Grothendieck/Schmidhuber/Friston) au point où poser la conjecture est légitime. **Ce prototype n'est pas une preuve**, c'est une **forme** qui se laisse réfuter empiriquement sur substrat.
>
> **Cycle c.1331p258**, lane `myia-po-2027:CoursIA-2`. Issue de veille : [#8182](https://github.com/jsboige/CoursIA/issues/8182). PR : à ouvrir (`feature/8182-strates-adjunctions-prototype`).

## 1. La conjecture, en une phrase

Soit la séquence verticale de strates ICT — **S1 (auto-organisation, tri)**, **S2 (morphogenèse, Gray-Scott)**, **S3 (agents réactifs, Axelrod)**, **S4 (agents situés/inhibés, Laborit)**, **S5 (LLM, transformeur)** —, augmentée de la jambe transverse de la tresse (`#7738`) : **S⊥ (cohomologie Čech)**, **S↔ (Friston FEP)**, **S≈ (Schmidhuber MDL)**. **Conjecture** : *chaque strate `S_{k+1}` ajoute à `S_k` au moins une **adjonction** au sens catégoriel (un foncteur `L ⊣ R`, ou une triple d'adjoints) qui manquait à `S_k` ; cette adjonction est **interne** au substrat (elle code une capacité cognitive/calculatoire nouvelle) et **externe** au vocabulaire modal de Schreiber (Cohesion `∮⊣♭⊣♯` / Elasticity `Re⊣ℑ⊣&` / Solidity `⇉⊣⇝⊣Rh` — [nLab Perì Pantheōrías](https://ncatlab.org/schreiber/show/Per%C3%AC+Panthe%C5%8Dr%C3%ADas)).*

Dit autrement : la progression verticale d'ICT n'est pas une *liste* de substrats de complexité croissante, c'est une **dérivation** où chaque strate se construit depuis la précédente par adjonction d'une structure catégorielle qui n'était pas disponible.

## 2. Trois adjonctions plausibles, à titre d'exemple

### 2.1 S1 → S2 : adjonction **Free ⊣ Forgetful** (auto-organisation → morphogenèse)

- **S1** (tri auto-organisé par bulle de Voronoï, Boltzmann simple) : la dynamique est markovienne, l'état interne est un point dans un espace métrique, l'**observation** est un clustering. Catégorie naturelle : `Set` ou `Met`. Pas de notion de *pattern* local persistant.
- **S2** (Gray-Scott, Turing patterns) : un **champ scalaire 2D** `(u, v)(t, x, y)` admet une dynamique de réaction-diffusion. La catégorie naturelle devient `Vect_{R}^{ReacDiff}` (foncteurs vers les champs) où la morphogenèse est une **limite** de cocycle.
- **Adjonction candidate** : `Forgetful : Vect_{R}^{ReacDiff} → Set` (oublier la structure de réaction-diffusion, garder juste l'ensemble des concentrations ponctuelles) admet un adjoint à gauche `Free : Set → Vect_{R}^{ReacDiff}` qui construit le **champ libre** sur un ensemble discret.
- **Capacité nouvelle** : la *localité* (un point du substrat n'agit que sur ses voisins) — c'est précisément ce que le `∮` (« shape ») de Schreiber formalise comme **cohésion** (Cohesion `∮⊣♭⊣♯`).
- **Test falsifiable sur S1 → S2** : une strate S1 "périodisée" sur réseau 2D, à fort couplage, doit exhiber des structures dissipatives (Turing) qui sont **strictement invisibles** dans la lecture S1 markovienne. La prédiction chiffrée est à pré-enregistrer (cf. §4).

### 2.2 S3 → S4 : adjonction **Forgetful ⊣ Free** sur la politique (Axelrod → Laborit)

- **S3** (Axelrod, jeux itérés) : la politique est une fonction `pol : State → Action` — un morphisme dans `Set^{State × Action}`. Pas de coût d'inhibition, pas d'état interne physiologique.
- **S4** (Laborit, animat inhibé ICT-12/12d) : l'agent a un état interne `i = (faim, peur, inhibition)` et la politique devient `pol : (State, i) → Action` où `i` est mis à jour par une dynamique physiologique.
- **Adjonction candidate** : `Forgetful : Set^{State × i × Action} → Set^{State × Action}` (oublier l'état interne) admet un adjoint à droite `Free : Set^{State × Action} → Set^{State × i × Action}` qui construit l'état interne *canonique* (le moins informatif qui rende la politique cohérente).
- **Capacité nouvelle** : l'**inhibition comme mécanisme négatif distinct de l'incapacité** (cf. case 8 `ICT-30` du tableau de dissociation). C'est précisément l'**Elasticity** de Schreiber (`Re⊣ℑ⊣&`) : le rapport entre le réel, l'imaginaire et la modalité d'action.
- **Test falsifiable sur S3 → S4** : un agent Axelrod "augmenté d'un état interne nutrition" doit exhiber une dette d'inhibition mesurable quand on lui retire la capacité d'agir, dette **strictement nulle** sur Axelrod pur. ICT-30 (`docs/ict/dissociations-matrix.md`) teste cette case et la confirme déjà partiellement.

### 2.3 S⊥ (Čech cohomologie) : adjonction **Const ⊣ Γ** (Global sections — Presheaf constant)

- **Substrat transversal** : à toute strate `S_k` on peut attacher un **site** (catégorie des ouverts d'observation) et un **faisceau** (sections locales = mesures ICT-15d, cf. `ICT-15d-CechObstruction.ipynb`).
- **Adjonction candidate** : `Γ : Sh(X) → Set` (sections globales) admet un adjoint à gauche `Const : Set → Sh(X)` (préfaisceau constant).
- **Capacité nouvelle** : l'**obstruction** au recollement, mesurée par `H¹(X, F) ≠ 0`. C'est précisément la **Solidity** de Schreiber (`⇉⊣⇝⊣Rh`) : le rapport entre le vide, l'horizon et le rythme qui tient ensemble.
- **Test falsifiable** : `ICT-15d` a déjà livré la mesure `s2/s1, cob, rank` sur 4 substrats avec verdict `NON_TRIVIAL` (cf. `dissociations-matrix.md` § ICT-15d-corr). Mais la mesure est **SVD-dominée**, pas Čech-discriminante (note 12183/12257). Le discriminant falsifiable : *est-ce que la cohomologie Čech **distingue** un substrat cohérent d'un substrat incohérent mieux que ne le ferait une mesure scalaire agrégée ?* — à pré-enregistrer.

## 3. Cohesion / Elasticity / Solidity — les trois adjonctions de Schreiber, mappées sur ICT

Urs Schreiber, dans *Perì Pantheōrías* (nLab, 2025-03-08), pose trois triplets d'adjoints comme vocabulaire modal de la physique dérivée :

| Triplet Schreiber | Sémantique physique | Mapping ICT plausible | Test substrat |
|---|---|---|---|
| **Cohesion** `∮ ⊣ ♭ ⊣ ♯` | Forme (shape) qui se ramasse depuis le diffus | La localité d'un substrat (S1 → S2) : la réaction-diffusion comme cohesion | Turing patterns émergent à fort couplage |
| **Elasticity** `Re ⊣ ℑ ⊣ &` | Réel / Imaginaire / modal | L'inhibition (S3 → S4) : ce qui aurait pu être fait mais ne l'est pas | ICT-30 dette d'inhibition (déjà confirmé partiellement) |
| **Solidity** `⇉ ⊣ ⇝ ⊣ Rh` | Vide / horizon / rythme | L'obstruction cohomologique (S⊥) : ce qui ne se recolle pas | ICT-15d Čech discriminant |

**Conjecture forte** : *les trois triplets de Schreiber sont les adjonctions qui, ajoutées successivement à un substrat markovien S1, construisent S2 (cohésion), S4 (élasticité), S⊥ (solidité) — les trois jambes de la tresse sont des adjonctions, pas des « analogies »*. Cette conjecture est **plus forte** que le prototype ci-dessus : elle identifie la séquence modale de Schreiber à la séquence verticale d'ICT.

**Ce que ce n'est pas** : Schreiber pose ces triplets au grade A d'une physique dérivée (SUGRA 11D, M-théorie). ICT les pose au grade C documentaire (cf. `grothendieckian-lens.md` § *« Quand le recollement échoue — l'obstruction pour seul invariant »*, où le témoignage de Schreiber figure en prose). **L'isomorphisme formel n'est pas garanti** — la transitivité du grade A vers le grade C est une **hypothèse de travail**, pas un théorème.

## 4. Prédiction chiffrée falsifiable sur ICT-12c

Le substrat **ICT-12c `PregnanceAnimat`** (`MyIA.AI.Notebooks/IIT/ICT-Series/ict/pregnance_animat.py`, lignée `PregnanceAnimat`, CPU-only) porte déjà :

- Un état interne `i = (faim, baseline_pi, baseline_p_hat, position)` (cf. `ict/pregnance_animat.py` l. 80+)
- Une politique `pol : (State, i) → Action` avec coût d'inhibition (cf. `inhibited_action.py`)
- Une dissociation mesurée `s ⟂ π` (case 1 du tableau)

**Prédiction grade C** (à pré-enregistrer avant exécution, dans `docs/ict/dissociations-matrix.md` comme nouvelle case) :

> *Si l'on dote l'animat ICT-12c d'une **adjonction explicite** entre `s` (saillance perceptuelle) et `π` (valence apprise) — c'est-à-dire d'un canal `s ⇄ π` médié par une fonction `f_aj : Saillance × Prégnance → Engagement` qui est un **adjoint** au sens catégoriel (existence d'un co-adjoint vérifiant les lois d'adjonction `hom(L(x), y) ≅ hom(x, R(y))`) — alors :*
> **(P1)** *la dissociation `s ⟂ π` mesurée ICT-12c disparaît au profit d'une **corrélation contrôlée** : `corr(engagement, (s, π)) ∈ [0.5, 0.9]` médiane sur 5 seeds ;*
> **(P2)** *la dette d'inhibition (ICT-30) passe de **non-nulle** à **nulle** : la médiation adjonctive **absorbe** l'inhibition (l'agent peut désormais « décider » de coupler s et π, ce qui élimine la paralysie) ;*
> **(P3)** *la complexité algorithmique de `pol` **augmente d'au plus un facteur 2** (l'adjonction est gratuite en coût) ; toute augmentation > 5× **falsifie** la conjecture « adjonction = capacité sans coût ».*

**Null adversarial** : un animat dont `f_aj` est un **foncteur sans adjoint** (par exemple une composition libre sans co-unit) ne modifie ni (P1) ni (P2) — c'est l'**absence d'adjonction** qui tue la prédiction.

**Statut au 2026-08-30** : prédiction originale **EXÉCUTÉE ET FALSIFIÉE COMME SPÉCIFICATION** ; signature empirique plus faible du canal couplé **SUPPORTÉE**. Le protocole, les tests et les résultats reproductibles vivent dans `ict/adjonction_saillance_pregnance.py`, `ict/tests/test_adjonction_saillance_pregnance.py` et `ict/results/adjonction_saillance_pregnance_results.json`.

### 4.1 Amendement pré-exécution — observables et frontières

**Scellé avant toute exécution de la tranche.** La relecture du code révèle que les trois prédictions ci-dessus ne sont pas toutes mesurables telles quelles ; elles restent conservées comme hypothèses originales et ne sont pas réécrites après coup.

1. Dans `pregnance_animat.py`, la variable nommée `salience` vaut déjà `pi + intr`. ICT-12c mesure donc surtout `p̂ ⟂ π`, pas la dissociation `s ⟂ π`. L'exécution réutilise la batterie dédiée `salience_valence_dissociation.py`, où `s` et `π` sont tirés indépendamment, puis ajoute un canal de décision bilinéaire `σ(κs + μπ + νsπ)`.
2. Une fonction scalaire `f_aj(s, π)` n'est **pas** une adjonction catégorielle : aucune catégorie, paire de foncteurs, naturalité ou bijection de hom-sets n'est définie ici. Le traitement est nommé **canal couplé**, jamais preuve d'adjonction. Les nulls sont les canaux `s`-seul et `π`-seul.
3. La dette d'inhibition d'ICT-30 vit dans `inhibited_action.py` / `inhibited_invention.py`, pas dans ce substrat. **P2 originale est non testable dans cette tranche** ; une entropie de décision est rapportée comme diagnostic exploratoire, sans être renommée « dette d'inhibition ».
4. `corr(engagement, (s, π))` n'a pas de définition canonique. **P1 opérationnelle**, évaluée sur les graines `(0, 1, 7, 42, 99)`, exige dans au moins 4/5 graines : `|ρ(dec, π | s)| ≥ 0,40` et `|ρ(dec, s | π)| ≥ 0,40` pour le canal couplé, tandis que chaque null doit laisser son canal absent sous `0,20`. Aucune bande ne sera recalibrée après mesure.
5. **P3 opérationnelle** compte les opérations scalaires ajoutées avant la sigmoïde commune : ratio `≤ 2` confirmé, `> 5` falsifié, intervalle `(2, 5]` explicitement **INCONCLUSIF**. L'ordre asymptotique reste `O(n)` dans tous les bras.

Le verdict global distingue donc deux niveaux : (a) **conjecture originale telle que spécifiée**, falsifiée si elle exige une vraie adjonction ou l'annulation de la dette ICT-30 ; (b) **signature empirique du canal couplé**, supportée seulement si P1 passe sur au moins 4/5 graines. Ce découpage empêche un succès du jouet de valider rétroactivement la thèse catégorielle.

### 4.2 Verdict post-exécution — cinq graines, seuils inchangés

L'exécution sur les graines `(0, 1, 7, 42, 99)` donne :

| Porte pré-enregistrée | Passage |
|---|---:|
| Canal couplé : les deux corrélations partielles ≥ 0,40 | **5/5** |
| Null `s`-seul : canal `π` absent ≤ 0,20 et canal `s` présent ≥ 0,40 | **5/5** |
| Null `π`-seul : canal `s` absent ≤ 0,20 et canal `π` présent ≥ 0,40 | **4/5** |
| P3 : ratio d'opérations scalaires ≤ 2 | **5/5**, ratio = **2,0** |

Les médianes du traitement sont `|ρ(dec, π | s)| = 0,9803` et `|ρ(dec, s | π)| = 0,7948`. La graine 99 du null `π`-seul dépasse le plafond de canal absent (`0,2704 > 0,20`) ; elle est conservée comme échec, sans exclusion ni recalibrage. L'ordre asymptotique demeure `O(n)`.

- **Verdict de la spécification originale : `FALSIFIED_SPECIFICATION`.** Le traitement n'instancie aucune adjonction catégorielle et P2 n'est pas mesurable sur ce substrat.
- **Verdict du canal empirique : `SUPPORTED_OPERATIONAL_CHANNEL`.** Le traitement répond aux deux canaux et les nulls mono-canal discriminent l'effet dans au moins 4/5 graines.
- **P2 : `NOT_TESTABLE_ON_THIS_SUBSTRATE`.** L'entropie de décision archivée est exploratoire ; elle ne mesure pas la dette d'inhibition ICT-30.
- **Adjonction catégorielle : `NOT_ESTABLISHED`.** Les résultats ne valident ni les hom-sets, ni la naturalité, ni la transposition Schreiber ↔ ICT.

Le JSON committé est vérifié contre une ré-exécution fraîche par le test automatisé, avec égalité exacte des champs discrets et tolérance numérique `1e-12` sur les flottants.

## 5. Honnêteté grade C

- **(a)** La transposition Schreiber ↔ ICT est une **lecture** du substrat ICT à travers le vocabulaire modal de Schreiber, pas une validation de la thèse « la physique catégorielle est l'articulation du réel ». Schreiber est grade A (SUGRA dérivée) ; ICT reste grade C documentaire.
- **(b)** Les adjonctions proposées (Forgetful ⊣ Free sur S1→S2, S3→S4, Global sections ⊣ Const sur S⊥) sont des **candidates plausibles** : elles rendent la conjecture non-vide, mais leur caractère « minimal » ou « canonique » n'est pas démontré. D'autres adjonctions candidates (par exemple `Tensor ⊣ Hom`, `Left adjoint ⊣ Right adjoint` au sens de Day/Kan) pourraient également capturer la transition S_k → S_{k+1}.
- **(c)** Le test chiffré § 4 utilise ICT-12c comme substrat — un choix **arbitraire** parmi ~30 substrats ICT candidats. La conjecture « adjonction = capacité cognitive » est **invérifiable** sur un seul substrat : une **triade de substrats** (S1+S2+S3 ou S2+S3+S4 ou S⊥+S2+S5) serait nécessaire pour discriminer « adjonction » de « simple augmentation de capacité ».
- **(d)** La conjecture forte § 3 (« les trois triplets de Schreiber **sont** les adjonctions ») est **disproportionnée** à la base grade C documentaire. À étiqueter explicitement comme **spéculative**, jamais à présenter au-dessus de son grade.
- **(e)** Aucune **preuve formelle** (Lean, Coq) n'est fournie — Schreiber lui-même travaille en homotopie type theory au grade A, ICT n'a pas (encore) cette capacité. La formalisation Lean d'ICT en adjoint est un **chantier à part** (cf. `grothendieck_lean/` lake, qui porte déjà les concepts `SheafCohomology` au grade A ; l'extension aux adjonctions Cohesion/Elasticity/Solidity est faisable mais non livrée).

## 6. Crédit témoin & sources

- **Schreiber, U.** « Perì Pantheōrías », *nLab*, 2025-03-08 (notes pour *Theories of Everything with Curt Jaimungal*). Vérifié firsthand : la page **ne parle pas** de conscience (cf. [#8182](https://github.com/jsboige/CoursIA/issues/8182) § « Précaution cardinale »). L'importation est donc **structurelle** (vocabulaire modal), pas thématique.
- **ICT strates** : cadrage `docs/grothendieckian-lens.md` § « deux axes » + `docs/ict/dissociations-matrix.md` (matrice 4-objets `(s, q, π, W)`).
- **Cohomologie Čech** : `ICT-15d-CechObstruction.ipynb` + `dissociations-matrix.md` § ICT-15d-corr.
- **Adjonction Forgetful ⊣ Free** : forme catégorielle classique (Mac Lane, *Categories for the Working Mathematician*, Springer 1998, ISBN 978-0387984032). Grade A (mathématique), importation grade C.
- **Tresse** : [#7738](https://github.com/jsboige/CoursIA/issues/7738) CLOSED — la cartographie Thom/Grothendieck/Schmidhuber/Friston est posée.
- **Iceberg** : [#8182](https://github.com/jsboige/CoursIA/issues/8182) § « La carte des insights » — aucun des trois triplets de Schreiber n'était listé en L1-L5 (Schreiber est L0, hors-iceberg) ; l'apport de ce prototype est de **refermer** la boucle Schreiber ↔ tresse en proposant un mapping catégorie-par-catégorie.

## 7. Suite (hors scope PR)

- **(a)** Pré-enregistrement chiffré ICT-12c § 4 à pousser dans `docs/ict/dissociations-matrix.md` (case supplémentaire, gated sur pré-enregistrement — pas une livraison immédiate).
- **(b)** Test d'exécution : créer `MyIA.AI.Notebooks/IIT/ICT-Series/ict/adjonction_saillance_pregnance.py` (canal `f_aj` adjoint + 5 seeds + verdict honnête). **Une PR séparée** (chantier exécution), ce prototype ne fait que poser la conjecture.
- **(c)** Formalisation Lean des adjonctions S1→S2 et S3→S4 (chantier `grothendieck_lean/` à étendre). Faisable mais demande un lake grade A — pas une livraison de ce cycle.
- **(d)** Discussion sur l'invariant catégoriel minimal : Forgetful ⊣ Free, Tensor ⊣ Hom, ou une adjonction non-standard ? Hors scope, à débattre en `tresse-cartographie.md` si la case § 4 livre `CONFIRMED` ou `PARTIEL`.

## 8. Index

- **Issue de veille** : [#8182](https://github.com/jsboige/CoursIA/issues/8182) — jalon 3 (conjecture strates = adjonctions).
- **Tresse conceptuelle** : [#7738](https://github.com/jsboige/CoursIA/issues/7738) — CLOSED, cadrage livré.
- **Substrat-test proposé** : ICT-12c `PregnanceAnimat` (`MyIA.AI.Notebooks/IIT/ICT-Series/ict/pregnance_animat.py`).
- **Matrice de dissociation** : `docs/ict/dissociations-matrix.md` (la case « s ⟂ π » est déjà testée).
- **Lens grothendieckienne** : `docs/grothendieckian-lens.md` § *« Quand le recollement échoue — l'obstruction pour seul invariant »* (témoignage de Schreiber en prose, pas une section nommée).

— myia-po-2027:CoursIA-2, c.1331p258, prototype grade C
