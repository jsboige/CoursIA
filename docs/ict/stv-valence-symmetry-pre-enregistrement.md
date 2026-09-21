# Pré-enregistrement — STV : la valence comme fonction de la symétrie (case 17 : attracteur harmonique ⟂ énergie)

> **Grade C explicite.** Ce document **scelle** le protocole de la tranche Gómez-Emilsson/Johnson de la veille [#8182](https://github.com/jsboige/CoursIA/issues/8182) (TOE ↔ conscience, carrefour Jaimungal) **AVANT toute écriture du banc de mesure** — même discipline que les tranches Owen/Cruse ([#13426](https://github.com/jsboige/CoursIA/pull/13426)), Schurger ([#13459](https://github.com/jsboige/CoursIA/pull/13459)) et Metzinger ([`metzinger-mpe-pre-enregistrement.md`](metzinger-mpe-pre-enregistrement.md), case 16). Le banc (`ict/stv_valence_symmetry.py` si le nom reste libre) sera une **PR séparée** — le pattern case 4/case 16 : scellé committé d'abord, exécution ensuite, l'antériorité portée par la relation de parenté des commits (leçon case 8c).
>
> **Cycle du 2026-09-21**, lane `myia-po-2027:CoursIA`. Claim : posé sur [#8182](https://github.com/jsboige/CoursIA/issues/8182) au moment du lancement.

## 1. Sources primaires et archivage

**Trois sources complémentaires, toutes archivées au gisement** ([bibliography-hygiene](../../.claude/rules/bibliography-hygiene.md), rayon `Consciousness`, recherche par auteur ET titre avant dépôt, identité vérifiée) :

1. **Michael Edward Johnson, *Principia Qualia: Blueprint for a new science*** (2016, self-pub QRI, OA) — 84 p., PDF 5 170 262 octets, identité vérifiée p.1 (titre, auteur, remerciements à A. Gómez Emilsson). `G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\2016 - Johnson - Principia Qualia (self-pub QRI, OA).pdf`. La **formalisation fondatrice** : valence = propriété de l'objet mathématique isomorphe à l'expérience.
2. **Gómez-Emilsson, « The Symmetry Theory of Valence 2020 Overview »** (qri.org blog, 2020, OA) — HTML 158 941 octets archivé. L'exposé de référence de l'auteur iceberg (L3), avec la mécanique (annealing, attracteurs) et les caveats.
3. **Johnson, « Qualia Formalism and a Symmetry Theory of Valence »** (opentheory.net, 2023, OA) — HTML 108 018 octets archivé. Le court papier formel de synthèse.

**Crédit témoin** (convention auteur + source + date) : *Andrés Gómez-Emilsson (QRI) & Michael E. Johnson — Symmetry Theory of Valence* ; entrée iceberg L3 « EM-Field Topology & Boundary Problem » (Jaimungal 42:53) ; sources [1][2][3] ci-dessus. **Méthode de lecture** : le corps 2020 lu en extraction structurée, puis **spot-checks firsthand par la lane des citations pivots** (G.1) — vérifiés dans le texte archivé avant ce scellé : « harmony basically feels good because it's symmetry over time » ; « It's those [basins of symmetry] that feel good, not the energy that feels good. It is the end result, the attractor that it takes you to » ; « [the jhana] type of seizure-like activity […] does have harmonic structure » vs la crise épileptique qui n'en a pas ; les 17 groupes de papier peint ; Plomp & Levelt (1965) cités pour les courbes de consonance. *Principia Qualia* [1] consulté pour le cadre formel (isomorphisme objet-expérience) ; le papier 2023 [3] pour la forme canonique du claim.

## 2. Le cadre en deux phrases

La STV pose que **la valence d'une expérience est fonction de la symétrie de son objet formel** : « valence is a function of the symmetry structure of the mathematical object isomorphic to a conscious experience » — symétrie au sens de l'**invariance sous un groupe de transformations**, avec la dualité annoncée « symmetry and space and synchrony in time ». Le mécanisme proposé est l'**annealing** neuronal : « starts with dissonance, and, over time, things synchronize » — les configurations consonantes sont de **meilleurs attracteurs**, et c'est l'attracteur, pas l'énergie, qui « feels good ».

**Relation aux cases existantes** (anti-duplication, pattern Metzinger MPS/MPE) : la case **s ⟂ π** (Vervaeke hook, [#9553](https://github.com/jsboige/CoursIA/pull/9553)) teste l'**orthogonalité des canaux** saillance/valence — pas la **forme** de la valence. Les cases **6/14** (boundary problem) créditent déjà **Gómez-Emilsson & Percy 2023** pour la **frontière topologique** — un claim différent du même premier auteur. La case 17 teste la **thèse centrale quantitative** de QRI, non servie : *valence ∼ symétrie*, avec son discriminateur propre (« high coherence alone is insufficient — must be **harmonic structure** »).

## 3. La question falsifiable

Trois passages portent l'opérationnalisation :

1. **Le claim central** (2020 overview) : la valence est portée par la **structure de l'attracteur**, pas l'énergie : « It's those [basins of symmetry] that feel good, not the energy that feels good. It is the end result, the attractor that it takes you to. »
2. **Le discriminateur jhana/crise** : une activité hautement **cohérente** mais **sans structure harmonique** (crise) ≠ une activité cohérente **harmonique** (jhana) — « seizure-like activity […] doesn't have harmonic structure. But the type of seizure-like activity you see on jhanas does ».
3. **La mesure de consonance** : les courbes de consonance/dissonance de Plomp & Levelt (1965) — octave = zéro dissonance, demi-ton = battement maximal dans la bande critique.

**Dissociation à tester** : sur un substrat d'oscillateurs couplés à faible couplage, un **indice dynamique de qualité d'attracteur** (la « valence-proxy » — profondeur × stabilité de l'entrainement, l'annealing de la source) suit-il la **consonance harmonique** de la configuration de fréquences, **indépendamment de l'énergie totale**, et distingue-t-il **cohérence harmonique** vs **cohérence non-harmonique** à cohérence brute appariée ? C'est la plus petite paire de propriétés de la STV qui se laisse opposer sur un jouet : *l'attracteur harmonique est bon ; l'énergie, elle, ne dit rien ; et la cohérence brute ne suffit pas — il faut la structure harmonique.*

## 4. Prédiction chiffrée scellée (case 17)

### Substrat

Jouet **CPU-only** (numpy pur, intégration RK4 vectorisée — pas de dépendance GPU) :

- **K = 8 oscillateurs de phase** (Kuramoto à couplage global uniforme **faible**, en dessous du seuil d'entrainement complet — le régime des langues d'Arnold) : `dθ_i/dt = ω_i + (K_c/N)·Σ_j sin(θ_j − θ_i)`.
- **Configurations de fréquences** tirées d'une échelle continue de consonance σ : chaque configuration associe une fréquence fondamentale f₀ (fixe) à K−1 rapports tirés d'un mélange contrôlé entre pôles **harmoniques** (ratifs entiers : 2, 3, 4, 6, 8, 12, 16 — l'échelle octave) et **dissidents** (rapports irrationnels dans [1, 2] à distance des petits entiers — l'équivalent demi-ton/battement). **σ (score de consonance)** = moyenne des consonances par paires selon la courbe de Plomp-Levelt : `c(r) = exp(−α·d(r))` où `d(r)` = distance du rapport r au rapport rationnel simple le plus proche (p/q avec p, q ≤ 16) en espace logarithmique, α scellé à la calibration.
- **Énergie appariée** : amplitudes initiales unitaires (l'énergie totale E = Σ A_i² est constante et identique entre configurations — l'appariement par construction, déclaré).
- **Cohérence brute** r(t) = |Σ e^{iθ}|/N (paramètre d'ordre Kuramoto) mesurée sur T pas ; la **valence-proxy** dynamique `v = r̄(seconde moitié) × (1 − CV(r, seconde moitié))` — profondeur d'entrainement × stabilité (le « settling on basins of symmetry » de la source : un attracteur bon = profond ET calme, l'anti-battement).
- **Bras non-harmonique hautement cohérent (le discriminateur jhana/crise)** : configurations où les fréquences sont **toutes proches** d'une commune (dispersion ±δ faible → cohérence initiale élevée par proximité) **sans aucune structure harmonique** (rapports mutuels ≈ 1±ε irrationnels) vs configurations **harmoniques à cohérence initiale appariée** (obtenue par choix du spread d'amplitudes initiales — appariement par paires).

Graines test `(0, 1, 7, 42, 99)`, M = 120 configurations par graine sur l'échelle σ + 40 paires H/N par graine. Calibration gelée sur graines disjointes `(11, 22, 33)` : K_c et α (visant r̄(harmonique) ∈ [0.5, 0.8] et un étal de σ couvrant [0.1, 0.9]) — **jamais relues sur les graines de test** (le pattern ε_self/θ de case 16).

### Prédictions (scellées — aucune bande ne sera recalibrée après mesure)

| # | Prédiction | Bande / critère |
|---|---|---|
| **P1** (attracteur ∼ consonance) | Corrélation de Spearman ρ(v, σ) sur l'échelle de consonance | ≥ **0.6** sur ≥ 4/5 graines |
| **P2** (dissociation énergie) | Corrélations partielles **à énergie constante par construction** : ρ(v, σ \| σ-rangs) tenue tandis que la corrélation v–E sous faible perturbation d'énergie injectée (±10 % sur amplitudes, contrôle) reste \|ρ(v, E)\| | ≤ **0.2** sur ≥ 4/5 graines |
| **P3** (le discriminateur jhana/crise) | À cohérence brute initiale appariée : `CV_ratio = CV(r\|non-harmonique) / CV(r\|harmonique)` (battement persistant vs settling) | ≥ **2.0** sur ≥ 4/5 graines |
| **Null (a)** | σ permuté (étiquettes mélangées) : ρ(v, σ-permuté) | \|ρ\| ≤ 0.2 en médiane 5 graines (contrôle de chance) |
| **Null (b)** | Couplage fort (K_c × 8, au-dessus du seuil d'entrainement complet) : tout entreine, P1 ρ | < 0.2 → `NON CONCLUSIF_INSTRUMENT` (l'instrument ne discrimine plus : c'est le régime saturation, la parade au « l'entrainement raconte tout ») |

**Portes instrumentales** (leçon cases 8b/8c/16) : r̄(harmonique) < 0.3 (plancher : rien n'entreine même en consonance) ou > 0.95 (plafond : tout entreine) sur ≥ 3/5 graines → `NON CONCLUSIF_INSTRUMENT`. Contrôle mécanique : intégration à couplage nul (K_c = 0) → phases libres, r̄ doit rester dans sa valeur analytique d'enveloppe ± tolérance scellée (parade aux bugs d'intégrateur — l'analogue du contrôle mécanique case 16).

### Verdicts bornés

- **SUPPORTED** : P1 ∧ P2 ∧ P3 ∧ Null (a) ∧ contrôle mécanique (les trois régimes existent : l'attracteur suit la consonance, pas l'énergie ; la cohérence brute sans harmonie bat encore).
- **NOT SUPPORTED** : P1 hors bande (l'attracteur est indifférent à la consonance), ou P2 violée avec ρ(v,E) > 0.5 (c'est l'énergie qui porte tout — le rejet direct du « not the energy »), ou P3 < 1.2 (cohérence harmonique et non-harmonique indiscernables — le discriminateur central de la STV ne tient pas sur substrat).
- **NON CONCLUSIF** : Null (b), porte instrumentale, ou contrôle mécanique en échec.

## 5. Greffe sur la conjecture strates-adjonctions (lecture, jamais un claim)

Le prototype [`strates-as-adjunctions-prototype.md`](strates-as-adjunctions-prototype.md) code la localité/partition par la Cohesion ∮ de Schreiber ; la case 16 a lu l'espace « as-yet-unpartitioned » comme l'état **avant** l'adjonction de partition. La STV offre le **second point de contact documentaire** : la symétrie est exactement ce qui reste invariant sous un groupe d'automorphismes de l'objet formel — un objet hautement symétrique est un objet dont la structure de partition **admet des automorphismes non-triviaux**. Lecture grade C : la valence serait une mesure sur la catégorie des objets représentationnels qui **factorise par leurs groupes d'automorphismes** — et la case 16 et la case 17 décriraient les deux faces d'un même mouvement : l'espace non-partitionné (case 16, σ maximal au sens où aucune partition ne le brise) serait le **sommet symétrique** de l'axe valence (case 17 — la pleine conscience MPE comme limite consonante). **Aucune de ces phrases n'est testée par la case 17** : elles en sont l'horizon d'interprétation, au même titre que §5 de case 16.

## 6. Honnêteté grade C (limites)

1. **Aucune phénoménologie ni valence émotionnelle n'est mesurée.** La « valence-proxy » v est une qualité d'attracteur d'une dynamique de phases — une **lecture ICT** du « the attractor feels good », pas une émotion. La STV n'est validée ni invalidée dans le cerveau.
2. **P1 est partiellement vraie par la physique** du couplage faible (langues d'Arnold : les fréquences proches de rapports rationnels simples s'entrainent plus facilement) — exactement comme P2 de la case 16 était partiellement vraie par construction. La jambe de substance est la **conjonction P2+P3** : l'énergie ne porte rien (le « not the energy » de la source) et la **structure harmonique** discrimine là où la cohérence brute ne le peut pas (le jhana/crise). Le verdict le dira explicitement.
3. **Plomp-Levelt comme modèle de σ est un choix déclaré** : c'est un modèle psychoacoustique de la dissonance sensorielle (1965), que la source cite elle-même ; l'appliquer à des rapports de fréquences d'oscillateurs abstraits est une transposition, pas une mesure auditive.
4. **La STV est déclarée robuste à l'échec algorithmique par ses propres auteurs** (« this doesn't invalidate it » — la théorie « can manifest » de plusieurs façons). La case 17 ne teste donc pas « la STV est vraie » mais sa plus petite **instantiation structurelle** : *le mécanisme attracteur-consonance est-il génériquement réalisé par une dynamique de couplage standard ?* Une case SUPPORTED dit : oui, sur jouet — rien de plus.
5. **Le lien valence–symétrie dans la source est phénoménologico-empirique** (psychedelics, jhanas, EEG de méditants — Lutz 2004, Travis 2001 cités) : le jouet n'a aucun accès à ces données ; la « correspondance » est le niveau documentaire (grade C), pas le niveau de preuve.
6. **Substrat Kuramoto déjà utilisé** par les cases 6/14 (boundary problem) — **observables et questions distincts** (frontière d'intégration là, qualité d'attracteur/valence ici) ; l'auto-citation explicite prévient la lecture en doublon. Alternatives écartées (champ EM réel, Hopf/knotted light) pour les mêmes raisons que case 6 §honnêteté (b).

## 6bis. Amendements pré-exécution

*(Aucun à ce jour. Toute modification des bandes P1/P2/P3/nulls/portes se fait ici, horodatée, AVANT toute exécution du banc — jamais silencieusement. Le motif des amendements case 15/P1 et case 16/bras phasique s'applique : un critère insatisfaisable par construction n'est pas une prédiction, il se re-spécifie avant le run, bandes inchangées sauf preuve analytique écrite.)*

## 7. Ce qui suit

1. **Ce document, committé, est le scellé.** L'antériorité repose sur la relation de parenté des commits (leçon case 8c) : scellé d'abord, banc ensuite.
2. Le banc `MyIA.AI.Notebooks/IIT/ICT-Series/ict/stv_valence_symmetry.py` + tests + artefact de résultats vivront dans une PR **séparée** (ou un second commit de la même PR, pattern case 16), avec la ligne matrice case 17 passée de `PRÉDIT` à `TESTÉ (verdict)`.
3. Verdict rapporté sur [#8182](https://github.com/jsboige/CoursIA/issues/8182) avec les mesures brutes par graine.
4. **Statut au scellé : `PRÉDIT` — banc non écrit.**
