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

## 6bis. Amendement pré-exécution v1 → v2 (scellé avant toute exécution du banc — 2026-09-21, detection analytique au moment de l'écriture du banc, zero run effectué)

**Raison : trois défauts analytiques de la spécification v1 §4, détectés en concevant le banc — jamais mesurés sur données.** Le motif des amendements case 15/P1 et case 16/bras phasique s'applique : un critère insatisfaisable **par construction** n'est pas une prédiction. Les bandes P1/P2/P3, graines, portes, nulls et verdicts restent **inchangés** — seule la mécanique d'opérationnalisation est re-spécifiée.

1. **Couplage v2 — contenu harmonique fixe.** La v1 spécifiait un couplage `sin(θ_j − θ_i)` (Kuramoto du premier ordre) : ce couplage ne produit **que des locks 1:1** — les rapports harmoniques m:n (2:1, 3:1…) n'y sont **pas des attracteurs**, et P1 échouerait pour une raison de **physique du couplage**, pas de la thèse testée. v2 : `H(φ) = Σ_{h=1..4} (1/h)·sin(hφ)` — contenu harmonique **fixe, non accordé** (décroissance 1/h, aucune amplitude ajustée pour favoriser un rapport particulier). C'est l'analogue substrat des résonances harmoniques que la source pose — **déclaré** comme choix de modélisation (comme le bruit partagé de la case 16), et reporté dans l'honnêteté §6.2 (P1 reste « partiellement physique » ; la charge reste sur P2+P3).

2. **Observable v v2 — stationnarité des rapports de fréquences.** Le paramètre d'ordre `r(t) = |Σ e^{iθ}|/N` est **aveugle aux locks m:n** (une paire verrouillée 2:1 y contribue par deux phaseurs contre-rotatifs → r ≈ faible même installé). v2 : `v = mean_pairs(1 − CV_temporel(ω̂_i/ω̂_j sur la seconde moitié)) × dwell_lock`, où `ω̂_i(t)` est la fréquence instantanée (différences de phase dépliées) et `dwell_lock` la fraction de paires dont le rapport reste dans ±2 % d'une valeur stable — la mesure ne lit **jamais la valeur du ratio**, seulement sa **stationnarité** (pas de circularité avec σ : un lock irrationnel proche compterait autant qu'un lock harmonique — c'est P1 qui établit que seuls les harmoniques installent, pas la définition de v). `r(t)` est conservé **uniquement** pour le discriminateur P3 (CV de r), où la cohérence brute est précisément l'objet.

3. **σ v2 — courbe de dissonance de Sethares (1993).** La formule v1 `c(r) = exp(−α·min_{p,q≤16}|ln(r)−ln(p/q)|)` est **dégénérée** : les rationnels à p, q ≤ 16 sont assez denses dans [1, 2] (pas ~1/16²) pour que toute configuration soit « proche d'un ratio simple » → σ ≈ 1 partout, échelle sans étal. v2 : dissonance par paires de sons purs `d(f₁, f₂) = exp(−3.51·s) − exp(−5.75·s)` avec `s = |f₂ − f₁| / (0.021·min(f₁,f₂) + 19)` (Sethares, *Tuning, Timbre, Spectrum, Scale*, 1993 — la forme standard des courbes de Plomp-Levelt), `σ = 1 − D/D_réf`, `D` = dissonance moyenne par paires de la configuration, `D_réf` = dissonance moyenne sous tirage uniforme des ratios dans [1, 2], **estimée une fois sur les graines de calibration puis gelée**. f₀ = 220 Hz (plage où les constantes de Sethares s'appliquent), ensembles de fréquences = f₀ × ratios.

4. **P2 v2 — précision de la perturbation.** La perturbation d'énergie ±10 % s'applique aux **amplitudes initiales de couplage effectif** (a_i ∈ {1 ± 0.1}), le couplage restant `K_c·a_i·a_j/N` — l'énergie modifie la force de couplage ressentie par paire sans toucher aux fréquences : c'est le test « l'énergie porte-t-elle la valence ? » rendu mécanique.

## 6ter. Amendement pré-exécution v2 → v3 (scellé AVANT tout run sur graines de test — 2026-09-21, sondes de calibration graine 11 uniquement, zéro donnée de graine de test)

**Raison : trois défauts de l'instrument v2, constatés en calibration (graines 11, disjointes des graines de test) — les graines de test n'ont jamais été exécutées à ce stade.** Motif des amendements case 15/16 : un critère insatisfaisable **par construction d'instrument** n'est pas une prédiction. **Bandes P1/P2/P3, graines, portes, nulls, verdicts et critères d'appariement restent inchangés** — seule l'opérationnalisation est re-spécifiée, une seconde fois.

### 6ter.1 — Sonde de calibration (graine 11, K_c balayé de 8 à 128, échelle octave vs 4 configurations dissidentes)

| K_c | v_H (v2 stationnarité) | v_diss (v2) | r̄_H | r̄_diss |
|---|---|---|---|---|
| 8 | 0.771 | **0.828** | 0.319 | 0.996 |
| 16 | 0.712 | **0.780** | 0.332 | 0.937 |
| 32 | 0.999 | 0.856 | 0.659 | 0.937 |

**Deux régimes, deux défauts, aucun recouvrement exploitable.**

### 6ter.2 — Défaut A : la stationnarité (v2) compte aussi les paires LIBRES

Une paire d'oscillateurs libres a une fréquence instantanée **constante** (ω̂ = ω) : son rapport est parfaitement stationnaire. La « qualité d'attracteur » v2 ne distingue donc pas un verrouillage d'une absence de couplage — d'où v_diss > v_H à faible couplage (tableau ci-dessus), **l'instrument discrimine à l'envers** exactement là où il devait discriminer.

**v3 (observable)** — `v = fraction de paires verrouillées m:n`. Une paire est lock s'il existe un couple d'entiers `(m, n) ≤ LOCK_MAX = 4` — **aligné sur le contenu harmonique du couplage** (1/h, h ≤ 4), non accordé — tel que la phase combinée `m·θᵢ − n·θⱼ` satisfasse **deux** critères sur la seconde moitié : concentration circulaire (écart-type circulaire < 1.5 rad) **et** dérive nulle (|dψ/dt| < 0.03 rad/unité). Le second critère est nécessaire : une dérive lente (< 1 tour par fenêtre) échappe à la concentration seule — les décalages inharmoniques de 3 à 8 % imposent une dérive ≥ 0.06 rad/unité sur le meilleur couple, un verrouillage réel l'annule. **La valeur du ratio n'est jamais lue** : un lock 2:1 compte exactement autant qu'un lock 3:2 (vérifié par test synthétique), et une paire libre stationnaire (rapport √2, aucun (m, n) ≤ 4 disponible) n'est **pas** comptée.

**Plafond structurel déclaré** : seuls les couples dont le rapport s'écrit m/n avec m, n ≤ 4 peuvent verrouiller — **20 des 28 couples** de l'échelle octave. v_H est donc borné par 0.714 au régime m:n (il atteint 1.0 seulement au régime de collapse, cf. 6ter.4) ; P1 corrèle des **rangs**, jamais des niveaux.

### 6ter.3 — Défaut B : le pôle dissident v2 est un quasi-unisson qui collapse en 1:1

Le pôle dissident v2 (ratios uniformes dans [1, 2]) place toutes les fréquences **à moins d'une octave** les unes des autres : leur détuning est petit, et elles s'entraînent **1:1** à un couplage bien plus faible que celui requis par les langues m:n. Mesuré : r̄_diss ≥ 0.937 dès K_c = 8, à tout point de fonctionnement — la cible de calibration r̄(H) ∈ [0.5, 0.8] (K_c ≈ 32) laisse le pôle dissident **entièrement collapsé**. P1 est alors **insatisfaisable par construction** : le pôle « dissonant » est toujours plus verrouillé que le pôle harmonique.

**v3 (pôle dissident)** — les deux pôles partagent la **même permutation de l'échelle octave** ; chaque membre est soit **exact** (prob u), soit **décalé** de ±3 à 8 % en log. L'étallement de fréquences est **apparié par construction** entre les pôles — seule l'harmonicité varie, plus le détuning. Le paramètre u balaie l'échelle de consonance.

**Conséquence honnête, déclarée** : le lien harmonicité → verrouillage est la physique des langues d'Arnold (une configuration dont les rapports tombent sur des résonances disponibles se verrouille ; une configuration décalée non). P1 reste donc **partiellement vraie par la physique du substrat**, exactement comme §6.2 l'annonçait déjà — **la jambe de substance reste la conjonction P2 + P3**.

### 6ter.4 — Défaut C : σ Sethares mesure la roughness de proximité, anti-corrélée à la facilité de verrouillage

Sethares/Plomp-Levelt attribue la dissonance maximale aux fréquences **proches** (bande critique) — précisément la région où le couplage verrouille le plus facilement (1:1). σ_v2 et v_v3 sont donc anti-corrélés par construction sur ce substrat, indépendamment de la thèse.

**v3 (σ)** — `σ = harmonicité octave-repliée` : chaque rapport de paire est replié dans [1, 2) par octaves (2.0 ≡ 1.0), puis scoré `exp(−d/τ)` avec `d` = distance logarithmique **circulaire** au point de repliement `p/q` le plus proche du jeu `p, q ≤ 4` (= `LOCK_MAX` : les résonances que le couplage possède réellement) et `τ = 0.03` gelé. C'est la formalisation directe du construct de la source (« symétrie de l'objet formel ») : l'unison et l'octave sont maximalement harmoniques, un rapport 21:20 ne l'est pas.

**Pourquoi p, q ≤ 4 et non ≤ 8 ou ≤ 16** : un jeu de Farey d'ordre supérieur est **plus dense que les décalages eux-mêmes** — à p, q ≤ 8 l'écart minimal entre points est 0.014 en log, inférieur à `SHIFT_LO = 0.03`, si bien qu'un membre décalé de 5 % retombe près de 6/5 ou 7/6 et demeure « harmonique ». Mesuré : σ(échelle décalée uniformément de e) = 0.878 (e = 0.02), 0.843 (e = 0.05), 0.886 (e = 0.10) — **non monotone**, l'échelle ne discrimine plus. C'est la dégénérescence de la forme v1 (p, q ≤ 16) qui réapparaît à l'ordre 8. Au jeu p, q ≤ 4, σ est strictement décroissante en e (1.0 → 0.878 → 0.797 → 0.759) et vaut 1.0 sur l'échelle octave complète. La VALEUR de σ n'est utilisée par aucune autre observable.

### 6ter.5 — Ce qui n'est PAS amendé

- **P3 et son bras N** (6 fréquences proches + 2 irrationnelles) : conservés tels quels. Le collapse 1:1 de ce bras — cohérence brute élevée **sans** structure harmonique — est l'analogue « crise » de la source ; qu'il soit ou non distinguable du bras H par `CV(r)` est **le résultat empirique attendu**, pas un défaut d'instrument à réparer. Le réparer (par exemple en pondérant la richesse des locks) serait ajuster l'observable à la thèse.
- Le couplage `H(φ) = Σ_{h≤4} sin(hφ)/h`, la perturbation P2, les nulls, les portes, le contrôle mécanique, les graines, les bandes, les verdicts bornés.

## 7. Ce qui suit

1. **Ce document, committé, est le scellé.** L'antériorité repose sur la relation de parenté des commits (leçon case 8c) : scellé d'abord, banc ensuite.
2. Le banc `MyIA.AI.Notebooks/IIT/ICT-Series/ict/stv_valence_symmetry.py` + tests + artefact de résultats vivront dans une PR **séparée** (ou un second commit de la même PR, pattern case 16), avec la ligne matrice case 17 passée de `PRÉDIT` à `TESTÉ (verdict)`.
3. Verdict rapporté sur [#8182](https://github.com/jsboige/CoursIA/issues/8182) avec les mesures brutes par graine.
4. **Statut au scellé : `PRÉDIT` — banc non écrit ; amendements v2 §6bis et v3 §6ter posés avant toute exécution sur graines de test** (couplage harmonique fixe ; v = verrouillage m:n détecté par concentration **et** dérive nulle ; pôle dissident à étallement apparié ; σ = harmonicité octave-repliée p, q ≤ 4 ; perturbation P2 mécanisée — **bandes, graines, nulls, portes et verdicts inchangés**).
