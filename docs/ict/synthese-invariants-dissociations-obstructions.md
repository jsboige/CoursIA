# ICT — trois régimes de lecture d'une trajectoire : invariants, dissociations, obstructions

> **Statut.** Document de synthèse transversal, grade **C-documentaire** (consolidation, pas de nouveau dispatch). Consolidé depuis le cadrage stratégique du 2026-07-19 et la série ICT ([Epic #4588](https://github.com/jsboige/CoursIA/issues/4588)).
> **Objet.** Poser opérationnellement — non pas seulement conceptuellement — une grille à trois régimes pour *lire* une trajectoire causale already instrumentée dans le dépôt, et la relier aux deux chantiers actifs : [#7395](https://github.com/jsboige/CoursIA/issues/7395) (N1 — l'obstruction comme objet expérimental) et [#7396](https://github.com/jsboige/CoursIA/issues/7396) (N2 — invariants et dissociations sur les trajectoires de *représentations*).
> **Discipline.** Synthèse consolidante. Pas d'unification prématurée, pas de formalisme catégorique plaqué trop tôt (cf [#7289](https://github.com/jsboige/CoursIA/issues/7289) / [#7291](https://github.com/jsboige/CoursIA/issues/7291), gelées). Le document décrit la grille, cite des cas concrets déjà instrumentés, et relie aux livrables existants ; il ne crée **aucune** nouvelle dépendance de dispatch. See [#7399](https://github.com/jsboige/CoursIA/issues/7399). Part of [#4588](https://github.com/jsboige/CoursIA/issues/4588).

## Pourquoi cette grille

La série ICT (cf [README ICT-Series](../../MyIA.AI.Notebooks/IIT/ICT-Series/README.md)) est partie chercher un *scalaire universel* — une grandeur unique qui mesurerait, à travers tous les substrats, l'intégration, l'irréversibilité, ce qu'on ose appeler conscience. Elle a rapporté sans fard qu'un tel scalaire **n'existe pas** : sur la synthèse cross-substrat, deux proxys se suivent quand un troisième diverge. Ce constat — et non le nombre manquant — est le résultat.

Le document companion [« La mer qui monte »](../grothendieckian-lens.md) (issue [#7299](https://github.com/jsboige/CoursIA/issues/7299)) lit cette falsification comme un **candidat à une obstruction de type cohomologique** au recollement : on était parti chercher une section globale, et l'on tient, en `H¹ ≠ 0`, un *candidat* de classe d'obstruction — lecture proposée (grade C), à démontrer une fois le complexe de Čech expérimental construit (cf *Ce que ce document n'est* ci-dessous). Cette grille en tire trois régiments de lecture, distincts et complémentaires, que chaque substrat déjà instrumenté (tri auto-organisé, réaction-diffusion, Axelrod, grokking, Jeu de la Vie) peut traverser l'un après l'autre.

La grille ne remplace pas les mesures. Elle dit, pour une même trajectoire, *quelle question on est en train de poser* à la mesure — et donc quel verdict on en attend, et quel piège on évite en la surinterprétant.

## Les trois régimes

Chaque régime se définit par une question opératoire et un cas concret déjà instrumenté dans le dépôt. On ne mélange pas les régimes sur une même mesure : c'est précisément quand on les confond qu'une intuition séduisante devient un fantôme statistique.

### 1. Invariants — *ce qui se transporte*

> **Question.** *Qu'est-ce qui reste constant d'un substrat à l'autre ?* Qu'est-ce qui survit au changement de matériau — du tri auto-organisé à la réaction-diffusion, d'Axelrod à un LLM ?

L'invariant n'est pas un nombre : c'est ce qui *se recolle* quand on change d'ouverture. En langue grothendieckienne, ce sont les sections globales — `H⁰`, le cran où le local se globalise sans reste. Le dépôt possède l'instrument qui les calcule : le module [`SheafCohomology`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/Grothendieck/SheafCohomology/Basic.lean) du lake `grothendieck_lean` (`H0_equiv_global_sections`, [Mayer-Vietoris](../../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/Grothendieck/SheafCohomology/MayerVietoris.lean) exact, zéro `sorry` de production).

**Cas concret instrumenté.** [ICT-1-PhiTrajectories](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-1-PhiTrajectories.ipynb) : $\Phi$ comme invariant mesuré cross-substrat, suivi le long d'un attracteur. La trajectoire de $\Phi$ est ce qu'on cherche à transporter d'un substrat à l'autre — la *photographie IIT mise en mouvement*. Ce régime demande : *existe-t-il, à travers les substrats, une grandeur dont la trajectoire se recolle ?* La réponse honnête de la série est **non** — et ce non est précisément ce qui fait basculer dans le régime 3 (obstruction).

**Piège évité.** Confondre « invariant » et « scalaire universel ». L'invariant est une *section qui se recolle* ; exiger un scalaire unique, c'est exiger que toute la classe se ramène à une dimension — une exigence que la série a falsifiée.

### 2. Dissociations — *où les proxys se séparent*

> **Question.** *Où deux mesures, qu'on croyaient alignées, divergent-elles — et que révèle leur séparation ?*

Une dissociation n'est pas un bruit de mesure : c'est le moment où deux proxys, censés suivre la même trajectoire, se séparent. Le motif de la séparation est l'information — il pointe ce que chaque proxy mesure réellement, par contraste avec ce qu'on *voulait* qu'il mesure.

**Cas concrets instrumentés.**

- **ICT-synthèse cross-substrat** (strate 5, [ICT-Series](../../MyIA.AI.Notebooks/IIT/ICT-Series/README.md)) : trois proxys de l'intégration, deux se suivent, un diverge. La dissociation est le résultat, pas un échec.
- [**ICT-18b-ReversibilityBudget**](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-18b-ReversibilityBudget.ipynb) ([#7287](https://github.com/jsboige/CoursIA/issues/7287)) : la réversibilité y est dissociée en un **moyen** (production d'entropie $\sigma$ de Schnakenberg — *mesuré*) et une **fin** (compétence de régénération au sens de Levin — *nommée comme une autre grandeur, jamais mesurée*). Le verdict `P2 DISSOCIATION` capture exactement ce régime : on croyait mesurer « la » réversibilité, on mesurait son coût, pas sa finalité.
- [**ICT-15b-SensitivityCanonicity**](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15b-SensitivityCanonicity.ipynb) ([#7288](https://github.com/jsboige/CoursIA/issues/7288)) : degré spectral et sensibilité de Huang, deux lectures d'une même dynamique, divergent sur la question « lequel est canonique ? ». La dissociation révèle que le choix du proxy *est* un choix de préfaisceau.

**Piège évité.** Lire une dissociation comme un « bruit à corriger ». Réconcilier deux proxys divergents par moyenne les vide de leur information — c'est exactement l'unification prématurée que cette grille interdit.

### 3. Obstructions — *ce qui empêche le recollement*

> **Question.** *Qu'est-ce qui empêche les sections locales de se raccorder en une section globale — et cette impossibilité est-elle stable cross-substrat ?*

L'obstruction n'est pas un échec de méthode : c'est une **structure**. Quand des données locales, chacune cohérente sur son ouvert, refusent de se recoller en un tout global, ce refus est une propriété du réel, et Grothendieck lui a donné nom et mesure : la cohomologie. Au premier cran, ce qui se recolle (`H⁰`) ; au cran suivant, la *classe de l'obstruction* (`H¹`) — nulle quand tout se raccorde, non nulle exactement à la hauteur de ce qui résiste. Le dépôt formalise ce geste (cf [« Quand le recollement échoue »](../grothendieckian-lens.md), grade A sur le langage).

**Cas concrets instrumentés.**

- **Scalaire universel falsifié** (strate 5) : la non-existence d'une section globale recollant tous les proxys = un *candidat* de classe d'obstruction non nulle (la falsification est un fait ; sa lecture comme classe de cohomologie `H¹` est proposée, grade C). *C'est le résultat, pas un manque.*
- [**social_choice_lean**](../../MyIA.AI.Notebooks/GameTheory/social_choice_lean/) : l'impossibilité d'Arrow, 0 `sorry` — le local (préférences individuelles) ne se globalise pas en une fonction de choix, et c'est un théorème.
- [**#7290 Kochen-Specker**](https://github.com/jsboige/CoursIA/issues/7290) : aucune assignation globale non contextuelle n'existe — `H¹ ≠ 0` érigé en impossibilité (lecture cohomologique d'Abramsky-Brandenburger). Le dépôt le pose en problème de contraintes où la section se recolle (SAT) ou se refuse (UNSAT).
- **Jeu de la Vie** ([Lean-16b](../../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-16b-Conway-Game-of-Life-Lean.ipynb) / [-16c](../../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-16c-Conway-Game-of-Life-Golly.ipynb) / [-16d](../../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-16d-Conway-Game-of-Life-Lean-Native.ipynb)) : la règle locale `B3/S23` et la complétude de Turing ne se recollent pas « gratuitement » — l'écart est mesuré, et la preuve du bond HashLife (`hashlife_correct`) vit dans cet écart.

**Piège évité.** Lire une obstruction comme un trou à combler. Combler l'obstruction (forcer un scalaire, moyenné les proxys) détruit l'information qu'elle porte — on revient au régime 2 en pire.

## Le triptyque théorique de fond

Les trois régimes se soutiennent d'un triptyque qui traverse la série :

| Régime | Père théorique | Geste | Point d'ancrage dépôt |
|---|---|---|---|
| Invariants | **Grothendieck** (recollement) | Le local qui se globalise sans reste | [`SheafCohomology`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/Grothendieck/SheafCohomology/Basic.lean), `H⁰` |
| Dissociations | **Schmidhuber** (compression / grokking) | Deux proxys se séparent quand l'un comprime mieux que l'autre | [ICT-17b-Grokking](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-17b-Grokking-CompressionProgress.ipynb) |
| Obstructions | **Thom** (catastrophe) + **Grothendieck** (cohomologie) | Le refus du recollement comme structure informative | Arrow, Kochen-Specker, scalaire falsifié |

Le lien Schmidhuber/dissociations mérite d'être dit : [ICT-17b](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-17b-Grokking-CompressionProgress.ipynb) lit l'apprentissage comme une compression progressive (transition de phase représentationnelle). Quand deux proxys divergent, c'est souvent que l'un a franchi le seuil de compression et l'autre pas — la dissociation *est* la signature d'un grokking partiel. Thom, lui, nomme la bifurcation du mode de représentation (catastrophe), et Grothendieck dit si le nouveau mode se recolle à l'ancien — l'obstruction mesurant ce qui ne se recolle pas.

## Un substrat vu sous les trois régimes : Axelrod

[ICT-13-AxelrodStrategicMorphodynamics](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-13-AxelrodStrategicMorphodynamics.ipynb) se laisse traverser par les trois régimes pour montrer que la grille est opératoire, pas décorative.

- **Invariants.** Qu'est-ce qui se transporte d'un tournoi Axelrod à l'autre, indépendamment des stratégies seed ? Une structure de morphodynamique stratégique — la *forme* du paysage de coopération, pas son contenu.
- **Dissociations.** Deux proxys du « succès » d'une stratégie (score cumulé vs robustesse face à l'invasion) se séparent : une stratégie peut dominer le score et perdre à l'invasion. Le motif de la séparation révèle que « succès » portait deux sens confondus.
- **Obstructions.** Aucune stratégie unique ne recolle en gagnant global sur tous les paysages — la circularité (Condorcet) est une obstruction, et elle est stable. Ce n'est pas un défaut du tournoi ; c'est sa structure.

## Lien vers les chantiers actifs

Cette synthèse ne lance aucun nouveau dispatch. Elle éclaire deux chantiers déjà ouverts :

- **N1 — [#7395](https://github.com/jsboige/CoursIA/issues/7395), l'obstruction comme objet expérimental minimal.** Plutôt que d'ajouter un proxy de plus, stabiliser l'objet qui décrit le *motif* du désaccord entre proxys. Le régime 3 ci-dessus en est le cadre de lecture ; N1 en cherche la réalisation concrète bornée.
- **N2 — [#7396](https://github.com/jsboige/CoursIA/issues/7396), invariants et dissociations sur les trajectoires de *représentations*.** Le pivot états → représentations : l'objet suivi n'est plus l'état du système mais sa représentation interne, apprise. Les régimes 1 et 2 s'y transportent directement — l'invariant devient *ce qui se recolle à travers les représentations*, la dissociation *où deux représentations divergent pour un même état*.

## Ce que ce document n'est pas

- **Pas un théorème.** Grade C-documentaire : la grille est une *direction de lecture*, vérifiable sur des cas concrets, mais la lecture qui fait des divergences ICT des classes de cohomologie est, à ce jour, *proposée*, pas démontrée (cf [« La mer qui monte »](../grothendieckian-lens.md), qui le dit sans fard). Seul le langage cohomologique est au grade A (formalisé, 0 `sorry` de production).
- **Pas une unification.** La grille décrit une famille de phénomènes ; elle ne force pas une théorie unique. Trois régimes distincts, pas un méta-proxy.
- **Pas un nouveau dispatch.** Aucune nouvelle dépendance expérimentale n'est créée ici. Les chantiers N1/N2 existent par ailleurs ; ce document les éclaire, ne les déclenche pas.

## Repères vérifiables

- Série ICT : [`MyIA.AI.Notebooks/IIT/ICT-Series/`](../../MyIA.AI.Notebooks/IIT/ICT-Series/) ([Epic #4588](https://github.com/jsboige/CoursIA/issues/4588)) — strate 5 « scalaire universel falsifié ».
- Doc companion obstruction/recollement : [`docs/grothendieckian-lens.md`](../grothendieckian-lens.md) ([#7299](https://github.com/jsboige/CoursIA/issues/7299)).
- Langage cohomologique formalisé : [`grothendieck_lean/Grothendieck/SheafCohomology/`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/Grothendieck/SheafCohomology/Basic.lean) (0 `sorry` de production).
- Dissociations instrumentées : [ICT-15b](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15b-SensitivityCanonicity.ipynb) ([#7288](https://github.com/jsboige/CoursIA/issues/7288)), [ICT-18b](../../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-18b-ReversibilityBudget.ipynb) ([#7287](https://github.com/jsboige/CoursIA/issues/7287)).
- Obstructions érigées en impossibilité : [`social_choice_lean`](../../MyIA.AI.Notebooks/GameTheory/social_choice_lean/) (Arrow), [#7290](https://github.com/jsboige/CoursIA/issues/7290) (Kochen-Specker).
