# Prérequis Lean 4 et Mathlib — Social Choice Theory

Ce document liste les prérequis nécessaires pour lire, comprendre et reproduire les preuves formelles du projet `social_choice_lean/`. Trois parcours sont proposés selon le niveau de familiarité avec Lean 4 et Mathlib.

---

## Parcours 1 — Débutant : Découverte de Lean 4

**Public** : Aucune experience Lean ou verification formelle. Connaissances en logique classique (première année universitaire).

**Objectif** : Être capable de lire les definitions de `Basic.lean` et comprendre la structure d'un énoncé Lean.

### Ressources externes

| Ressource | Type | Durée estimée | Contenu |
|-----------|------|---------------|---------|
| [Theorem Proving in Lean 4 (TPIL)](https://lean-lang.org/theorem_proving_in_lean4/) | Livre interactif | 8-10h | Syntaxe, tactiques, types inductifs, typeclasses |
| [Natural Number Game (NNG)](https://adam.math.hhu.de/#/g/leanprover-community/NNG) | Jeu en ligne | 3-4h | Tactiques de base (rw, apply, exact, intro) sur les naturels |
| [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) | Livre interactif | 6-8h | Tactiques avancées, Mathlib, structures algébriques |

### Compétences cibles après ce parcours

- Comprendre les declarations `def`, `theorem`, `lemma`, `example`
- Lire les signatures de type (`ι → PrefOrder σ`)
- Comprendre les typeclasses (`[Fintype ι]`, `[DecidableEq σ]`)
- Utiliser les tactiques de base : `intro`, `exact`, `apply`, `rw`, `simp`, `obtain`

### Modules lisibles

- `Basic.lean` : Definitions de `P`, `I`, `PrefOrder`, `Profile`, `SWF` (lecture partielle)

### Durée totale estimée : 18-22h (lecture seule)

La reproduction des preuves de `Basic.lean` n'est pas realiste a ce niveau — les preuves utilisent des tactiques Mathlib avancées (`ext`, `simp` avec lemmes spécifiques, `Classical.dec`).

---

## Parcours 2 — Intermédiaire : Mathlib pour le choix social

**Public** : Parcours 1 terminé, ou experience préalable avec Lean 4. Bonne maîtrise des mathématiques discretes (relations d'ordre, ensembles finis).

**Objectif** : Comprendre toutes les definitions et la majorite des preuves de `Basic.lean` et `Voting.lean`. Lire les énoncés des théorèmes d'Arrow et de Sen.

### Prérequis Mathlib par module

#### `SocialChoice/Basic.lean`

| Concept Mathlib | Import | Usage dans le module |
|-----------------|--------|---------------------|
| `Finset`, `Finset.card`, `Finset.univ` | `Mathlib.Data.Finset.Basic`, `Mathlib.Data.Finset.Card` | Ensembles finis d'individus et d'alternatives |
| `Reflexive`, `Transitive`, `Total` (relations) | `Mathlib.Logic.Relation` | Axiomes des relations de preference |
| `Relation.TransGen` | `Mathlib.Logic.Relation` | Fermeture transitive pour la preuve d'antisymmetrie |
| `DecidableEq` | `Mathlib.Data.Fintype.Basic` | Décision procedure pour l'égalité sur les alternatives |
| `CoeFun` (coercion) | Standard | Conversion `Profile ι σ → PrefOrder σ` |
| `Classical.dec` | `Mathlib.Tactic` | instances `Decidable` non-constructives |

**Concepts cles** :
- `P R x y` : preference stricte (asymétrique + transitive), définie comme un `And` (pas un type inductif)
- `I R x y` : indifference (reflexive + antisymétrique), définie comme un `And`
- `PrefOrder α` : structure avec champs `refl`, `total`, `trans` — pas une typeclass mais un enregistrement explicite
- `Profile ι σ` : fonction des individus vers les ordres de preference

#### `SocialChoice/Voting.lean`

| Concept Mathlib | Import | Usage dans le module |
|-----------------|--------|---------------------|
| `Fintype`, `Fintype.card` | `Mathlib.Data.Fintype.Card`, `Mathlib.Data.Fintype.Basic` | Comptage des électeurs |
| `Finset.filter`, `Finset.image` | `Mathlib.Data.Finset.Basic` | Filtrage d'électeurs par preference |
| `Finset.sort`, `List.mergeSort` | `Mathlib.Data.Finset.Sort` | Tri des pics pour le Median Voter Theorem |
| `LinearOrder` | `Mathlib.Order.Defs.LinearOrder` | Ensemble d'alternatives ordonne (single-peaked) |
| `List.IsChain` | Standard | Cycles dans les relations (Split Cycle) |
| `Odd` (parité) | Standard | Hypothèse du Median Voter Theorem |
| `Inhabited` | Standard | Valeur par défaut pour `median_peak` |

**Concepts cles** :
- `margin` : différence des comptes pairwise (entier relatif via coercion `ℤ`)
- `SCC ι σ` : Social Choice Correspondence (fonction profiles + ensemble → ensemble choisi)
- Critères de vote : `condorcet_criterion`, `condorcet_loser_criterion`, `pareto_scc`, `monotonicity`
- `single_peaked` : preferences unimodales sur un ensemble linéairement ordonne
- `split_cycle_defeats` : règle de Holliday-Pacuit 2023, annule les defeats les plus faibles dans les cycles

#### `SocialChoice/Arrow.lean`

| Concept Mathlib | Import | Usage dans le module |
|-----------------|--------|---------------------|
| Tous les concepts de `Basic.lean` | Transitif | Réutilise `PrefOrder`, `Profile`, `SWF`, `P`, `I` |
| `Nat.strongRecOn` | Standard | Induction bien fondée pour l'existence du pivot |
| `Nonempty` | Standard | Hypothèses d'existence d'individus/alternatives |
| `Classical.dec` | `Mathlib.Tactic` | Toutes les instances `Decidable` non-constructives |
| `ite` (if-then-else) | Standard | Construction des profils manipulés (`maketop_rel`, etc.) |

**Structure de la preuve** (Geanakoplos 2005) :
1. **Lemme extremal** : Si tous placent b en haut ou en bas, la société aussi
2. **Existence du pivot** : Chaque alternative b a un individu pivot i(b)
3. **Extension** : Le pivot i(b) est dictateur sur les paires ne contenant pas b
4. **Dictature complete** : Tous les pivots coincident → un seul dictateur

**NB** : La reproduction des preuves d'Arrow necessite de maîtriser la manipulation de profils (`maketop_rel`, `makebot_rel`, `makeabove_rel`) et les arguments d'induction bien fondée. C'est le module le plus exigeant du projet.

#### `SocialChoice/Sen.lean`

| Concept Mathlib | Import | Usage dans le module |
|-----------------|--------|---------------------|
| Concepts de `Basic.lean` + `Arrow.lean` | Transitif | Réutilise `P`, `PrefOrder`, `Profile`, `weak_pareto` |
| `ite` + `dite` | Standard | Construction du profil de contre-exemple |
| `Finset.card` comparisons | Standard | Cardinalite des ensembles d'alternatives |

**Concepts cles** :
- `is_decisive_over` : decisivite bidirectionnelle (pas seulement unidirectionnelle comme dans certains textes)
- `minimal_liberal` : au moins 2 individus decisifs chacun sur au moins une paire
- Preuve par cas : paires chevauchantes vs disjointes

### Durée totale estimée : 30-38h (lecture + exercices Mathlib)

Pour reproduire les preuves existantes : **45-55h** supplémentaires. Les preuves d'Arrow.lean (~950 lignes) représentent le gros du travail.

---

## Parcours 3 — Avance : Reproduction et extension

**Public** : Parcours 2 terminé, ou équivalence démontrée. Experience avec les preuves formelles dans un assistant de preuve (Lean, Coq, Agda, Isabelle).

**Objectif** : Reproduire les preuves d'Arrow et de Sen depuis les énoncés. Etendre le framework (nouvelles règles de vote, théorèmes supplémentaires).

### Compétences supplémentaires requises

| Competence | Ressource | Durée |
|------------|-----------|-------|
| Tactiques avancées (`split_ifs`, `ext`, `constructor`, `rcases`) | Mathematics in Lean, chap. 4-5 | 4-6h |
| Manipulation de `Finset` (filter, image, card) | Mathlib docs + exercices | 3-4h |
| Induction bien fondée (`Nat.strongRecOn`, `WellFounded`) | TPIL chap. 8 | 2-3h |
| Profils manipulés (construire des contre-exemples) | Lire `Arrow.lean` en detail | 4-6h |
| Structures de typeclass vs enregistrements | Mathlib docs | 1-2h |

### Extensions possibles

1. **Median Voter Theorem** : Compléter la preuve `sorry` dans `Voting.lean` (comptage Finset + tri)
2. **Nouvelles règles de vote** : Borda, Copeland, Schulze (voir `SCC ι σ`)
3. **Axiomes supplémentaires** : Anonymat, neutralite, resoluteness
4. **Integration DominikPeters** : Porter des résultats depuis `SocialChoiceLean` (Phase 3 du README)

### Durée totale estimée : 50-70h (reproduction complete)

---

## Carte des dependances entre modules

```
Basic.lean          ←   indépendant (definitions fondamentales)
  ↓
Arrow.lean          ←   depend de Basic.lean
  ↓
Sen.lean            ←   depend de Basic.lean + Arrow.lean (réutilise weak_pareto)
Voting.lean         ←   depend de Basic.lean uniquement
```

**Ordre de lecture recommandé** : `Basic.lean` → `Voting.lean` → `Arrow.lean` → `Sen.lean`

L'ordre `Voting.lean` avant `Arrow.lean` est recommandé car :
- `Voting.lean` introduit des concepts plus intuitifs (marge, gagnant de Condorcet)
- Les preuves de `Voting.lean` sont plus courtes et plus accessibles
- `Arrow.lean` est le module le plus exigeant techniquement

---

## Glossaire Lean / choix social

| Terme Lean | Terme choix social | Signification |
|------------|-------------------|---------------|
| `PrefOrder σ` | Ordre de preference | Relation reflexive, totale, transitive sur σ |
| `Profile ι σ` | Profil de preferences | Fonction individus → ordres de preference |
| `SWF ι σ` | Fonction de bien-être social | Profil → preference sociale |
| `SCC ι σ` | Correspondance de choix social | Profil + ensemble → ensemble choisi |
| `P R x y` | Preference stricte | x est strictement prefere a y |
| `I R x y` | Indifference | x et y sont également classes |
| `Fintype ι` | Ensemble fini d'individus | Ensemble avec cardinalite calculable |
| `DecidableEq σ` | Alternatives discernables | On peut decider si deux alternatives sont egales |
| `weak_pareto` | Principe d'unanimite | Si tous preferent x a y, la société aussi |
| `ind_of_irr_alts` | IIA | Independence des alternatives irrelevantes |
| `is_dictatorship` | Dictature | Un individu determine le classement social |
| `margin prof x y` | Marge pairwise | Score net de x contre y |
| `condorcet_winner` | Gagnant de Condorcet | Bat tous les autres en pairwise |
| `single_peaked` | Preferences unimodales | Unicite du pic, monotonie de chaque côté |
| `split_cycle_defeats` | Defaite Split Cycle | Victoire pairwise non bloque par un cycle plus fort |
| `clone_set` | Ensemble de clones | Candidats toujours adjacents dans les classements |

---

## Points d'entrée rapides

**Pour lire les énoncés sans reproduire les preuves** :
1. Ouvrir `Basic.lean`, lire les `def` et `structure` (lignes 1-80)
2. Ouvrir `Arrow.lean`, lire les definitions de `weak_pareto`, `ind_of_irr_alts`, `is_dictatorship`, puis l'énoncé `arrow_impossibility`
3. Ouvrir `Sen.lean`, lire `is_decisive_over`, `minimal_liberal`, puis l'énoncé `sen_impossibility`

**Pour comprendre une preuve spécifique** :
1. Identifier les hypothotheses du théorème
2. Lire les lemmes auxiliaires d'abord (ils sont au-dessus du théorème principal)
3. Suivre la structure de la preuve en ignorant les tactiques Mathlib — se concentrer sur les commentaires pédagogiques

---

## Différence avec le framework DominikPeters/SocialChoiceLean

| Aspect | Notre projet | Peters |
|--------|-------------|--------|
| Type de preference | `PrefOrder α` (reflexif, total, transitif) | `LinearOrder A` (strict, Mathlib) |
| Règle de vote | `SCC ι σ` (types fixes) | `VotingRule` (polymorphe) |
| Preuves d'Arrow | Geanakoplos 2005 (profils manipulés) | Geanakoplos 2005 (variantes) |
| Preuves de Sen | Decisivite bidirectionnelle | Non present |
| Voting.lean | Marges, Condorcet, Split Cycle, clones | 15+ règles avec axiomes |
| Toolchain | `v4.28.0-rc1` | `v4.27.0-rc1` |

Les deux projets sont complementaires : notre framework offre une introduction plus progressive avec des preuves accessibles, tandis que Peters couvre davantage de résultats avec des techniques avancées.
