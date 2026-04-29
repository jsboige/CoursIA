# Social Choice Theory - Lean 4 Formulations

Ce répertoire contient les formalisations mathématiques de la théorie du choix social en Lean 4, développées dans le cadre de la série GameTheory.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Formalisations Lean | 3 théorèmes majeurs |
| Preuves | Complètes et vérifiées |
| dépendances | Mathlib4, Lake |

## Théorèmes formalisés

### 0. DominikPeters/SocialChoiceLean (reference externe)

Un dépôt de référence majeur pour la formalisation du choix social en Lean 4 :

- **Auteur** : Dominik Peters (University of Glasgow)
- **Dépôt** : https://github.com/DominikPeters/SocialChoiceLean
- **Licence** : MIT

Résultats formalisés par Peters :
- **Gibbard-Satterthwaite** : Manipulabilité stratégique implique dictature (>= 3 candidats)
- **Duggan-Schwartz** : Extension au multi-winner avec optimist/pessimist strategyproofness
- **4 impossibilités Condorcet** : Participation, Reinforcement, Strategyproofness, Anon+Neutral+Resolute
- **15+ règles de vote** avec vérification d'axiomes : Split Cycle, Schulze, Copeland, Black, IRV, Borda, etc.

**Intégration dans notre projet** (3 phases) :
1. **Phase 1** (ce dépôt) : Citations et références croisées
2. **Phase 2** : Notebook dédié (`GameTheory-16e-SocialChoiceLean-Tour.ipynb`) + projet Lake séparé (`social_choice_lean_peters/`)
3. **Phase 3** : Portage sélectif dans notre framework `PrefOrder` (impossibilités Condorcet, règles de scoring)

**Différences de framework** :
| Aspect | Notre projet (ChaseNorman) | DominikPeters |
|--------|---------------------------|---------------|
| Type de préférence | `PrefOrder α` (réflexif, total, transitif) | `LinearOrder A` (strict, Mathlib) |
| Règle de vote | `SCC ι σ` (types fixés) | `VotingRule` (polymorphe sur V, A) |
| Toolchain | `v4.28.0-rc1` | `v4.27.0-rc1` |

```

### 1. Théorème d'Impossibilité d'Arrow (Arrow's Impossibility Theorem)

**Dans `SocialChoice/Arrow.lean`** :

- **Énoncé** : Toute fonction de welfare social sur au moins 3 alternatives qui satisfait :
  1. **Faible Pareto** : Si tout le monde préfère x à y, la société aussi
  2. **Indépendance des Alternatives Irrelevantes (IIA)** : Le classement social de x vs y dépend uniquement des classements individuels de x vs y

- **Conclusion** : Doit être une **dictature** (un individu détermine tous les classements sociaux)

- **Structure de la preuve** :
  1. **Lemme extrême** : Si tous placent b en haut ou en bas, la société aussi
  2. **Existence du pivot** : Chaque alternative a un individu pivot
  3. **Troisième étape** : Les pivots deviennent des dictateurs sur les paires non-b
  4. **Quatrième étape** : La dictature partielle s'étend à une dictature complète

### 2. Paradoxe de la Libéralité de Sen (Sen's Liberal Paradox)

**Dans `SocialChoice/Sen.lean`** :

- **Énoncé** : Aucune procédure de décision sociale ne peut simultanément satisfaire :
  1. **Critère de Pareto faible**
  2. **Libéralisme minimal** : Certains individus sont décisifs sur certaines paires

### 3. Théorème de l'Électeur Médian (Median Voter Theorem)

*À venir*

## Structure des fichiers

```text
social_choice_lean/
├── README.md                          # Documentation générale
├── lakefile.lean                      # Configuration du projet Lake
├── lean-toolchain                     # Version de Lean (v4.28.0-rc1)
├── SocialChoice.lean                  # Fichier d'imports principaux
├── SocialChoice/                      # Module principal
│   ├── Basic.lean                    # Définitions de base (P, I, PrefOrder, Profile)
│   ├── Arrow.lean                   # Théorème d'Arrow (Geanakoplos 2005)
│   ├── Sen.lean                     # Paradoxe de Sen (bidirectionnel)
│   └── Voting.lean                  # Définitions de vote (margin, Condorcet, SCC,
│                                     # critères de vote, single-peaked, Split Cycle, clones)
└── examples/
    ├── arrow_simple.lean            # Exemple simple d'Arrow
    └── sen_liberal_paradox.lean     # Exemple du paradoxe de Sen
```

## Dépendances

- **Lean 4** : Version stable (via `lean-toolchain`)
- **Mathlib4** : Bibliothèque standard de mathématiques formelles
- **Lake** : Gestionnaire de paquets pour Lean

## Construction et compilation

```bash
# Récupérer le cache Mathlib (première fois)
lake exe cache get

# Compiler le projet
lake build

# Exécuter les tests
lake test
```

## Concepts clés formels

| Concept | Définition Lean |
|---------|----------------|
| `P R x y` | Préférence stricte : x est strictement préféré à y |
| `I R x y` | Indifférence : x et y sont également classés |
| `PrefOrder α` | Relation de préférence complète et transitive sur α |
| `Profile n α` | Affectation de préférences à n individus sur α |
| `SWF n α` | Fonction de welfare social : profiles → préférence sociale |
| `weak_pareto` | Condition d'unanimité |
| `ind_of_irr_alts` | Indépendance des alternatives irrelevantes |
| `is_dictatorship` | Existence d'un dictateur |

## Intégration avec la série GameTheory

Ces formalisations Lean sont les bases théoriques pour les notebooks :

- **GameTheory-16b-Lean-SocialChoice** : Applications pratiques
- **GameTheory-16c-SocialChoice-Python** : Simulations numériques
- **GameTheory-16e-SocialChoiceLean-Tour** : Tour des résultats de DominikPeters/SocialChoiceLean

## Liens utiles

- [Documentation Mathlib4](https://leanprover-community.github.io/mathlib4_docs/)
- [Référence originale Arrow/Sen](https://github.com/asouther4/lean-social-choice) (Lean 3)
- [DominikPeters/SocialChoiceLean](https://github.com/DominikPeters/SocialChoiceLean) (Lean 4, MIT)
- [Série GameTheory](../README.md)

## Licence

Voir la licence du repository principal.