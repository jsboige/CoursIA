/-!

# Bibliothèque sur les structures mathématiques finies (Annexe A, Tegmark R16)

Bibliothèque **constructive** Lean 4 illustrant la définition d'une *structure
mathématique finie* telle que donnée en Annexe A de Tegmark (2007), *The
Mathematical Universe* ([arXiv:0704.0646](https://arxiv.org/abs/0704.0646)).

Ce module racine est un **agrégateur d'import**. Il joue le rôle d'**entrée
bilingue** pour la convention i18n de l'EPIC #4980, c'est-à-dire qu'il porte
la documentation de la bibliothèque dans ses deux langues de référence. Le
but est de faciliter la lecture par les publics francophones et anglophones
depuis un point d'entrée unique, sans dupliquer la substance tactique : les
modules scientifiques (`MUH.Structure`, `MUH.Encoding`, `MUH.Boolean`,
`MUH.Cyclic`, `MUH.Decidable`) restent monolingues.

## Pourquoi réintroduire la MUH en Lean ?

Tegmark (Annexe A §1) énonce que **l'équivalence de deux structures finies est
décidable par algorithme haltant** — c'est la base de la **CUH** (Computable
Universe Hypothesis) au §VII.E. Formaliser cette décidabilité constructivement
en Lean 4 :

  - **sécurise** le pont entre « structure mathématique » (concept) et
    « programme qui l'engendre » (artefact),
  - **isole** la définition générale de ses exemples (Boolean, C₂, C₃),
  - **illustre** la composition de relations (règle (3) du §1) sans dépendre
    de Mathlib.

C'est ce que cette bibliothèque fait. Les modules :
  - `MUH.Structure` : signature d'une structure finie (sets + relations
    génératrices + arités/types + table de valeurs).
  - `MUH.Encoding` : encodage selon Tegmark §c (`# of sets | # of relations |
    sizes... | rels...`) et complexité `H(s) = Σᵢ log₂(2 + kᵢ)` (§d).
  - `MUH.Boolean` : algèbre de Boole à 2 éléments, avec preuve que la
    définition à 1 générateur (Sheffer / NAND) est équivalente à la définition
    à 8 générateurs (Tegmark §2a).
  - `MUH.Cyclic` : groupes cycliques C₂ et C₃ (Tegmark §2b).
  - `MUH.Decidable` : algorithme énumératif haltant pour décider l'équivalence
    dans le cas restreint (arité ≤ 2, cardinal ≤ 3). -/


/-- Sous-bibliothèques de la MUH, exposées en un seul import. -/
import MUH.Structure
import MUH.Encoding
import MUH.Boolean
import MUH.Cyclic
import MUH.Decidable