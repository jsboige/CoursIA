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
  - `MUH.Boolean` : algèbre de Boole à 2 éléments — **exemples canoniques**
    (F, T, NOT, AND à 4 générateurs + Sheffer NAND à 1 générateur) au sens
    de Tegmark §2a. *L'équivalence Sheffer ↔ 4 générateurs est **hors-scope**
    de cette introduction* ; voir le suivi #16958.
  - `MUH.Cyclic` : groupes cycliques C₂ et C₃ (Tegmark §2b), avec tables
    complètes et preuves par `rfl` ligne par ligne.
  - `MUH.Decidable` : **squelette énumératif** documenté pour le cas restreint
    (arité ≤ 2, cardinal ≤ 3, 1 seul ensemble). Le code livré est un *stub*
    (`decideEq` retourne `nSets == nSets`, `ClosedUnderComp` est `trivial`) —
    **pas** un algorithme haltant. L'implémentation effective reste à faire ;
    voir le suivi #16958.

**Scope réel** de cette PR : (1) formaliser le vocabulaire Tegmark Annexe A
(`Structure` / `Rel` / `Encoding`), (2) exhiber des exemples canoniques
(Boole complet + Sheffer, C₂, C₃), (3) prouver que `Aut(S)` est un
sous-monoïde de `Π i, Sym(S.sizes i)`. *Pas* la décidabilité complète, *pas*
l'équivalence Sheffer/4-gen — claims ouverts à une PR future (#16958).
-/


/-- Sous-bibliothèques de la MUH, exposées en un seul import. -/
import MUH.Structure
import MUH.Encoding
import MUH.Boolean
import MUH.Cyclic
import MUH.Decidable