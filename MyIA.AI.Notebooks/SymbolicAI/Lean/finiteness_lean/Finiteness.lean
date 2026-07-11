/-!

# Bibliothèque sur la finitude des dérivées symboliques

Bibliothèque **constructive** Lean 4 illustrant l'intuition du théorème de
finitude de **Brzozowski** (1964) sur les dérivées d'expressions régulières,
dans la lignée de la formalisation en cours de Zhuchko, Maarand, Veanes et
Ebner (ITP 2025).

Le module canonique est `Finiteness.Basic` — toute la substance (le type
inductif `Regex`, les prédicats `nullable` / `accepts`, l'opérateur de
dérivée `deriv`, ainsi que des exemples concrets) y est défini.

Ce module racine ne déclare volontairement **aucune** définition : c'est un
*agrégateur d'import*. Il joue le rôle d'**entrée bilingue** pour la
convention i18n de l'EPIC #4980 (cf. ci-dessous), c'est-à-dire qu'il porte
la documentation de la bibliothèque dans ses deux langues de référence. Le
but est de faciliter la lecture par les publics francophones et anglophones
depuis un point d'entrée unique, sans dupliquer la substance tactique : les
modules scientifiques (`Finiteness.Basic`, etc.) restent monolingues.

## Pourquoi réintroduire la finitude ?

Une expression régulière `r` sur un alphabet `α` dérive en un nouvel objet
`D_a(r)` qui reconnaît exactement les mots `w` tels que `a :: w ∈ L(r)`.
Itérée sur les caractères d'un mot, la dérivée effectue la reconnaissance
**sans retour arrière** (« non-backtracking ») : `w ∈ L(r)` ssi la dérivée
de `r` par rapport à `w` est *nullable* (reconnaît le mot vide ε).

Brzozowski (1964) démontre que l'ensemble des dérivées itérées d'une
expression régulière est **fini** — modulo l'équivalence ACI (Associativité,
Commutativité, Idempotence) des unions. C'est cette finitude qui garantit
la **terminaison** et la complexité **linéaire** des reconnaisseurs modernes
(non-backtracking) :

  * .NET `RegexOptions.NonBacktracking` (PLDI 2023) ;
  * **RE#** (POPL 2025, Varatalu / Veanes / Ernits) ;
  * SymPy (submodule `regexp`).

## La formalisation constructive en Lean 4 (ITP 2025)

La formalisation **constructive** complète en Lean 4 — qui construit un
ensemble fini *bornant* l'espace des dérivées modulo l'équivalence — est
due à **Ekaterina Zhuchko, Hendrik Maarand, Margus Veanes, Gabriel Ebner**
(*Finiteness of Symbolic Derivatives in Lean*, ITP 2025), dépôt
[`ezhuchko/finiteness-derivatives`](https://github.com/ezhuchko/finiteness-derivatives).

Sa licence upstream étant incertaine, **ce dépôt ne vendor pas leur code** :
il illustre l'intuition avec des définitions et des exemples originaux,
sans dépendance (pas de Mathlib). Le notebook
[`Lean-14-Finiteness-Derivatives.ipynb`](../../Lean-14-Finiteness-Derivatives.ipynb)
développe la présentation pédagogique et fait le pont avec l'épopée Conway
#2162.

---

# Library on the finiteness of symbolic derivatives

A **constructive** Lean 4 library illustrating the intuition behind
**Brzozowski's** (1964) finiteness theorem for derivatives of regular
expressions, in line with the in-progress formalisation by Zhuchko,
Maarand, Veanes, and Ebner (ITP 2025).

The canonical module is `Finiteness.Basic` — it carries the full substance
(the inductive type `Regex`, the predicates `nullable` / `accepts`, the
derivative operator `deriv`, plus concrete examples).

This root module deliberately declares **no** definition: it acts as an
*import aggregator*. It plays the role of a **bilingual entry point** for
EPIC #4980's i18n convention (see below), i.e. it carries the library
documentation in its two reference languages. The goal is to ease reading
for both Francophone and Anglophone audiences from a single entry point,
without duplicating the tactical substance: the scientific modules
(`Finiteness.Basic`, etc.) remain monolingual.

## Why reintroduce finiteness?

A regular expression `r` over an alphabet `α` derives into a new object
`D_a(r)` that recognises exactly the words `w` such that `a :: w ∈ L(r)`.
Iterated over the characters of a word, the derivative performs recognition
**without backtracking**: `w ∈ L(r)` iff the derivative of `r` with respect
to `w` is *nullable* (recognises the empty word ε).

Brzozowski (1964) proves that the set of iterated derivatives of a regular
expression is **finite** — modulo ACI equivalence (Associativity,
Commutativity, Idempotence) of unions. It is this finiteness that guarantees
the **termination** and **linear** complexity of modern (non-backtracking)
recognisers:

  * .NET `RegexOptions.NonBacktracking` (PLDI 2023);
  * **RE#** (POPL 2025, Varatalu / Veanes / Ernits);
  * SymPy (`regexp` submodule).

## The constructive Lean 4 formalisation (ITP 2025)

The complete **constructive** formalisation in Lean 4 — which constructs a
finite set *bounding* the derivative space modulo equivalence — is due to
**Ekaterina Zhuchko, Hendrik Maarand, Margus Veanes, Gabriel Ebner**
(*Finiteness of Symbolic Derivatives in Lean*, ITP 2025), repository
[`ezhuchko/finiteness-derivatives`](https://github.com/ezhuchko/finiteness-derivatives).

As its upstream licence is unconfirmed, **this repository does not vendor
their code**: it illustrates the intuition with original definitions and
examples, with no dependency (no Mathlib). The notebook
[`Lean-14-Finiteness-Derivatives.ipynb`](../../Lean-14-Finiteness-Derivatives.ipynb)
develops the pedagogical presentation and the bridge to the Conway epic
#2162.

---

# Convention i18n (EPIC #4980, décision user 2026-07-04)

Ce fichier racine `Finiteness.lean` est un **agrégateur bilingue inline** :
la documentation est portée à la fois en français (canonique) et en anglais
(miroir). Le code tactique, en revanche, est monolingue (anglophone) pour
la compatibilité avec Mathlib et les outils Lean — il vit dans les modules
scientifiques (ex. `Finiteness.Basic`) qui restent non dupliqués.

Pour les modules de substance (non-agrégateurs), la convention recommandée
est :

  * `Foo.lean` — version canonique (FR-first si l'auteur est francophone,
    ou dans la langue de l'auteur sinon).
  * `Foo_en.lean` — optionnel, **miroir EN** dans le namespace suffixé
    `_en`, imports suffixés `_en` pour éviter toute collision (anti-name
    clash). Le contenu non-docstring est strictement byte-identique à
    celui de `Foo.lean` — c'est la base de la détection automatique de
    drift par CI.

Cette asymétrie (agrégateur bilingue inline vs substance à sibling `_en`)
suit la pratique déjà adoptée dans 6/11 lakes au 2026-07-10 (pilote
`CooperativeGames.lean` MERGED, et autres lacs : Sudoku, ML
`learning_theory`, kelly, astar, minimax).

Hors-scope : `.lake/packages/`, `_peters/`, fixtures, libraries vendored.

-/

import Finiteness.Basic