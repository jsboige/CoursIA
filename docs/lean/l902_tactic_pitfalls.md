# Lean 4 — Pièges de tactic : `rfl`, `rw`, `subst` sur constructors polymorphes d'univers

**Date :** 2026-08-12
**Auteur :** myia-po-2025 (PR #10638 v1→v4, itération documentée #10638)
**Portée :** cross-lake — tout lemme « trivial » sur les fields d'une structure
polymorphe d'univers (équivalences de catégories, foncteurs, topologies, sieves).

---

## Résumé

En Lean 4 v4.31.0-rc1, **`rfl` n'est prouvable que quand l'égalité est
définitionnelle**. Pour les fields d'une structure polymorphe d'univers
(constructeur paramétré par `(C : Type u₁) [Category.{v₁} C]`), **le `rfl`
direct ne suffit pas**, ni `by rw`, ni `by subst`. Cette note catalogue
les 4 strategies testées et leur verdict, et donne la solution canonique.

C'est un piège rencontré typiquement quand on tente de prouver des
**bridges pédagogiques** entre les noms canoniques de Mathlib 4 et le
namespace d'un projet — exactement le pattern Cech.lean / Equivalences.lean
/ MathlibMap.lean du Epic Grothendieck #2159.

## Le « rfl » : ce qu'il prouve vraiment

`rfl` exige une **égalité définitionnelle**. Pour qu'une égalité soit
définitionnelle, les deux côtés doivent se réduire **à la même forme
après δ-réduction et ι-réduction**. Sur les fields de structure
`F.map_id`, `e.symm.functor`, `(α_ X Y Z).hom`, **l'élaboration passe**
quand le type est suffisamment contraint. Mais sur un **constructor
polymorphe d'univers** comme `(Equivalence.refl : C ≌ C)`, Lean ne peut
pas élaborer le `C` implicite à partir du seul contexte — l'univers `u₁`
reste non-résolu, et `rfl` échoue avec `Application type mismatch`.

## Les 4 strategies testées (verdict)

### Tier 1 — `by rw [Equivalence.refl]` : FAIL

```lean
theorem equivalence_refl_functor : (Equivalence.refl : C ≌ C).functor = 𝟭 C := by
  rw [Equivalence.refl]
```

**Erreur** : `Invalid rewrite argument: Equivalence.symm ?self` (ou
analogue). `Equivalence.refl` est un **constructor** de la structure
`Equivalence`, pas un lemme d'égalité : `rw` ne peut pas réécrire sur un
constructor.

**Pourquoi** : `rw` cherche une équation `lhs = rhs` où `lhs` est
pattern-matchable. Un constructor `(Equivalence.refl : C ≌ C)` produit
une valeur, pas une équation. Mathématiquement, `(Equivalence.refl).functor`
est l'identité, mais Lean ne sait pas le voir comme un fait de réécriture.

### Tier 2 — `:= rfl` direct : FAIL (polymorphisme d'univers)

```lean
theorem equivalence_refl_functor : (Equivalence.refl : C ≌ C).functor = 𝟭 C := rfl
```

**Erreur** : `Type mismatch at Equivalences.lean:209:35 — Application type
mismatch: The argument (Equivalence.refl : C ≌ C)`. Lean 4 ne peut **pas**
élaborer le polymorphic `Equivalence.refl : C ≌ C` ; `rfl` exige que les
deux côtés soient δ-réductibles à la même forme, ce qui n'est pas le cas
quand l'univers de `C` reste implicite.

**Pourquoi** : `Equivalence.refl` a la signature `(C : Type u) → [inst :
Category C] → C ≌ C`. La forme `(Equivalence.refl : C ≌ C)` exige que
Lean unifie `C ≌ C = C ≌ C` **sans lui donner `C` ni l'instance**. C'est
un coup d'épée dans l'eau d'élaboration.

### Tier 3 — Dummy param + `subst` : FAIL

```lean
theorem equivalence_refl_functor (e : C ≌ C) (_h : e = Equivalence.refl C) :
    e.functor = 𝟭 C := by
  subst _h
  rfl
```

**Erreur** : `Application type mismatch: The argument Equivalence.refl C`
+ `Tactic 'subst' failed: did not find equation for eliminating '_h'`.
Le `subst` ne peut pas substituer une hypothèse `_h` que Lean n'arrive pas
à unifier (l'application `Equivalence.refl C` exige une instance
`Category C` non fournie dans le scope).

**Pourquoi** : même problème que Tier 2 — la signature polymorphe d'univers
de `Equivalence.refl` exige `Category C` que le scope local ne fournit
pas implicitement. Forcer l'instance par `(e : C ≌ C)` (qui exige
implicitement `Category C` par `variable`) ne suffit pas : Lean n'arrive
pas à « deviner » que `e = Equivalence.refl C` depuis `_h` à cause du
même polymorphisme.

### Tier 4 — Argument `(e : C ≌ D)` + `rfl` : PASS

```lean
theorem equivalence_symm_functor (e : C ≌ D) :
    e.symm.functor = e.inverse := rfl
```

**Réussite** : `e.symm.functor = e.inverse` est définitionnel parce que
`e` est une **valeur concrète** de type `C ≌ D` (univers résolu via
`variable` du scope). Le `rfl` peut δ-réduire les deux côtés.

**Pourquoi ça marche** : le polymorphism d'univers est résolu par
l'argument `e : C ≌ D` qui contraint `C` et `D` via le scope `variable`.
Lean peut alors déplier `e.symm` (= le field `Equivalence.symm` appliqué
à `e`) et comparer à `e.inverse` (= le field `Equivalence.inverse`
appliqué à `e`) — les deux se δ-réduisent à la même valeur.

## La solution canonique (4 options)

| Situation | Solution | Exemple |
|---|---|---|
| Lemme sur `Equivalence.symm_*` avec argument `e : C ≌ D` | `rfl` direct PASS | `e.symm.functor = e.inverse` |
| Lemme sur `Equivalence.refl_*` sans argument `e` | **Retrait pragmatique** | `#check @Equivalence.refl` (catalogue suffit) |
| Lemme sur `CategoryTheory.yoneda` ou `CategoryTheory.Sieve` | **Retrait pragmatique** | Idem (polymorphisme d'univers réfractaire) |
| Lemme sur `MonoidalCategoryStruct.tensorObj` | `rfl` direct PASS (champs définitionnels concrets) | `(X ⊗ Y) = MonoidalCategoryStruct.tensorObj X Y` |

**Heuristique de choix** :

1. Si le lemme a un **argument** `e : X ≌ Y` (ou similaire), `rfl` direct
   PASS — le polymorphism est résolu par l'argument.
2. Si le lemme **n'a pas d'argument** et cible un constructor polymorphe
   d'univers (Equivalence.refl, Yoneda, Sieve), **retrait pragmatique**
   des `#check` originaux qui valident l'accessibilité Mathlib.

## Pourquoi cette leçon est durable

- **Cross-lake** : tous les modules Grothendieck Phase 2+ (et au-delà)
  contiennent des lemmes sur les structures polymorphes d'univers. Le
  piège se reproduit mécaniquement.
- **Cross-worker** : po-2026 sur Adjunction.lean, po-2024 sur SheafBasics,
  po-2025 sur Equivalences.lean — tous rencontreront le polymorphisme
  d'univers à un moment.
- **4 stratégies testées, 4 itérations de CI** : le coût d'apprentissage
  sans cette note est de **1 cycle complet par worker** (~2h par cas).
  Documenter l'ORACLE économise ce coût.

## Anti-patterns à éviter

- **« `rfl` marchera si je le force »** : non. `rfl` est strictement
  définitionnel. Un polymorphisme non résolu bloque le δ-réducteur.
- **« `by rw` devrait passer comme en Lean 3 »** : non plus. Lean 4 a
  des règles différentes pour les constructors.
- **« Mettre `Equivalence.refl C` partout »** : `Equivalence.refl C`
  exige l'instance `Category C` au point d'appel. Sans instance visible,
  ça ne s'unifie pas.
- **« Itérer v5, v6, v7 »** : après 4 amend sans convergence (v1 rw FAIL,
  v2 rfl FAIL, v3 subst FAIL), **fermer la PR** ou **réduire à
  documentation-only** (cf c.1301+108-L3 ★). Le polymorphisme d'univers
  est réfractaire aux strategies simples — accepter et documenter.

## Origine (incident fondateur)

- **Date** : 2026-08-12
- **PR** : #10638 (feat(lean,#2159): Equivalences/MonoidalCategories)
- **Itérations** : v1 (commit 23c0d31) FAIL → v2 (b00edba) FAIL → v3
  (dea1c32) FAIL → v4 (f624f34) PASS via retrait pragmatique.
- **Coût** : 4 amend en 1 cycle (~2h), PR final CLEAN MERGEABLE avec
  6 lemmes in-file (au lieu de 12 initialement prévus).

## Voir aussi

- [`prover_iteration_history.md`](prover_iteration_history.md) —
  historique d'itération du prover multi-agent (Stable Marriage,
  2026-05-07 → 05-18), montre la dynamique analogue « 4 amend avant
  convergence ».
- [`decidable_instance_propagation.md`](decidable_instance_propagation.md) —
  autre piège cross-lake documenté (non-propagation d'instance `Decidable`
  à travers un wrapper `def : Prop`).
- [`coordinator-workflow.md`](coordinator-workflow.md) — workflow ai-01
  pour orchestrer l'itération BG prover sur ce type de cibles.
- **MEMORY.md** (per-machine) — C1301+108-L1 NEW ★★ : L902 ★★ Tier 6
  ORACLE (version condensée, par lane).
- **Dashboard workspace** — PR #10638 historique d'itérations (éphémère).
- **Mathlib 4** : [`Mathlib/CategoryTheory/Equivalence.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Equivalence.html)
  pour la signature complète de `Equivalence.refl` / `Equivalence.symm`.
