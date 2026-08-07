# Lean 4 — Piège : l'instance `Decidable` ne se propage pas à travers une `def : Prop`

**Date :** 2026-08-07
**Auteur :** myia-po-2026 (PR #9780, Livrable B #9568)
**Portée :** cross-lake — tout wrapper `def ... : Prop` autour d'une Prop qui a une instance `Decidable`.

---

## Résumé

En Lean 4, définir un prédicat comme un wrapper `def` autour d'une proposition qui possède déjà une instance `Decidable` **ne propage pas automatiquement** cette instance à travers le wrapper. Résoudre le prédicat par `by decide` ou `by native_decide` échoue alors avec :

```
failed to synthesize Decidable (mon_predicat témoin)
```

alors même que l'instance sous-jacente existe bel et bien. C'est un piège récurrent
lorsqu'on factorise un prédicat pédagogique ou de fragment au-dessus d'un prédicat
« moteur » du codebase (margin, décidabilité, etc.).

## Pourquoi

Lean ne réduit **pas** une `def` non-`@[reducible]` lors de la synthèse d'instance.
L'unificateur trouve l'instance `Decidable (Prop_sous-jacente x)` pour la tête
`Prop_sous-jacente`, mais le wrapper `mon_predicat` est opaque : l'unificateur ne le
déplie pas pour découvrir l'instance qu'il recouvre. La synthèse échoue donc au niveau
du wrapper, pas de la Prop sous-jacente.

## Les 3 fixes (par ordre de préférence)

### 1. Instance compagnon (pattern canonique du codebase)

Déclarer explicitement l'instance au niveau du wrapper, en se déchargeant sur l'instance
sous-jacente via `inferInstanceAs`. C'est exactement ce que fait le codebase Conway :
`BoxAssezGrandN` déclare sa propre instance au-dessus de l'instance native
(`Conway/Life/HashlifeCorrectness.lean`, ~L227) :

```lean
def BoxAssezGrandN (g : Grid) (n : Nat) : Prop := box_assez_grandN g n = true

instance (g : Grid) (n : Nat) : Decidable (BoxAssezGrandN g n) :=
  inferInstanceAs (Decidable (box_assez_grandN g n = true))
```

Pour un wrapper au-dessus de `BoxAssezGrandN` :

```lean
def supportInMargin (c : MacroCell) (k : Nat) : Prop :=
  BoxAssezGrandN (c.toGrid (0, 0)) (2^k)

instance (c : MacroCell) (k : Nat) : Decidable (supportInMargin c k) :=
  inferInstanceAs (Decidable (BoxAssezGrandN (c.toGrid (0, 0)) (2^k)))
```

### 2. `abbrev` au lieu de `def`

`abbrev` est `@[reducible]` par construction, donc l'instance sous-jacente est trouvée
par réduction. Convient quand le wrapper est purement un alias sans sémantique propre.

### 3. `@[reducible] def`

Même effet que `abbrev`, mais conserve la sémantique de `def`. À utiliser si l'on tient
au mot-clé `def` pour la lisibilité.

## Incident fondateur (PR #9780, Livrable B #9568)

Le prédicat de fragment `supportInMargin c k := BoxAssezGrandN (c.toGrid (0,0)) (2^k)`
(Livrable B #9568) enclenchait 4 sanity-checks `by native_decide` sur le bestiaire :

```lean
theorem cexBlock1_supportInMargin_k0 : supportInMargin cexBlock1 0 := by native_decide
```

Build WSL (v4.31.0-rc1) échouait sur les 4 avec
`failed to synthesize Decidable (supportInMargin cexBlock1 0)`. L'instance
`Decidable (BoxAssezGrandN g n)` existe pourtant (HashlifeCorrectness L227). Fix appliqué :
instance compagnon (option 1), mirroir du pattern `BoxAssezGrandN`. Build repassé vert
(FR 8500 jobs / EN 8500 jobs, EXIT 0).

## Diagnostic — comment le reconnaître

**Signal caractéristique :** `failed to synthesize Decidable (<votre_def> ...)` alors que
la Prop sous-jacente a démontrableement une instance `Decidable`.

**À ne pas faire :** chercher une instance manquante sur le type sous-jacent (elle existe,
c'est le wrapper qui bloque). La cause est la non-réduction de la `def` lors de la
synthèse, pas une instance absente.

**Réflexe :** déclarer l'instance compagnon au niveau du wrapper.

## Voir aussi

- `Conway/Life/HashlifeCorrectness.lean` ~L227 — instance `Decidable (BoxAssezGrandN)`,
  le pattern compagnon de référence.
- PR #9780 — application concrète (`supportInMargin`, Livrable B #9568).
- Issue #9568 — cadrage du fragment « fenêtre à marge » et de l'acceptance B.
- Leçon mémoire `lean-decidable-instance-not-propagated-through-def-prop` (cycle c.939).
