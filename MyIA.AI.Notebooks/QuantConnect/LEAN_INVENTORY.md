# Inventaire des projets Lean 4 — `QuantConnect`

Inventaire transverse des projets de formalisation Lean 4 sous `QuantConnect/`, sur le
modèle de [`GameTheory/LEAN_INVENTORY.md`](../GameTheory/LEAN_INVENTORY.md) et
[`SymbolicAI/Lean/LEAN_INVENTORY.md`](../SymbolicAI/Lean/LEAN_INVENTORY.md). Source de
vérité : corps de l'Epic [#4038](https://github.com/jsboige/CoursIA/issues/4038) +
vérification `firsthand`. Colonne *Sorry (production)* = métrique CI `real` (commentaires
strippés [ligne `--` et bloc `/- -/`] puis `\bsorry\b` — les mentions prose « 0 sorry »
n'entrent pas dans ce compte ; cf. `lean-ci-sorry-filter`).

## Résumé

| Lake | Toolchain | sorry (production) | Modules | Notebook câblé | Classe | Suivi |
|------|-----------|--------------------:|--------:|---------------:|--------|-------|
| `kelly_lean` | v4.32.1 | 0 | 3 | 1 | PEDA/REF | #4052, #4038 |
| **Total** | — | **0** | **3** | — | — | — |

¹ Notebook Lean câblé = `kelly_lean/Kelly_companion_lean.ipynb` (kernel `lean4-wsl`, importe
`Kelly.*`, vérifie chaque énoncé par `#check`). Companion conceptuel Python =
`Kelly_companion.ipynb`. Premier lake Lean de la famille QuantConnect (roadmap #4038 Tier 2,
#4052) — position sizing lié à un résultat formel.

---

## Par lake

### kelly_lean — PEDAGOGIQUE / REFERENCE

**Objectif** : **optimalité du critère de Kelly** — pour un pari de Bernoulli (probabilité
`p` de gain, cote nette `b`), la fraction optimale `f* = (b·p − q)/b` maximise de façon
unique le taux de croissance espéré `g(f) = p·log(1+b·f) + q·log(1−f)`. Prouvé via la
tangente `log t ≤ t − 1`, sans concavité abstraite (roadmap #4038 Tier 2, #4052).

- **Toolchain** : v4.32.1 · **Dépendance** : Mathlib4
- **lib** : `Kelly` (`globs := #[.submodules \`Kelly]`), package `kelly_lean`
- **Modules** : `Kelly/Kelly.lean`, `Kelly/Bet.lean`, `Kelly/Growth.lean` (FR ; jumeaux `_en`
  exclus, i18n #4980)
- **sorry (production)** : **0** (métrique CI `real`, baseline `"0"`).

#### Théorèmes prouvés (0 sorry)

- **`kelly_optimal`** : `f* = (b·p − q)/b` maximise `g` (taux de croissance espéré du
  portefeuille en pari unique).
- **`kelly_unique`** : sur-pari / sous-pari strictement sous-optimaux — unicité de la
  fraction optimale.
- **`kelly_growth_nonneg`**, `kelly_growth_eq_zero_iff` : signe de `g` selon `p`/`q`.
- Lemmes de support : `growthGrad_kelly_zero`, `growth_diff_le`, `winWealth_pos`,
  `loseWealth_kelly`, `pq_add_eq_one` …

#### Honnêteté du périmètre (G.3/G.9)

L'**optimalité du critère de Kelly en pari unique** est prouvée 0 sorry. Ce qui reste
**OPEN (non sorry-backed)**, documenté honnêtement :

- **Kelly multi-périodes / portefeuille continu** — le lake formalise une seule décision,
  pas la trajectoire de répartition dynamique.
- **Fractional Kelly** (facteur de prudence) et l'effet des coûts de transaction (5 bps SPY /
  10 bps crypto) sur `f*`.

## Notes transverses

- **CI** : `.github/workflows/lean-kelly.yml` (`project-path: …/kelly_lean`,
  `sorry-filter-mode: real`, baseline `"0"`), caller de `lean-build.yml@main`. `real` =
  awk canonique (lean-build.yml) — rattrape `exact sorry`, `:= by sorry`, `sorry -- c`, pas
  les mentions prose.
- **i18n (#4980)** : jumeaux `Kelly/Kelly_en.lean` etc. — les comptes sorries et le décompte
  de modules de l'inventaire portent sur les fichiers FR (les `_en` sont exclus).
