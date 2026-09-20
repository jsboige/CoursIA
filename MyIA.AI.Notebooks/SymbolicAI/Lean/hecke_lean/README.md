# hecke_lean — Opérateurs de Hecke classiques

Lake Lean 4 autonome dédié aux **opérateurs de Hecke classiques** sur le
demi-plan supérieur : construction explicite des représentants
`γ_{p,j} = !![1, j; 0, p]` et `!![p, 0; 0, 1]`, opérateurs `U_p` et `T_p`
via l'action de slash, linéarité complète (addition, opposé, soustraction,
scalaires), et **formule des coefficients de Fourier**

$$
(T_p f)_n \;=\; a(np) + \begin{cases} p^{k-1}\, a(n/p) & \text{si } p \mid n, \\ 0 & \text{sinon}, \end{cases}
$$

formalisée par `coeffHeckeT` avec ses deux lemmes de lecture
`coeffHeckeT_of_dvd` / `coeffHeckeT_of_not_dvd`, plus des exemples
calculables (poids 12, `p ∈ {2, 3}`).

Le lake porte aussi le théorème **`seven_pid`** : l'anneau des entiers
`𝓞 ℚ(ζ₇) = ℤ[ζ₇]` du 7-ième corps cyclotomique est principal — premier
palier au-delà des `three_pid` / `five_pid` de Mathlib, via le critère de
Marcus (chaque idéal premier `P` au-dessus d'un `p` avec `p ^ f ≤ ⌊M K⌋₊`
est principal).

## Origine

Sous-grain de #14771 (cartographie du dépôt `anthropics/fermats-last-theorem`
pour CoursIA), livré sous #14784. Les modules sont des ports pédagogiques des
fichiers amont (commit `aa2d8b34692b`) : énoncés et preuves repris tels
quels, docstrings FR + sibling EN (`ModularForm_en`, `CyclotomicPID_en`),
exemples calculables ajoutés — voir `NOTICE.md` pour l'attribution Apache-2.0.
`seven_pid` : tranche 1 de #16557 (`eleven_pid` et `thirteen_pid` en tranches
suivantes).

## Compilation

```bash
lake update && lake exe cache get && lake build
```

Cible : Lean `v4.33.0`, Mathlib pin `db584cd6d46c` (ancre #14773).
Aucun `sorry`, aucun `native_decide` ; axiomes des déclarations phares :
`[propext, Classical.choice, Quot.sound]`.

## Structure

| Fichier | Contenu |
|---------|---------|
| `Hecke/HeckeOperator.lean` | Module principal (docstrings FR) |
| `Hecke/HeckeOperator_en.lean` | Sibling anglais, namespace `ModularForm_en` |
| `Hecke/SevenPid.lean` | `ℤ[ζ₇]` est principal (docstrings FR) |
| `Hecke/SevenPid_en.lean` | Sibling anglais, namespace `CyclotomicPID_en` |
| `Hecke.lean` / `Hecke_en.lean` | Agrégateurs racines |

## Suites

Le produit de Petersson et les cusp forms forment un grain aval
(cf. #14784). Les autres sous-grains FLT (complétions adiques #14783,
groupes de ramification #14786…) vivent dans `galois_lean` après la
migration #14773 — ce lake est autonome et n'en dépend pas. Tranches
suivantes de #16557 : `eleven_pid`, `thirteen_pid`.
