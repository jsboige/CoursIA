# Problème inverse de Galois — M₂₃ groupe de Galois sur ℚ

Lake `galois_lean` : couche de preuve pour le notebook **Lean-19** (problème inverse de Galois), autour du groupe sporadique de Mathieu M₂₃.

## Contexte

Le préprint [arXiv:2608.08538](https://arxiv.org/abs/2608.08538) (Poonen et al., 9 août 2026) établit que **M₂₃ est un groupe de Galois sur ℚ** — clôture d'un programme de 40 ans. Le user a demandé de vérifier si la formalisation Lean était accessible avec notre bagage.

Deux énoncés, soigneusement distingués dans le notebook :

| Énoncé | Statut |
|--------|--------|
| M₂₃ est un groupe simple d'ordre 10 200 960 | **prouvé** (Lean, sorry-free) |
| M₂₃ est un **groupe de Galois sur ℚ** | **cité, non formalisé** (préprint ; Belyi absent de Mathlib) |

## Ce que ce lake contient

- **`Galois/M23Lean4Web.lean`** (8115 lignes) : version single-file Lean4Web de la preuve M₂₃, *vendored* depuis l'amont [`KitaKen1/finite-simple-groups-lean`](https://github.com/KitaKen1/finite-simple-groups-lean) (Apache-2.0). Démontre `Sporadic.card_M23 : Nat.card M23 = 10200960` et `Sporadic.simple_M23 : IsSimpleGroup M23` par une **chaîne de stabilisateurs à certificats** (Schreier–Sims matérialisé) — pas `native_decide`, pas `sorry`. La simplicité passe par le stabilisateur de point (M₂₂ embarqué) + un certificat de conjugaison excluant le cas régulier d'ordre 23.
- **`Galois.lean`** : agrégateur racine (`import Galois.M23Lean4Web`) — permet au `lean_lib Galois` *bare* (sans `globs`) de builder toute la preuve via la closure d'imports de la racine, sur le pattern conway_lean. Le forme `globs := #[`Galois.*]` déclenche un quirk de trace *job-computation* de lake v4.31.0-rc1 (« some modules have bad imports ») sur ce lac à module unique, alors que tous les modules compilent — la forme bare + agrégateur racine l'évite.

## État

- **Toolchain** : `leanprover/lean4:v4.31.0-rc1`
- **Mathlib** : rev `d568c8c` (v4.31.0-rc1)
- **Sorry** : **0** (mode `real`, comptage Lean-aware) — 0 `sorry` tactique, 0 `native_decide`, 0 `axiom` déclaré
- **Axiomes** : `#print axioms Sporadic.card_M23` / `simple_M23` → `{propext, Classical.choice, Quot.sound}` = whitelist §B
- **Build** : `lake build Galois` SUCCESS exit 0 — cible lib clean via agrégateur racine (1324 jobs ; feasibility gate c.1039 : M23Lean4Web compilé en 241s sous le pin v4.31.0-rc1)
- **Dépendances** : Mathlib 4 uniquement (8 imports `Mathlib.GroupTheory.*`)

## Pourquoi réutiliser l'amont plutôt que réécrire

Per `sota-not-workaround` : refaire une échelle de petits groupes à côté d'une preuve M₂₃ déjà faite (sorry-free, Apache-2.0) serait la **réimplémentation-jouet** interdite. On réutilise l'amont avec attribution. La partie *from-scratch* du lake (notebook Lean-19) porte sur la **pédagogie du problème inverse de Galois** (vérification indépendante du polynôme de degré 23 via sympy, système de Steiner S(4,7,23), vocabulaire SGA1), pas sur la réémergence de la preuve de groupe.

## Attribution

- Amont : Copyright (c) 2026 Kenta. — licence Apache-2.0. Chaque fichier dérivé préserve l'en-tête amont + la note *« AI usage: Developed with assistance from Claude Code (Fable 5, 1M context, high reasoning) »*.
- Le notebook Lean-19 (à venir) documentera explicitement que l'identification `23T5 = M23` (groupe de Galois) requiert Magma propriétaire et n'est **pas** reproduite — seule la vérification du polynôme (degré, irréductibilité, discriminant) est exécutable en sympy.

## Voir aussi

- [Lean-15-Grothendieck-Tribute](../Lean-15-Grothendieck-Tribute.ipynb) — hommage comparable (prouve ce qu'il annonce)
- `grothendieck_lean` — angle SGA1 (π₁ étale, existence de Riemann) pour le chaînon-pont vers la réalisation galoisienne
- EPIC i18n #4980 : siblings `_en` à venir
