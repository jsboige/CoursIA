# kls_lean — socle KLS pour ANALYSE-05

Lake Lean 4 (Mathlib `v4.32.1`, pin `520045a`) portant les premières
définitions du socle utilisé par la conjecture Kannan–Lovász–Simonovits :
mesure log-concave (Borell), log-concavité fonctionnelle, isotropie,
constante de Poincaré, constante de Cheeger (version frontière **et**
version Minkowski — épaississement `thick`, rapport `minkowskiRatio`,
constante `cheegerMinkowski`) — plus les théorèmes prouvés
`gaussProfile_logConcave` (log-concavité du profil gaussien) et
`thick_Icc` (épaississement exact d'un intervalle compact, le calcul qui
porte l'exemple unidimensionnel du carnet).

## Pourquoi ce lac existe

Audit du 2026-10-07 (#19765) : au pin Mathlib ci-dessus, aucune de ces
notions n'existe (`IsLogConcave` : 0 occurrence toutes casses confondues ;
Poincaré pour mesures : absent ; Cheeger : absent). Le carnet
`../ANALYSE-05-KLS-Lean-Python.ipynb` digère la preuve
Bizeul–Klartag–Lehec (arXiv:2610.05474) et s'appuie sur ce socle pour
énoncer ses objets.

## Ce que le lac ne contient pas (volontairement)

Les énoncés de la chaîne BKL — Théorème 1.1 (`∃ C, C_P(μ) ≤ C`), thin-shell
Chen–Klartag (`Var |X|² ≤ 8n`), germe quadratique Letwin — ne sont **pas**
formalisés ici : leur preuve n'existe dans aucun lac au pin. Ils vivent en
prose commentée dans le carnet, jamais en `sorry`.

## Build

```bash
lake build KLS.Defs
```

Toolchain : `leanprover/lean4:v4.32.1` (elan l'installe à la demande).
