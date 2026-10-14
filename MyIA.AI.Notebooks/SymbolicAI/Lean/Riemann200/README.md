# Riemann 200 — Distillations

Série née du bicentenaire de Bernhard Riemann (17/09/1826 – 20/07/1866), célébré en 2026 par les *Riemann Topic Days* de Göttingen — EPIC [#20403](https://github.com/jsboige/CoursIA/issues/20403). Comme [Serre 100](../Serre100/README.md), c'est un hommage à événement réel ; à la différence de Serre, Riemann a publié peu — et chacun de ses textes a fondé un champ.

Le geste « distillation » : prendre un énoncé ou une construction centrale de Riemann et le rendre **calculé dans une sortie** — l'énoncé devient une expérience numérique vérifiable, démontrable en Lean quand Mathlib le permet (chaque grain grounde ce qui y vit), et exerçable (≥ 3 exercices par notebook).

## Notebooks

| # | Notebook | Source / écho | Outil |
|---|----------|---------------|-------|
| 01 | *(à venir)* | Le mémoire de 1859 : zeta et l'hypothèse — produit eulérien, prolongement, premiers zéros sur la ligne critique | mpmath (`zetazero`) |
| 02 | *(à venir)* | La formule explicite — ψ(x) = x − Σ ρ⁻ˣ/ρ : les zéros font « la musique des premiers » | mpmath |
| 03 | [03-series-rearrangement.ipynb](03-series-rearrangement.ipynb) | Thèse d'habilitation (1854) : séries de Riemann et théorème de réarrangement — convergence conditionnelle mesurée, preuve gloutonne exécutable, hypothèses pré-enregistrées (H1 vitesse, H2 proportion, H3 fini vs infini et série harmonique aléatoire) | Python stdlib + matplotlib |
| 04 | *(à venir)* | L'intégrale de Riemann — née de la même thèse d'habilitation ; sommes de Darboux, passage à la limite mesuré | Python stdlib |
| 05 | *(à venir)* | Sphère de Riemann et Möbius — compactification, transformations conformes | matplotlib ; `RiemannSphere` existe dans Mathlib |
| 06 | *(à venir)* | Surfaces de Riemann — sqrt(z), log(z) : la monodromie rendue visible | Python stdlib |
| 07 | *(à venir)* | Géométrie riemannienne — l'habilitation de 1854 : distances, géodésiques (désendroit [#19333](https://github.com/jsboige/CoursIA/issues/19333)) | Python stdlib |
| 08 | *(à venir)* | Riemann mapping — toute région simplement connexe ≠ ℂ est conforme au disque | Python stdlib |
| 09 | *(à venir)* | Riemann–Lebesgue et Fourier — noyau de Dirichlet, phénomène de Gibbs | Python stdlib + matplotlib |

Le versant **preuves** vivra dans le lake compagnon `riemann200_lean/`, à créer au premier grain Lean de la série (même maison que [`serre100_lean/`](../Serre100/serre100_lean/)).

## Conventions

- Français d'abord, calcul en stdlib pur (aucune dépendance au-delà de matplotlib pour les figures) — mêmes conventions que Serre 100.
- ≥ 3 exercices C.1 par notebook (convention [#2161](https://github.com/jsboige/CoursIA/issues/2161)), exécution complète commitée (C.2).
- Chaque hypothèse quantitative est **pré-enregistrée** avant sa mesure, et le verdict — y compris REFUTÉ — reste dans la sortie.
- Verdict SOTA écrit au body de chaque PR ([#3801](https://github.com/jsboige/CoursIA/issues/3801)).
- Grounding Mathlib par grain : ce qui existe dans Mathlib est cité avec son fichier ; ce qui n'existe pas est dit tel quel (le carnet 03 mesure cette frontière pour le théorème de réarrangement).

## Raccords au dépôt

- [Serre 100](../Serre100/README.md) — carnets 11–15 : le monde pré-analytique que 1854/1859 ont prolongé.
- [ANALYSE](../ANALYSE/) — l'intégrale de Riemann y est un sol (ANALYSE-02 Tao) ; R-04 fera pont, pas doublon.
- [#19333](https://github.com/jsboige/CoursIA/issues/19333) (géométrie différentielle Sheydvasser) et [#18286](https://github.com/jsboige/CoursIA/issues/18286) (formes modulaires Borcherds) — périmètres cités par R-07 et R-01/R-02, frontière vérifiée à chaque grain.
