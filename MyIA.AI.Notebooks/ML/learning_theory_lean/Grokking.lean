/-
# Grokking — théorie effective de l'apprentissage des représentations

Racine de la bibliothèque `Grokking` (issue #16752, tranche R02 du corpus Tegmark
#16741). Formalise les énoncés courts de « Towards Understanding Grokking — An
Effective Theory of Representation Learning » (Liu, Michaud, Tegmark,
arXiv:2205.10343) :

* `Grokking.Effective` — parallélogrammes de représentation : Définition 1 et
  Propositions 1-2 (perte nulle ⟹ parallélogrammes permis ; décodeur injectif ⟹
  formation des parallélogrammes), plus l'ensemble des quadruples permis `P₀`.
* `Grokking.Conservation` — Appendice F : les deux symétries de la perte ℓ₀
  (translation, échelle), la conservation de `Z₀` le long du flot de `ℓ_eff = ℓ₀/Z₀`,
  la conservation de `C` le long du flot de `ℓ₀`, et le terme résiduel
  `dC/dt = (2ℓ₀/Z₀²) • C` que la preuve du papier omet — d'où l'invariance de
  l'hyperplan centré `C = 0`.
-/
import Grokking.Effective
import Grokking.Conservation
