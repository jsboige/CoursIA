import Mathlib
import GradientFlow.Plain
import GradientFlow.Residual

/-!
# GradientFlow — digestion formelle : pourquoi le gradient survit aux blocs résiduels

Tranche de l'EPIC digestion **#13106** (forme *formalisation*, comme le pilote
CHSH #14858 de po-2025 et la grille PFR #14566 de ai-01). Le protocole de
digestion (Tao, ICM 2026 — opération *digérer*) exige, par grain enfant, une
grille à 10 points ; elle est déroulée ici.

1. **Énoncé exact.** Pour une pile « plain » de `n` blocs dérivables dont
   chacun contracte la dérivée (`|f'_k| ≤ c`), la dérivée de la composition
   vérifie `|(f_{n-1} ∘ … ∘ f_0)'| ≤ c ^ n` (`abs_deriv_plainStack_le`), et
   pour `c < 1` la borne tend vers `0` (`plainStack_gradient_vanishes`).
   Pour une pile de blocs résiduels `h ↦ h + f h` avec `c ≤ 1`,
   `(1 - c) ^ n ≤ |(g_{n-1} ∘ … ∘ g_0)'|`
   (`abs_deriv_residualStack_ge`) : le gradient survit géométriquement.
2. **Provenance.** Le raccourci identité : He, Zhang, Ren & Sun, *Deep
   Residual Learning for Image Recognition*, arXiv:1512.03385 (2015) ; la
   lecture ensembliste : Veit, Wilber & Belongie, *Residual Networks Behave
   Like Ensembles of Relatively Shallow Networks*, arXiv:1605.06431 (2016).
   Le contenu digéré est **notre propre notebook**
   `DataScienceWithAgents/04-Vision/4.2-ConvNet-Profonde-Residuelles.ipynb`
   (§3 : mesure du facteur ≈ 0,4/bloc ; §6 : plain 43,1 % vs prenorm 58,4 %
   d'accuracy pairwise sur 3 graines).
3. **Nouveauté réelle.** Premier module du lake (et du dépôt, grep vain) à
   formaliser la mécanique du gradient profond : la paire
   majoration/minoration ci-dessus n'existait sous aucune forme ; les frères
   `Perceptron` (Novikoff) et `PacLearning` (Valiant) couvrent la convergence
   algorithmique et la généralisation, pas l'optimisation.
4. **Carte de dépendances.** Mathlib uniquement (`HasDerivAt.comp`,
   `HasDerivAt.add`, `abs_mul`, `abs_sub_abs_le_abs_add`,
   `Real.tendsto_pow_atTop_nhds_0_nat`, `norm_num`) ; aucune dépendance aux
   modules frères du lake — le module s'ajoute sans coupler.
5. **Trivial condensé vs nouveau développé.** Les briques sont des
   condensés honnêtes (règle de chaîne + induction + monotonie du produit) ;
   ce qui est **neuf** est la paire d'énoncés et le couplage aux ancres
   numériques du cours (`0,4 ^ 20 < 1e-7` côté plain, `3e-5 < 0,6 ^ 20` côté
   résiduel).
6. **Friction naturelle.** Naviguer l'API `Deriv`/`HasDerivAt` (l'ordre des
   arguments de `.comp`, la forme exacte des lemmes d'absolue) ; maintenir
   0-sorry sur des récurrences syntaxiques (la valeur dérivée portée par
   `HasDerivAt` plutôt que ré-exprimée via `deriv`).
7. **Chemin de découverte.** Le notebook 4.2-ConvNet mesure d'abord (pente
   droite en semilog : facteur ~0,4/bloc, `0,4 ^ 20 ≈ 1e-8`), le lake démontre
   ensuite : la mesure précède la preuve, exactement l'ordre que le protocole
   de digestion veut institutionaliser.
8. **Limites.** Modèle jouet 1-D sur `ℝ` : pas de Jacobiennes, pas de valeurs
   propres, pas de pré-norme/LayerNorm. La formalisation capture la survie
   par raccourci identité, **pas** la réparation par normalisation (le
   notebook distingue les deux ; le lake ne couvre que la première).
9. **Raccord corpus.** Notebook `4.2-ConvNet-Profonde-Residuelles` (§3, §6) ;
   lake `learning_theory_lean` (frères `Perceptron`, `PacLearning`) ; README
   du lake mis à jour (section module + références).
10. **Transmission.** Docstrings FR (canoniques) + siblings EN
    (`GradientFlow_en`, convention #4980) ; grille résumée dans le README ;
    ancres numériques vérifiées par `norm_num`.

## Statut

Tranche 1 **livrée** : `Plain.lean` (majoration `c ^ n` + évanouissement +
ancre `0,4 ^ 20`), `Residual.lean` (minoration `(1-c) ^ n` + ancre `0,6 ^ 20`),
tous deux 0-sorry. Extension naturelle (hors périmètre de cette tranche) :
le modèle matriciel (jacobiennes, rayon spectral) et la pré-norme.
-/

namespace GradientFlow

/-- Statut : tranche 1 livrée (digestion #13106) — pile plain majorée par
`c ^ n` (`abs_deriv_plainStack_le`, évanouissement
`plainStack_gradient_vanishes`), pile résiduelle minorée par `(1-c) ^ n`
(`abs_deriv_residualStack_ge`), ancres numériques du notebook 4.2-ConvNet
(`two_fifths_pow_twenty_lt`, `three_fifths_pow_twenty_gt`). Extensions ouvertes
hors périmètre : modèle matriciel (jacobiennes/spectral), pré-norme. -/
abbrev Status : Prop := True

end GradientFlow
