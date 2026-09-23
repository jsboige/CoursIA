# Opérateurs de Hecke classiques — hecke_lean

Formalisation pédagogique des opérateurs de Hecke classiques `T_p` / `U_p`
sur le demi-plan supérieur, avec la formule induite sur les coefficients
de Fourier, et des théorèmes « l'anneau des entiers de `ℚ(ζₚ)` est
principal » pour `p ∈ {7, 11, 13}`.

## Sources

Port pédagogique (docstrings FR + sibling EN + exemples calculables ajoutés)
du dépôt [`anthropics/fermats-last-theorem`](https://github.com/anthropics/fermats-last-theorem),
commit `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`. Les énoncés et preuves sont
repris tels quels ; seule la documentation et les exemples de la section
`Examples` sont des additions CoursIA.

| Fichier CoursIA | Fichier amont FLT |
|---|---|
| `Hecke/HeckeOperator.lean` (+ sibling `_en`) | `Definitions/Def_ModularForm_HeckeOperator.lean` |
| `Hecke/SevenPid.lean` (+ sibling `_en`) | `P2M/Sol/S_IsCyclotomicExtension_Rat_seven_pid.lean` (tranche 1 de #16557) |
| `Hecke/ElevenPid.lean` (+ sibling `_en`) | `P2M/Sol/S_IsCyclotomicExtension_Rat_eleven_pid.lean` (tranche 2 de #16557) |
| `Hecke/ThirteenPid.lean` (+ sibling `_en`) | `P2M/Sol/S_IsCyclotomicExtension_Rat_thirteen_pid.lean` (tranche 3 de #16557) |
| `Hecke/FltRoute.lean` (+ sibling `_en`) | `P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean` (exercices 3-4 ; les exercices 1-2 et la documentation sont des additions CoursIA, cible #16556) |

## Licence

Le code source est publié sous licence **Apache 2.0** par le dépôt amont ;
ce port préserve cette licence (voir `LICENSE` amont du dépôt FLT). Les
additions CoursIA suivent la même licence.

## Environnement

- Lean : `leanprover/lean4:v4.33.0`
- Mathlib : `db584cd6d46c92f209a44c0f1c829460d327499d`
  (ancre cohérente avec #14773 ; le cache binaire Mathlib est disponible
  pour ce pin — vérifié firsthand dans l'issue #14784).

## Structure

| Fichier | Contenu |
|---------|---------|
| `Hecke/HeckeOperator.lean` | Représentants `heckeMatrix`/`heckeDiagMatrix`, opérateurs `heckeU`/`heckeT`, linéarité, `coeffHeckeT` (p ∣ n / p ∤ n), exemples calculables |
| `Hecke/HeckeOperator_en.lean` | Sibling anglais (namespace `ModularForm_en`), signatures et preuves identiques |
| `Hecke/SevenPid.lean` / `Hecke/ElevenPid.lean` | `ℤ[ζ₇]` / `ℤ[ζ₁₁]` principaux (critère de Marcus, docstrings FR) |
| `Hecke/SevenPid_en.lean` / `Hecke/ElevenPid_en.lean` | Siblings anglais (namespace `CyclotomicPID_en`), preuves identiques |
| `Hecke/ThirteenPid.lean` | `ℤ[ζ₁₃]` principal : lemme `F₂₇`, certificats 13/53/79/131/157, dispatch A-D (docstrings FR) |
| `Hecke/ThirteenPid_en.lean` | Sibling anglais, preuves identiques |
| `Hecke/FltRoute.lean` | La route FLT en exercices guidés : S₂(Γ₀(2)) = 0 prouvé (normalisation de Frey `frey_congr_mod_eight`, courbe de Frey `freyCurve`, indice `[SL₂(ℤ):Γ₀(2)] = 3`, percée de la norme `s2_gamma0_2_eq_zero`, théorème-bilan `flt_of_full_route` — étapes 2-5 admises) |
| `Hecke/FltRoute_en.lean` | Sibling anglais (namespace `FltRoute_en`), preuves identiques |
| `Hecke.lean` / `Hecke_en.lean` | Agrégateurs racines |

Hors périmètre (grains aval) : produit de Petersson, cusp forms.
