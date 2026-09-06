# Opérateurs de Hecke classiques — hecke_lean

Formalisation pédagogique des opérateurs de Hecke classiques `T_p` / `U_p`
sur le demi-plan supérieur, avec la formule induite sur les coefficients
de Fourier.

## Source

Port pédagogique (docstrings FR + sibling EN + exemples calculables ajoutés)
du dépôt [`anthropics/fermats-last-theorem`](https://github.com/anthropics/fermats-last-theorem),
fichier `Definitions/Def_ModularForm_HeckeOperator.lean`, commit
`aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`. Les énoncés et preuves sont
repris tels quels ; seule la documentation et les exemples de la section
`Examples` sont des additions CoursIA.

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
| `Hecke.lean` / `Hecke_en.lean` | Agrégateurs racines |

Hors périmètre (grains aval) : produit de Petersson, cusp forms.
