# Scripts Tweety archivés — réorganisation one-shot de la série

Ce dossier conserve l'unique script de réorganisation de la série Tweety,
entré dans `_archive/` avec le sweep de renumérotation
[#11840](https://github.com/jsboige/CoursIA/issues/11840) (bande 1, `git mv` atomiques, PR #16002 mergée le
2026-09-15).

## Registre de disposition

| Script | Verdict | Superseded by | Verdict recorded in |
|---|---|---|---|
| `reorganize_tweety.py` | OBSOLETE (one-shot exécuté) — découpait `Tweety-5` en `Tweety-5` (argumentation abstraite, Dung) + `Tweety-6` (argumentation structurée, ASPIC+/DeLP/ABA), puis renommait l'ancien `Tweety-6` en `Tweety-7`. Non rejouable tel quel : la série a depuis été renumérotée et éclatée | `none` (script one-shot, opération terminée) — le résultat vit dans la série courante [`Tweety-06-Structured-Argumentation-*`](../../Tweety-06-Structured-Argumentation-CSharp.ipynb) | En-tête de disposition du fichier ; PR #16002 (`renum(#11840)`) ; ce registre |

## Disposition par fonction

Le script n'a pas de successeur à proprement parler : c'est une opération
d'édition exécutée une fois. La disposition est donc portée fonction par
fonction, comme l'exige la [convention](../../../../../docs/reference/_archive-convention.md).

| Fonction | Devenue | Preuve |
|---|---|---|
| `read_notebook()` / `write_notebook()` | Utilitaires d'E/S one-shot, sans successeur — remplacés dans l'outillage courant par les helpers de `scripts/notebook_tools/` | Aucune référence hors de ce fichier (`git grep`) |
| `create_notebook_from_cells()` | A produit les notebooks de la série découpée ; le résultat est **vivant** dans `Tweety-06-Structured-Argumentation-CSharp.ipynb` et `Tweety-06-Structured-Argumentation-Python.ipynb` (présents sur `main`, renumérotés depuis) | Présence des deux notebooks sur `main` ; titre du script (« Sépare Tweety-5 en deux notebooks ») |
| `main()` | Exécuté une fois, non rejouable tel quel : il opère sur des noms de fichiers d'avant la renumérotation (`Tweety-5`/`Tweety-6`/`Tweety-7` non padés) que la PR #16002 a précisément remplacés | PR #16002 (15 `git mv`, padding zéro + suffixe noyau canonique) |

## Vérifications faites à la mise au standard (2026-09-25)

- **Zéro appelant** — `git grep reorganize_tweety` ne rend, hors de ce dossier,
  que deux mentions **documentaires** dans le [`README.md`](../../README.md) de
  la série (arborescence ligne 448, prose ligne 454) : aucun import, aucun
  appel, aucun chemin d'exécution.
- **Résultat vérifiable** — la cible du script (`Tweety-06-Structured-Argumentation-*`)
  existe sur `main`.
- L'en-tête de disposition a été ajouté à `reorganize_tweety.py` par la même
  passe : le fichier n'en portait pas.