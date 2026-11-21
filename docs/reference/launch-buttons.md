# Boutons de lancement des pages de carnet (pli 2.3 de l'Epic #27543)

Ce document decrit les **boutons de lancement** que porte chaque page de
carnet du site publie : Codespaces, Colab, JupyterLite. Il decrit l'organe
(`scripts/notebook_tools/launch_buttons.py`), les **mesures** qui
autorisent chaque bouton, et ce que la passe ne fait pas.

Il ne decrit pas le critere d'eligibilite (pli 2.1,
[pyodide-eligibilite.md](pyodide-eligibilite.md)) ni la construction du bundle
(pli 2.2, [jupyterlite-deploy.md](jupyterlite-deploy.md)) : il s'en **sert**.

## Le principe : une eligibilite calculee, jamais posee a la main

Un bouton n'est emis que si la condition qui le justifie est **mesurable sur
l'arbre** au moment du rendu :

| Bouton | Condition | Mesure |
|---|---|---|
| **Codespaces** | le depot a un devcontainer | `.devcontainer/devcontainer.json` present a la racine |
| **Colab** | le carnet est de la famille Python | `language_info.name` fait foi, le nom du `kernelspec` est le repli (meme regle que le critere d'eligibilite) |
| **JupyterLite** | le carnet est publie dans le bundle | il figure dans le **manifeste** du bundle (`_site/jupyterlite/manifest.json`) |

Un carnet qui n'a pas droit a un bouton ne l'a **pas** : le bouton est
absent, jamais grise sans explication. C'est une exigence du pli 2.3
(« les boutons d'un carnet non eligible sont absents, pas grises sans
explication »).

La regle Python est **celle du critere** (pli 2.1) : le nom du noyau
(`ict-py313`, `py310-gpu`, `.net-csharp`) nomme un environnement, pas une
langue ; c'est `language_info.name` qui dit la langue. Les deux lectures
sont comparees mecaniquement par un test sur un echantillon de carnets
reels du depot (`test_la_regle_python_est_celle_du_critere`).

## Aucune URL de lien mort

- l'URL **JupyterLite** est celle du manifeste publie du bundle : c'est le
  bundle lui-meme qui l'a ecrite, elle ne peut pas diverger ;
- l'URL **Colab** est la forme `https://colab.research.google.com/github/<depot>/blob/<branche>/<chemin>` -- celle que le depot sait deja lire
  (`scripts/notebook_tools/check_external_consumer_links.py`, verifie par un
  test) ;
- l'URL **Codespaces** est celle du devcontainer publie, avec le chemin du
  `devcontainer.json` en parametre.

## La passe : post-rendu, dans la pipeline de publication

La passe agit sur `_site/`, **jamais** sur les sources du depot : c'est le
meme type de passe que la reecriture des liens non servables (#10921). Elle
est **idempotente** (marqueur `data-coursia-launch-buttons`) et elle est
**fail-soft** dans la pipeline : une panne de la passe ne doit pas
empêcher la publication du site (meme doctrine que les decks Slidev et le
lot JupyterLite). Le compte rendu reste dans le log du job.

```bash
python scripts/notebook_tools/launch_buttons.py --site-dir _site --repo-root .
python scripts/notebook_tools/launch_buttons.py --site-dir _site --check   # rc 1 si des insertions sont dues
```

La page de carnet est reconnue par son **carnet source** : une page
`X.html` n'est traitee que si `X.ipynb` existe dans le depot. Les pages de
README, de documentation et les pages du bundle lui-meme ne sont donc pas
touchees.

**Le site construit en local ne porte pas les boutons** : l'injection se
fait dans la pipeline de publication, comme la passe des liens. Le site
**publie** les porte.

## Mesures

Census sur le `main` courant (1 940 carnets suivis), avec le devcontainer du
pli 1.4 present :

| Bouton | Carnets concernees |
|---|---:|
| Codespaces | 1 940 (tous) |
| Colab | 1 472 (famille Python) |
| JupyterLite | 7 (le lot publie dans le bundle) |

Familles de noyau rencontrees : `python` (1 472), `C#` (381), `lean4` (72),
`polyglot-notebook` (11), `Rust` (1), `.net-csharp` (1), deux carnets sans
metadonnees de noyau.

Echantillon verifie **en ligne** (HTTP 200 sur l'URL reelle), un carnet par
famille de noyau :

| Famille | Carnet | Boutons | Etat |
|---|---|---|---|
| python | `CaseStudies/Diagnostic-Medical/solution/Diagnostic-Medical-Python.ipynb` | Codespaces, Colab | 200 / 200 |
| C# | `Complexity/Complexity-01-StepCounting-CSharp.ipynb` | Codespaces | 200 |
| .net-csharp | `SymbolicAI/OR-tools-Stiegler.ipynb` | Codespaces | 200 |
| lean4 | `Compression/Compression_lean/Compression-01b-Kraft-McMillan-Lean.ipynb` | Codespaces | 200 |
| Rust | `Sudoku/Sudoku-02-DancingLinks-Rust.ipynb` | Codespaces | 200 |
| polyglot-notebook | `GenAI/SemanticKernel/fort-boyard-csharp.ipynb` | Codespaces | 200 |

L'URL JupyterLite ne peut etre **verifiee en ligne** qu'apres la publication
du bundle (pli 2.2, #27699) : elle est prise du manifeste, donc egale a
celle que le bundle a publiee.

## Ce que la passe ne fait pas

- elle ne **pose** aucun bouton dans les sources : rien n'est ecrit dans un
  carnet ni dans un README ;
- elle n'invente pas de page JupyterLite : un carnet absent du manifeste
  n'a pas de bouton, meme s'il est eligible au sens du critere ;
- elle ne rend pas le bouton Codespaces disponible sans devcontainer :
  l'absence du devcontainer retire le bouton.

## Tests

```
scripts/notebook_tools/tests/test_launch_buttons.py  (25)
```

Le noyau du carnet, la regle Python (comparee a celle du critere), la
presence/absence de chaque bouton (les trois conditions, chacune dans les
deux sens), les formes d'URL (dont la compatibilite avec l'organe des liens
externes), l'idempotence de l'injection, le repli d'ancre, le fait que la
passe ne touche que les pages de carnet, les codes de sortie (`0` / `1` en
`--check` / `2` instrument casse).

## Voir aussi

- [pyodide-eligibilite.md](pyodide-eligibilite.md) — le critere (pli 2.1)
- [jupyterlite-deploy.md](jupyterlite-deploy.md) — le bundle et son manifeste (pli 2.2)
- `scripts/notebook_tools/launch_buttons.py` — l'organe
- `scripts/ci/quarto_site_link_targets.py` — la passe de reecriture des liens (#10921), meme famille de mechanism
