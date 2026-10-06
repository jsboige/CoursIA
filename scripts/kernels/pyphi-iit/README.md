# pyphi-iit kernel spec (artefact portable, #17185)

Kernel spec canonique pour la strate Φ des notebooks ICT (cf issue #17185, EPIC #4588).

## Source de verite

L'env canonique est defini par :

- `MyIA.AI.Notebooks/IIT/requirements.txt` -- pins complets (`pyphi==1.2.0`, `numpy>=1.21,<2.0`, `pyemd==0.5.1`)
- `MyIA.AI.Notebooks/IIT/ICT-Series/pyproject.toml` -- `requires-python = ">=3.9,<3.10"`, `pyphi==1.2.0`
- `MyIA.AI.Notebooks/IIT/scripts/setup_pyphi_env.ps1` -- script d'install automatise (conda env `pyphi` + pip install)

L'env conda `pyphi` (Python 3.9) est l'env canonique pour les 4 carnets de la strate Φ :

| Carnet | Outputs venus de |
|---|---|
| `ICT-01-PhiTrajectories-Python` | Python 3.9.25 (PyPhi) |
| `ICT-05-CausalEmergence-Python` | Python 3.9.25 (PyPhi) |
| `ICT-18-ArrowOfTimeReversibilization-Python` | Python 3.9.25 (PyPhi) |
| `ICT-Synthese-CrossSubstrat` | Python 3.9.25 (PyPhi) |

(Source : `scripts/notebook_tools/notebook_env_census.py` sur `MyIA.AI.Notebooks/IIT/ICT-Series/`, 2026-10-06, mesure 77 carnets.)

## Installation

```bash
# 1. Creer l'env conda canonique
conda create -n pyphi python=3.9 -y -c conda-forge --override-channels
conda activate pyphi
pip install -r MyIA.AI.Notebooks/IIT/requirements.txt

# 2. Installer le kernel spec (user-level)
jupyter kernelspec install scripts/kernels/pyphi-iit --name=pyphi-iit --user
```

## Verification

```bash
jupyter kernelspec list         # doit inclure 'pyphi-iit'
jupyter kernelspec list --json   # verifie que argv[0] == "python" (herite du PATH conda)
```

## Utilisation

```bash
jupyter nbconvert --execute --inplace \
  --ExecutePreprocessor.kernel_name=pyphi-iit \
  MyIA.AI.Notebooks/IIT/ICT-Series/ICT-01-PhiTrajectories-Python.ipynb
```

Note (cf kernels-runtime.md § "MCP jupyter-papermill HANG") : Papermill/MCP async ignore `kernel_name` et lit le `kernelspec.name` stocke dans le notebook -- c'est le kernelspec stocke qui determine l'env d'execution. Les 4 carnets strate Φ portent deja `kernelspec.name = "pyphi-iit"` (commit a venir), donc le MCP async executera bien sous Python 3.9.

## Pourquoi pas de chemin absolu dans `argv`

Le kernel.json de cette serie est **delibement portable** : `argv = ["python"]` (pas de chemin absolu). L'env conda `pyphi` place `python` en tete de PATH, donc `python` resout vers l'interpreteur conda quel que soit le chemin d'installation (`~/.conda/envs/pyphi`, `~/miniconda3/envs/pyphi`, `/opt/conda/envs/pyphi`, etc.).

C'est le pattern de portabilite qui manque a la version precedente du kernel spec (`pyphi` local a `/Users/jsboi/.conda/envs/pyphi/python.exe`, chemin machine-dependant) -- mesure 2026-09-21, #17185.

## Pourquoi pas un seul kernel pour toute la serie ICT

La serie ICT a **neuf envs distincts** (census 2026-10-06) -- 77 carnets repartis sur Python 3.9 (4 strate Φ), 3.10 (2), 3.11 (6), 3.12 (9) et 3.13 (55). Normaliser une strate detruit la conformite des autres : 73 carnets sont au-dessus de 3.10, et le pin `pyphi==1.2.0 -> collections.Iterable` (retire en 3.10) bloque toute re-execution. La portee du kernel `pyphi-iit` est donc **restreinte a la strate Φ** (4 carnets), comme precise dans l'issue #17185.

## Voir aussi

- `docs/reference/kernels-runtime.md` section "Serie IIT/ICT -- env canonique pyphi"
- `MyIA.AI.Notebooks/IIT/ICT-Series/pyproject.toml`
- `MyIA.AI.Notebooks/IIT/requirements.txt`
- `MyIA.AI.Notebooks/IIT/scripts/setup_pyphi_env.ps1`
- Issue #17185
- Branch de mesure `test/17185-reexec-phi-env` (ICT-01, ICT-05, ICT-18, ICT-Synthese re-executes sous pyphi39)

## Provenance

- C.1068 (2026-10-06) -- Creation de l'artefact portable et ouverture PR.
- C.1068+ -- re-execution des 4 carnets strate Φ sous `pyphi-iit` + mise a jour `kernelspec.name` dans les carnets.