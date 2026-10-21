# Gateway Z3 Sudoku — service Kernel Gateway

Premier service du **pli 0** de l'Epic #19571 : exposer le carnet phare
[`Z3-02-Sudoku-Python.ipynb`](../Z3-02-Sudoku-Python.ipynb) en microservice REST via
Jupyter **Kernel Gateway** (mode `notebook-http`).

## Contrat

`POST /sudoku/solve`

| Entrée | Sortie |
|---|---|
| `{"puzzle": "<81 caracteres, 0 ou . pour vide>"}` | `{"status": "sat"\|"unsat"\|"invalid", "solution": "<81 caracteres>\|null", "time_ms": <float>}` |

- `sat` : puzzle résolu, `solution` = grille aplatie de 81 chiffres ;
- `unsat` : indices contradictoires (par exemple deux 5 sur une même ligne) ;
- `invalid` : entrée qui n'est pas 81 cases valides (longueur ou caractères).

Les séparateurs (retours ligne, espaces) sont ignorés : une grille collée sur
plusieurs lignes est acceptée.

## Démarrage

```bash
pip install -r requirements.txt
python -m kernel_gateway \
  --KernelGatewayApp.api=kernel_gateway.notebook_http \
  --KernelGatewayApp.seed_uri=z3-sudoku-service.ipynb \
  --KernelGatewayApp.port=8899 \
  --JupyterWebsocketPersonality.list_kernels=True
```

`python -m kernel_gateway` est équivalent à `jupyter kernelgateway` quand le
dossier `Scripts` du Python est dans le `PATH`. `list_kernels=True` est requis
par le mode `notebook-http`.

Journal de démarrage mesuré (2026-10-16) :

```
[I 2026-10-16 12:37:50.453 KernelGatewayApp] Registering resource: /sudoku/solve, methods: (['POST'])
[I 2026-10-16 12:37:50.453 KernelGatewayApp] Registering resource: /_api/spec/swagger.json, methods: (GET)
[I 2026-10-16 12:37:50.454 KernelGatewayApp] Jupyter Kernel Gateway 3.0.1 is available at http://127.0.0.1:8899
[I 2026-10-16 12:37:50.893 KernelGatewayApp] Kernel started: 52ddee1d-c49f-4c47-ba5b-71660dc91fc8
```

## Usage (exemples réellement exécutés le 2026-10-16)

Les `time_ms` viennent d'une exécution sur une machine donnée : ils varient d'une
machine à l'autre, et le contrat ne porte que sur `status` et `solution`.

Puzzle facile du carnet phare (30 indices) :

```bash
curl -X POST -H "Content-Type: application/json" \
  -d '{"puzzle": "530070000600195000098000060800060003400803001700020006060000280000419005000080079"}' \
  http://localhost:8899/sudoku/solve
```

```json
{"status": "sat", "solution": "534678912672195348198342567859761423426853791713924856961537284287419635345286179", "time_ms": 77.37}
```

Puzzle contradictoire — deux 5 sur la première ligne :

```json
{"status": "unsat", "solution": null, "time_ms": 130.38}
```

Entrée invalide — `{"puzzle": "trop court"}` :

```json
{"status": "invalid", "solution": null, "time_ms": 0.046}
```

## OpenAPI

Le descripteur est servi sur `/_api/spec/swagger.json` (chemin de la v3 ;
`/api` rend 404 dans cette version) :

```json
{"swagger": "2.0", "paths": {"/sudoku/solve": {"post": {"responses": {"200": {"description": "Success"}}}}}, "info": {"version": "0.0.0", "title": "z3-sudoku-service"}}
```

## Tests

```bash
python test_z3_sudoku_core.py
```

12 tests (validation d'entrée, résolution, insatisfiable, respect des indices),
sans réseau ni service. Câblés dans `.github/workflows/scripts-tests.yml`
(job pytest, avec `z3-solver`).

## Fichiers

| Fichier | Rôle |
|---|---|
| `z3_sudoku_core.py` | Cœur : validation, modèle Z3, contrat JSON (repris du carnet phare) |
| `z3-sudoku-service.ipynb` | Carnet de service `notebook-http` (endpoint `# POST /sudoku/solve`) |
| `test_z3_sudoku_core.py` | Tests unitaires (CI) |
| `requirements.txt` | `z3-solver`, `jupyter_kernel_gateway` |

## Notes d'implémentation

- Le carnet s'exécute aussi **hors gateway** (mode local) : l'endpoint retombe
  alors sur le puzzle de démonstration du carnet phare — c'est ce que montrent
  les sorties enregistrées dans le carnet.
- Sous Kernel Gateway 3.x, la variable injectée `REQUEST` est une **chaîne
  JSON** (sérialisée deux fois côté serveur) ; le carnet accepte chaîne et
  dictionnaire pour rester compatible entre versions.