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
python run_gateway.py                 # port 8899
python run_gateway.py --port 8900     # autre port
python run_gateway.py --check-only    # preflight seul : 0 = prêt, 2 = problème
```

`run_gateway.py` se place dans **son propre dossier** avant de démarrer le
gateway, publie ce dossier dans `Z3_GATEWAY_CORE_DIR` pour la cellule de
préparation du carnet, et **vérifie le cœur avant de démarrer** (issue #22439).
Il peut donc être lancé depuis n'importe quel répertoire : c'est la forme à
préférer, y compris depuis un script d'orchestration qui ne se place pas dans
le dossier.

Le lancement manuel reste possible, mais **doit se faire depuis ce dossier** :

```bash
cd MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/gateway
python -m kernel_gateway \
  --KernelGatewayApp.api=kernel_gateway.notebook_http \
  --KernelGatewayApp.seed_uri=z3-sudoku-service.ipynb \
  --KernelGatewayApp.port=8899 \
  --JupyterWebsocketPersonality.list_kernels=True
```

`python -m kernel_gateway` est équivalent à `jupyter kernelgateway` quand le
dossier `Scripts` du Python est dans le `PATH`. `list_kernels=True` est requis
par le mode `notebook-http`.

Le paquet PyPI s'appelle `jupyter_kernel_gateway`, mais **son module s'importe
`kernel_gateway`** : un `pip install` qui répond « already satisfied » pendant
que `import jupyter_kernel_gateway` échoue ne signale aucune installation
manquante.

Journal de démarrage mesuré (2026-10-16) :

```
[I 2026-10-16 12:37:50.453 KernelGatewayApp] Registering resource: /sudoku/solve, methods: (['POST'])
[I 2026-10-16 12:37:50.453 KernelGatewayApp] Registering resource: /_api/spec/swagger.json, methods: (GET)
[I 2026-10-16 12:37:50.454 KernelGatewayApp] Jupyter Kernel Gateway 3.0.1 is available at http://127.0.0.1:8899
[I 2026-10-16 12:37:50.893 KernelGatewayApp] Kernel started: 52ddee1d-c49f-4c47-ba5b-71660dc91fc8
```

## Échec de démarrage — ce que voit l'opérateur

Si le kernel meurt au *seed*, Kernel Gateway **ne s'arrête pas** : il enregistre
la ressource, sert `/_api/spec/swagger.json` en 200, et laisse `POST
/sudoku/solve` sans réponse — le client expire sans distinguer une panne d'un
calcul lent (mesuré le 2026-10-25, issue #22439). La cause n'apparaît que dans
la trace Tornado du journal.

C'est ce que `run_gateway.py` supprime : le preflight refuse de démarrer quand
le cœur manque, n'est pas importable ou n'expose pas `solve_request`, avec un
code retour `2` et la cause en clair.

```
$ python run_gateway.py --check-only          # depuis le bon dossier
[gateway] preflight OK : <dossier gateway>

$ python run_gateway.py --check-only          # cœur absent
[gateway] coeur absent : <dossier>/z3_sudoku_core.py
[gateway] demarrage refuse : dans cet etat le service repondrait 200
sur /_api/spec/swagger.json sans jamais repondre sur /sudoku/solve (voir #22439).
$ echo $?
2
```

Corollaire pour un client : `swagger` en 200 **ne prouve pas** que le kernel est
prêt. C'est `/sudoku/solve` qui le prouve.

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
python test_run_gateway.py
```

`test_z3_sudoku_core.py` : 12 tests (validation d'entrée, résolution,
insatisfiable, respect des indices), sans réseau ni service.
`test_run_gateway.py` : 9 tests du lanceur (résolution du dossier indépendante
du répertoire courant, cœur absent ou cassé refusé avant démarrage, `--check-only`
qui sort 0 sur le dossier livré et 2 sur un dossier vide).
Les deux fichiers sont câblés dans `.github/workflows/scripts-tests.yml`
(job pytest, avec `z3-solver`).

## Fichiers

| Fichier | Rôle |
|---|---|
| `z3_sudoku_core.py` | Cœur : validation, modèle Z3, contrat JSON (repris du carnet phare) |
| `z3-sudoku-service.ipynb` | Carnet de service `notebook-http` (endpoint `# POST /sudoku/solve`) |
| `run_gateway.py` | Lanceur : preflight, dossier servi, démarrage (#22439) |
| `test_z3_sudoku_core.py` | Tests unitaires du cœur (CI) |
| `test_run_gateway.py` | Tests du lanceur (CI) |
| `requirements.txt` | `z3-solver`, `jupyter_kernel_gateway` |

## Notes d'implémentation

- Le carnet s'exécute aussi **hors gateway** (mode local) : l'endpoint retombe
  alors sur le puzzle de démonstration du carnet phare — c'est ce que montrent
  les sorties enregistrées dans le carnet.
- Sous Kernel Gateway 3.x, la variable injectée `REQUEST` est une **chaîne
  JSON** (sérialisée deux fois côté serveur) ; le carnet accepte chaîne et
  dictionnaire pour rester compatible entre versions.