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

La forme recommandée passe par le lanceur, qui fait un pré-vol puis sonde
l'endpoint avant de déclarer le service disponible (voir « Rejeu des deux cas ») :

```bash
pip install -r requirements.txt
python run_z3_sudoku_gateway.py --port 8899
```

La commande brute reste utilisable depuis la racine du dépôt ou n'importe quel
de ses répertoires (le résolveur remonte les parents pour trouver le cœur).
Depuis un répertoire **sans rapport avec le dépôt**, le kernel ne peut pas
deviner où vit le cœur : poser `Z3_SUDOKU_CORE_DIR` explicitement —

```bash
python -m kernel_gateway \
  --KernelGatewayApp.api=kernel_gateway.notebook_http \
  --KernelGatewayApp.seed_uri=z3-sudoku-service.ipynb \
  --KernelGatewayApp.port=8899 \
  --JupyterWebsocketPersonality.list_kernels=True
```

Le **lanceur**, lui, n'a pas cette limite : il résout le dossier du cœur depuis
son propre emplacement et le publie au processus kernel via
`Z3_SUDOKU_CORE_DIR`, que la cellule de préparation du carnet lit en premier
candidat. La passe de main lanceur → kernel est ainsi explicite, et le pré-vol
vert du lanceur prouve bien que le kernel trouvera le cœur.

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

## Rejeu des deux cas

Les deux commandes ci-dessous se lancent **depuis la racine du dépôt** — c'est le
cas qui échouait avant la correction du défaut a (issue #22439).

**Cas nominal.** Le pré-vol charge le cœur et résout le puzzle de démonstration
avant d'ouvrir un port ; la sonde attend ensuite un résultat exploitable :

```bash
python MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/gateway/run_z3_sudoku_gateway.py --check --port 8899
```

```
[pre-vol] coeur charge depuis ...\Z3-API\gateway
[pre-vol] puzzle de demonstration resolu en 82.9 ms
[sonde] service disponible sur http://127.0.0.1:8899/sudoku/solve (status=sat, 78.7 ms)
```

Code de sortie `0`. `--preflight-seul` s'arrête après le pré-vol, sans ouvrir de
port (code `2` si le cœur est introuvable ou casse).

**Cas où le cœur n'est pas chargeable.** Ce que voit l'opérateur, et ce que
reçoit le client — plus de pendaison :

- le lanceur refuse de démarrer : `[pre-vol] ECHEC -- coeur z3_sudoku_core.py
  introuvable ; dossiers essayes : ...`, code de sortie `2`, aucun port ouvert ;
- si le gateway a été démarré à la main (sans lanceur) et que le kernel survit
  sans son cœur, l'endpoint **répond** au lieu de laisser expirer le client :

```json
{"status": "error", "error": "kernel core unavailable", "detail": "module z3_sudoku_core.py introuvable ; dossiers essayes : ..."}
```

Mesuré le 2026-10-25 : réponse en **1,61 s**, là où la même situation laissait
auparavant le client expirer sans aucune réponse (90 s côté client, descripteur
`/_api/spec/swagger.json` à `200` entre-temps).

Le cœur est cherché dans cet ordre : `Z3_SUDOKU_CORE_DIR` si la variable est
posée, puis le répertoire courant, puis le chemin du cœur relativement à chaque
répertoire parent (8 niveaux). La variable d'environnement est le recours
explicite quand le service est lancé depuis un répertoire arbitraire. C'est un
**candidat, pas une contrainte** : si le dossier qu'elle désigne ne porte pas
le cœur, la recherche continue et un avertissement l'indique (pré-vol du
lanceur comme sortie de la cellule de préparation) — l'opérateur sait alors
que sa variable a été ignorée.

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
| `run_z3_sudoku_gateway.py` | Lanceur : pré-vol du cœur + sonde de l'endpoint, codes de sortie 2/3/4 (#22439) |
| `test_z3_sudoku_core.py` | Tests unitaires (CI) |
| `requirements.txt` | `z3-solver`, `jupyter_kernel_gateway` |

## Notes d'implémentation

- Le carnet s'exécute aussi **hors gateway** (mode local) : l'endpoint retombe
  alors sur le puzzle de démonstration du carnet phare — c'est ce que montrent
  les sorties enregistrées dans le carnet.
- Le cœur n'est plus cherché dans `os.getcwd()` seul : la cellule de préparation
  essaie `Z3_SUDOKU_CORE_DIR`, puis le répertoire courant, puis le chemin du
  cœur relativement à chaque répertoire parent. Un import qui échoue **ne tue
  plus le kernel** — la cause est conservée et l'endpoint la restitue, parce
  qu'un kernel mort laissait le pool vide et faisait pendre chaque requête.
- Sous Kernel Gateway 3.x, la variable injectée `REQUEST` est une **chaîne
  JSON** (sérialisée deux fois côté serveur) ; le carnet accepte chaîne et
  dictionnaire pour rester compatible entre versions. Même chose pour le corps
  dans la clé `body` : dict déjà parsé ou chaîne JSON brute (double encodage),
  les deux formes sont décodées — un corps en chaîne non décodé partait
  auparavant tout entier dans le solveur et revenait en `invalid` silencieux.