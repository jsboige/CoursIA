# Service Kernel Gateway — CFR OpenSpiel

Microservice REST qui expose la résolution **CFR** (*Counterfactual Regret
Minimization*, jeu à information imparfaite) du carnet phare
[GameTheory-13-ImperfectInfo-CFR-Python.ipynb](../GameTheory-13-ImperfectInfo-CFR-Python.ipynb),
via Jupyter **Kernel Gateway** en mode `notebook-http`.

Grain du **pli 0** de l'Epic #19571 (issue #21104). Le carnet pédagogique n'est
pas modifié : ce dossier ajoute un carnet de service à côté.

## Contrat

`POST /gametheory/cfr`

Corps (JSON) :

```json
{"game": "kuhn_poker", "iterations": 300}
```

- `game` : `kuhn_poker` | `leduc_poker` | `matrix_rps`
- `iterations` : entier, 1..5000 (défaut 300 si absent)

Réponse (JSON, HTTP 200) :

```json
{"status": "ok", "game": "kuhn_poker", "iterations": 300,
 "exploitability": 0.003034, "nash_conv": 0.006068,
 "policy": {"<état d'information>": {"<action>": <probabilité>}}}
```

`exploitability` et `nash_conv` sont les mesures de convergence du moteur
(`nash_conv` = 2 × `exploitability` pour un jeu à somme nulle à 2 joueurs) ;
`policy` est la stratégie **moyenne** par état d'information, parcourue sur
l'arbre (les états de chance sont traversés, les terminaux ignorés).

Entrée hors contrat (jeu non supporté, itérations non entières ou hors bornes) :
`{"status": "invalid", "error": "..."}` — le service ne lève jamais d'exception.

## Fichiers

| Fichier | Rôle |
|---|---|
| `openspiel_cfr_core.py` | Coeur du service (chargement du jeu, CFR, sérialisation) — testable hors kernel |
| `openspiel-cfr-service.ipynb` | Carnet de service : cellule de préparation + endpoint annoté `# POST /gametheory/cfr` |
| `test_openspiel_cfr_core.py` | 18 tests du coeur (hors kernel, hors gateway) |
| `requirements.txt` | `open_spiel`, `jupyter_kernel_gateway` |

## Démarrage

```bash
cd MyIA.AI.Notebooks/GameTheory/gateway
pip install -r requirements.txt
python -m kernel_gateway \
  --KernelGatewayApp.api=kernel_gateway.notebook_http \
  --KernelGatewayApp.seed_uri=openspiel-cfr-service.ipynb \
  --KernelGatewayApp.port=8899 \
  --JupyterWebsocketPersonality.list_kernels=True
```

Le carnet s'exécute aussi **hors gateway** (`jupyter nbconvert --execute`) : il
sert alors de démonstration sur `kuhn_poker`, sans `REQUEST`.

## Exemples mesurés

Environnement de la mesure : Python 3.13.14, `open_spiel` 2.0.2,
`jupyter_kernel_gateway` 3.0.1, Windows 11, service sur le port 8901.

Convergence du poker de Kuhn (12 états d'information, sortie réelle) :

```bash
curl -s -H "Content-Type: application/json" \
  -d '{"game":"kuhn_poker","iterations":300}' \
  http://127.0.0.1:8901/gametheory/cfr
```

```json
{"status": "ok", "game": "kuhn_poker", "iterations": 300, "exploitability": 0.003034, "nash_conv": 0.006068, "policy": {"0": {"Pass": 0.811179, "Bet": 0.188821}, "1p": {"Pass": 0.988333, "Bet": 0.011667}, "0pb": {"Pass": 0.998973, "Bet": 0.001027}, "1b": {"Pass": 0.658747, "Bet": 0.341253}, "2p": {"Pass": 0.003333, "Bet": 0.996667}, "2b": {"Pass": 0.001667, "Bet": 0.998333}, "1": {"Pass": 0.975026, "Bet": 0.024974}, "0p": {"Pass": 0.665731, "Bet": 0.334269}, "1pb": {"Pass": 0.470903, "Bet": 0.529097}, "0b": {"Pass": 0.998333, "Bet": 0.001667}, "2": {"Pass": 0.431393, "Bet": 0.568607}, "2pb": {"Pass": 0.001932, "Bet": 0.998068}}}
```

`HTTP 200 en 0.090287s`

Leduc (936 états d'information — l'exploitabilité décroît avec les itérations) :

```bash
curl -s -H "Content-Type: application/json" \
  -d '{"game":"leduc_poker","iterations":100}' http://127.0.0.1:8901/gametheory/cfr
```

```json
{"status": "ok", "game": "leduc_poker", "iterations": 100, "exploitability": 0.095716, "nash_conv": 0.191433, "policy": {… 936 états …}}
```

`HTTP 200 en 4.008677s`

Pierre-papier-ciseaux (jeu à coup simultané, chargé via la transformation
canonique `turn_based_simultaneous_game` — CFR exige un arbre séquentiel) :
l'équilibre trouvé est uniforme, ce qui est le résultat de théorie des jeux
attendu pour ce jeu.

```json
{"status": "ok", "game": "matrix_rps", "iterations": 300, "exploitability": 0.0, "nash_conv": 0.0, "policy": {"Current player: 0\nObserving player: 0. Non-terminal": {"Rock": 0.333333, "Paper": 0.333333, "Scissors": 0.333333}, "Current player: 1\nObserving player: 1. Non-terminal": {"Rock": 0.333333, "Paper": 0.333333, "Scissors": 0.333333}}}
```

`HTTP 200 en 0.034075s`

Entrées hors contrat (aucune exception, le service répond) :

```json
{"status": "invalid", "error": "jeu non supporte: 'poker' (supportes: kuhn_poker, leduc_poker, matrix_rps)"}
{"status": "invalid", "error": "iterations invalides: 0 (entier entre 1 et 5000)"}
{"status": "invalid", "error": "jeu non supporte: None (supportes: kuhn_poker, leduc_poker, matrix_rps)"}
```
`HTTP 200 en 0.040460s` / `0.021308s` / `0.021419s`

## Journal de démarrage (extrait réel)

```
Registering resource: /gametheory/cfr, methods: (['POST'])
Registering resource: /_api/spec/swagger.json, methods: (GET)
Jupyter Kernel Gateway 3.0.1 is available at http://127.0.0.1:8899
Kernel started: 719e69df-acea-4f73-a417-2bd5c95c8664
200 POST /gametheory/cfr (127.0.0.1) 95.87ms
200 POST /gametheory/cfr (127.0.0.1) 3890.75ms
200 POST /gametheory/cfr (127.0.0.1) 29.60ms
200 GET /_api/spec/swagger.json (127.0.0.1) 0.64ms
```

Descripteur OpenAPI servi par le mode `notebook-http` sur
`/_api/spec/swagger.json` : `title: openspiel-cfr-service`, `version: 0.0.0`,
`paths: ['/gametheory/cfr']`.

## Tests

```bash
python test_openspiel_cfr_core.py      # 18 tests
python -m pytest test_openspiel_cfr_core.py -q
```

18 tests : convergence de Kuhn (`exploitability < 0.05`, `nash_conv`
= 2 × exploitability), amélioration avec les itérations, somme des
probabilités par état d'information, déterminisme, RPS via transformation,
Leduc (plus de 100 états d'information), itérations par défaut, et entrées
invalides paramétrées (jeu inconnu, type non textuel, casse différente,
itérations nulles/négatives/hors bornes/non entières/booléennes).

Le coeur est chargé **par chemin de fichier** dans le module de test : la suite
partagée `scripts-tests.yml` tourne en `--import-mode importlib` (pytest.ini),
où le dossier du test n'est pas ajouté à `sys.path` — un import de paquet y
serait une erreur de collecte, qui avorte toute la session pytest et masque les
autres résultats.

## Verdict SOTA

**SOTA-OK** — le service invoque le vrai moteur : `pyspiel.CFRSolver`,
`pyspiel.exploitability` et `pyspiel.nash_conv` d'OpenSpiel, sans
réimplémentation ni substitution. Aucune sortie dégradée n'est committée.

## Notes

- Les clés de `policy` sont les chaînes d'état d'information du moteur
  (`state.information_state_string()`), donc lisibles et stables pour un même jeu.
- `matrix_rps` passe par `turn_based_simultaneous_game(game=matrix_rps())` :
  CFR exige un arbre séquentiel, la forme normale est rejetée telle quelle par
  le moteur.
- Un service Kernel Gateway est **mono-kernel** : les requêtes sont sérialisées
  par le kernel du carnet. Leduc à 100 itérations (~4 s) est le cas le plus
  long mesuré ; `iterations` est borné à 5000 côté service.
