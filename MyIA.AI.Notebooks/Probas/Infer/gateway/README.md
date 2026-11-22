# Gateway TrueSkill — service Kernel Gateway

Deuxième service du **pli 0 v2** de l'Epic #19571 : exposer le carnet jumeau
[`Infer-08b-TrueSkill-Formules-Fermees-Python.ipynb`](../Infer-08b-TrueSkill-Formules-Fermees-Python.ipynb)
en microservice REST via Jupyter **Kernel Gateway** (mode `notebook-http`).
Le carnet reste un cours exécutable : il n'existe pas de second carnet réservé
au service.

## Contrat

`POST /probas/trueskill`

```json
{
  "games": [
    {"teams": [["A", "B"], ["C"]], "ranks": [1, 2]}
  ],
  "initial": {"mu": 25.0, "sigma": 8.3333333333},
  "beta": 4.1666666667,
  "draw_probability": 0.1
}
```

Seul `games` est obligatoire. Les parties sont appliquées dans leur ordre ;
les rangs égaux décrivent un match nul. `initial` et `beta` sont facultatifs
et reprennent par défaut les paramètres du carnet Infer-08.

| Réponse | Signification |
|---|---|
| `{"status": "ok", "data": {"players": {"A": {"mu": 29.2052, "sigma": 7.1945}, ...}}}` | Postérieurs de tous les joueurs |
| `{"status": "invalid", "error": "<motif>"}` | Entrée incohérente ou incomplète |
| `{"status": "error", "error": "<motif>"}` | Défaut interne, notamment cœur indisponible |

Le calcul est l'apprentissage **en ligne** de TrueSkill : une passe par partie,
formes fermées EP et répartition de la mise à jour d'équipe au prorata de la
variance de chaque joueur. Le 1v1 coïncide exactement avec le jumeau C#.
La bibliothèque publique `trueskill`, qui itère EP sur le graphe complet, est
seulement un oracle indépendant dans les tests ; elle n'est pas le moteur du
service.

## Démarrage

```bash
pip install -r requirements.txt
python run_gateway.py                 # port 8897
python run_gateway.py --port 8901     # autre port
python run_gateway.py --check-only    # preflight seul : 0 = prêt, 2 = problème
```

Le lanceur résout son propre dossier, publie `PROBAS_GATEWAY_CORE_DIR` pour la
cellule de préparation du carnet, puis vérifie que le cœur est importable et
expose `solve_request` **avant** de démarrer. Il refuse ainsi un service dont
`/_api/spec/swagger.json` répondrait 200 alors que l'endpoint resterait muet
(défaut mesuré sur le précédent Z3, issue #22439).

Le lancement manuel reste possible depuis ce dossier :

```bash
python -m kernel_gateway \
  --KernelGatewayApp.api=kernel_gateway.notebook_http \
  --KernelGatewayApp.seed_uri=../Infer-08b-TrueSkill-Formules-Fermees-Python.ipynb \
  --KernelGatewayApp.port=8897 \
  --JupyterWebsocketPersonality.list_kernels=True
```

Le paquet PyPI s'appelle `jupyter_kernel_gateway`, mais son module s'importe
`kernel_gateway`.

## Exemples réellement exécutés le 2026-11-18

Victoire de A sur B, tous deux au prior :

```bash
curl -X POST -H "Content-Type: application/json" \
  -d '{"games":[{"teams":[["A"],["B"]],"ranks":[1,2]}]}' \
  http://127.0.0.1:8897/probas/trueskill
```

```json
{"status":"ok","data":{"players":{"A":{"mu":29.2052,"sigma":7.1945},"B":{"mu":20.7948,"sigma":7.1945}}}}
```

Match 2v2, l'équipe A/B bat C/D : les joueurs gagnants obtiennent
`mu = 27.9735`, les perdants `mu = 22.0265`, avec `sigma = 7.1945`.
Entrée vide `{"games":[]}` :

```json
{"status":"invalid","error":"champ 'games' : liste non vide requise"}
```

Le descripteur OpenAPI est servi sur `/_api/spec/swagger.json`.

## Mode local du carnet

Hors gateway, `REQUEST` est absent : la cellule d'endpoint rejoue le match de
démonstration du cours, puis compare le résultat du service à celui calculé
dans les sections précédentes. Les sorties committées montrent cette vérification
locale ; elles ne prétendent pas qu'un serveur externe était actif pendant
l'exécution Papermill.

## Tests

```bash
python test_trueskill_core.py
python test_run_gateway.py
python test_flagship_endpoint.py
```

Les trois suites couvrent respectivement le calcul et ses cas limites, le
preflight du lanceur, puis la structure et le comportement de la cellule
d'endpoint sous les différentes formes de `REQUEST`. Elles sont câblées dans
`.github/workflows/scripts-tests.yml` ; l'oracle indépendant `trueskill` est
réservé aux tests du cœur.

## Fichiers

| Fichier | Rôle |
|---|---|
| `trueskill_core.py` | Formes fermées EP, apprentissage en ligne et contrat JSON |
| [`../Infer-08b-TrueSkill-Formules-Fermees-Python.ipynb`](../Infer-08b-TrueSkill-Formules-Fermees-Python.ipynb) | Cours, exercices et cellule `# POST /probas/trueskill` |
| `run_gateway.py` | Preflight et démarrage du gateway |
| `test_trueskill_core.py` | Tests du cœur et comparaison indépendante |
| `test_run_gateway.py` | Tests du lanceur |
| `test_flagship_endpoint.py` | Tests structurels et fonctionnels du carnet servi |
| `requirements.txt` | Dépendances du service et de son oracle de test |
