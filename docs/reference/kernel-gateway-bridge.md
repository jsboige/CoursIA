# Pont kernel_gateway — contrat du lanceur

> REFERENCE — vivante — dernière révision 2026-11-28

Contrat écrit du pont HTTP [kernel_gateway_service.py](../../scripts/notebook_tools/kernel_gateway_service.py)
(tranche 1 de #27071, issue #28965 — surface 3 « Pilotage » de la note de conception du 17/11,
choix c). Le code est la vérité : chaque point ci-dessous cite le code ; les routes
d'infrastructure sont citées par `git grep` (`SWAGGER_PATH` ligne 24,
`kernel_gateway.notebook_http` ligne 81, `KG_AUTH_TOKEN` ligne 151).

## Ce que le pont est — et n'est pas

Le pont est un **lanceur** : il démarre le [Jupyter Kernel Gateway](https://pypi.org/project/jupyter_kernel_gateway/)
officiel (paquet PyPI `jupyter_kernel_gateway`) en mode `notebook-http`
(`--KernelGatewayApp.api=kernel_gateway.notebook_http`, ligne 81) sur un carnet **existant**.
**Les routes métier ne sont pas portées par le lanceur** : elles sont définies par les
annotations Kernel Gateway du notebook, transmis tel quel comme seed
(`--KernelGatewayApp.seed_uri=<nom du carnet>`, cwd = répertoire du carnet) — le lanceur
« ne reconstitue ni ne réécrit ses routes » (docstring). Le seul endpoint d'infrastructure
que le lanceur lui-même connaît est le descripteur OpenAPI :
`GET /_api/spec/swagger.json` (constante `SWAGGER_PATH`, ligne 24).

## Invariants de sécurité

| Invariant | Mécanisme (code) |
|---|---|
| Loopback uniquement | `_loopback_host` refuse tout `--host` hors `127.0.0.1`, `localhost`, `::1` (`argparse.ArgumentTypeError`) — aucune exposition réseau hors localhost |
| Jeton aléatoire par lancement | `KG_AUTH_TOKEN = secrets.token_urlsafe(32)`, passé à l'enfant par l'environnement (ligne 151) ; requêtes authentifiées par `Authorization: token <jeton>` |
| Pas de dérive de port | `--KernelGatewayApp.port_retries=0` : un port occupé est une erreur dure, jamais un port voisin |
| Identité confirmée avant toute sonde | la sonde sans jeton sur le descripteur **doit** recevoir 401 ; tout autre statut → `EXIT_PROBE` (« identité du serveur non confirmée ») |

## CLI

```
python scripts/notebook_tools/kernel_gateway_service.py <carnet.ipynb> [options]
```

| Argument | Défaut | Contrat |
|---|---|---|
| `carnet` (positionnel) | — | carnet existant ; résolu en chemin absolu |
| `--host` | `127.0.0.1` | loopback uniquement (invariant ci-dessus) |
| `--port` | `8899` | `1..65535` |
| `--check-only` | — | pré-vol seul (seed + dépendances), sans démarrer ; exit 0 si OK |
| `--probe-path` | — | chemin HTTP absolu (`/x`, pas `//`) ; avec `--probe-json`, teste la route après démarrage |
| `--probe-json` | — | corps JSON de la sonde ; **exigé** en POST, **interdit** en GET |
| `--probe-method` | `POST` | `GET` ou `POST` |
| `--probe-timeout` | `30.0` s | délai global de démarrage + enregistrement de la route dans OpenAPI + réponse de la sonde |

Validation des combinaisons (erreurs `parser.error`, exit 2 argparse) : `--probe-json`
exige `--probe-path` ; une sonde GET n'accepte pas `--probe-json` ; une sonde POST exige
`--probe-json`.

## Pré-vol (exit 2)

`preflight()` refuse le démarrage, avec un diagnostic explicite par problème, si :
carnet introuvable · JSON invalide · aucune cellule de code · `kernelspec.name` absent ·
kernel Jupyter déclaré absent de la machine · dépendance absente (`jupyter_client` ou
module `kernel_gateway` — le message donne le nom du paquet PyPI à installer).

## Codes de sortie

| Code | Constante | Signification |
|---|---|---|
| 0 | — | pré-vol OK (`--check-only`) · sonde reçue 2xx · (mode foreground) serveur lancé, laissé en premier plan |
| 2 | `EXIT_PREFLIGHT` | pré-vol refusé (raisons ci-dessus) · démarrage impossible (`OSError`) |
| 3 | `EXIT_PROBE` | route absente du descripteur OpenAPI · descripteur jamais disponible · réponse de sonde non 2xx · identité non confirmée (≠ 401 sans jeton) · échec HTTP/JSON de la sonde. En cas d'échec, les 6000 derniers caractères du log serveur sont imprimés sur stderr |

## Déroulé d'une sonde

1. Le gateway est démarré en enfant (log capturé dans un fichier temporaire).
2. Le lanceur sonde le descripteur OpenAPI jusqu'à l'enregistrement de la route
   (boucle 0,2 s, bornée par `--probe-timeout`).
3. Confirmation d'identité : requête **sans** jeton → 401 exigé.
4. Un seul appel authentifié à la route ; stdout : `HTTP <statut> <MÉTHODE> <chemin>`
   puis le corps JSON trié. Exit 0 si 2xx, sinon 3.
5. Arrêt : `terminate` → attente 5 s → `kill` si nécessaire (`_stop`).

## Exemples

```bash
# Pré-vol seul
python scripts/notebook_tools/kernel_gateway_service.py mon-carnet.ipynb --check-only

# Lancement foreground (Ctrl-C pour arrêter)
python scripts/notebook_tools/kernel_gateway_service.py mon-carnet.ipynb --port 8899

# Sonde de bout en bout (démarrage, appel, arrêt)
python scripts/notebook_tools/kernel_gateway_service.py mon-carnet.ipynb \
  --port 8901 --probe-path /add --probe-json '{"a": 20, "b": 22}' --probe-timeout 25
# stdout attendu : HTTP 200 POST /add  puis  {"status": "ok", "sum": 42}
```

## Test

[`tests/test_kernel_gateway_service.py`](../../scripts/notebook_tools/tests/test_kernel_gateway_service.py)
— 6 tests : 4 contrats unitaires (pré-vol seed absent/cassé, dépendance absente avec nom
d'installation, kernel absent, construction de la commande) + 2 fumées CPU sur une
**fixture jetable hors dépôt** (notebook minimal + kernel isolé dans un répertoire
temporaire, port libre réservé par socket) : une sonde de bout en bout réelle
(démarrage → `POST /add` → `{"sum": 42}` → arrêt) et un port occupé par un autre serveur
(la sonde doit échouer **sans appeler la route de l'autre**). Les 2 fumées sont
`skipUnless` si `jupyter_kernel_gateway` est absent de l'environnement.

Mesure locale (2026-11-28, machine po-2024) : `6 passed in 7.97s` — sous le seuil de
30 s, aucun marquage lent nécessaire (critère #28965).

## Hors périmètre (#28965)

Aucun nouveau service · aucune exposition réseau hors localhost · aucun carnet de cours
(les tests utilisent une fixture jetable, jamais un carnet du dépôt).
