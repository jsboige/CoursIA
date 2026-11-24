# Service Kernel Gateway — MDP (iteration de la valeur et de la politique)

Exposition REST de l'**iteration de la valeur** et de l'**iteration de la politique**
du carnet phare [RL-05 — MDP, programmation dynamique et Q-learning](../RL-05-MDP-Programmation-Dynamique-Q-Learning-Python.ipynb)
— programmation dynamique sur MDP, chapitre 14 d'AIMA.

Feuille de service de l'Epic AIMA-Gateway [#19571](https://github.com/jsboige/CoursIA/issues/19571).
Le carnet pedagogique n'est **pas modifie** : ce dossier `gateway/` ajoute deux carnets
de service a cote, sur le meme motif que les pilotes `GameTheory/gateway/`,
`Probas/Infer/gateway/`, `Z3-API/gateway/` et `NLP/gateway/`.

Deux services, un meme contrat de MDP, un meme gridworld de demonstration :

| Service | Algorithme | `POST` | Mesure sur le gridworld 4x3 |
|---|---|---|---|
| Iteration de la valeur | backups de Bellman | `/rl/mdp-value-iteration` | **133** backups |
| Iteration de la politique | evaluation + amelioration gloutonne | `/rl/mdp-policy-iteration` | **5** cycles d'amelioration |

Sur le meme MDP, les deux convergent vers la **meme** politique et la **meme** valeur
optimales — l'iteration de la politique l'atteint en nettement **moins** de cycles : c'est
le **discriminant** mesurable entre les deux services, visible dans les sorties ci-dessous.

## Contrat

Les deux endpoints partagent le **meme corps** — un MDP complet :

```json
{
  "states":  ["0,0", "0,3", "2,0", "2,3", "..."],
  "actions": ["N", "S", "E", "W"],
  "T":  {"0,0": {"N": {"0,0": 0.9, "0,1": 0.1}, "E": {"0,1": 1.0}, "...": {}}, "...": {}},
  "R":  {"0,0": {"N": -0.04, "E": -0.04, "...": 0.0}, "0,3": {"N": 1.0, "...": 1.0}},
  "gamma": 0.9,
  "theta": 1e-6,
  "max_iterations": 1000
}
```

- `states` : liste de noms d'etats (non vide, sans doublon).
- `actions` : liste de noms d'actions (non vide, sans doublon).
- `T` : `T[s][a][s'] = probabilite` de passer de `s` a `s'` en jouant `a`. Chaque
  `T[s][a]` est une distribution (entrees ≥ 0, somme ≈ 1) ; toute paire `(s, a)` est
  presente (MDP complet).
- `R` : `R[s][a] = recompense immediate` (reel quelconque), presente pour toute paire `(s, a)`.
- `gamma` : facteur d'escompte, `0 <= gamma < 1` (garantit la convergence).
- `theta` : seuil de convergence, > 0 (defaut `1e-6`).
- `max_iterations` : plafond de securite (defaut `1000` pour l'iteration de la valeur,
  `100` pour l'iteration de la politique).

Reponse `POST /rl/mdp-value-iteration` (JSON, HTTP 200) :

```json
{
  "status": "ok",
  "policy":  {"0,0": "E", "0,3": "N", "2,0": "N", "2,3": "W", "...": "..."},
  "value":   {"0,0": 6.7708, "0,3": 10.0, "2,0": 4.0735, "2,3": 5.9828, "...": 0.0},
  "iterations": 133,
  "converged": true,
  "n_states": 10
}
```

- `policy` : action gloutonne optimale par etat (argmax du backup de Bellman).
- `value` : fonction de valeur optimale `V*(s)`.
- `iterations` : nombre de backups de Bellman effectues.
- `converged` : `true` si `theta` est atteint avant `max_iterations`.

Reponse `POST /rl/mdp-policy-iteration` (JSON, HTTP 200) :

```json
{
  "status": "ok",
  "policy":  {"0,0": "E", "0,3": "N", "2,0": "N", "2,3": "W", "...": "..."},
  "value":   {"0,0": 6.7708, "0,3": 10.0, "2,0": 4.0735, "2,3": 5.9828, "...": 0.0},
  "improvement_steps": 5,
  "converged": true,
  "n_states": 10
}
```

- `improvement_steps` : nombre de cycles d'amelioration (evaluation de politique +
  amelioration gloutonne) avant stabilisation.
- La `policy` et la `value` sont **identiques** a celles de l'iteration de la valeur sur
  le meme MDP (verifie par un test dedie).

Entree hors contrat (cles manquantes, `T` non normalise, probabilite negative, `gamma`
hors bornes) : `{"status": "invalid", "error": ...}` — **le service ne leve jamais
d'exception**.

## Fichiers

| Fichier | Role |
|---|---|
| `mdp_value_iteration_core.py` | Cœur du service **iteration de la valeur** : backups de Bellman + politique gloutonne, validation du MDP, `run()`. Testable hors kernel. |
| `mdp-value-iteration-service.ipynb` | Carnet de service : cellule d'entree `# POST /rl/mdp-value-iteration`, demarrage dans le kernel du gateway. |
| `test_mdp_value_iteration_core.py` | **16** tests du coeur (contrat ok / invalid, determinisme, politique gloutonne = argmax, gridworld 4x3). |
| `mdp_policy_iteration_core.py` | Cœur du service **iteration de la politique** : evaluation (rechauffee) + amelioration gloutonne, validation du MDP, `run()`. Testable hors kernel. |
| `mdp-policy-iteration-service.ipynb` | Carnet de service : cellule d'entree `# POST /rl/mdp-policy-iteration`, avec le **discriminant** au nombre de cycles face a l'iteration de la valeur. |
| `test_mdp_policy_iteration_core.py` | **18** tests du coeur, dont les croisements avec l'iteration de la valeur (meme politique/valeur, **moins** de cycles). |
| `requirements.txt` | `jupyter_kernel_gateway`. |

## Demarrage

Un serveur par service (mono-kernel : une feuille = un kernel) :

```bash
# Iteration de la valeur, sur le port 8993
python -m kernel_gateway \
  --KernelGatewayApp.api=kernel_gateway.notebook_http \
  --KernelGatewayApp.seed_uri=mdp-value-iteration-service.ipynb \
  --KernelGatewayApp.port=8993 \
  --JupyterWebsocketPersonality.list_kernels=True
```

```bash
# Iteration de la politique, sur le port 8994
python -m kernel_gateway \
  --KernelGatewayApp.api=kernel_gateway.notebook_http \
  --KernelGatewayApp.seed_uri=mdp-policy-iteration-service.ipynb \
  --KernelGatewayApp.port=8994 \
  --JupyterWebsocketPersonality.list_kernels=True
```

Le kernel demarre **dans ce dossier** : la cellule de preparation charge le coeur par
chemin relatif (`mdp_value_iteration_core.py` / `mdp_policy_iteration_core.py`). Les
carnets s'executent aussi **hors gateway** (`papermill` / `jupyter nbconvert --execute`)
: `kernel_gateway` n'est alors pas importe et la cellule d'entree degrade proprement en
mode demo.

## Exemples mesures

Exeques le 2026-11-24 via papermill (kernel `python3`), hors gateway — les sorties
ci-dessous sont **reelles**, produites par `run()` dans les cellules de demonstration
des carnets de service. Le MDP est le **gridworld 4x3 d'AIMA ch. 14** (2 obstacles,
2 terminaux `+1` / `-1`, cout par pas `-0.04`, bruit 0.8/0.2). En mode gateway, le meme
corps passe par `curl` et recoit la meme reponse.

Payload valide (corps du gridworld 4x3) :

```bash
curl -s -X POST http://localhost:8993/rl/mdp-value-iteration \
  -H "Content-Type: application/json" \
  -d '{ "states": [...], "actions": ["N","S","E","W"], "T": {...}, "R": {...}, "gamma": 0.9 }'
```

Reponse (reelle, extrait) :

```json
{
  "status": "ok",
  "policy":  {"0,0": "E", "0,3": "N", "2,0": "N", "2,3": "W"},
  "value":   {"0,0": 6.7708, "0,3": 10.0, "2,0": 4.0735, "2,3": 5.9828},
  "iterations": 133,
  "converged": true,
  "n_states": 10
}
```

L'iteration de la politique, sur le **meme** MDP, retourne la **meme** politique et la
**meme** valeur, en **5** cycles d'amelioration :

```json
{
  "status": "ok",
  "policy":  {"0,0": "E", "0,3": "N", "2,0": "N", "2,3": "W"},
  "value":   {"0,0": 6.7708, "0,3": 10.0, "2,0": 4.0735, "2,3": 5.9828},
  "improvement_steps": 5,
  "converged": true,
  "n_states": 10
}
```

Entrée hors contrat (distribution de transition non normalisee) — reponse reelle :

```json
{"status": "invalid", "error": "T['0,0']['N']: somme = 0.600000, distribution normalisee (somme ~ 1) attendue"}
```

## Tests

34 tests (16 + 18), tous verts. Chaque test charge son coeur **par chemin de fichier**
(`importlib` + `Path(__file__)`) : la suite partagee `scripts-tests.yml` tourne en
`--import-mode importlib` (`pytest.ini`) et le dossier du test n'est pas ajoute a
`sys.path`, un import par nom echouerait. Les tests de l'iteration de la politique
croisent aussi l'iteration de la valeur : sur un meme MDP, meme politique, meme valeur,
et **moins** de cycles.

```bash
pytest MyIA.AI.Notebooks/RL/gateway/test_mdp_value_iteration_core.py \
       MyIA.AI.Notebooks/RL/gateway/test_mdp_policy_iteration_core.py -v
```

## Verdict SOTA

**SOTA-OK.** Les deux services exposent l'iteration de la valeur et de la politique du
carnet phare RL-05 — l'**organe natif** de la serie RL pour ces algorithmes
(programmation dynamique sur MDP, AIMA ch. 14). Les reprises sont **auto-contenues et
fideles** au carnet : meme algorithme, meme gridworld, aucun import du carnet.

Copie pedagogique declaree : le carnet **enseigne precisement** les algorithmes que les
services exposent, il n'y a pas d'outil externe que le service pretendrait utiliser sans
le faire. Des solveurs RL externes existent, mais le point d'un service de cette serie
pedagogique est d'exposer l'**implementation de reference du carnet**, pas de la deleger
a une bibliotheque.

Le probleme de demonstration est **non degenere** : un gridworld 4x3 avec obstacles,
terminals competiteurs (`+1` / `-1`) et bruit 0.8/0.2 — la capacite annoncee
(convergence vers la politique optimale et le **discriminant** entre les deux
algorithmes) est **visible dans la sortie**, pas un cas trivial ou les deux algorithmes
se confondent.

## Notes

- **Discriminant** : l'iteration de la politique et de la valeur convergent vers la meme
  politique/valeur optimale ; l'iteration de la politique y parvient en moins de cycles
  (chacun resout une evaluation de politique complete, rechauffee a la valeur du cycle
  precedent), verifie par un test dedie.
- **MDP complet** : le contrat exige que toute paire `(etat, action)` porte une
  distribution de transition normalisee et une recompense — c'est la forme dans laquelle
  le gridworld d'AIMA est encode (un heurt de mur / un obstacle ramene a l'etat courant).
- **Mono-kernel** : une feuille = un kernel ; chaque serveur `kernel_gateway` sert un
  endpoint MDP a la fois.
