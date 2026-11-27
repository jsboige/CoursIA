# Service Kernel Gateway — MDP (iteration de la valeur et de la politique)

Exposition REST de l'**iteration de la valeur** et de l'**iteration de la politique**
du carnet phare [RL-05 — MDP, programmation dynamique et Q-learning](../RL-05-MDP-Programmation-Dynamique-Q-Learning-Python.ipynb)
— programmation dynamique sur MDP.

Feuille de service de l'Epic AIMA-Gateway [#19571](https://github.com/jsboige/CoursIA/issues/19571).
Le carnet pedagogique n'est **pas modifie** : ce dossier `gateway/` ajoute deux carnets
de service a cote, sur le meme motif que les pilotes `GameTheory/gateway/`,
`Probas/Infer/gateway/`, `Z3-API/gateway/` et `NLP/gateway/`.

Deux services, un meme contrat de MDP, un meme gridworld de demonstration :

| Service | Algorithme | `POST` | Mesure sur le gridworld 4x3 |
|---|---|---|---|
| Iteration de la valeur | backups de Bellman | `/rl/mdp-value-iteration` | **19** backups |
| Iteration de la politique | evaluation + amelioration gloutonne | `/rl/mdp-policy-iteration` | **4** cycles d'amelioration |

Sur ce MDP, les deux méthodes donnent la même politique et des valeurs proches à la
tolérance numérique près. Les cycles de politique et les itérations de valeur sont des
unités différentes : chaque cycle comprend une évaluation itérative de la politique.
Leurs nombres ne permettent donc pas de comparer directement le coût de calcul.

## Contrat

Les deux endpoints partagent le **meme corps** — un MDP complet :

```json
{
  "states":  ["0,0", "0,3", "2,0", "2,3", "..."],
  "actions": ["N", "S", "E", "W"],
  "T":  {"0,0": {"N": {"0,0": 0.9, "0,1": 0.1}, "E": {"0,1": 1.0}, "...": {}}, "...": {}},
  "R":  {"0,0": {"N": -0.04, "E": -0.04, "...": 0.0}, "0,3": {"N": 0.0, "...": 0.0}},
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
  "value":   {"0,0": 0.6726, "0,3": 0.0, "2,0": 0.0, "2,3": 0.5547, "...": 0.0},
  "iterations": 19,
  "converged": true,
  "n_states": 10
}
```

- `policy` : action gloutonne par état pour la valeur calculée.
- `value` : approximation de la fonction de valeur optimale `V*(s)`.
- `iterations` : nombre d'itérations de Bellman effectuées.
- `converged` : `true` si le seuil `theta` est atteint, y compris à la dernière itération autorisée. Si `false`, le plafond a été atteint sans satisfaire ce critère.

Reponse `POST /rl/mdp-policy-iteration` (JSON, HTTP 200) :

```json
{
  "status": "ok",
  "policy":  {"0,0": "E", "0,3": "N", "2,0": "N", "2,3": "W", "...": "..."},
  "value":   {"0,0": 0.6726, "0,3": 0.0, "2,0": 0.0, "2,3": 0.5547, "...": 0.0},
  "improvement_steps": 4,
  "converged": true,
  "n_states": 10
}
```

- `improvement_steps` : nombre de cycles effectués (évaluation de politique et amélioration gloutonne).
- `converged` : `true` lorsque la politique est stable et que son évaluation a atteint le seuil `theta`. Si le plafond est atteint, les valeurs et la politique retournées ne sont pas garanties optimales. Si la dernière amélioration change la politique, une évaluation supplémentaire bornée produit une approximation pour la politique retournée ; elle peut elle aussi rester non convergée.
- Sur ce MDP, la `policy` est identique et la `value` est proche de celle obtenue par
  iteration de la valeur (tolérance absolue de `1e-3` dans le test dédié).

Entree hors contrat (cles manquantes, `T` non normalise, probabilite negative, `gamma`
hors bornes) : `{"status": "invalid", "error": ...}` pour les erreurs de validation traitées.

## Fichiers

| Fichier | Role |
|---|---|
| `mdp_value_iteration_core.py` | Cœur du service **iteration de la valeur** : backups de Bellman + politique gloutonne, validation du MDP, `run()`. Testable hors kernel. |
| `mdp-value-iteration-service.ipynb` | Carnet de service : cellule d'entree `# POST /rl/mdp-value-iteration`, demarrage dans le kernel du gateway. |
| `test_mdp_value_iteration_core.py` | **26** tests du coeur (contrat ok / invalid, determinisme, politique gloutonne = argmax, gridworld 4x3). |
| `mdp_policy_iteration_core.py` | Cœur du service **iteration de la politique** : evaluation (rechauffee) + amelioration gloutonne, validation du MDP, `run()`. Testable hors kernel. |
| `mdp-policy-iteration-service.ipynb` | Carnet de service : cellule d'entrée `# POST /rl/mdp-policy-iteration` et comparaison des politiques obtenues. |
| `test_mdp_policy_iteration_core.py` | **26** tests du coeur, dont les croisements avec l'iteration de la valeur sur les exemples testés. |
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

Exécutés le 2026-11-27 via Papermill (kernel `python3`), hors gateway : les exemples
ci-dessous présentent des extraits arrondis des résultats des démonstrations, et non une
preuve d'exécution HTTP. Le MDP est une **variante du gridworld 4x3 d'AIMA** (ch. 17,
§ 17.1 ; 2 obstacles, soit 10 états, 2 terminaux `+1` / `-1`, cout par pas `-0.04`,
bruit 0.8/0.2). La récompense
terminale est versée à l'entrée ; les terminaux sont ensuite absorbants, avec
récompense nulle. Les actions affichées sur ces états sont arbitraires.

Schéma indicatif d'appel (les points de suspension doivent être remplacés par le MDP complet) :

```bash
curl -s -X POST http://localhost:8993/rl/mdp-value-iteration \
  -H "Content-Type: application/json" \
  -d '{ "states": [...], "actions": ["N","S","E","W"], "T": {...}, "R": {...}, "gamma": 0.9 }'
```

Résultat de la démonstration (extrait arrondi, hors HTTP) :

```json
{
  "status": "ok",
  "policy":  {"0,0": "E", "0,3": "N", "2,0": "N", "2,3": "W"},
  "value":   {"0,0": 0.6726, "0,3": 0.0, "2,0": 0.0, "2,3": 0.5547},
  "iterations": 19,
  "converged": true,
  "n_states": 10
}
```

L'iteration de la politique, sur le **meme** MDP, retourne la **meme** politique et la
**meme** valeur à la tolérance numérique près, en **4** cycles d'amelioration :

```json
{
  "status": "ok",
  "policy":  {"0,0": "E", "0,3": "N", "2,0": "N", "2,3": "W"},
  "value":   {"0,0": 0.6726, "0,3": 0.0, "2,0": 0.0, "2,3": 0.5547},
  "improvement_steps": 4,
  "converged": true,
  "n_states": 10
}
```

Entrée hors contrat (distribution de transition non normalisee) — reponse reelle :

```json
{"status": "invalid", "error": "T['0,0']['N']: somme = 0.600000, distribution normalisee (somme ~ 1) attendue"}
```

## Tests

52 tests (26 pour la valeur et 26 pour la politique), tous verts. Chaque test charge son coeur **par chemin de fichier**
(`importlib` + `Path(__file__)`) : la suite partagee `scripts-tests.yml` tourne en
`--import-mode importlib` (`pytest.ini`) et le dossier du test n'est pas ajoute a
`sys.path`, un import par nom echouerait. Les tests de l'iteration de la politique
croisent aussi l'iteration de la valeur : sur les exemples testés, les politiques
coïncident et les valeurs sont proches à la tolérance précisée plus haut.

```bash
pytest MyIA.AI.Notebooks/RL/gateway/test_mdp_value_iteration_core.py \
       MyIA.AI.Notebooks/RL/gateway/test_mdp_policy_iteration_core.py -v
```

## Verdict SOTA

**SOTA-OK.** Les deux services exposent l'iteration de la valeur et de la politique du
carnet phare RL-05 — l'**organe natif** de la serie RL pour ces algorithmes
(programmation dynamique sur MDP). Les reprises sont **auto-contenues et
fideles** aux algorithmes du carnet ; la démonstration utilise une variante du gridworld, sans import du carnet.

Copie pedagogique declaree : le carnet **enseigne precisement** les algorithmes que les
services exposent, il n'y a pas d'outil externe que le service pretendrait utiliser sans
le faire. Des solveurs RL externes existent, mais le point d'un service de cette serie
pedagogique est d'exposer l'**implementation de reference du carnet**, pas de la deleger
a une bibliotheque.

Le probleme de demonstration est **non degenere** : cette variante du gridworld 4x3, avec
obstacles, terminals competiteurs (`+1` / `-1`) et bruit 0.8/0.2 — la capacite annoncee
(calcul d'une politique sur un MDP stochastique) est visible dans les sorties.
Les compteurs affichés ne constituent toutefois pas une comparaison de performance.

## Notes

- **Compteurs** : sur cet exemple, le nombre de cycles d'amélioration et le nombre
  d'itérations de valeur diffèrent. Un cycle comprend plusieurs étapes d'évaluation :
  ces compteurs ne mesurent pas le même travail et ne démontrent pas une performance
  supérieure.
- **MDP complet** : le contrat exige que toute paire `(etat, action)` porte une
  distribution de transition normalisee et une recompense — c'est la forme dans laquelle
  cette variante du gridworld est encodée (un heurt de mur ou un obstacle ramène à l'état courant).
- **Mono-kernel** : une feuille = un kernel ; chaque serveur `kernel_gateway` sert un
  endpoint MDP a la fois.
