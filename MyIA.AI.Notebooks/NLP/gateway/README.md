# Service Kernel Gateway — HMM / Viterbi

Exposition REST du **decodage de Viterbi** (et de l'algorithme de l'avant) du
carnet phare [05-HMM-Viterbi.ipynb](../05-HMM-Viterbi.ipynb) — raisonnement
probabiliste sur la duree, ch. 14 d'AIMA.

Feuille de service du **pli 1** de l'Epic AIMA-Gateway [#19571](https://github.com/jsboige/CoursIA/issues/19571).
Le carnet pedagogique n'est **pas modifie** : ce dossier `gateway/` ajoute un
carnet de service a cote, sur le meme motif que les pilotes `GameTheory/gateway/`,
`Probas/gateway/` et `Z3-API/gateway/`.

## Contrat

`POST /nlp/viterbi`

Corps (JSON) :

```json
{
  "states":       ["EnSoleil", "Pluie"],
  "observations": ["promenade", "magasin", "nettoyage"],
  "pi":           [0.6, 0.4],
  "A":            [[0.7, 0.3], [0.4, 0.6]],
  "B":            {"EnSoleil": {"promenade": 0.7, "magasin": 0.4, "nettoyage": 0.1},
                   "Pluie":    {"promenade": 0.1, "magasin": 0.4, "nettoyage": 0.6}}
}
```

- `states` : liste de noms d'etats (non vide, sans doublon).
- `observations` : liste de symboles observes (non vide).
- `pi` : distribution initiale (longueur = nombre d'etats, somme ≈ 1).
- `A` : matrice de transition n×n, entrees ≥ 0.
- `B` : emissions par etat, `B[etat][symbole] = probabilite` (≥ 0).

Reponse (JSON, HTTP 200) :

```json
{
  "status": "ok",
  "best_path": ["EnSoleil", "EnSoleil", "Pluie"],
  "best_path_log_prob": -3.855264671609537,
  "observation_log_prob": -2.900422093749666,
  "n_states": 2,
  "n_observations": 3
}
```

- `best_path` : suite d'etats maximisant la probabilite jointe (decodage de Viterbi).
- `best_path_log_prob` : log de la probabilite de ce meilleur chemin.
- `observation_log_prob` : log de `P(observations | modele)` (algorithme de l'avant) —
  elle **majorise** `best_path_log_prob`, car elle somme sur **toutes** les trajectoires.

Un symbole absent de `B[etat]` vaut une emission plafonnee a `EPS` (floor), pas une
erreur. Entree hors contrat (cles manquantes, longueurs incoherentes, probabilites
negatives) : `{"status": "invalid", "error": ...}` — **le service ne leve jamais
d'exception**.

## Fichiers

| Fichier | Role |
|---|---|
| `hmm_viterbi_core.py` | Cœur du service : Viterbi + avant en espace des log, validation du modèle, `run()`. Testable hors kernel. |
| `hmm-viterbi-service.ipynb` | Carnet de service : cellule d'entree `# POST /nlp/viterbi`, demarrage dans le kernel du gateway. |
| `test_hmm_viterbi_core.py` | 18 tests du coeur (contrat ok / invalid, determinisme, floor, majoration avant ≥ Viterbi). |
| `requirements.txt` | `jupyter_kernel_gateway`. |

## Demarrage

```bash
python -m kernel_gateway \
  --KernelGatewayApp.api=kernel_gateway.notebook_http \
  --KernelGatewayApp.seed_uri=hmm-viterbi-service.ipynb \
  --KernelGatewayApp.port=8991 \
  --JupyterWebsocketPersonality.list_kernels=True
```

Le kernel demarre **dans ce dossier** : la cellule de preparation charge le coeur par
chemin relatif (`hmm_viterbi_core.py`). Le carnet s'execute aussi **hors gateway**
(`papermill` / `jupyter nbconvert --execute`) : `kernel_gateway` n'est alors pas
importe et la cellule d'entree degrade proprement en mode demo.

## Exemples mesures

Exeques le 2026-11-24 via papermill (kernel `python3`), hors gateway — les sorties
ci-dessous sont **reelles**, produites par `run()` dans les cellules de demonstration
du carnet de service. En mode gateway, le meme corps passe par `curl` et recoit la
meme reponse.

Payload valide (exemple meteo du carnet phare) :

```bash
curl -s -X POST http://localhost:8991/nlp/viterbi \
  -H "Content-Type: application/json" \
  -d '{
    "states": ["EnSoleil", "Pluie"],
    "observations": ["promenade", "magasin", "nettoyage"],
    "pi": [0.6, 0.4],
    "A": [[0.7, 0.3], [0.4, 0.6]],
    "B": {"EnSoleil": {"promenade": 0.7, "magasin": 0.4, "nettoyage": 0.1},
          "Pluie": {"promenade": 0.1, "magasin": 0.4, "nettoyage": 0.6}}
  }'
```

Reponse (reelle) :

```json
{
  "status": "ok",
  "best_path": ["EnSoleil", "EnSoleil", "Pluie"],
  "best_path_log_prob": -3.855264671609537,
  "observation_log_prob": -2.900422093749666,
  "n_states": 2,
  "n_observations": 3
}
```

Entrée hors contrat (`pi` de 3 valeurs pour 2 états) — reponse reelle :

```json
{"status": "invalid", "error": "pi: liste de 2 probabilites attendue"}
```

## Tests

18 tests, tous verts. Le test charge le coeur **par chemin de fichier**
(`importlib` + `Path(__file__)`) : la suite partagee `scripts-tests.yml` tourne en
`--import-mode importlib` (`pytest.ini`) et le dossier du test n'est pas ajoute a
`sys.path`, un import par nom echouerait.

```bash
pytest MyIA.AI.Notebooks/NLP/gateway/test_hmm_viterbi_core.py -v
```

## Verdict SOTA

**SOTA-OK.** Le service expose le decodage Viterbi / avant du carnet phare —
l'**organe natif** de la serie NLP pour cet algorithme (construit a la main dans le
carnet, ch. 14 AIMA). La reprise est **auto-contenue et fidele** au carnet : meme
algorithme, en **espace des logarithmes** pour la stabilite numerique (un symbole
inconnu est plafonne a `EPS`, jamais `log(0) = -inf`).

Copie pedagogique declaree : le carnet **enseigne precisement** l'algorithme que le
service expose, il n'y a pas d'outil externe que le service pretendrait utiliser sans
le faire. `hmmlearn` existe comme alternative externe, mais le point d'un service de
cette serie pedagogique est d'exposer l'**implementation de reference du carnet**,
pas de la deleger a une bibliotheque.

## Notes

- **Espace des log** : `best_path_log_prob` et `observation_log_prob` sont des
  log-probabilites (nombres negatifs), pas des probabilites brutes — la
  normalisation par la base du log est la meme partout.
- **Majoration** : `observation_log_prob >= best_path_log_prob` par construction
  (l'avant somme sur toutes les trajectoires) ; verifie par un test dedie.
- **Mono-kernel** : une feuille = un kernel ; un serveur `kernel_gateway` sert
  `POST /nlp/viterbi` seul.
