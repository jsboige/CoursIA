# Consultation HTTP du cursus

Ce service en lecture seule utilise `query_curriculum.py`, les formes SHACL et
le Kernel Gateway du dépôt. Il charge l'export Turtle au démarrage ; pour un
nouvel export, redémarrer le service. Installer `rdflib`, `pyshacl`,
`jupyter_kernel_gateway` et disposer du kernel `python3`.

```bash
python scripts/notebook_tools/curriculum_gateway/service.py --graph CURRICULUM.generated.ttl --port 8899
curl -X POST -H 'Content-Type: application/json' -d '{"action":"series"}' http://127.0.0.1:8899/curriculum/query
```

La route `POST /curriculum/query` accepte `series`, `path` et `prerequisites`.
Les deux dernières actions exigent `path`, identifiant exact du carnet relatif
à `MyIA.AI.Notebooks/`. Les réponses portent `status` (`ok`, `invalid` ou
`not_found`) et `results`. Le lecteur signale les prérequis non renseignés :
cela ne prouve pas leur absence. L'export RDF contient les niveaux de sous-série
imbriqués, mais le lecteur partagé ne restitue que la sous-série directement
liée au carnet, sans ses parents. Le service utilise un seed Kernel Gateway
temporaire, supprimé à l'arrêt ; il ne crée aucun carnet supplémentaire dans le cursus. L'écoute
est limitée à loopback par le lanceur partagé.
