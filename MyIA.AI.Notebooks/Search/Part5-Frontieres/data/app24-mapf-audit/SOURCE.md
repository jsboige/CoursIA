# Provenance — App-24 MAPF Guarantee Audit

## Travail étudiant distillé

- **Auteurs** : Matteo Atkinson et Paul Witkowski
- **Projet** : *Coordination de drones par Multi-Agent Path Finding*, groupe G3, EPITA SCIA, Programmation par Contraintes 2026
- **Dépôt source** : <https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/tree/main/groupe-G3-Coordination_de_drones_par_Multi-Agent_Path_Finding>
- **Historique cumulé** : [PR #33](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/pull/33) (rendu principal), [PR #36](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/pull/36) (instructions de lancement), [PR #42](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/pull/42) (slides)
- **Commit reproduit** : `b5f3f0351dbd41f3a76f047cf02e9c93e81192f3`
- **Licence source** : MIT, copyright 2026, *The 2026-Epita-Programmation-par-Contraintes contributors*

Le dispositif étudiant comprend quatre solveurs (CP-SAT, CBS, ECBS, OD-A*), onze scénarios, une API Flask et une visualisation Three.js. App-24 ne recopie aucun solveur ni notebook étudiant : il conserve seulement trois petites instances et les trajectoires produites lors d'un rerun frais afin de les soumettre à un validateur et à un oracle CoursIA indépendants.

## Collecte fraîche

Collecte effectuée le **28 août 2026** sous Python 3.13 depuis le code source au commit ci-dessus.

```powershell
python -m pip install -r groupe-G3-Coordination_de_drones_par_Multi-Agent_Path_Finding/requirements.txt
$env:PYTHONPATH = ".../groupe-G3-Coordination_de_drones_par_Multi-Agent_Path_Finding"
python -m pytest tests/test_grid.py tests/test_mapf.py tests/test_cbs.py tests/test_od_astar.py tests/test_api.py --import-mode=importlib -q
python collect_g3_fresh.py
```

Résultat du test ciblé : **39 tests passés**. Le script ponctuel `collect_g3_fresh.py` est un instrument de collecte hors dépôt ; il charge les scénarios 01–03, exécute CP-SAT/CBS/OD-A* avec une limite de 30 secondes, sérialise statuts, objectifs et trajectoires, puis exécute le cas minimal de contrainte future au but. Il n'est pas une dépendance du notebook.

## Schéma de `fresh_runs.json`

- `source_*`, `students`, `collected_on`, `python` : métadonnées de provenance ;
- `scenarios[]` : définition de grille, bâtiments, drones et `runs[]` ;
- `runs[]` : nom du solveur, statut déclaré, makespan, flowtime et trajectoires ;
- `future_goal_case` : cas 1×3, but `(0, 2)`, interdiction au même but à `t=4`, chemin retourné par le low-level A* étudiant.

## Séparation des responsabilités

| Élément | Origine |
|---|---|
| Scénarios, solveurs, statuts et trajectoires sérialisées | Travail étudiant, rerun frais |
| Validateur de trajectoires | CoursIA, réécriture indépendante |
| Oracle CP-SAT time-expanded | CoursIA, modèle indépendant |
| Audit admissibilité / arrêt au but / niveaux de preuve | CoursIA |
| Conclusions générales et exercices | CoursIA |

## Limites

Le snapshot porte sur trois scénarios seulement et un commit précis. Les temps machine ne sont pas conservés. Une trajectoire validée prouve seulement sa faisabilité. L'oracle du notebook établit un optimum pour chaque modèle fini et l'horizon testé ; il ne certifie ni l'implémentation étudiante entière, ni les performances annoncées sur les grands scénarios, ni l'API ou la visualisation 3D.
