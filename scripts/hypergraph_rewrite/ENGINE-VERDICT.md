# Pli 5 (#23093) — verdict d'outil : `RECOVERABLE-LOCAL`

Mesure du 2026-10-28, lane `myia-po-2023:CoursIA-2`. Instrument : `pli5_engine.py`,
résultats verbatim : `pli5_results.json`.

Le corps du pli impose l'ordre : le **verdict d'outil est le premier livrable**, et il
précède toute mesure. Les trois branches sont donc épuisées dans l'ordre demandé, avec
la preuve de ce qui a été tenté.

## Branche 1 — `SetReplace` / moteur Wolfram

| Mesure | Résultat |
|---|---|
| `wolframscript` sur le `PATH` | absent |
| `WolframKernel` sur le `PATH` | absent |
| dossier `C:/Program Files/Wolfram Research` | absent |
| dépôt de référence `maxitg/SetReplace` | MIT, langue déclarée `Mathematica`, non archivé, dernier push 2026-07-18 |

`SetReplace` est un paquet en langage Wolfram : il n'existe pas de chemin d'exécution
sans un moteur Wolfram, dont l'activation passe par un compte — c'est la décision de
**mainteneur** que le corps du pli identifie. La branche ne peut donc pas être fermée
positivement sur cette machine, et elle n'a pas eu à l'être : la branche 2 la ferme
autrement.

## Branche 2 — alternative ouverte (la branche à épuiser avant de conclure)

| Mesure | Résultat |
|---|---|
| `setreplace` 0.2.0 sur PyPI | présent, licence MIT, `requires_python >= 3.9` |
| Roue disponible pour cette machine | `setreplace-0.2.0-cp39-abi3-win_amd64.whl` |
| Dépôt `kovasb/setreplace-py` | MIT (fichier `LICENSE` lu : « MIT License / Copyright (c) 2026 Kovas Boguta »), Rust/PyO3, 2 étoiles, dernier push 2026-06-11 |
| Sémantique annoncée à la source | « hypergraph substitution with the exact semantics of Max Piskunov's SetReplace », mêmes valeurs par défaut d'ordre d'événements, même déterminisme |
| Installation et invocation locales | faites, cible isolée, **contrôle de correction PASS** |

**Verdict : `RECOVERABLE-LOCAL`** — l'outil réel est installable et invoquable sur cette
machine, sans moteur Wolfram et sans décision de mainteneur. Aucune réimplémentation
maison n'est donc nécessaire, et le pli ne se rabat pas sur la « copie pédagogique
déclarée ».

**Ce que ce verdict ne dit pas**, et qui doit être écrit plutôt que supposé :

- le paquet est **jeune** (2 étoiles, 2 versions, dernier push 2026-06-11) et son
  auteur est unique. Un accord avec la référence Wolfram est **déclaré** par sa
  documentation, pas vérifié ici — il ne peut pas l'être sans le moteur Wolfram ;
- la surface exposée est celle de l'évolution à **chemin unique** : `evolve`,
  `final_state`, `states_by_event`, `causal_graph_edges`. La sonde de capacités
  (`MULTIWAY_HINTS`) ne trouve **aucune** énumération multiway ;
- le compteur de graine (`random_seed`) est accepté et le déterminisme est vérifié à
  graine égale, mais aucune comparaison inter-moteurs n'est possible sans la référence.

## Ce que la mesure donne, une fois le moteur établi

Série aux nombres d'événements `1, 2, 3, 5, 8, 13, 21`, ordre `LeastRecentEdge` par
défaut, graine 0.

| Règle | Arêtes | Atomes | Modèle retenu |
|---|---|---|---|
| `{{x,y}} -> {{x,y},{y,z}}` sur `{{1,1}}` | `n + 1` | `n + 1` | affine, pente 1,000, ordonnée 1,000, R² = 1,0000 |
| `{{x,y},{x,z}} -> {{x,y},{x,w},{y,w},{z,w}}` sur `{{1,1},{1,1}}` | `2n + 2` | `n + 1` | affine, pente 2,000, ordonnée 2,000, R² = 1,0000 |

Le fan-out du graphe causal vaut **1** sur les deux règles au terme de 13 événements :
sur un chemin unique, aucun jeton n'est consommé par plus d'un événement, donc **le
chemin unique ne branche pas** (témoin négatif déclaré avant la mesure, `FANOUT_CAP = 1`).

### Le piège que la mesure a attrapé

Ajustées en loi de puissance, les deux séries rendent `alpha = 0,797` avec
`R² = 0,9926` — et un classement naïf conclurait « croissance sous-linéaire » sur une
série qui est **exactement affine**. L'instrument compare donc deux modèles de deux
paramètres chacun et retient le R² le plus haut (`compare_models`) ; le classement
d'exposant ne sert plus que lorsque la loi de puissance décrit réellement la série.
Un test dédié fige ce piège.

Le même piège avait été attrapé en sens inverse pendant la mise au point : l'attente
écrite à la main « deux événements ⇒ quatre arêtes » était fausse (un événement consomme
une arête et en produit deux, donc `n + 1`), et c'est le contrôle de correction qui l'a
signalée avant tout commit.

## Ce que le pli garde à faire

- **Grain B — la réductibilité du nombre de branches** n'est **pas** tranchée ici : elle
  demande une énumération multiway que le moteur retenu n'expose pas. La mesure cidessus
  porte sur un seul ordre d'événements et ne dit rien du nombre d'états multiway. Deux
  voies restent ouvertes : construire l'énumération au-dessus de l'API (toutes les
  paires règle/occurrence à chaque génération), ou rouvrir la question du moteur Wolfram
  comme décision de mainteneur. C'est un point d'arbitrage, pas un résultat.
- **Grain C — la structure causale** est accessible sans travail supplémentaire
  (`causal_graph_edges`, `causal_graph_dot`), et le pont Gorard reste à écrire, chaque
  citation portant le chemin de la copie archivée au gisement.
- **L'hôte du carnet** n'est pas tranché : aucune cellule n'a été écrite, conformément à
  l'interdiction du corps de l'issue avant le design-gate.

## Reproduire

```bash
python -m pip install --target .tmp/hg_pkg setreplace
PYTHONPATH=.tmp/hg_pkg python -m scripts.hypergraph_rewrite.pli5_engine --write
PYTHONPATH=.tmp/hg_pkg python -m pytest scripts/tests/test_hypergraph_rewrite_pli5.py -q
```

Sans le moteur, le module rend le verdict `RECOVERABLE-USER-HAND` et refuse de mesurer ;
les tests qui l'exigent sont sautés, les autres tournent.
