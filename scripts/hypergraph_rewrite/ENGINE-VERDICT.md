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
| Roues publiées (relevé PyPI du 2026-10-28) | quatre **abi3** (`>=3.9`) : `win_amd64`, `manylinux_2_17_x86_64`, `manylinux_2_17_aarch64`, `macosx` x86_64/arm64/universal2 — plus une source `.tar.gz` |
| Roue utilisée sur ce siège | `setreplace-0.2.0-cp39-abi3-win_amd64.whl` |
| Dépôt `kovasb/setreplace-py` | MIT (fichier `LICENSE` lu : « MIT License / Copyright (c) 2026 Kovas Boguta »), Rust/PyO3, 2 étoiles, dernier push 2026-06-11 |
| Sémantique annoncée à la source | « hypergraph substitution with the exact semantics of Max Piskunov's SetReplace », mêmes valeurs par défaut d'ordre d'événements, même déterminisme |
| Installation et invocation locales | faites, cible isolée, **contrôle de cohérence PASS** |

**Verdict : `RECOVERABLE-LOCAL`** — l'outil réel est installable et invoquable sur cette
machine, sans moteur Wolfram et sans décision de mainteneur. Aucune réimplémentation
maison n'est donc nécessaire, et le pli ne se rabat pas sur la « copie pédagogique
déclarée ».

**Ce que ce verdict ne dit pas**, et qui doit être écrit plutôt que supposé :

- le paquet est **jeune** (2 étoiles, 2 versions, dernier push 2026-06-11) et son
  auteur est unique. Un accord avec la référence Wolfram est **déclaré** par sa
  documentation, pas vérifié ici — il ne peut pas l'être sans le moteur Wolfram ;
- la surface exposée est celle de l'évolution à **chemin unique** : `evolve`,
  `final_state`, `states_by_event`, `causal_graph_edges`. La sonde de capacités ne
  trouve **aucune** énumération multiway — et elle le mesure sur le module **et sur
  chaque classe publique** (`HypergraphSystem` : 17 méthodes), pas sur le module seul ;
- `set_replace_all` rend les **états suivants distincts** d'un état donné : c'est la
  brique avec laquelle une énumération multiway se **construirait**, pas l'énumération
  elle-même. `enumerate_rules` énumère des **règles** de même signature
  (`EnumerateWolframModelRules`), pas des états : aucun des deux ne ferme le grain B ;
- le compteur de graine (`random_seed`) est accepté et le déterminisme est vérifié à
  graine égale, mais aucune comparaison inter-moteurs n'est possible sans la référence.

## Ce que la mesure donne, une fois le moteur établi

Série aux nombres d'événements `1, 2, 3, 5, 8, 13, 21`, ordre `LeastRecentEdge` par
défaut, graine 0.

| Règle | Arêtes | Atomes | Modèle retenu |
|---|---|---|---|
| `{{x,y}} -> {{x,y},{y,z}}` sur `{{1,1}}` | `n + 1` | `n + 1` | affine, pente 1,000, ordonnée 1,000, R² = 1,0000 |
| `{{x,y},{x,z}} -> {{x,y},{x,w},{y,w},{z,w}}` sur `{{1,1},{1,1}}` | `2n + 2` | `n + 1` | affine, pente 2,000, ordonnée 2,000, R² = 1,0000 |

**La frontière d'occurrences, elle, varie** — et c'est ce qui la distingue du témoin
qu'elle remplace. Nombre d'états suivants distincts rendus par `set_replace_all` à
chaque génération (13 événements) :

| Règle | g0 | g1 | g2 | g3 | g4 | g5 |
|---|---|---|---|---|---|---|
| `chaine` | 2 | 4 | 8 | 16 | 28 | — |
| `branchante` | 4 | 8 | 14 | 26 | 46 | 50 |

Un seul événement est appliqué par génération dans les deux cas : c'est une propriété
**structurelle** du chemin unique, pas un témoin négatif. La mesure précédente
(`max_consumers`, seuil `FANOUT_CAP = 1`) valait 1 sur cinq règles différentes, y
compris la branchante — elle ne pouvait pas rougir, donc elle ne prouvait rien. La
série ci-dessus est l'**entrée** du grain B (combien d'occurrences une énumération
multiway aurait à explorer) ; elle ne dit rien du nombre d'états multiway.

### Le piège que la mesure a attrapé

Ajustées en loi de puissance **log-log**, les deux séries rendent `alpha = 0,797` avec
`R² = 0,9926` — et un classement naïf conclurait « croissance sous-linéaire » sur une
série qui est **exactement affine**. L'instrument compare donc deux modèles de deux
paramètres chacun (`compare_models`), et il les compare **sur la même variable
réponse** : le R² de la loi de puissance est recalculé en espace brut
(`fit_power_law_raw`), pas dans celui du logarithme. Sur la série `n + 1` cela donne
`alpha = 0,886` et `R² brut = 0,9982` contre `R² = 1,0000` pour l'affine — l'affine
gagne parce qu'elle décrit la série, et non parce que les deux nombres ne mesuraient
pas la même chose. Les deux R² restent rendus côte à côte pour que l'écart d'espace
soit lisible. Un test fige le piège, un autre vérifie l'égalité (à égalité, la loi de
puissance l'emporte, conformément à la règle écrite).

### Ce que le contrôle de cohérence prouve, et ce qu'il ne prouve pas

Il rejoue le modèle écrit à la main dans `CALIBRATION` et compare chaque point aux
constantes écrites à la main **avant** toute exécution : il attrape une erreur
d'arithmétique du modèle (il l'a fait pendant la mise au point — l'attente « deux
événements ⇒ quatre arêtes » était fausse), donc une **valeur** fausse. Il ne valide
pas l'adéquation de la règle au moteur, et il ne discrimine pas un **modèle** faux :
les deux côtés de la comparaison sont écrits par la même main. C'est une cohérence
interne, ce que le nom du bloc dit désormais.

Le même piège avait été attrapé en sens inverse pendant la mise au point : l'attente
écrite à la main « deux événements ⇒ quatre arêtes » était fausse (un événement consomme
une arête et en produit deux, donc `n + 1`), et c'est le contrôle de correction qui l'a
signalée avant tout commit.

## Ce que le pli garde à faire

- **Grain B — la réductibilité du nombre de branches** n'est **pas** tranchée ici : elle
  demande une énumération multiway que le moteur retenu n'expose pas. La frontière
  d'occurrences mesurée ci-dessus (`occurrences`) en est l'**entrée** : elle dit
  combien de successeurs distincts chaque génération offre au chemin unique. La mesure cidessus
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
