# AgentInterfaces — Interfaces agentiques de CoursIA

Série de **découverte** : comment les agents (LLM, harnais, scripts) s'interfacent
au dépôt CoursIA. Le carnet 01 **mesure** les trois classes d'interfaces que le
dépôt offre — serveurs **MCP**, outils **CLI** (`scripts/`) et **bridges**
notebook → service HTTP — et leur **couverture documentaire**.

La série part d'un constat mesurable : une grande partie de l'outillage du dépôt
n'est pas encore décrite dans une référence qu'un agent peut lire. Avant de
construire quoi que ce soit « pour les agents », il faut d'abord **mesurer ce
qui existe déjà**.

## Notebooks

| Notebook | Public | Contenu | Langue |
|---|---|---|---|
| [`AgentInterfaces-01-Inventaire-Interfaces-Agentiques.ipynb`](AgentInterfaces-01-Inventaire-Interfaces-Agentiques.ipynb) | Découverte | Inventaire **mesuré** des trois classes d'interfaces agentiques (MCP / CLI / bridge) et de leur couverture dans la référence native `docs/reference/scripts-reference.md` ; chaque nombre est produit par le code, re-exécuté, pas affirmé | Français |

## Méthode — « mesuré, pas affirmé »

Chaque chiffre du carnet est **produit par son code** et **re-exécuté** (règle C.2
du dépôt) : le carnet compte lui-même les serveurs `.mcp.json`, les scripts
`def main()` + `argparse` de `scripts/`, et les bridges notebook → HTTP. La racine
du dépôt est **recherchée** (présence de `scripts/` + `MyIA.AI.Notebooks/`), jamais
hardcodée, pour que la mesure reste valide quand l'arbre bouge.

## Position dans le dépôt

Première série de l'EPIC [#27071](https://github.com/jsboige/CoursIA/issues/27071)
(« CoursIA pour les agents : découverte, interfaces exécutables et base de
connaissances »). Le carnet 01 pose la **ligne de base mesurable** sur laquelle
les suites de la série (découverte guidée, interfaces exécutables, base de
connaissances) viendront se greffer.

## Prérequis

Python 3 (kernel `python3`) : **stdlib uniquement** (`json`, `pathlib`) — aucune
dépendance externe. Le carnet s'exécute de bout en bout sur n'importe quelle
machine qui a le dépôt.

## Exercices

Le carnet embarque trois exercices (`TODO etudiant`) : lister les serveurs MCP,
classifier une interface comme « agent-ready », et mesurer la couverture d'une
sous-famille de scripts. Les stubs s'exécutent sans erreur (règle C.1 du dépôt).
