# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

> **Audit vision po-2025 c.469 (2026-07-14, doctrine #5780)** : les 6 PNG ci-dessous ont été ouverts un par un via l'outil `Read` et comparés à leur alt-text. Verdict par figure dans le champ *Contenu réel vérifié*. Cohérence caption ↔ image = 4/6 exacts, 2 corrections appliquées (sw12_graphrag_c18_o0 + sw13_reasoner c49/c52, alt-text sur-vendait).

## sw11_kg_c46_o0.png

- **Source** : notebook `SymbolicAI/SemanticWeb/SW-11-Python-KnowledgeGraphs.ipynb` (cellule 46, output 0)
- **Alt-text (FR)** : Sous-graphe orienté filtré par SPARQL sur les films de Christopher Nolan (vocabulaire schema.org) — noeuds colorés par type (Film / Personne / Genre), arêtes orientées étiquetées par relation (director, actor, genre).
- **Contenu réel vérifié** : Graphe orienté titré « Filmographie de Christopher Nolan - Sous-graphe du KG » — 3 films (Inception, Interstellar, The Dark Knight) + 6 personnes (Nolan, Bale, Hathaway, Hardy, DiCaprio, McConaughey, Ledger) + 2 genres (Science-Fiction, Action). Légende = Film (bleu) / Personne (vert) / Genre (orange). Arêtes orientées étiquetées par relation (`director` rouge, `actor` bleu, `genre` orange). **Alt-text cohérent avec l'image.**
- **Poids** : 153.1 KB (PIL optimise)

## sw11_kg_c71_o0.png

- **Source** : notebook `SymbolicAI/SemanticWeb/SW-11-Python-KnowledgeGraphs.ipynb` (cellule 71, output 0)
- **Alt-text (FR)** : Exercice 2 — même requête SPARQL ré-aimée sur les films de Quentin Tarantino ; la taille des noeuds-films est proportionnelle à la note (aggregateRating), illustrant un enrichissement du graphe de base.
- **Contenu réel vérifié** : Graphe orienté titré « Filmographie de Quentin Tarantino - Sous-graphe du KG » — 2 films (Kill Bill Vol. 1, Pulp Fiction, Django Unchained) + personnes (Tarantino, Travolta, Thurman, Waltz, Jackson, Liu, Foxx) + genres (Western, Crime, Action). Légende figure = « Film (taille proportionnelle à la note) » — la proportionnalité à `aggregateRating` est explicite dans le rendu. **Alt-text cohérent avec l'image.**
- **Poids** : 159.2 KB (PIL optimise)

## sw12_graphrag_c18_o0.png

- **Source** : notebook `SymbolicAI/SemanticWeb/SW-12-Python-GraphRAG.ipynb` (cellule 18, output 0)
- **Alt-text (FR)** *(corrigé c.469)* : Graphe orienté des entités extraites par LLM (filmographie Nolan) — noeuds colorés par **4 types d'entité effectivement visibles** (Person / Movie / Organization / Award), arêtes étiquetées par la relation extraite (acted_in, directed_by, starred_in, won, produced_by, etc.).
- **Contenu réel vérifié** : Graphe orienté titré « Graphe de connaissances extrait par LLM - Filmographie Nolan » — légende figure = exactement 4 couleurs/types (Person rouge, Movie vert clair, Organization bleu, Award jaune). 19 noeuds visibles (films, personnes, awards, organisation Warner Bros). Arêtes orientées étiquetées par relation. **Alt-text précédent sur-vendait (annonçait 6 types Person/Movie/Organization/Award/Genre/Concept alors que la figure n'en montre que 4) — corrigé.**
- **Poids** : 137.0 KB (PIL optimise)

## sw12_graphrag_c30_o1.png

- **Source** : notebook `SymbolicAI/SemanticWeb/SW-12-Python-GraphRAG.ipynb` (cellule 30, output 1)
- **Alt-text (FR)** : Détection de communautés par modularité gloutonne (networkx.algorithms.community.greedy_modularity_communities) sur le graphe non-dirigé — chaque couleur = une communauté, partition des entités pour la synthèse multi-niveau.
- **Contenu réel vérifié** : Graphe non-orienté titré « Détection de communautés dans le graphe de connaissances » — 6 communautés (légende = Communauté 1 à 6, chacune une couleur : rouge, vert, bleu, jaune, vert clair, violet). Arêtes grises non-orientées. Détection cohérente avec `greedy_modularity_communities` sur projection non-dirigée du KG. **Alt-text cohérent avec l'image.**
- **Poids** : 121.2 KB (PIL optimise)

## sw13_reasoner_c49_o0.png

- **Source** : notebook `SymbolicAI/SemanticWeb/SW-13-Python-Reasoners.ipynb` (cellule 49, output 0)
- **Alt-text (FR)** *(corrigé c.469)* : Diagramme en barres des temps d'exécution de **2 raisonneurs OWL** (`owlrl` 0.0721 s, `reasonable` 0.0016 s) — comparaison du coût de calcul de l'inférence sur ce benchmark (deux implémentations couvertes par la cellule 49).
- **Contenu réel vérifié** : Bar chart titré « Comparaison des temps d'exécution des raisonneurs OWL » — axe X = Raisonneur (2 valeurs : `owlrl`, `reasonable`), axe Y = Temps (secondes), 2 barres bleues + rouges annotées des valeurs exactes (0.0721 s et 0.0016 s). **Alt-text précédent sur-vendait (« un raisonneur par barre » suggérait une longue série) — corrigé pour refléter les 2 implémentations effectives du benchmark cellule 49.** (Le notebook couvre d'autres raisonneurs en cellules 45-48 ; ce benchmark particulier compare les 2 plus rapides.)
- **Poids** : 22.6 KB (PIL optimise)

## sw13_reasoner_c52_o0.png

- **Source** : notebook `SymbolicAI/SemanticWeb/SW-13-Python-Reasoners.ipynb` (cellule 52, output 0)
- **Alt-text (FR)** *(corrigé c.469)* : Diagramme en barres du **nombre de triples inférés** par **2 raisonneurs OWL 2 RL** (`owlrl` 211, `reasonable` 36) — comparaison du rendement de l'inférence entre les deux implémentations évaluées sur le benchmark cellule 52.
- **Contenu réel vérifié** : Bar chart titré « Triples inférés par raisonneur (OWL 2 RL) » — axe X = Raisonneur (2 valeurs : `owlrl`, `reasonable`), axe Y = Nombre de triples inférés, 2 barres bleues annotées des valeurs exactes (211 et 36). **Alt-text précédent parlait de « raisonneurs » au pluriel sans préciser le compte effectif — corrigé pour refléter les 2.**
- **Poids** : 19.9 KB (PIL optimise)