# Web Semantique - Semantic Web

Serie de notebooks pour explorer le **Web Semantique**, combinant **.NET C#** (dotNetRDF, fondations) et **Python** (rdflib, standards modernes, IA).

---

## Presentation

Le Web Semantique etend le Web classique en permettant aux machines de comprendre la signification des donnees. Cette serie couvre l'ensemble du spectre : des fondations RDF aux graphes de connaissances integres aux LLMs (GraphRAG), en passant par SPARQL, OWL, SHACL, JSON-LD et RDF 1.2.

La vision originale de Tim Berners-Lee etait de creer un "Web de donnees" ou les informations seraient liees de facon signifiante, permettant aux machines d'effectuer des raisonnements automatiques. Cette serie vous accompagnera depuis les concepts fondamentaux jusqu'aux applications modernes integrant l'IA generative.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 13 + 1 bonus |
| Duree totale | ~10h + 45min (bonus) |
| Langages | .NET C# (1-7), Python (8-14) |
| Niveau | Debutant a avance |

---

## Structure detaillee des notebooks

### Partie 1 : Fondations RDF (.NET C#)

Cette partie pose les fondations du Web Semantique en utilisant l'ecosysteme .NET avec la bibliotheque **dotNetRDF**, l'une des implementations RDF les plus completes pour C#.

#### SW-1-Setup : Premier pas dans le Web Semantique (20 min)

Ce notebook d'introduction vous guide a travers l'installation de dotNetRDF et decouvre la vision historique du Web Semantique. Vous creerez votre premier graphe RDF "Hello World" et comprendrez l'architecture en couches du W3C (le fameux "Layer Cake").

**Points cles appris** :
- La pile technologique W3C : Unicode → URI → RDF → RDFS → OWL → SPARQL
- Installation de dotNetRDF via NuGet dans .NET Interactive
- Creation d'un graphe et assertion de triplets (sujet-predicat-objet)
- Les differents types de noeuds : URI, blank nodes, litteraux

C'est le point de depart ideal pour comprendre pourquoi le Web Semantique matter : permettre aux machines de "comprendre" les donnees, pas seulement de les afficher.

#### SW-2-RDFBasics : Triples, Noeuds et Serialisation (45 min)

Dans ce notebook, vous approfondirez votre comprehension du modele de donnees RDF. Vous manipulerez les differents types de noeuds (URI, blank nodes, litteraux avec types et langues) et decouvrirez les principaux formats de serialisation.

**Points cles appris** :
- Structure d'un triplet RDF : sujet (URI/blank), predicat (URI), objet (URI/blank/literal)
- Litteraux typés (xsd:integer, xsd:dateTime, etc.) et avec tags de langue ("Bonjour"@fr)
- Formats de serialisation : Turtle (lisible), N-Triples (une ligne = un triplet), RDF/XML (historique)
- Creation de namespaces pour simplifier l'ecriture (ex: `ex:` pour `http://example.org/`)

Vous comprendrez pourquoi RDF est flexible : tout peut etre decrit avec des triplets, des simples proprietes aux relations complexes.

#### SW-3-GraphOperations : Manipulation Avancee de Graphes (50 min)

Ce notebook couvre les operations quotidiennes sur les graphes RDF : lecture depuis des fichiers, ecriture dans differents formats, fusion de graphes, et selection avancee avec LINQ.

**Points cles appris** :
- Parsers (`TurtleParser`, `NTriplesParser`) et Writers (`CompressingTurtleWriter`, `RdfXmlWriter`)
- Fusion de graphes avec `Merge()` : deduplication automatique, renommage des blank nodes
- Methodes `GetTriplesWithXxx()` pour la selection pattern-based
- Utilisation de LINQ pour des requetes complexes sur les triplets
- Listes RDF : `AssertList()`, `GetListItems()`, `AddToList()`, `RetractList()`

C'est ici que vous deviendrez efficace dans la manipulation quotidienne de graphes RDF.

#### SW-4-SPARQL : Le Langage de Requete du Web Semantique (45 min)

SPARQL est au RDF ce que SQL est aux bases de donnees relationnelles. Ce notebook vous apprendra a interroger vos graphes avec le Query Builder de dotNetRDF.

**Points cles appris** :
- SELECT SPARQL : projections, patterns de base
- Filtrage : `FILTER`, comparaisons, regex, tests d'existence
- Jointures implicites et `OPTIONAL` (LEFT JOIN semantics)
- `UNION` pour combiner plusieurs patterns
- `ORDER BY`, `LIMIT`, `OFFSET` pour pagination
- Constructeurs programmatiques avec `SparqlParameterizedString`

Vous pourrez ecrire des requetes complexes pour extraire exactement les informations necessaires depuis vos graphes.

---

### Partie 2 : Donnees Liees et Ontologies (.NET C#)

Cette partie etend vos competences aux donnees du Web ouvert (Linked Open Data) et aux ontologies qui permettent le raisonnement automatique.

#### SW-5-LinkedData : DBpedia, Wikidata et Requetes Federees (50 min)

Decouvrez le Web de donnees liees en interrogeant des endpoints publics comme DBpedia (extraction RDF de Wikipedia) et Wikidata (base de connaissances collaborative).

**Points cles appris** :
- Endpoint SPARQL public vs. graphe local
- `SparqlRemoteEndpoint` pour executer des requetes distantes
- Requetes federees avec `SERVICE` : interroger plusieurs endpoints simultanement
- Exploration de DBpedia : sujets, categories, liens inter-langues
- Wikidata et ses Q-items/P-properties : identifiants uniques vs. URIs lisibles

Vous decouvrirez la richesse des donnees deja disponibles sur le Web et comment les integrer dans vos applications.

#### SW-6-RDFS : Schema et Inference (40 min)

RDFS (RDF Schema) est la couche vocabulaire du Web Semantique. Ce notebook vous montre comment definir des classes, des proprietes et comment l'inference fonctionne.

**Points cles appris** :
- Vocabulaire RDFS : `rdfs:Class`, `rdfs:subClassOf`, `rdfs:domain`, `rdfs:range`
- Hierarchies de classes et transitivite de `subClassOf`
- Inference RDFS : deduction automatique de types et de relations
- `OntologyGraph` de dotNetRDF pour activer l'inference
- Differentes entre donnees assertees et inferrees

C'est votre premier pas vers le raisonnement automatique : la machine deduit de nouvelles connaissances a partir de regles.

#### SW-7-OWL : Ontologies et Raisonnement Avance (50 min)

OWL (Web Ontology Language) etend RDFS avec des constructeurs logiques puissants. Ce notebook presente les profils OWL 2 (EL, QL, RL) et le raisonnement.

**Points cles appris** :
- OWL 2 vs. RDFS : expressivite accrue (restrictions, cardinalites, disjonction)
- Profils OWL 2 : EL (grandes ontologies), QL (query rewriting), RL (regles)
- Constructeurs clés : `owl:equivalentClass`, `owl:unionOf`, `owl:intersectionOf`
- Restrictions : `owl:someValuesFrom` (∃), `owl:allValuesFrom` (∀)
- Raisonnement avec `OntologyGraph` et deduction de nouvelles connaissances

Vous comprendrez comment definir des ontologies formelles et les utiliser pour des raisonnements complexes.

---

### Partie 3 : Ecosysteme Python et Standards Modernes

Cette partie fait le pont vers l'ecosysteme Python, dominant pour l'IA et la data science, et couvre les standards modernes du Web Semantique.

#### SW-8-PythonRDF : rdflib et SPARQLWrapper (50 min)

Decouvrez rdflib, l'equivalent Python de dotNetRDF, et SPARQLWrapper pour interroger des endpoints distants. Une comparaison exhaustive avec dotNetRDF est fournie.

**Points cles appris** :
- API rdflib : `Graph()`, `URIRef()`, `Literal()`, `Namespace()`
- Methodes `g.add((s, p, o))` (tuple Python) vs. `g.Assert()` (objet Triple)
- Serialisation : `g.serialize(format="turtle")`
- SPARQL local avec `g.query()`
- SPARQLWrapper pour DBpedia et Wikidata : `SPARQLWrapper.setQuery()`, `.query().convert()`
- Tableau d'equivalence dotNetRDF ↔ rdflib

Ce notebook facilite la transition entre .NET et Python pour le Web Semantique.

#### SW-9-SHACL : Validation de Qualite des Donnees (45 min)

SHACL (Shapes Constraint Language) est le standard W3C pour valider la conformite des donnees RDF. Ce notebook utilise pySHACL pour definir des shapes et valider des graphes.

**Points cles appris** :
- Concepts SHACL : `NodeShape`, `PropertyShape`, contraintes
- Contraintes communes : `sh:minCount`, `sh:maxCount`, `sh:datatype`, `sh:nodeKind`
- `sh:property` pour valider les proprietes d'un noeud
- `sh:pattern` (regex), `sh:in` (enum), `sh:class` (type checking)
- Validation avec pySHACL : `Validate(graph, data_graph)`
- Rapport de validation : `conforms`, `results`

SHACL est essentiel pour garantir la qualite des donnees dans des systemes de production.

#### SW-10-JSONLD : Donnees Structurees pour le Web (40 min)

JSON-LD est le pont entre le monde JSON des developpeurs web et le Web Semantique. Ce notebook montre comment utiliser JSON-LD avec Schema.org pour le SEO.

**Points cles appris** :
- Format JSON-LD : `@context`, `@id`, `@type` pour mapper JSON vers RDF
- Integration Schema.org (vocabulaire Google, Bing, Yahoo)
- Compactage et expansion JSON-LD avec `jsonld` Python
- Rich snippets Google : 73% des resultats utilisent des donnees structurees
- Cas d'usage : e-commerce (Produit), articles (Article), organisations (Organization)
- Outils de validation : Google Rich Results Test

JSON-LD est pratique pour integrer le Web Semantique dans des applications web modernes.

#### SW-11-RDFStar : Annotations et Provenance (40 min)

RDF-Star (RDF 1.2) permet d'exprimer des statements a propos de statements, essentiel pour les annotations, la provenance et la confiance.

**Points cles appris** :
- Quoted triples : `<<<:s :p :o>>> :confidence 0.9`
- Use cases : annotations, provenance, confiance, probabilites
- Syntaxe Turtle-Star et N-Triples-Star
- SPARQL-Star : requetes sur les quoted triples
- rdflib support experimental RDF-Star
- Limitations et futures directions

RDF-Star est indispensable pour les applications nécessitant de raisonner sur les donnees elles-memes (metadonnees de metadonnees).

---

### Partie 4 : Graphes de Connaissances et IA

Cette partie connecte le Web Semantique avec l'IA moderne, notamment les LLMs et les graphes de connaissances.

#### SW-12-KnowledgeGraphs : Construction et Visualisation (55 min)

Ce notebook pratique vous guide dans la construction d'un graphe de connaissances complet, depuis des donnees brutes jusqu'a la visualisation interactive.

**Points cles appris** :
- kglab : abstraction haut niveau pour les KGs (Pandas + NetworkX + rdflib)
- Import depuis CSV/JSON vers RDF
- OWLReady2 : manipulation d'ontologies Python, raisonnement HermiT
- Visualisation avec NetworkX et pyvis : graphes interactifs HTML
- Patterns de modelling : entites, relations, attributs
- Integration d'ontologies externes (Wikidata, DBpedia)

Vous construirez un KG de demonstration (ex: films, acteurs) et le visualiserez.

#### SW-13-GraphRAG : KG + LLMs pour le RAG (50 min)

GraphRAG combine les graphes de connaissances avec les LLMs pour un Retrieval-Augmented Generation structure. Ce notebook presente l'approche de Microsoft GraphRAG.

**Points cles appris** :
- RAP (Retrieval-Augmented Generation) : limiter les hallucinations LLM
- GraphRAG Microsoft : extraction d'entites, construction de communautes
- LeMay-Huan framework : KG + LLM pour question answering
- Implementation avec OpenAI/Anthropic APIs
- Prompt engineering pour la generation structuree
- Comparaison RAP vectoriel vs. RAP structure (GraphRAG)

C'est la pointe de l'intersection Web Semantique / IA generative.

---

### Bonus : Comparaison de Raisonneurs OWL

#### SW-14-Reasoners : Benchmarks et Performances (45 min)

Ce notebook bonus compare differents raisonneurs OWL (owlrl, HermiT, reasonable, Growl) sur des criteres de performance et de facilite d'integration.

**Points cles appris** :
- owlrl : Python pur, OWL 2 RL, facile a installer
- OWLReady2 + HermiT : Java bridge, OWL 2 DL complet
- reasonable : Rust + Python bindings, OWL 2 RL, performance native
- Growl : C (verifie Z3), OWL 2 RL, installation manuelle
- Benchmark temps d'execution : Python vs. compile
- Choix du raisonneur selon le cas d'usage

Vous saurez quel raisonneur choisir selon vos contraintes : performance, expressivite, facilité d'installation.

---

## Statut de maturite

| # | Notebook | Cellules | Exercices | Statut |
|---|----------|----------|-----------|--------|
| 1 | Setup | 18 | - | **COMPLET** |
| 2 | RDFBasics | 48 | 2 | **COMPLET** |
| 3 | GraphOperations | 34 | 3 | **COMPLET** |
| 4 | SPARQL | 36 | 3 | **COMPLET** |
| 5 | LinkedData | 38 | 3 | **COMPLET** |
| 6 | RDFS | 33 | 2 | **COMPLET** |
| 7 | OWL | 35 | 2 | **COMPLET** |
| 8 | PythonRDF | 56 | 3 | **COMPLET** |
| 9 | SHACL | 43 | 3 | **COMPLET** |
| 10 | JSONLD | 60 | 3 | **COMPLET** |
| 11 | RDFStar | 52 | 2 | **COMPLET** |
| 12 | KnowledgeGraphs | 75 | 3 | **COMPLET** |
| 13 | GraphRAG | 44 | 3 | **COMPLET** |
| 14 | Reasoners (bonus) | 38 | 3 | **COMPLET** |

---

## Prerequisites

### Pour les notebooks .NET (1-7)

- .NET SDK 9.0+
- .NET Interactive (Jupyter kernel)
- VS Code avec Polyglot Notebooks (recommande)

### Pour les notebooks Python (8-14)

- Python 3.10+
- pip install -r requirements.txt

### Pour le notebook 13 (GraphRAG)

- Cle API OpenAI ou Anthropic (voir `.env.example`)

## Installation

### 1. Environnement .NET

```bash
dotnet tool install -g Microsoft.dotnet-interactive
dotnet interactive jupyter install
```

### 2. Environnement Python

```bash
python -m venv venv
venv\Scripts\activate  # Windows
pip install -r requirements.txt
```

### 3. Configuration API (optionnel, pour SW-13)

```bash
cp .env.example .env
# Editer .env avec vos cles API
```

## Technologies et versions

| Technologie | Version | Notebooks | Role |
|-------------|---------|-----------|------|
| dotNetRDF | 3.4.1 | SW-1 a SW-7 | Core RDF/SPARQL en .NET |
| rdflib | 7.5.0 | SW-8 a SW-14 | Core RDF/SPARQL en Python |
| pySHACL | 0.27.0 | SW-9 | Validation SHACL |
| OWLReady2 | 0.50+ | SW-12 | Manipulation ontologies |
| SPARQLWrapper | 2.0+ | SW-5, SW-8 | Requetes endpoints distants |
| kglab | 0.6.1+ | SW-12 | Abstraction graphes de connaissances |
| owlrl | 6.0+ | SW-14 | Raisonneur OWL 2 RL Python pur |
| reasonable | 0.1+ | SW-14 | Raisonneur OWL 2 RL Rust |

## Standards W3C couverts

| Standard | Version | Notebook |
|----------|---------|----------|
| RDF | 1.1 / 1.2 | SW-2, SW-11 |
| SPARQL | 1.1 | SW-4, SW-5 |
| RDFS | 1.0 | SW-6 |
| OWL | 2 | SW-7 |
| SHACL | 1.0 | SW-9 |
| JSON-LD | 1.1 | SW-10 |

## Structure des fichiers

```
SemanticWeb/
├── README.md
├── requirements.txt
├── .env.example
├── data/
│   ├── Example.ttl          # Exemple Turtle (de RDF.Net)
│   ├── example.srj           # Resultats SPARQL JSON
│   ├── example.srx           # Resultats SPARQL XML
│   ├── animals.ttl            # Hierarchie RDFS
│   ├── university.owl         # Ontologie OWL 2
│   ├── person-shape.ttl       # Shapes SHACL
│   ├── person-data.ttl        # Donnees test (avec erreurs)
│   ├── product.jsonld         # Exemple Schema.org
│   └── movies.csv             # Dataset pour KG
├── RDF.Net-Legacy/
│   ├── RDF.Net.ipynb        # Notebook original (173 cellules, reference)
│   ├── Example.ttl
│   ├── example.srj
│   └── example.srx
├── SW-1-Setup.ipynb
├── SW-2-RDFBasics.ipynb
├── ...
└── SW-14-Reasoners.ipynb
```

## Origine

Cette serie est une refonte complete du notebook monolithique `RDF.Net.ipynb` (173 cellules), eclate en 13 notebooks progressifs et enrichi de tous les standards modernes du Web Semantique (2024-2026).

Le notebook original est conserve dans [RDF.Net-Legacy/](RDF.Net-Legacy/) a titre de reference historique.

## Ressources

- [dotNetRDF](https://dotnetrdf.org/) - Bibliotheque .NET pour RDF
- [rdflib](https://rdflib.readthedocs.io/) - Bibliotheque Python pour RDF
- [W3C RDF](https://www.w3.org/RDF/) - Standard RDF
- [W3C SPARQL](https://www.w3.org/TR/sparql11-overview/) - Standard SPARQL
- [W3C OWL](https://www.w3.org/OWL/) - Standard OWL
- [W3C SHACL](https://www.w3.org/TR/shacl/) - Standard SHACL
- [JSON-LD](https://json-ld.org/) - JSON pour les donnees liees
- [DBpedia](https://dbpedia.org/) - Donnees structurees de Wikipedia
- [Wikidata](https://www.wikidata.org/) - Base de connaissances libre

## Licence

Voir la licence du repository principal.
