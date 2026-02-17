# Web Semantique - Semantic Web

Serie de notebooks pour explorer le **Web Semantique**, combinant **.NET C#** (dotNetRDF, fondations) et **Python** (rdflib, standards modernes, IA).

---

## Presentation

Le Web Semantique etend le Web classique en permettant aux machines de comprendre la signification des donnees. Cette serie couvre l'ensemble du spectre : des fondations RDF aux graphes de connaissances integres aux LLMs (GraphRAG), en passant par SPARQL, OWL, SHACL, JSON-LD et RDF 1.2.

La vision originale de Tim Berners-Lee etait de creer un "Web de donnees" ou les informations seraient liees de facon signifiante, permettant aux machines d'effectuer des raisonnements automatiques. Cette serie vous accompagnera depuis les concepts fondamentaux jusqu'aux applications modernes integrant l'IA generative.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks principaux | 12 + 1 bonus |
| Sidetracks Python | 4 optionnels |
| Duree totale | ~10h + 45min (bonus) |
| Langages | .NET C# (1-7), Python (8-13) |
| Niveau | Debutant a avance |

> **Nouvelle convention** : Tous les noms de notebooks incluent explicitement le langage (`CSharp` ou `Python`) pour une identification immediate.

---

## Progression recommandee

### Parcours principal
Suivez les notebooks **SW-1 a SW-12** dans l'ordre numerique pour une progression logique des concepts.

### Sidetracks Python (optionnels)
Les sidetracks marques `b-Python` sont des notebooks complementaires qui presentent l'equivalent Python des concepts .NET. Ils sont **optionnels** mais recommandes si vous souhaitez travailler avec Python plutot qu'avec .NET.

| Sidetrack | Notebook principal | Contenu |
|-----------|-------------------|---------|
| SW-2b-Python-RDFBasics | SW-2-CSharp-RDFBasics | RDF en Python avec rdflib |
| SW-4b-Python-SPARQL | SW-4-CSharp-SPARQL | SPARQL en Python avec rdflib |
| SW-5b-Python-LinkedData | SW-5-CSharp-LinkedData | DBpedia/Wikidata avec SPARQLWrapper |
| SW-7b-Python-OWL | SW-7-CSharp-OWL | Ontologies OWL avec OWLReady2 |

---

## Structure detaillee des notebooks

### Partie 1 : Fondations RDF (.NET C#)

Cette partie pose les fondations du Web Semantique en utilisant l'ecosysteme .NET avec la bibliotheque **dotNetRDF**.

| # | Notebook | Duree | Sidetrack Python |
|---|----------|-------|------------------|
| 1 | **SW-1-CSharp-Setup** | 20 min | - |
| 2 | **SW-2-CSharp-RDFBasics** | 45 min | SW-2b-Python-RDFBasics |
| 3 | **SW-3-CSharp-GraphOperations** | 50 min | - |
| 4 | **SW-4-CSharp-SPARQL** | 45 min | SW-4b-Python-SPARQL |

#### SW-1-CSharp-Setup : Premier pas dans le Web Semantique (20 min)

Ce notebook d'introduction vous guide a travers l'installation de dotNetRDF et decouvre la vision historique du Web Semantique. Vous creerez votre premier graphe RDF "Hello World" et comprendrez l'architecture en couches du W3C.

**Points cles appris** :
- La pile technologique W3C : Unicode → URI → RDF → RDFS → OWL → SPARQL
- Installation de dotNetRDF via NuGet dans .NET Interactive
- Creation d'un graphe et assertion de triplets (sujet-predicat-objet)
- Les differents types de noeuds : URI, blank nodes, litteraux

#### SW-2-CSharp-RDFBasics : Triples, Noeuds et Serialisation (45 min)

Dans ce notebook, vous approfondirez votre comprehension du modele de donnees RDF. Vous manipulerez les differents types de noeuds et decouvrirez les principaux formats de serialisation.

**Points cles appris** :
- Structure d'un triplet RDF : sujet (URI/blank), predicat (URI), objet (URI/blank/literal)
- Litteraux typés (xsd:integer, xsd:dateTime) et avec tags de langue ("Bonjour"@fr)
- Formats de serialisation : Turtle, N-Triples, RDF/XML
- Creation de namespaces pour simplifier l'ecriture

> **Sidetrack Python disponible** : [SW-2b-Python-RDFBasics](SW-2b-Python-RDFBasics.ipynb) - Equivalent Python avec rdflib

#### SW-3-CSharp-GraphOperations : Manipulation Avancee de Graphes (50 min)

Ce notebook couvre les operations quotidiennes sur les graphes RDF : lecture/ecriture, fusion, et selection avancee avec LINQ.

**Points cles appris** :
- Parsers (`TurtleParser`, `NTriplesParser`) et Writers (`CompressingTurtleWriter`, `RdfXmlWriter`)
- Fusion de graphes avec `Merge()` : deduplication automatique, renommage des blank nodes
- Methodes `GetTriplesWithXxx()` pour la selection pattern-based
- Utilisation de LINQ pour des requetes complexes sur les triplets
- Listes RDF : `AssertList()`, `GetListItems()`, `AddToList()`

#### SW-4-CSharp-SPARQL : Le Langage de Requete (45 min)

SPARQL est au RDF ce que SQL est aux bases de donnees relationnelles. Ce notebook vous apprendra a interroger vos graphes avec le Query Builder de dotNetRDF.

**Points cles appris** :
- SELECT SPARQL : projections, patterns de base
- Filtrage : `FILTER`, comparaisons, regex, tests d'existence
- Jointures implicites et `OPTIONAL` (LEFT JOIN semantics)
- `UNION` pour combiner plusieurs patterns
- `ORDER BY`, `LIMIT`, `OFFSET` pour pagination

> **Sidetrack Python disponible** : [SW-4b-Python-SPARQL](SW-4b-Python-SPARQL.ipynb) - Equivalent Python avec rdflib

---

### Partie 2 : Donnees Liees et Ontologies (.NET C#)

Cette partie etend vos competences aux donnees du Web ouvert et aux ontologies qui permettent le raisonnement automatique.

| # | Notebook | Duree | Sidetrack Python |
|---|----------|-------|------------------|
| 5 | **SW-5-CSharp-LinkedData** | 50 min | SW-5b-Python-LinkedData |
| 6 | **SW-6-CSharp-RDFS** | 40 min | - |
| 7 | **SW-7-CSharp-OWL** | 50 min | SW-7b-Python-OWL |

#### SW-5-CSharp-LinkedData : DBpedia, Wikidata et Requetes Federees (50 min)

Decouvrez le Web de donnees liees en interrogeant des endpoints publics comme DBpedia et Wikidata.

**Points cles appris** :
- Endpoint SPARQL public vs. graphe local
- `SparqlRemoteEndpoint` pour executer des requetes distantes
- Requetes federees avec `SERVICE` : interroger plusieurs endpoints simultanement
- Exploration de DBpedia : sujets, categories, liens inter-langues
- Wikidata et ses Q-items/P-properties

> **Sidetrack Python disponible** : [SW-5b-Python-LinkedData](SW-5b-Python-LinkedData.ipynb) - DBpedia/Wikidata avec SPARQLWrapper

#### SW-6-CSharp-RDFS : Schema et Inference (40 min)

RDFS (RDF Schema) est la couche vocabulaire du Web Semantique. Ce notebook vous montre comment definir des classes, des proprietes et comment l'inference fonctionne.

**Points cles appris** :
- Vocabulaire RDFS : `rdfs:Class`, `rdfs:subClassOf`, `rdfs:domain`, `rdfs:range`
- Hierarchies de classes et transitivite de `subClassOf`
- Inference RDFS : deduction automatique de types et de relations
- `OntologyGraph` de dotNetRDF pour activer l'inference

#### SW-7-CSharp-OWL : Ontologies et Raisonnement Avance (50 min)

OWL (Web Ontology Language) etend RDFS avec des constructeurs logiques puissants. Ce notebook presente les profils OWL 2 et le raisonnement.

**Points cles appris** :
- OWL 2 vs. RDFS : expressivite accrue (restrictions, cardinalites, disjonction)
- Profils OWL 2 : EL (grandes ontologies), QL (query rewriting), RL (regles)
- Constructeurs clés : `owl:equivalentClass`, `owl:unionOf`, `owl:intersectionOf`
- Restrictions : `owl:someValuesFrom` (∃), `owl:allValuesFrom` (∀)
- Raisonnement avec `OntologyGraph`

> **Sidetrack Python disponible** : [SW-7b-Python-OWL](SW-7b-Python-OWL.ipynb) - Ontologies OWL avec OWLReady2

---

### Partie 3 : Standards Modernes (Python uniquement)

Cette partie couvre les standards modernes du Web Semantique, exclusivement en Python (ecosystem dominant pour l'IA).

| # | Notebook | Duree | Contenu |
|---|----------|-------|---------|
| 8 | **SW-8-Python-SHACL** | 45 min | Validation de donnees avec pySHACL |
| 9 | **SW-9-Python-JSONLD** | 40 min | Donnees structurees pour le web |
| 10 | **SW-10-Python-RDFStar** | 40 min | RDF 1.2, annotations et provenance |

#### SW-8-Python-SHACL : Validation de Qualite des Donnees (45 min)

SHACL (Shapes Constraint Language) est le standard W3C pour valider la conformite des donnees RDF. Ce notebook utilise pySHACL pour definir des shapes et valider des graphes.

**Points cles appris** :
- Concepts SHACL : `NodeShape`, `PropertyShape`, contraintes
- Contraintes communes : `sh:minCount`, `sh:maxCount`, `sh:datatype`, `sh:nodeKind`
- `sh:property` pour valider les proprietes d'un noeud
- `sh:pattern` (regex), `sh:in` (enum), `sh:class` (type checking)
- Validation avec pySHACL : `Validate(graph, data_graph)`

#### SW-9-Python-JSONLD : Donnees Structurees pour le Web (40 min)

JSON-LD est le pont entre le monde JSON des developpeurs web et le Web Semantique. Ce notebook montre comment utiliser JSON-LD avec Schema.org pour le SEO.

**Points cles appris** :
- Format JSON-LD : `@context`, `@id`, `@type` pour mapper JSON vers RDF
- Integration Schema.org (vocabulaire Google, Bing, Yahoo)
- Compactage et expansion JSON-LD avec `jsonld` Python
- Rich snippets Google : 73% des resultats utilisent des donnees structurees
- Cas d'usage : e-commerce (Produit), articles (Article), organisations (Organization)

#### SW-10-Python-RDFStar : Annotations et Provenance (40 min)

RDF-Star (RDF 1.2) permet d'exprimer des statements a propos de statements, essentiel pour les annotations, la provenance et la confiance.

**Points cles appris** :
- Quoted triples : `<<<:s :p :o>>> :confidence 0.9`
- Use cases : annotations, provenance, confiance, probabilites
- Syntaxe Turtle-Star et N-Triples-Star
- SPARQL-Star : requetes sur les quoted triples
- rdflib support experimental RDF-Star

---

### Partie 4 : Graphes de Connaissances et IA (Python)

Cette partie connecte le Web Semantique avec l'IA moderne, notamment les LLMs et les graphes de connaissances.

| # | Notebook | Duree | Contenu |
|---|----------|-------|---------|
| 11 | **SW-11-Python-KnowledgeGraphs** | 55 min | Construction et visualisation de KGs |
| 12 | **SW-12-Python-GraphRAG** | 50 min | KG + LLMs pour le RAG |
| **Bonus** | **SW-13-Python-Reasoners** | 45 min | Comparaison raisonneurs OWL |

#### SW-11-Python-KnowledgeGraphs : Construction et Visualisation (55 min)

Ce notebook pratique vous guide dans la construction d'un graphe de connaissances complet, depuis des donnees brutes jusqu'a la visualisation interactive.

**Points cles appris** :
- kglab : abstraction haut niveau pour les KGs (Pandas + NetworkX + rdflib)
- Import depuis CSV/JSON vers RDF
- OWLReady2 : manipulation d'ontologies Python, raisonnement HermiT
- Visualisation avec NetworkX et pyvis : graphes interactifs HTML
- Patterns de modelling : entites, relations, attributs

#### SW-12-Python-GraphRAG : KG + LLMs pour le RAG (50 min)

GraphRAG combine les graphes de connaissances avec les LLMs pour un Retrieval-Augmented Generation structure. Ce notebook presente l'approche de Microsoft GraphRAG.

**Points cles appris** :
- RAP (Retrieval-Augmented Generation) : limiter les hallucinations LLM
- GraphRAG Microsoft : extraction d'entites, construction de communautes
- LeMay-Huan framework : KG + LLM pour question answering
- Implementation avec OpenAI/Anthropic APIs
- Comparaison RAP vectoriel vs. RAP structure (GraphRAG)

#### SW-13-Python-Reasoners (Bonus) : Benchmarks et Performances (45 min)

Ce notebook bonus compare differents raisonneurs OWL (owlrl, HermiT, reasonable, Growl) sur des criteres de performance et de facilite d'integration.

**Points cles appris** :
- owlrl : Python pur, OWL 2 RL, facile a installer
- OWLReady2 + HermiT : Java bridge, OWL 2 DL complet
- reasonable : Rust + Python bindings, OWL 2 RL, performance native
- Growl : C (verifie Z3), OWL 2 RL, installation manuelle
- Benchmark temps d'execution : Python vs. compile

---

## Statut de maturite

| # | Notebook | Kernel | Cellules | Exercices | Statut |
|---|----------|--------|----------|-----------|--------|
| 1 | SW-1-CSharp-Setup | .NET | 18 | - | **COMPLET** |
| 2 | SW-2-CSharp-RDFBasics | .NET | 48 | 2 | **COMPLET** |
| 2b | SW-2b-Python-RDFBasics | Python | 30 | 2 | **COMPLET** |
| 3 | SW-3-CSharp-GraphOperations | .NET | 34 | 3 | **COMPLET** |
| 4 | SW-4-CSharp-SPARQL | .NET | 36 | 3 | **COMPLET** |
| 4b | SW-4b-Python-SPARQL | Python | 25 | 2 | **COMPLET** |
| 5 | SW-5-CSharp-LinkedData | .NET | 38 | 3 | **COMPLET** |
| 5b | SW-5b-Python-LinkedData | Python | 25 | 2 | **COMPLET** |
| 6 | SW-6-CSharp-RDFS | .NET | 33 | 2 | **COMPLET** |
| 7 | SW-7-CSharp-OWL | .NET | 35 | 2 | **COMPLET** |
| 7b | SW-7b-Python-OWL | Python | 30 | 2 | **COMPLET** |
| 8 | SW-8-Python-SHACL | Python | 43 | 3 | **COMPLET** |
| 9 | SW-9-Python-JSONLD | Python | 60 | 3 | **COMPLET** |
| 10 | SW-10-Python-RDFStar | Python | 52 | 2 | **COMPLET** |
| 11 | SW-11-Python-KnowledgeGraphs | Python | 75 | 3 | **COMPLET** |
| 12 | SW-12-Python-GraphRAG | Python | 44 | 3 | **COMPLET** |
| 13 | SW-13-Python-Reasoners (bonus) | Python | 38 | 3 | **COMPLET** |

---

## Prerequisites

### Pour les notebooks .NET (SW-1 a SW-7)

- .NET SDK 9.0+
- .NET Interactive (Jupyter kernel)
- VS Code avec Polyglot Notebooks (recommande)

### Pour les notebooks Python (SW-8 a SW-13 et sidetracks)

- Python 3.10+
- pip install -r requirements.txt

### Pour le notebook 12 (GraphRAG)

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

### 3. Configuration API (optionnel, pour SW-12)

```bash
cp .env.example .env
# Editer .env avec vos cles API
```

## Technologies et versions

| Technologie | Version | Notebooks | Role |
|-------------|---------|-----------|------|
| dotNetRDF | 3.4.1 | SW-1 a SW-7 | Core RDF/SPARQL en .NET |
| rdflib | 7.5.0 | Sidetracks, SW-8 a SW-12 | Core RDF/SPARQL en Python |
| pySHACL | 0.27.0 | SW-8 | Validation SHACL |
| OWLReady2 | 0.50+ | SW-7b, SW-11 | Manipulation ontologies |
| SPARQLWrapper | 2.0+ | SW-5b | Requetes endpoints distants |
| kglab | 0.6.1+ | SW-11 | Abstraction graphes de connaissances |
| owlrl | 6.0+ | SW-13 | Raisonneur OWL 2 RL Python pur |
| reasonable | 0.1+ | SW-13 | Raisonneur OWL 2 RL Rust |

## Standards W3C couverts

| Standard | Version | Notebook |
|----------|---------|----------|
| RDF | 1.1 / 1.2 | SW-2, SW-10 |
| SPARQL | 1.1 | SW-4, SW-5 |
| RDFS | 1.0 | SW-6 |
| OWL | 2 | SW-7, SW-13 |
| SHACL | 1.0 | SW-8 |
| JSON-LD | 1.1 | SW-9 |

## Structure des fichiers

```
SemanticWeb/
├── README.md
├── requirements.txt
├── .env.example
├── data/
│   ├── Example.ttl          # Exemple Turtle
│   ├── animals.ttl          # Hierarchie RDFS
│   ├── university.owl       # Ontologie OWL 2
│   ├── person-shape.ttl     # Shapes SHACL
│   ├── person-data.ttl      # Donnees test (avec erreurs)
│   └── movies.csv           # Dataset pour KG
├── SW-1-CSharp-Setup.ipynb
├── SW-2-CSharp-RDFBasics.ipynb
├── SW-2b-Python-RDFBasics.ipynb     # Sidetrack
├── SW-3-CSharp-GraphOperations.ipynb
├── SW-4-CSharp-SPARQL.ipynb
├── SW-4b-Python-SPARQL.ipynb        # Sidetrack
├── SW-5-CSharp-LinkedData.ipynb
├── SW-5b-Python-LinkedData.ipynb    # Sidetrack
├── SW-6-CSharp-RDFS.ipynb
├── SW-7-CSharp-OWL.ipynb
├── SW-7b-Python-OWL.ipynb           # Sidetrack
├── SW-8-Python-SHACL.ipynb
├── SW-9-Python-JSONLD.ipynb
├── SW-10-Python-RDFStar.ipynb
├── SW-11-Python-KnowledgeGraphs.ipynb
├── SW-12-Python-GraphRAG.ipynb
└── SW-13-Python-Reasoners.ipynb     # Bonus
```

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
