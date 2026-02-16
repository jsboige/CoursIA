# Web Semantique - Semantic Web

Serie de notebooks pour explorer le **Web Semantique**, combinant **.NET C#** (dotNetRDF, fondations) et **Python** (rdflib, standards modernes, IA).

## Presentation

Le Web Semantique etend le Web classique en permettant aux machines de comprendre la signification des donnees. Cette serie couvre l'ensemble du spectre : des fondations RDF aux graphes de connaissances integres aux LLMs (GraphRAG), en passant par SPARQL, OWL, SHACL, JSON-LD et RDF 1.2.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 13 |
| Duree totale | ~10h |
| Langages | .NET C# (1-7), Python (8-13) |
| Niveau | Debutant a avance |

## Structure

**13 notebooks** organises en **4 parties** progressives.

### Partie 1 : Fondations RDF (.NET C#)

| # | Notebook | Kernel | Contenu | Duree |
|---|----------|--------|---------|-------|
| 1 | [SW-1-Setup](SW-1-Setup.ipynb) | .NET C# | Installation dotNetRDF, concepts RDF, premier graphe | 20 min |
| 2 | [SW-2-RDFBasics](SW-2-RDFBasics.ipynb) | .NET C# | Triples, noeuds, URI, bnodes, litteraux, serialisation | 45 min |
| 3 | [SW-3-GraphOperations](SW-3-GraphOperations.ipynb) | .NET C# | Lecture, ecriture, fusion, selection, listes RDF | 50 min |
| 4 | [SW-4-SPARQL](SW-4-SPARQL.ipynb) | .NET C# | Query Builder, SELECT, FILTER, OPTIONAL, UNION, ORDER BY | 45 min |

### Partie 2 : Donnees Liees et Ontologies (.NET C#)

| # | Notebook | Kernel | Contenu | Duree |
|---|----------|--------|---------|-------|
| 5 | [SW-5-LinkedData](SW-5-LinkedData.ipynb) | .NET C# | DBpedia, Wikidata, requetes federees SERVICE | 50 min |
| 6 | [SW-6-RDFS](SW-6-RDFS.ipynb) | .NET C# | Vocabulaire RDFS, inference, hierarchies de classes | 40 min |
| 7 | [SW-7-OWL](SW-7-OWL.ipynb) | .NET C# | OWL 2, OntologyGraph, profils EL/QL/RL, raisonnement | 50 min |

### Partie 3 : Ecosysteme Python et Standards Modernes

| # | Notebook | Kernel | Contenu | Duree |
|---|----------|--------|---------|-------|
| 8 | [SW-8-PythonRDF](SW-8-PythonRDF.ipynb) | Python | rdflib, SPARQLWrapper, comparaison dotNetRDF vs rdflib | 50 min |
| 9 | [SW-9-SHACL](SW-9-SHACL.ipynb) | Python | Validation pySHACL, contraintes, qualite des donnees | 45 min |
| 10 | [SW-10-JSONLD](SW-10-JSONLD.ipynb) | Python | JSON-LD, Schema.org, donnees structurees web | 40 min |
| 11 | [SW-11-RDFStar](SW-11-RDFStar.ipynb) | Python | RDF 1.2 (RDF-Star), quoted triples, SPARQL-Star | 40 min |

### Partie 4 : Graphes de Connaissances et IA

| # | Notebook | Kernel | Contenu | Duree |
|---|----------|--------|---------|-------|
| 12 | [SW-12-KnowledgeGraphs](SW-12-KnowledgeGraphs.ipynb) | Python | Construction KGs, kglab, OWLReady2, visualisation | 55 min |
| 13 | [SW-13-GraphRAG](SW-13-GraphRAG.ipynb) | Python | KG + LLMs, Microsoft GraphRAG, extraction entites | 50 min |

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
| 13 | GraphRAG | 72 | 3 | **COMPLET** |

## Prerequisites

### Pour les notebooks .NET (1-7)

- .NET SDK 9.0+
- .NET Interactive (Jupyter kernel)
- VS Code avec Polyglot Notebooks (recommande)

### Pour les notebooks Python (8-13)

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
| rdflib | 7.5.0 | SW-8 a SW-13 | Core RDF/SPARQL en Python |
| pySHACL | 0.27.0 | SW-9 | Validation SHACL |
| OWLReady2 | 0.50+ | SW-12 | Manipulation ontologies |
| SPARQLWrapper | 2.0+ | SW-5, SW-8 | Requetes endpoints distants |
| kglab | 0.6.1+ | SW-12 | Abstraction graphes de connaissances |

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
└── SW-13-GraphRAG.ipynb
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
- [DBpedia](https://www.dbpedia.org/) - Donnees structurees de Wikipedia
- [Wikidata](https://www.wikidata.org/) - Base de connaissances libre

## Licence

Voir la licence du repository principal.
