---
theme: ../theme-ia101
title: "Web Semantique - dotNetRDF & Python"
info: IA 101 - Web semantique, ontologies et graphes de connaissances
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Web Semantique — RDF, SPARQL, OWL et Knowledge Graphs

- Modele de donnees : RDF, triplets, graphes nommes
- Interrogation : SPARQL, requetes federees, Linked Data
- Schema et ontologies : RDFS, OWL 2, SHACL
- Web moderne : JSON-LD, RDF-Star, Knowledge Graphs
- Integration IA : GraphRAG, raisonneurs OWL

---
layout: section
---

# Plan

---

# Sommaire

## Objectifs pedagogiques

- Comprendre le **modele RDF** : triplets, URI, types de noeuds, serialisation
- Interroger des graphes avec **SPARQL** et les endpoints du Web of Data
- Modeliser des **ontologies** : RDFS (classes, proprietes) et OWL 2 (logiques de description)
- Valider des donnees avec **SHACL** et manipuler JSON-LD, RDF-Star
- Construire des **Knowledge Graphs** et des pipelines **GraphRAG**

## Prerequis

- C# .NET Interactive (series SW-1 a SW-7) · Python 3.10+ (series SW-2b, SW-4b, SW-5b, SW-7b, SW-8+)
- Connaissances de base en logique et en bases de donnees relationnelles

## Duree totale estimee

**~9 heures** (13 notebooks, 20 min a 55 min chacun)

---
layout: section
---

# Fondations

---

# SW-1 — Configuration et Pile Technologique

## La vision du Web Semantique (Berners-Lee, 2001)

- Web actuel : donnees pour les humains (HTML)
- Web Semantique : donnees comprehensibles par les **machines**
- Pile technologique : **URI → RDF → RDFS → OWL → SPARQL → SHACL**

## dotNetRDF : la bibliotheque de reference

```csharp
#r "nuget: dotNetRDF, 3.2.0"

using VDS.RDF;
using VDS.RDF.Parsing;

var graph = new Graph();
graph.LoadFromFile("data.ttl");
Console.WriteLine($"Triplets : {graph.Triples.Count}");
```

- **dotNetRDF** : parsing, requetes, raisonnement pour .NET
- Formats supportes : Turtle, RDF/XML, N-Triples, JSON-LD
- Namespace central : `VDS.RDF` + sous-espaces `Parsing`, `Query`, `Writing`

> **Notebook** : `SW-1-CSharp-Setup.ipynb` — 20 min

---

# SW-2 — Fondamentaux RDF (C#)

## Anatomie d'un triplet RDF

Un triplet = `(sujet, predicat, objet)` — la phrase atomique du Web Semantique

| Composant | Type | Exemple |
|-----------|------|---------|
| **Sujet** | URI ou Blank node | `ex:Alan_Turing` |
| **Predicat** | URI | `foaf:name` |
| **Objet** | URI, Blank node ou Literal | `"Alan Turing"@en` |

## Construction et serialisation

```csharp
var graph = new Graph();
graph.NamespaceMap.AddNamespace("ex", new Uri("http://example.org/"));
graph.NamespaceMap.AddNamespace("foaf", new Uri("http://xmlns.com/foaf/0.1/"));

IUriNode turing = graph.CreateUriNode("ex:Alan_Turing");
IUriNode name = graph.CreateUriNode("foaf:name");
ILiteralNode nameVal = graph.CreateLiteralNode("Alan Turing", "en");
graph.Assert(turing, name, nameVal);
```

- Serialisations : Turtle (lisible), RDF/XML (legacy), N-Triples (streaming)
- `PlainLiteral`, `TypedLiteral` (`xsd:integer`, `xsd:dateTime`...)

> **Notebook** : `SW-2-CSharp-RDFBasics.ipynb` — 45 min

---

# SW-2b — RDF Fondamentaux (Python)

## rdflib : l'equivalent Python de dotNetRDF

```python
from rdflib import Graph, Namespace, Literal, URIRef
from rdflib.namespace import FOAF, RDF, XSD

g = Graph()
EX = Namespace("http://example.org/")

g.add((EX.Alan_Turing, FOAF.name, Literal("Alan Turing", lang="en")))
g.add((EX.Alan_Turing, EX.born, Literal("1912-06-23", datatype=XSD.date)))

# Serialiser en Turtle
print(g.serialize(format="turtle"))
```

## Comparaison C# / Python

| Feature | dotNetRDF | rdflib |
|---------|-----------|--------|
| Graph | `Graph()` | `Graph()` |
| Namespace | `NamespaceMap.AddNamespace` | `Namespace()` |
| Triple | `graph.Assert(s, p, o)` | `g.add((s, p, o))` |
| Serialize | `StringWriter` + `TurtleWriter` | `g.serialize(format=...)` |

> **Notebook** : `SW-2b-Python-RDFBasics.ipynb` — 40 min

---

# SW-3 — Operations sur les Graphes

## Lecture et ecriture de fichiers RDF

```csharp
// Lecture multi-format : auto-detection
var parser = new TurtleParser();
var graph = new Graph();
parser.Load(graph, "ontology.ttl");

// Fusion de graphes
var merged = new Graph();
merged.Merge(graph1);
merged.Merge(graph2);

// Ecriture en Turtle
using var writer = new StreamWriter("output.ttl");
var ttlWriter = new CompressingTurtleWriter();
ttlWriter.Save(merged, writer);
```

## Graphes nommes et TripleStore

- **Named Graph** : graphe avec une URI propre (`ex:graph1`)
- **TripleStore** : ensemble de graphes nommes (quad-store)
- **InMemoryDataset** : dataset SPARQL multi-graphes
- Requetes sur l'union de tous les graphes ou un graphe specifique

> **Notebook** : `SW-3-CSharp-GraphOperations.ipynb` — 50 min

---
layout: section
---

# Interrogation

---

# SW-4 — SPARQL : Le SQL du Web Semantique

## Types de requetes SPARQL

| Requete | Usage |
|---------|-------|
| **SELECT** | Retourne des tables de variables |
| **CONSTRUCT** | Construit un nouveau graphe RDF |
| **ASK** | Teste l'existence d'un pattern |
| **DESCRIBE** | Decrit une ressource |

## Requete SELECT avec dotNetRDF

```csharp
var query = @"
PREFIX foaf: <http://xmlns.com/foaf/0.1/>
SELECT ?person ?name WHERE {
    ?person foaf:name ?name ;
            foaf:age  ?age .
    FILTER (?age > 18)
} ORDER BY ?name LIMIT 10";

var results = graph.ExecuteQuery(query) as SparqlResultSet;
foreach (var result in results)
    Console.WriteLine($"{result["person"]} → {result["name"]}");
```

- **OPTIONAL** : jointure externe · **UNION** : disjonction · **MINUS** : difference
- Agregats : `COUNT`, `SUM`, `GROUP BY`, `HAVING`

> **Notebooks** : `SW-4-CSharp-SPARQL.ipynb` — 45 min | `SW-4b-Python-SPARQL.ipynb` — 30 min

---

# SW-5 — Linked Data : DBpedia et Wikidata

## Les 5 etoiles du Linked Data (Berners-Lee, 2010)

| Etoiles | Critere |
|---------|---------|
| ★ | Donnees sur le Web, quelle que soit la licence |
| ★★ | Donnees structurees (Excel, JSON) |
| ★★★ | Format ouvert non-proprietaire (CSV, RDF) |
| ★★★★ | URI pour identifier les ressources |
| ★★★★★ | Liens vers d'autres sources de donnees |

## Requetes federees SPARQL

```csharp
// Requete sur l'endpoint public DBpedia
var endpoint = new SparqlRemoteEndpoint(
    new Uri("http://dbpedia.org/sparql"));

var results = endpoint.QueryWithResultSet(@"
PREFIX dbo: <http://dbpedia.org/ontology/>
SELECT ?scientist ?birth WHERE {
    ?scientist a dbo:Scientist ;
               dbo:birthPlace dbr:France ;
               dbo:birthDate  ?birth .
} LIMIT 20");
```

- **SERVICE** : federe plusieurs endpoints en une requete
- Wikidata SPARQL endpoint : `https://query.wikidata.org/sparql`

> **Notebooks** : `SW-5-CSharp-LinkedData.ipynb` — 50 min | `SW-5b-Python-LinkedData.ipynb` — 35 min

---
layout: section
---

# Schema et Ontologies

---

# SW-6 — RDFS : Schema et Inference

## Le vocabulaire RDFS

- **`rdfs:subClassOf`** : hierarchie de classes (transitive)
- **`rdfs:subPropertyOf`** : hierarchie de proprietes
- **`rdfs:domain`** / **`rdfs:range`** : typage implicite par inference
- **`rdfs:label`** / **`rdfs:comment`** : documentation lisible

## Inference RDFS avec dotNetRDF

```csharp
using VDS.RDF.Reasoner;

var reasoner = new RdfsReasoner();
var schema = new Graph();
schema.LoadFromFile("schema.ttl");

// Appliquer les regles RDFS au graphe de donnees
reasoner.Initialise(schema);
reasoner.Apply(dataGraph);

// Nouveaux triplets inferres disponibles
Console.WriteLine($"Apres inference : {dataGraph.Triples.Count} triplets");
```

- **Monotone** : l'inference RDFS ne supprime jamais de triplets
- **Open World Assumption** : absence d'information ≠ faux

> **Notebook** : `SW-6-CSharp-RDFS.ipynb` — 45 min

---

# SW-7 — OWL 2 : Ontologies et Logiques de Description

## OWL 2 : au-dela de RDFS

| Feature | RDFS | OWL 2 |
|---------|------|-------|
| Equivalence de classes | — | `owl:equivalentClass` |
| Disjonction | — | `owl:disjointWith` |
| Cardinalite | — | `owl:maxCardinality` |
| Inverse de propriete | — | `owl:inverseOf` |
| Symetrie | — | `owl:SymmetricProperty` |

## Profils OWL 2

```csharp
using VDS.RDF.Ontology;

var ontology = new OntologyGraph();
ontology.LoadFromFile("foaf.owl");

// Explorer la hierarchie
var person = ontology.CreateOntologyClass(
    new Uri("http://xmlns.com/foaf/0.1/Person"));
foreach (var sub in person.DirectSubClasses)
    Console.WriteLine($"Sous-classe : {sub.Resource}");
```

- **OWL 2 EL** : expressivite polynomiale (ontologies medicales)
- **OWL 2 RL** : regles de production (integration avec bases de donnees)
- **OWL 2 DL** : maximum d'expressivite decidable (HermiT, Pellet)

> **Notebooks** : `SW-7-CSharp-OWL.ipynb` — 55 min | `SW-7b-Python-OWL.ipynb` — 45 min

---
layout: section
---

# Web Semantique Moderne

---

# SW-8 — SHACL : Validation des Donnees RDF

## SHACL vs OWL : deux philosophies

| | OWL | SHACL |
|-|-----|-------|
| Hypothese | Monde ouvert | Monde ferme |
| But | Inferer de nouvelles connaissances | Valider des contraintes |
| Erreur | Incoh coherence logique | Rapport de violations |
| Outil | Raisonneur (HermiT) | Validateur (pyshacl) |

## Definition d'une Shape SHACL

```python
from pyshacl import validate

shapes = """
@prefix sh: <http://www.w3.org/ns/shacl#> .
@prefix ex: <http://example.org/> .

ex:PersonShape a sh:NodeShape ;
    sh:targetClass ex:Person ;
    sh:property [
        sh:path ex:age ;
        sh:minInclusive 0 ;
        sh:maxInclusive 150 ;
    ] .
"""
results = validate(data_graph, shacl_graph=shapes)
print(results[2])  # rapport Turtle
```

> **Notebook** : `SW-8-Python-SHACL.ipynb` — 40 min

---

# SW-9 — JSON-LD : Le Web Semantique rencontre JSON

## JSON-LD : bridge entre JSON et Linked Data

```python
import json
from pyld import jsonld

# Document JSON-LD avec contexte
doc = {
    "@context": {
        "name": "http://xmlns.com/foaf/0.1/name",
        "birthDate": "http://schema.org/birthDate",
        "Person": "http://xmlns.com/foaf/0.1/Person"
    },
    "@type": "Person",
    "name": "Marie Curie",
    "birthDate": "1867-11-07"
}

# Expansion : toutes les URI en clair
expanded = jsonld.expand(doc)
# Aplatissement : un seul objet JSON
flattened = jsonld.flatten(doc)
# Compactage avec un nouveau contexte
compacted = jsonld.compact(doc, {"foaf": "http://xmlns.com/foaf/0.1/"})
```

- **`@context`** : mappe les cles JSON vers des URI
- **`@type`** : declare la classe de l'entite
- **Framing** : restructurer un graphe RDF en JSON specifique
- Adoption massive : Schema.org, ActivityPub, Verifiable Credentials

> **Notebook** : `SW-9-Python-JSONLD.ipynb` — 40 min

---

# SW-10 — RDF 1.2 (RDF-Star) : Assertions sur des Assertions

## Le probleme de la reification classique

**But** : annoter un triplet (confiance, source, date...)

**Avant RDF-Star** : 4 triplets supplementaires (`rdf:Statement`) — verbeux

**Avec RDF-Star** :

```python
from rdflib import ConjunctiveGraph
from rdflib.plugins.stores.memory import Memory

# Triple-star : un triplet comme sujet d'un autre triplet
g = ConjunctiveGraph()

# Syntaxe Turtle-Star
turtle_star = """
PREFIX ex: <http://example.org/>
PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>

<< ex:Turing ex:invented ex:ComputerScience >>
    ex:confidence 0.99 ;
    ex:source ex:Wikipedia .
"""
g.parse(data=turtle_star, format="turtle")
```

- Equivalent SPARQL-Star : `<< ?s ?p ?o >> ?meta ?val`
- Cas d'usage : provenance, versionnement, graphes de connaissances temporels

> **Notebook** : `SW-10-Python-RDFStar.ipynb` — 45 min

---
layout: section
---

# Applications

---

# SW-11 — Knowledge Graphs : Construction et Exploration

## Qu'est-ce qu'un Knowledge Graph ?

Un **graphe de connaissances** = graphe RDF a grande echelle, oriente metier

| Exemples | Triplets | Usage |
|---------|---------|-------|
| **Wikidata** | ~14 milliards | Encyclopedie universelle |
| **Google KG** | ~500 milliards | Recherche semantique |
| **DBpedia** | ~3 milliards | Extraction Wikipedia |
| **Schema.org** | — | Balisage SEO universel |

## Construction d'un KG avec rdflib

```python
from rdflib import Graph, Namespace, Literal
from rdflib.namespace import RDF, RDFS, OWL, XSD, FOAF

KG = Namespace("http://mykg.example.org/")
g = Graph()

# Entites et relations
g.add((KG.Turing, RDF.type, KG.Mathematician))
g.add((KG.Turing, FOAF.name, Literal("Alan Turing")))
g.add((KG.Turing, KG.workedAt, KG.Bletchley_Park))

# Requete SPARQL sur le graphe local
results = g.query("SELECT ?p WHERE { <http://mykg.../Turing> ?rel ?p }")
```

> **Notebook** : `SW-11-Python-KnowledgeGraphs.ipynb` — 55 min

---

# SW-12 — GraphRAG : Graphes et LLMs

## RAG classique vs GraphRAG

| | RAG classique | GraphRAG |
|-|--------------|---------|
| Index | Vecteurs (chunks) | Graphe de connaissances |
| Recherche | Similarite cosinus | Traversee de graphe + similarite |
| Relations | Implicites (embedding) | Explicites (triplets) |
| Multi-hop | Difficile | Naturel (SPARQL paths) |

## Architecture d'un pipeline GraphRAG

```python
from rdflib import Graph
from openai import OpenAI

# 1. Extraire des triplets depuis un texte (LLM)
def extract_triples(text: str) -> list[tuple]:
    response = client.chat.completions.create(
        model="gpt-4o-mini",
        messages=[{"role": "user",
                   "content": f"Extrais des triplets (sujet, predicat, objet) du texte : {text}"}])
    return parse_triples(response.choices[0].message.content)

# 2. Stocker dans un graphe RDF
kg = Graph()
for s, p, o in extract_triples(document):
    kg.add((URIRef(s), URIRef(p), Literal(o)))

# 3. Retrieval par SPARQL + reponse par LLM
```

> **Notebook** : `SW-12-Python-GraphRAG.ipynb` — 50 min

---

# SW-13 — Comparaison des Raisonneurs OWL

## Raisonneurs OWL : panorama

| Raisonneur | Langage | Points forts |
|-----------|---------|-------------|
| **owlrl** | Python | Leger, RDFS + OWL RL |
| **HermiT** | Java | OWL 2 DL complet, reference |
| **reasonable** | Rust | Tres rapide, OWL RL |
| **Growl** | Python | Interface simple, owlready2 |
| **Pellet** | Java | OWL 2 DL, explications |

## Benchmark et inference

```python
import owlrl
from rdflib import Graph

g = Graph()
g.parse("pizza.owl")

# Appliquer la cloture RDFS + OWL RL
owlrl.DeductiveClosure(owlrl.OWLRL_Semantics).expand(g)

print(f"Triplets apres inference : {len(g)}")

# Verifier la coherence
# (avec HermiT via JPype/TweetyProject)
from org.semanticweb.owlapi.apibinding import OWLManager
manager = OWLManager.createOWLOntologyManager()
ontology = manager.loadOntologyFromOntologyDocument(File("pizza.owl"))
```

> **Notebook** : `SW-13-Python-Reasoners.ipynb` — 45 min

---
layout: section
---

# Synthese et Ressources

---

# Ecosysteme Web Semantique

## Notebooks de la serie

| Notebook | Theme | Langage | Duree |
|---------|-------|---------|-------|
| SW-1 | Setup, pile technologique | C# | 20 min |
| SW-2 / SW-2b | RDF : triplets, serialisation | C# / Python | 45+40 min |
| SW-3 | Operations graphes, TripleStore | C# | 50 min |
| SW-4 / SW-4b | SPARQL : requetes, agregats | C# / Python | 45+30 min |
| SW-5 / SW-5b | Linked Data, DBpedia, Wikidata | C# / Python | 50+35 min |
| SW-6 | RDFS : schema, inference | C# | 45 min |
| SW-7 / SW-7b | OWL 2 : ontologies, profils | C# / Python | 55+45 min |
| SW-8 | SHACL : validation | Python | 40 min |
| SW-9 | JSON-LD : contextes, framing | Python | 40 min |
| SW-10 | RDF-Star : meta-assertions | Python | 45 min |
| SW-11 | Knowledge Graphs | Python | 55 min |
| SW-12 | GraphRAG : KG + LLMs | Python | 50 min |
| SW-13 | Raisonneurs OWL | Python | 45 min |

---

# Liens avec les autres series

## Connexions dans le cours IA 101

- **S6-TweetyProject** : raisonnement en Description Logics (DL) via TweetyProject — complement OWL
- **S7-Lean** : preuves formelles de proprietes logiques — fondements theoriques des ontologies
- **03-logique** : cours magistral sur la logique, base pour RDFS/OWL
- **GameTheory/social_choice_lean** : exemple de formalisation avec Arrow/Sen

## Standards W3C References

```
W3C Semantic Web Stack
├── RDF 1.1 + RDF 1.2 (RDF-Star)
├── RDFS (Schema)
├── OWL 2 (Ontology)
├── SPARQL 1.1
├── SHACL
└── JSON-LD 1.1
```

> **Documentation** : `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/README.md`

---

# Pour aller plus loin

## Documentation et references

- **W3C RDF 1.1** : https://www.w3.org/TR/rdf11-primer/
- **dotNetRDF** : https://dotnetrdf.org/ (Robert Vesse et al.)
- **rdflib** : https://rdflib.readthedocs.io/ (Python)
- **Schema.org** : https://schema.org/ (Google/Microsoft/Yahoo)
- **Wikidata Query** : https://query.wikidata.org/ (SPARQL live)
- **Bizer et al. (2009)** : "Linked Data — The Story So Far"
- **Hitzler et al. (2021)** : "A Review of the Semantic Web Field"

## Extensions possibles

- Integration **Neo4j** (Cypher + plugin RDF) pour visualisation de KG
- **SPARQL federation** : combiner Wikidata + DBpedia + endpoints prives
- **Ontologie medicale** : SNOMED-CT, GO (Gene Ontology) avec raisonneurs EL
- **LLM + SPARQL** : generation automatique de requetes (Text-to-SPARQL)

---
layout: section
---

# Questions?

---
layout: end
---

# Merci

Serie Web Semantique — IA 101

`MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/`
