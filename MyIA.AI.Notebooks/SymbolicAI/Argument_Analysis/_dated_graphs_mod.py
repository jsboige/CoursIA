#!/usr/bin/env python
# coding: utf-8

# # Graphes d'argumentation datés — l'instrument $G_t^{arg} \to G_{t+1}^{arg}$
# 
# L'Observatoire des formes relationnelles (Epic [#13303](https://github.com/jsboige/CoursIA/issues/13303)) vise la chaîne :
# 
# $$L_t \to L_{t+1} \;\text{(catégories lexicales)} \quad\Longrightarrow\quad A_t \to A_{t+1} \;\text{(catégories argumentatives)} \quad\Longmapsto\quad G_t^{arg} \to G_{t+1}^{arg} \;\text{(graphe d'argumentation)}$$
# 
# Ce notebook construit **l'instrument du dernier étage** : produire, depuis un corpus daté, une suite de
# graphes d'argumentation comparables, et une **mesure d'écart** entre deux dates. Il ne mesure **aucun
# phénomène social** — il fournit l'aiguille (issue [#13310](https://github.com/jsboige/CoursIA/issues/13310)).
# 
# **Substrat — s'y brancher, ne pas le refaire :**
# 
# - [Argument_Analysis_Ontology_AIF.ipynb](Argument_Analysis_Ontology_AIF.ipynb) : l'ontologie AIF, schéma de nœuds/liens dans lequel un graphe daté doit s'exprimer ;
# - [Argument_Analysis_Dung_AF_Semantics.ipynb](Argument_Analysis_Dung_AF_Semantics.ipynb) : les sémantiques de Dung, ce qu'« être accepté » veut dire à une date donnée ;
# - [Argument_Analysis_Ranking_Semantics.ipynb](Argument_Analysis_Ranking_Semantics.ipynb) : les sémantiques graduelles, utiles quand l'acceptation binaire écrase la variation (exercice 3).
# 
# **Le piège central** : deux graphes construits depuis deux échantillons différents diffèrent *toujours*.
# Une mesure d'écart $d(G_t, G_{t+1}) > 0$ ne dit donc rien tant qu'on ne connaît pas l'écart produit par
# le **bruit d'échantillonnage seul**. D'où l'exigence non négociable de ce notebook : tout écart inter-dates
# est publié **avec son plancher de bruit** (contrôle négatif), et l'instrument est validé sur un changement
# **connu par construction** (contrôle positif).
# 
# **Plan :** corpus daté synthétique → critère d'inclusion → graphe AIF conforme → cadre de Dung →
# deux mesures d'écart de familles différentes → contrôle négatif → écart inter-dates → contrôle positif → exercices.
# 

# ## 1. Le corpus daté — format d'entrée
# 
# Un corpus daté est une liste d'**énoncés**, chacun portant :
# 
# - une **date** (ici : un jour, entier — la granularité réelle sera fournie par le protocole [#13309](https://github.com/jsboige/CoursIA/issues/13309)) ;
# - une **proposition** identifiée par son contenu (`p1`, `p2`, …) — deux énoncés à des dates différentes peuvent **ré-énoncer la même proposition** (c'est le mécanisme qui rend deux fenêtres comparables) ;
# - un **acte de langage** (`assertif` ou `question`) ;
# - des **relations** exprimées vers d'autres propositions : `RA` (*rule application*, support inférentiel) ou `CA` (*conflict application*, attaque).
# 
# Le corpus ci-dessous est **entièrement synthétique** : un débat fictif sur la tarification de l'eau.
# Période $t$ = jours 1–30, période $t+1$ = jours 31–60. La plupart des relations sont **ré-exprimées**
# d'une moitié à l'autre (culture de restatement, comme dans un vrai débat qui se rejoue) — c'est ce qui
# garde le plancher de bruit (section 6) raisonnable. Aucun corpus réel ici : l'instrument se valide
# sur synthétique ; l'application réelle attend le protocole #13309.
# 

# In[1]:


from dataclasses import dataclass, field
from typing import Optional


@dataclass(frozen=True)
class Enonce:
    """Un enonce date : instantiation d'une proposition, portant ses relations."""
    jour: int
    prop: str
    acte: str                      # "assertif" ou "question"
    relations: tuple = ()          # couples (scheme, prop_cible), scheme in {"RA", "CA"}


# --- Periode t : jours 1-30 (30 enonces, deux moities de 15) ---
corpus_t = [
    # premiere moitie (jours 1-15)
    Enonce(1,  "p1",  "assertif"),
    Enonce(2,  "p2",  "assertif", (("CA", "p1"),)),
    Enonce(3,  "p3",  "assertif", (("CA", "p2"),)),
    Enonce(4,  "p4",  "assertif", (("CA", "p3"),)),
    Enonce(5,  "p5",  "assertif", (("RA", "p4"),)),
    Enonce(6,  "p6",  "assertif"),
    Enonce(7,  "p7",  "assertif", (("CA", "p6"),)),
    Enonce(8,  "p8",  "assertif", (("CA", "p7"),)),
    Enonce(9,  "p9",  "assertif", (("CA", "p8"),)),
    Enonce(10, "p11", "assertif", (("CA", "p6"),)),
    Enonce(11, "p10", "assertif", (("RA", "p9"),)),
    Enonce(12, "p13", "question"),                    # exclu par C1 (non assertif)
    Enonce(13, "p18", "assertif", (("CA", "p1"),)),   # attaquant ephemere : non re-entendu ensuite
    Enonce(14, "p12", "assertif", (("CA", "p9"),)),
    Enonce(15, "p1",  "assertif"),
    # seconde moitie (jours 16-30)
    Enonce(16, "p2",  "assertif", (("CA", "p1"),)),
    Enonce(17, "p3",  "assertif", (("CA", "p2"),)),
    Enonce(18, "p7",  "assertif", (("CA", "p6"),)),
    Enonce(19, "p8",  "assertif", (("CA", "p7"),)),
    Enonce(20, "p12", "assertif", (("CA", "p9"),)),
    Enonce(21, "p11", "assertif", (("CA", "p6"),)),
    Enonce(22, "p4",  "assertif", (("CA", "p3"),)),
    Enonce(23, "p5",  "assertif", (("RA", "p4"),)),
    Enonce(24, "p14", "assertif"),                    # exclu par C3 (aucune relation)
    Enonce(25, "p9",  "assertif", (("CA", "p8"),)),
    Enonce(26, "p6",  "assertif"),
    Enonce(27, "p10", "assertif", (("RA", "p9"),)),
    Enonce(28, "p12", "assertif", (("CA", "p9"),)),
    Enonce(29, "p1",  "assertif"),
    Enonce(30, "p13", "question"),                    # re-exclu par C1
]

# --- Periode t+1 : jours 31-60 (16 enonces) ---
corpus_t1 = [
    Enonce(31, "p15", "assertif", (("CA", "p12"),)),  # nouvelle attaque
    Enonce(32, "p16", "assertif", (("CA", "p11"),)),  # nouvelle attaque
    Enonce(33, "p2",  "assertif", (("CA", "p1"),)),
    Enonce(34, "p3",  "assertif", (("CA", "p2"),)),
    Enonce(35, "p4",  "assertif", (("CA", "p3"),)),
    Enonce(36, "p7",  "assertif", (("CA", "p6"),)),
    Enonce(37, "p8",  "assertif", (("CA", "p7"),)),
    Enonce(38, "p9",  "assertif", (("CA", "p8"),)),
    Enonce(39, "p11", "assertif", (("CA", "p6"),)),
    Enonce(40, "p12", "assertif", (("CA", "p9"),)),
    Enonce(41, "p5",  "assertif", (("RA", "p4"),)),
    Enonce(42, "p10", "assertif", (("RA", "p9"),)),
    Enonce(43, "p13", "question"),            # exclu par C1
    Enonce(44, "p14", "assertif"),            # re-exclu par C3
    Enonce(45, "p17", "assertif"),            # nouvel orphelin : exclu par C3
    Enonce(46, "p1",  "assertif"),            # p18, lui, n'est plus entendu
]

for nom, corpus in [("periode t (jours 1-30)", corpus_t), ("periode t+1 (jours 31-60)", corpus_t1)]:
    n_assert = sum(1 for e in corpus if e.acte == "assertif")
    n_q = len(corpus) - n_assert
    n_rel = sum(len(e.relations) for e in corpus)
    print(f"{nom} : {len(corpus)} enonces ({n_assert} assertifs, {n_q} questions), {n_rel} relations exprimees")

print("\nApercu des 5 premiers enonces de la periode t :")
for e in corpus_t[:5]:
    rel = ", ".join(f"{s}->{c}" for s, c in e.relations) or "(aucune)"
    print(f"  jour {e.jour:>2} | {e.prop:>4} | {e.acte:>8} | {rel}")


# ## 2. Critère d'inclusion — ce qui devient un nœud
# 
# **Critère (écrit, appliqué mécaniquement)** — un énoncé $E$ de la fenêtre contribue un nœud-I au graphe $G$ **si et seulement si** :
# 
# - **(C1)** son acte de langage est **assertif** (une question ne prend pas position : elle n'argumente pas) ;
# - **(C2)** son contenu propositionnel est **identifiable** — dans notre format, porté par un `prop` non vide (pas d'énoncé purement phatique ou d'élipse sans contenu) ;
# - **(C3)** il **entretient au moins une relation** RA ou CA — exprimée par lui **ou vers lui** — avec une autre proposition présente dans la même fenêtre.
# 
# Un énoncé qui échoue à C3 est un **singleton** : il ne structure pas le débat, il en est exclu — mais
# **son exclusion est comptée et publiée** (le taux d'exclusion fait partie de la sortie : un débat qui
# devient une suite de monologues se voit dans ce taux avant de se voir dans le graphe).
# 
# Les relations exprimées deviennent des **nœuds de scheme** AIF : un `RA-node` par lien de support,
# un `CA-node` par lien de conflit. Le graphe produit est donc bipartite au sens AIF : les nœuds-I
# portent le contenu, les nœuds de scheme portent les liens — et non des arêtes directes entre contenus.
# 

# In[2]:


@dataclass
class AIFGraph:
    """Graphe AIF d'une fenetre : noeuds-I (contenus) + noeuds de scheme (liens)."""
    i_nodes: dict = field(default_factory=dict)       # prop -> description factice
    scheme_nodes: dict = field(default_factory=dict)  # id scheme -> ("RA"|"CA", source, cible)
    excluded: list = field(default_factory=list)      # (prop, motif d'exclusion)


def build_aif_graph(enonces):
    """Corpus date -> graphe AIF-conforme, critere d'inclusion C1-C3."""
    g = AIFGraph()
    # passe 1 : propositions assertives presentes (C1) a contenu identifiable (C2)
    assertees = [e for e in enonces if e.acte == "assertif" and e.prop]
    presentes = {e.prop for e in assertees}
    # relations exprimees dans la fenetre ; les cibles referencees existent aussi
    # comme noeuds-I dans le graphe AIF (une attaque vise un contenu)
    relations = []
    for e in assertees:
        for scheme, cible in e.relations:
            relations.append((scheme, e.prop, cible))
    reliees = {s for _, s, _ in relations} | {c for _, _, c in relations}
    # passe 2 : exclusions publiees (C1, C3)
    vues = set()
    for e in enonces:
        if e.prop in vues:
            continue  # chaque proposition est jugee une seule fois par fenetre
        vues.add(e.prop)
        if e.acte != "assertif":
            g.excluded.append((e.prop, "C1 : acte non assertif"))
        elif e.prop in presentes and e.prop not in reliees:
            g.excluded.append((e.prop, "C3 : singleton (aucune relation dans la fenetre)"))
    # passe 3 : construction (les props exclues C1/C3 ne deviennent PAS noeuds)
    exclus = {p for p, _ in g.excluded}
    for p in sorted((presentes | reliees) - exclus):
        g.i_nodes[p] = f"proposition {p}"
    for scheme, src, dst in sorted(set(relations)):
        g.scheme_nodes[f"{scheme}_{src}_{dst}"] = (scheme, src, dst)
    return g


G_t = build_aif_graph(corpus_t)
G_t1 = build_aif_graph(corpus_t1)

for nom, g in [("G_t", G_t), ("G_t+1", G_t1)]:
    n_ca = sum(1 for v in g.scheme_nodes.values() if v[0] == "CA")
    n_ra = len(g.scheme_nodes) - n_ca
    print(f"{nom} : {len(g.i_nodes)} noeuds-I, {len(g.scheme_nodes)} noeuds de scheme "
          f"({n_ca} CA, {n_ra} RA), {len(g.excluded)} exclus")
    for prop, motif in g.excluded:
        print(f"    exclu : {prop} -- {motif}")


# ## 3. Conformité AIF — vocabulaire et sérialisation
# 
# Le graphe ci-dessus suit le vocabulaire de l'**Argument Interchange Format** (namespace
# `http://www.arg.dundee.ac.uk/aif#`) : nœuds `aif:I-node` (contenus), `aif:RA-node` (support),
# `aif:CA-node` (conflit), liés par des arêtes de scheme. On le vérifie de deux façons, en réutilisant
# la méthode du notebook [Ontology_AIF](Argument_Analysis_Ontology_AIF.ipynb) : l'ontologie Argumentum
# (`argumentum_fallacies.owl`, 4,7 MB) **ne se laisse pas parser par rdflib** (37 axiomes
# `ExactCardinality` mal formés) — on extrait donc ses déclarations de classes par regex tolérant, puis
# on sérialise nos graphes en RDF AIF bien formé.
# 

# In[3]:


import re
from pathlib import Path

from rdflib import Graph, Namespace, URIRef, Literal
from rdflib.namespace import RDF

AIF = Namespace("http://www.arg.dundee.ac.uk/aif#")

# 1) Classes AIF reellement declarees dans l'ontologie Argumentum (parseur regex tolere,
#    meme methode que Ontology_AIF : rdflib echoue sur les ExactCardinality mal formes)
_THIS_DIR = Path(__file__).resolve().parent
OWL = _THIS_DIR / "ontologies" / "argumentum_fallacies.owl"
owl_text = OWL.read_text(encoding="utf-8", errors="replace")
class_decls = re.findall(r'<Declaration>\s*<Class IRI="([^"]+)"\s*/>\s*</Declaration>', owl_text)
aif_classes = {c.split("#")[-1] for c in class_decls if "arg.dundee.ac.uk/aif" in c}
print("Classes AIF declarees dans l'ontologie :", sorted(aif_classes))

# 2) Nos types de noeuds doivent etre un sous-ensemble des classes declarees
nos_types = {"I-node", "RA-node", "CA-node"}
assert nos_types <= aif_classes, f"types hors AIF : {nos_types - aif_classes}"
print("Conformite vocabulaire :", sorted(nos_types), "<= classes declarees : OK")

# 3) Serialisation RDF AIF bien formee d'un graphe
def to_rdf(g):
    """AIFGraph -> rdflib.Graph avec triplets AIF (types + arbetes de scheme)."""
    rdf = Graph()
    rdf.bind("aif", AIF)
    for prop in g.i_nodes:
        n = URIRef(f"{AIF}{prop}")
        rdf.add((n, RDF.type, AIF["I-node"]))
        rdf.add((n, URIRef(f"{AIF}text"), Literal(g.i_nodes[prop])))
    for sid, (scheme, src, dst) in g.scheme_nodes.items():
        n = URIRef(f"{AIF}{sid}")
        rdf.add((n, RDF.type, AIF[f"{scheme}-node"]))
        rdf.add((URIRef(f"{AIF}{src}"), URIRef(f"{AIF}{scheme}edge"), n))   # source -> scheme
        rdf.add((n, URIRef(f"{AIF}edge{scheme}"), URIRef(f"{AIF}{dst}")))   # scheme -> cible
    return rdf

rdf_t = to_rdf(G_t)
print(f"\nG_t serialise : {len(rdf_t)} triplets AIF")
print(rdf_t.serialize(format="turtle")[:520])


# ## 4. Du graphe AIF au cadre de Dung
# 
# Pour la mesure **sémantique**, on projette le graphe AIF sur un cadre d'argumentation abstrait de Dung :
# 
# - les **arguments** = les nœuds-I ;
# - les **attaques** = les liens `CA` : si un `CA-node` relie $x$ (source) à $y$ (cible), alors $x$ attaque $y$ ;
# - les liens `RA` (support) **ne créent pas d'attaque** — la modélisation bipolaire (supports attaquant
#   des attaques, cf. AF bipolaires de Cayrol–Lagasquie–Schmid) est **hors scope** : documentée comme limite.
# 
# Les définitions de l'acceptation (admissible, *grounded*) sont **reprises telles quelles du substrat**
# [Dung_AF_Semantics](Argument_Analysis_Dung_AF_Semantics.ipynb) (cellules 2 à 10) — sémantique inchangée,
# reproduite ici pour l'auto-contenance du notebook.
# 

# In[4]:


# --- Reprise du substrat Argument_Analysis_Dung_AF_Semantics.ipynb (cellules 2-10) ---

class AF:
    """Cadre d'argumentation abstrait de Dung : <args, attacks>."""

    def __init__(self, args, attacks):
        self.args = set(args)
        self.attacks = set(attacks)  # ensemble de couples (attaquant, attaque)

    def attackers(self, x):
        return {a for (a, b) in self.attacks if b == x}

    def __repr__(self):
        att = ", ".join(f"{a}->{b}" for (a, b) in sorted(self.attacks))
        return f"AF(args={sorted(self.args)}, attacks=[{att}])"


def defeats(af, S, x):
    """True si S defait x (au moins un membre de S attaque x)."""
    return any((a, x) in af.attacks for a in S)


def defends(af, S, x):
    """True si S defend x : tout attaquant de x est defait par S."""
    return all(defeats(af, S, b) for b in af.attackers(x))


def grounded(af):
    """Extension grounded : point fixe a partir de l'ensemble vide."""
    S = set()
    while True:
        S_new = {x for x in af.args if defends(af, S, x)}
        if S_new == S:
            return S
        S = S_new


# --- Projection AIF -> Dung ---

def to_dung_af(g):
    """AIFGraph -> AF : arguments = noeuds-I, attaques = liens CA."""
    attacks = {(src, dst) for (scheme, src, dst) in g.scheme_nodes.values() if scheme == "CA"}
    return AF(g.i_nodes.keys(), attacks)


af_t, af_t1 = to_dung_af(G_t), to_dung_af(G_t1)
E_t, E_t1 = grounded(af_t), grounded(af_t1)

print(f"AF_t   : {len(af_t.args)} arguments, {len(af_t.attacks)} attaques")
print(f"AF_t+1 : {len(af_t1.args)} arguments, {len(af_t1.attacks)} attaques")
print(f"\nE_t   (grounded, {len(E_t)}/{len(af_t.args)}) : {sorted(E_t)}")
print(f"E_t+1 (grounded, {len(E_t1)}/{len(af_t1.args)}) : {sorted(E_t1)}")


# ## 5. Deux mesures d'écart de familles différentes
# 
# Deux graphes se comparent sur des plans indépendants — on en retient deux, de familles différentes :
# 
# **Mesure structurelle** (sur les ensembles, indépendante de toute sémantique) — la **distance de
# Jaccard** $1 - |A \cap A'| / |A \cup A'|$, calculée **deux fois** : sur les ensembles d'attaques
# ($d_{att}$) et sur les ensembles de nœuds ($d_{noeuds}$). Deux graphes identiques ont $d = 0$.
# 
# **Mesure sémantique** (sur le verdict d'acceptation, via Dung) :
# 
# $$d_{sem}(G, G') \;=\; 1 - \frac{|E \cap E'|}{|E \cup E'|}, \qquad E = Gr(G),\; E' = Gr(G')$$
# 
# Jaccard sur les **extensions grounded**. Deux graphes peuvent être structurellement proches et
# sémantiquement éloignés (une seule attaque bien placée renverse une acceptation), ou l'inverse.
# **Deux mesures qui bougent ensemble se renforcent ; deux qui divergent sont un résultat**, à publier tel quel.
# 

# In[5]:


def jaccard_distance(A, B):
    """Distance de Jaccard : 1 - |A n B| / |A u B| (0 si les deux sont vides)."""
    A, B = set(A), set(B)
    if not A and not B:
        return 0.0
    return 1.0 - len(A & B) / len(A | B)


def d_struct(af1, af2):
    """Ecart structurelle : (noeuds, attaques) en distances de Jaccard."""
    d_nodes = jaccard_distance(af1.args, af2.args)
    d_att = jaccard_distance(af1.attacks, af2.attacks)
    return d_nodes, d_att


def d_sem(af1, af2):
    """Ecart semantique : Jaccard sur les extensions grounded."""
    return jaccard_distance(grounded(af1), grounded(af2))


# Garde-fou : deux graphes identiques -> ecarts nuls
assert d_struct(af_t, af_t)[0] == 0.0 and d_struct(af_t, af_t)[1] == 0.0
assert d_sem(af_t, af_t) == 0.0
print("Sanity : d(G, G) = 0 sur les trois composantes : OK")


# ## 6. Contrôle négatif — le plancher de bruit
# 
# **Le point central de l'instrument.** Deux graphes construits depuis deux échantillons différents
# diffèrent *toujours*. Une valeur $d > 0$ ne devient un « changement » que si elle dépasse ce que produit
# le **bruit d'échantillonnage seul**.
# 
# Le contrôle : découper une **même** période en deux moitiés arbitraires — ici, **première contre
# seconde moitié sur l'ordre d'arrivée** (jours 1–15 vs 16–30 de la période $t$) — construire $G_a$ et
# $G_b$, mesurer $d(G_a, G_b)$. C'est le **plancher de bruit**. Un écart inter-dates qui ne le dépasse
# pas n'est pas un changement : c'est l'instrument qui respire.
# 
# Le plancher est publié **à côté** de toute mesure d'écart, dans la même sortie. Ici, la seule
# asymétrie entre moitiés est l'attaque éphémère `p18 → p1` (entendue jours 13, jamais ré-entendue) :
# c'est exactement du bruit d'échantillonnage, et c'est lui qui fixe le plancher.
# 

# In[6]:


def split_half(corpus):
    """Decoupe une periode en deux moities par ordre d'arrivee (premiere / seconde)."""
    trie = sorted(corpus, key=lambda e: e.jour)
    milieu = len(trie) // 2
    return trie[:milieu], trie[milieu:]


moitie_a, moitie_b = split_half(corpus_t)
G_a, G_b = build_aif_graph(moitie_a), build_aif_graph(moitie_b)
af_a, af_b = to_dung_af(G_a), to_dung_af(G_b)

floor_nodes, floor_att = d_struct(af_a, af_b)
floor_sem = d_sem(af_a, af_b)

print(f"Moitie a (jours 1-15)  : {len(af_a.args)} arguments, {len(af_a.attacks)} attaques | "
      f"grounded {len(grounded(af_a))}")
print(f"Moitie b (jours 16-30) : {len(af_b.args)} arguments, {len(af_b.attacks)} attaques | "
      f"grounded {len(grounded(af_b))}")
print(f"\nPlancher de bruit (split moities de la periode t) :")
print(f"  d_noeuds  = {floor_nodes:.3f}")
print(f"  d_att     = {floor_att:.3f}")
print(f"  d_sem     = {floor_sem:.3f}")


# ## 7. L'écart inter-dates, avec son plancher à côté
# 
# Période $t$ contre période $t+1$. Le changement réel du débat : deux nouvelles attaques (`p15 → p12`,
# `p16 → p11`) et la disparition de l'attaquant éphémère `p18`. Mesuré sur les trois composantes,
# chacune confrontée à son plancher. **Règle de lecture : un écart qui ne dépasse pas son plancher
# n'est pas un changement.**
# 

# In[7]:


gap_nodes, gap_att = d_struct(af_t, af_t1)
gap_sem = d_sem(af_t, af_t1)

print(f"{'composante':<12} {'ecart t->t+1':>14} {'plancher':>10} {'rapport':>9}  verdict")
print("-" * 72)
for nom, gap, floor in [("d_noeuds", gap_nodes, floor_nodes),
                        ("d_att", gap_att, floor_att),
                        ("d_sem", gap_sem, floor_sem)]:
    rapport = gap / floor if floor > 0 else float("inf")
    verdict = "DEPASSE" if gap > floor else "sous le bruit"
    print(f"{nom:<12} {gap:>14.3f} {floor:>10.3f} {rapport:>8.1f}x  {verdict}")


# In[8]:


# Ce que disent les extensions : qui entre, qui sort
entrees = sorted(E_t1 - E_t)
sorties = sorted(E_t - E_t1)
print(f"Entrees dans l'extension grounded (acceptes en t+1, pas en t) : {entrees}")
print(f"Sorties de l'extension grounded (acceptes en t, plus en t+1)   : {sorties}")


# In[9]:


# Lecture des mouvements (a confronter aux sorties ci-dessus)
print("Lecture des cascades :")
print("  - p15->p12 (non contré) fait sortir p12 ; p12 sortant, p9 n'est plus")
print("    contré -> p9 entre ; et p9 dans l'extension défait p8 -> p7 entre")
print("    (son attaquant p8 est desormais defait).")
print("  - p8 sort : il exigeait la defaite de son attaquant p9, qui n'etait")
print("    defait QUE par p12 -- p12 sortant, p8 perd sa defense.")
print("  - p16->p11 fait sortir p11 (non contré).")
print("  - p18 n'est plus entendu en t+1 : son attaque disparait (avec son noeud).")
print("  - p1 reste dehors : son attaquant p2 n'est jamais defait (p3, seul")
print("    attaquant de p2, n'entre jamais dans l'extension -- p4 indéfaisable).")


# ## 8. Contrôle positif — un changement connu par construction
# 
# L'instrument doit **détecter** un changement qu'on fabrique exprès. Opération explicite : on ajoute à la
# période $t$ **un seul nouvel énoncé assertif** `p_ctrl` qui attaque `p4`, sans que rien ne contra `p_ctrl`.
# 
# **Magnitude attendue — écrite AVANT la mesure** (dérivation à la main, sans exécuter) :
# 
# - `p4` était la racine jamais attaquée de la chaîne `p4 → p3 → p2` ; attaqué par `p_ctrl` non
#   contré, **`p4` sort** de l'extension (effet direct) ;
# - **effet paradoxal** : `p3`, dont `p4` était le seul attaquant, voit désormais son attaquant
#   **défait** (par `p_ctrl`) → **`p3` entre** dans l'extension — attaquer la racine *réhabilite*
#   sa victime directe ;
# - **cascade** : `p2` exigeait la défaite de `p3`, assurée par `p4` — `p4` hors extension, `p3`
#   n'est plus **défait** par personne (être dans l'extension n'est pas être défait), donc **`p2`
#   sort** ; `p1` était déjà dehors ;
# - `p_ctrl` entre (non attaqué) ; rien d'autre ne bouge (le flot `p9/p12`, la branche `p6`, sont
#   indépendants de `p4`) ;
# - d'où $E' = E_t \setminus \{p2, p4\} \cup \{p3, p_{ctrl}\}$ : $|E \cap E'| = 6$,
#   $|E \cup E'| = 10$ → $d_{sem}$ **attendu $= 1 - 6/10 = 0{,}4$** ;
# - structurellement : $d_{att} = 1 - 9/10 = 0{,}1$ — **sous le plancher de bruit** ($0{,}111$) :
#   la mesure structurelle ne doit PAS voir ce changement au-dessus du bruit. C'est précisément
#   pourquoi il faut deux familles de mesures.
# 

# In[10]:


# L'operation explicite : un seul nouvel enonce, attaque non contree
corpus_ctrl = corpus_t + [Enonce(31, "p_ctrl", "assertif", (("CA", "p4"),))]
G_ctrl = build_aif_graph(corpus_ctrl)
af_ctrl = to_dung_af(G_ctrl)
E_ctrl = grounded(af_ctrl)

gap_nodes_c, gap_att_c = d_struct(af_t, af_ctrl)
gap_sem_c = d_sem(af_t, af_ctrl)

print(f"E_ctrl = {sorted(E_ctrl)}")
print(f"\nattendu (ecrit avant)   : d_sem = 0.4, d_att = 0.1")
print(f"mesure                  : d_sem = {gap_sem_c:.3f}, d_att = {gap_att_c:.3f}")
ok_sem = abs(gap_sem_c - 0.4) < 1e-9
ok_att = abs(gap_att_c - 0.1) < 1e-9
print(f"\nControle positif : d_sem {'CONFORME' if ok_sem else 'DIVERGE'}, "
      f"d_att {'CONFORME' if ok_att else 'DIVERGE'} a l'attendu ecrit")
print(f"p4 sorti : {'p4' not in E_ctrl} | p2 sorti : {'p2' not in E_ctrl} | "
      f"p3 entre : {'p3' in E_ctrl} | p_ctrl entre : {'p_ctrl' in E_ctrl}")


# ## 9. Lecture — concordance et divergence
# 
# Ce que l'instrument a montré sur le corpus synthétique :
# 
# - **concordance inter-dates** : les trois composantes dépassent leur plancher (rapports ~2,5× en
#   structure, ~5× en sémantique) — le changement de période est réel sur les deux familles à la
#   fois, elles se renforcent ;
# - **divergence au contrôle positif** : une seule attaque bien placée produit un $d_{sem}$ de $0{,}4$
#   (détecté, conforme à l'attendu écrit avant — avec sa réhabilitation paradoxale de `p3`) mais un
#   $d_{att}$ de $0{,}1$ — **sous le plancher structurel** : invisible en structure. La mesure
#   sémantique est la seule à voir ce changement ;
# - la divergence entre familles **est un résultat, pas un échec** : elle dit à quelle famille de
#   changement on a affaire (renversement d'acceptation vs volume de structure).
# 
# Limite documentée : les liens `RA` (support) ne créent pas d'attaques — la projection AIF → Dung est
# une **perte d'information assumée** (pas de modélisation bipolaire). Une troisième mesure graduée
# (exercice 3) affinerait la granularité du verdict sémantique.
# 

# In[11]:


recap = {
    "plancher_bruit": {"d_noeuds": round(floor_nodes, 3), "d_att": round(floor_att, 3),
                       "d_sem": round(floor_sem, 3)},
    "ecart_inter_dates": {"d_noeuds": round(gap_nodes, 3), "d_att": round(gap_att, 3),
                          "d_sem": round(gap_sem, 3)},
    "controle_positif": {"d_sem_attendu": 0.4, "d_sem_mesure": round(gap_sem_c, 3),
                         "d_att_attendu": 0.1, "d_att_mesure": round(gap_att_c, 3)},
    "exclusions": {"t": dict(G_t.excluded), "t+1": dict(G_t1.excluded)},
}
print("Resume de l'instrument (toute mesure d'ecart avec son plancher) :")
for k, v in recap.items():
    print(f"  {k} : {v}")


# ## 10. L'hypothèse monotone — ce que l'instrument suppose du temps
# 
# L'instrument compare $G_t$ et $G_{t+1}$, mais sa **lecture cumulative** des corpus pose une hypothèse
# qui doit être énoncée au lieu de rester implicite (hypothèse absorbée de `Dated_AF_Instrument` §5,
# PR #13340, cellule markdown citée in extenso dans la PR de consolidation) :
# 
# > **Hypothèse monotone** : $G_{T_0} \subseteq G_{T_1} \subseteq G_{T_2}$ au sens ensembliste —
# > les arguments ne sont pas retirés ; le retrait est un chantier ultérieur.
# 
# Un instrument qui mesure $G_t \to G_{t+1}$ sans dire s'il autorise la disparition d'un argument est
# sous-spécifié. Cette section (1) construit les graphes cumulatifs et **vérifie** la monotonie sur le
# corpus synthétique — falsifiable dans la sortie, pas seulement énoncée en prose — puis (2) la **viole
# délibérément** et montre ce que les deux mesures d'écart en font.
# 

# In[12]:


# Graphes cumulatifs : le corpus de T1 = tout ce qui est paru jusqu'a la fin de T1.
cumul_t  = corpus_t                 # jours 1-30
cumul_t1 = corpus_t + corpus_t1     # jours 1-60 : les enonces s'accumulent, rien ne disparait

G_cumul_t,  G_cumul_t1  = build_aif_graph(cumul_t),  build_aif_graph(cumul_t1)
af_cumul_t, af_cumul_t1 = to_dung_af(G_cumul_t),     to_dung_af(G_cumul_t1)

print("Lecture cumulative :")
print(f"  G_cumul_t  : {len(af_cumul_t.args)} arguments, {len(af_cumul_t.attacks)} attaques")
print(f"  G_cumul_t1 : {len(af_cumul_t1.args)} arguments, {len(af_cumul_t1.attacks)} attaques")

# Verification de l'hypothese monotone (falsifiable en sortie) :
incl_args = set(af_cumul_t.args)    <= set(af_cumul_t1.args)
incl_att  = set(af_cumul_t.attacks) <= set(af_cumul_t1.attacks)
print("\nHypothese monotone sur ce corpus :")
print(f"  args    G_cumul_t inclus dans G_cumul_t1 : {incl_args}")
print(f"  attacks G_cumul_t inclus dans G_cumul_t1 : {incl_att}")
assert incl_args and incl_att
print("  -> VERIFIEE PAR CONSTRUCTION : sur des corpus emboites, build_aif_graph")
print("     n'exclut jamais un noeud deja relie (C3 ne frappe que les singletons, et")
print("     les relations s'accumulent). Ici la monotonie est un theoreme de")
print("     l'instrument ; elle ne le resterait pas devant un corpus reel retire des enonces.")


# ### Violation : un argument retiré entre deux dates
# 
# L'instrument n'a pas d'acte « rétractif » : le corpus non-monotone se construit en retirant du
# cumul les énoncés d'un argument — c'est exactement le graphe qu'un futur acte rétractif produirait.
# Deux familles de retraits ne parlent pas aux deux mesures de la même façon :
# 
# - retirer un argument **hors de l'extension grounded** (défait) : la mesure structurelle le voit,
#   la mesure sémantique peut rester immobile — sauf si l'argument retiré **attaquait** un candidat
#   à l'acceptation, auquel cas sa disparition peut *faire entrer* ce candidat dans grounded ;
# - retirer un argument **dans l'extension grounded** (accepté) : la mesure sémantique bouge
#   nécessairement (l'accepté disparaît de l'extension).
# 

# In[13]:


def sans_argument(corpus, prop):
    """Corpus non-monotone : tous les enonces portant `prop` ou le ciblant sont retires.

    C'est le graphe qu'un acte retractif produirait : l'argument disparait avec ses
    relations, y compris les attaques QUI LE VISENT (une attaque sans cible n'a pas
    de sens dans le cadre de Dung)."""
    return [e for e in corpus
            if e.prop != prop and all(cible != prop for _, cible in e.relations)]

E_cumul_t = grounded(af_cumul_t)
dans_grounded = sorted(E_cumul_t)
hors_grounded = sorted(set(af_cumul_t1.args) - E_cumul_t)   # args de t+1 hors grounded de t

print(f"Grounded de G_cumul_t ({len(dans_grounded)}/{len(af_cumul_t.args)}) : {dans_grounded}")
print(f"Hors grounded ({len(hors_grounded)}) : {hors_grounded}\n")

# (a) Tous les retraits hors-grounded : distribution honnete de l'effet sur d_sem
print("Retrait d'un argument DEFAIT (hors grounded) — effet mesure un par un :")
n_sem_nul = n_sem_bouge = 0
for prop in hors_grounded:
    af_r = to_dung_af(build_aif_graph(sans_argument(cumul_t1, prop)))
    d_n, d_a = d_struct(af_cumul_t1, af_r)
    d_s = d_sem(af_cumul_t1, af_r)
    tag = "d_sem immobile" if d_s == 0.0 else f"d_sem BOUGE ({d_s:.3f})"
    print(f"  retrait '{prop}': d_noeuds={d_n:.3f} d_att={d_a:.3f} d_sem={d_s:.3f}  {tag}")
    if d_s == 0.0:
        n_sem_nul += 1
    else:
        n_sem_bouge += 1
print(f"  -> {n_sem_nul} retraits laissent grounded inchange ; {n_sem_bouge} le font bouger")
print("     (un defait qui ATTAQUAIT un candidat peut, en disparaisant, le faire accepter)\n")

# (b) Retrait d'un argument ACCEPTE : la mesure semantique bouge necessairement
prop_accepte = dans_grounded[0]
af_r_acc = to_dung_af(build_aif_graph(sans_argument(cumul_t1, prop_accepte)))
d_n_acc, d_a_acc = d_struct(af_cumul_t1, af_r_acc)
d_s_acc = d_sem(af_cumul_t1, af_r_acc)
print(f"Retrait de '{prop_accepte}' [ACCEPTE, dans grounded] :")
print(f"  d_noeuds = {d_n_acc:.3f}   d_att = {d_a_acc:.3f}   d_sem = {d_s_acc:.3f}")

# Assertions robustes : ce que l'instrument FAIT quand l'hypothese est violee
assert d_n_acc > 0.0 and d_s_acc > 0.0, "le retrait d'un accepte doit bouger les deux mesures"
assert all(d_struct(af_cumul_t1, to_dung_af(build_aif_graph(sans_argument(cumul_t1, p))))[0] > 0.0
           for p in hors_grounded), "tout retrait doit etre visible structurellement"
print("\nCe que l'instrument fait sous violation :")
print("  d_noeuds > 0 pour TOUT retrait : la mesure structurelle voit chaque disparition ;")
print("  d_sem ne bouge QUE si le retrait touche l'extension grounded (directement, ou via")
print("      un attaquant disparu qui libere un candidat) ;")
print("  AUCUNE des deux mesures ne dit RETRAIT vs APPARITION : le sens du mouvement n'est")
print("  pas dans l'ecart de graphes — il est dans les evenements dates du corpus. C'est")
print("  la limite explicite que l'hypothese monotone permettait de ne pas poser.")


# ## 11. Exercices
# 
# Trois exercices pour prolonger l'instrument — chacun suit un exemple guidé de ce notebook.
# 

# ### Exercice 1 — Distance d'édition normalisée
# 
# **Contexte.** La distance de Jaccard traite ajout et suppression symétriquement et ignore la taille
# des graphes. Une **distance d'édition** (nombre d'ajouts + suppressions d'arêtes pour transformer $A$
# en $A'$, normalisé par la taille du plus grand graphe) pondère différemment les petites évolutions.
# 
# **Objectif.** Implémenter `edit_distance_attaques(af1, af2)` $= (|A_1 \setminus A_2| + |A_2 \setminus A_1|) / \max(|A_1|, |A_2|)$,
# puis la comparer à $d_{att}$ sur l'écart inter-dates et sur le contrôle positif : divergent-elles
# sur le classement des deux situations ?
# 
# **Indices.** `af.attacks` est un ensemble de couples — les différences ensemblistes suffisent ;
# attention au cas où les deux ensembles sont vides (retourner 0, comme `jaccard_distance`).
# 

# In[14]:


def edit_distance_attaques(af1, af2):
    """TODO etudiant : distance d'edition normalisee sur les ensembles d'attaques.

    (|A1 \ A2| + |A2 \ A1|) / max(|A1|, |A2|), et 0.0 si les deux sont vides.
    """
    # Etape 1 : extraire les deux ensembles d'attaques.
    # Etape 2 : calculer les ajouts et suppressions (differences ensemblistes).
    # Etape 3 : normaliser par la taille du plus grand ensemble.
    print("Exercice a completer")
    return None


print("Exercice 1 a completer : fonction definie, a vous de l'appeler sur af_t / af_t1")
resultat_ex1 = None  # TODO etudiant : edit_distance_attaques(af_t, af_t1)


# ### Exercice 2 — Plancher de bruit par split aléatoire répété
# 
# **Contexte.** Le split première/seconde moitié donne **un** plancher. La distribution du plancher sous
# découpage aléatoire (20 tirages de moitiés aléatoires) dit si le plancher observé est stable ou
# chanceux — c'est la version robuste du contrôle négatif.
# 
# **Objectif.** Répéter 20 fois : permutation aléatoire du corpus $t$, split en deux moitiés, mesure
# $d_{sem}(G_a, G_b)$. Publier moyenne, écart-type, min, max. L'écart inter-dates dépasse-t-il la borne
# haute du plancher (et non plus seulement une seule réalisation) ?
# 
# **Indices.** `random.Random(42)` pour un tirage reproductible ; `random.sample(corpus, len(corpus))`
# pour permuter ; les fonctions `build_aif_graph`, `to_dung_af`, `d_sem` existent déjà.
# 

# In[15]:


import random


def plancher_aleatoire(corpus, n_tirages=20, seed=42):
    """TODO etudiant : distribution du plancher de bruit sous splits aleatoires.

    Renvoie la liste des n_tirages valeurs de d_sem(G_a, G_b).
    """
    # Etape 1 : rng = random.Random(seed).
    # Etape 2 : pour chaque tirage, permuter le corpus puis le couper en deux moities.
    # Etape 3 : construire les graphes, mesurer d_sem, accumuler.
    print("Exercice a completer")
    return None


print("Exercice 2 a completer : fonction definie, a vous de produire la distribution")
distribution_ex2 = None  # TODO etudiant : plancher_aleatoire(corpus_t)


# ### Exercice 3 — Troisième mesure : classement gradué (fardeau)
# 
# **Contexte.** L'acceptation binaire de Dung écrase la variation : un argument marginalement attaqué
# et un argument submergé sont « dehors » pareillement. Les **sémantiques de classement** du substrat
# [Ranking_Semantics](Argument_Analysis_Ranking_Semantics.ipynb) (h-Categoriser, fardeau) donnent à chaque
# argument une *force* numérique — une troisième mesure d'écart, graduée, peut voir des déplacements
# invisibles à $d_{sem}$.
# 
# **Objectif.** Implémenter le classement par **fardeau** (burden) puis mesurer $d_{rank}$ = distance de
# Spearman (ou Kendall tau) entre les classements de $G_t$ et $G_{t+1}$.
# 
# **Indices.** Le fardeau de $x$ = nombre d'attaquants de $x$ non défaits par l'extension grounded $E$ ;
# `scipy.stats.spearmanr` si scipy est disponible, sinon des rangs moyens à la main sur les ex-aequo.
# 

# In[16]:


def fardeau(af, E):
    """TODO etudiant : fardeau de chaque argument = attaquants non defaits par E."""
    # Indice : un attaquant a est "defait" si un membre de E l'attaque.
    print("Exercice a completer")
    return None


def d_rank(af1, af2):
    """TODO etudiant : ecart de classement (Spearman) entre les fardeaux de deux graphes."""
    # Etape 1 : calculer les fardeaux avec l'extension grounded de chaque graphe.
    # Etape 2 : ranger les arguments communs par fardeau croissant dans chaque graphe.
    # Etape 3 : correlation de Spearman entre les deux rangs (1 - rho = distance).
    print("Exercice a completer")
    return None


print("Exercice 3 a completer : fonctions definies, a vous de produire le classement")
resultat_ex3 = None  # TODO etudiant : d_rank(af_t, af_t1)


# ## Conclusion — ce que l'instrument sait, et ne sait pas
# 
# **Sait** : transformer un corpus daté en graphe AIF conforme (critère d'inclusion écrit C1–C3,
# exclusions publiées), le projeter sur Dung, mesurer un écart sur deux familles indépendantes
# (structurelle, sémantique), et **situer chaque écart par rapport à son plancher de bruit** — avec un
# contrôle positif dont la magnitude attendue était écrite avant la mesure, et qui distingue ce que
# chaque famille voit (un renversement d'acceptation est invisible en structure).
# 
# **Ne sait pas (encore)** : rien sur un phénomène réel — l'instrument est neutre quant au domaine ; le
# brancher sur l'humour, le désir ou l'attachement est un grain ultérieur de l'Epic
# [#13303](https://github.com/jsboige/CoursIA/issues/13303), et le choix d'un corpus daté réel attend le
# protocole [#13309](https://github.com/jsboige/CoursIA/issues/13309). La projection AIF → Dung ignore
# les supports (pas de bipolaire) ; le classement gradué (exercice 3) est la voie naturelle pour
# affiner le verdict sémantique.
# 
