"""Organes canoniques de la ligne dowhy -- decouverte de structure (DoWhy-3).

Issue #14049 (grain DoWhy-3). DoWhy-1 section 4 s'intitule « le graphe
assume » et sa section 5 mesure la sensibilite a cette hypothese. Ce module
repond a la question suivante : **et si on ne l'a pas, ce graphe ?** Trois
familles SOTA de decouverte causale, reellement executees (regle F /
SOTA-OK -- ``causal-learn``, jamais de reimplementation jouet) :

1. **PC (contraintes)** -- tests d'independance conditionnelle (Fisher-z),
   v-structures, regles de Meek. Rend un CPDAG.
2. **GES (score)** -- recherche gloutonne BIC sur les classes
   d'equivalence. Rend un CPDAG.
3. **LiNGAM (fonctionnel)** -- linearite + bruit NON GAUSSIEN, ordre
   causal identifiable (DARM). Rend un DAG complet.

Le verdict honnete du module : sur donnees lineaires gaussiennes, PC et
GES rendent un CPDAG avec des aretes non orientees (``C--X`` et ``X--M``
dans notre monde). Cette ambiguite EST la classe d'equivalence de Markov
-- un resultat, pas un echec. LiNGAM tranche ces aretes, mais au prix
d'une HYPOTHESE (non-gaussianite du bruit) : sur bruit gaussien, LiNGAM
rend quand meme un DAG complet -- confiant, faux, et sans avertissement.
Le verdict doit venir du praticien, pas de la librairie.

Pieges pedagogiques que le module expose, mesures :

1. **L'ambiguite est structurelle** : augmenter ``n`` ne tranche pas
   ``C--X`` -- aucune quantite de donnees gaussiennes ne distingue
   ``C->X`` de ``X->C`` dans la meme classe de Markov.
2. **Le CPDAG n'est pas une devinette partielle** : ses extensions valides
   sont 3, pas 2^2 = 4 -- l'orientation ``C->X`` + ``M->X`` cree une
   v-structure a X que la donnee exclut (cf.
   ``enumerer_extensions_acycliques``).
3. **LiNGAM ne previent pas** : sur bruit gaussien il rend un DAG faux
   sans lever d'erreur ; l'instabilite inter-seeds est le seul signal
   (cf. section 6 du notebook).
4. **L'ambiguite se propage a l'estimand** : les 3 extensions valides du
   MEME CPDAG, sur les MEMES donnees, donnent 3 estimands dowhy
   differents (0.81 / 1.05 / 0.22 sur le monde par defaut) -- cf.
   ``effet_backdoor_depuis_aretes``.
5. **alpha de PC est un vrai compromis** : sur ce monde, alpha = 0.05
   perd la v-structure environ 1 seed sur 4 (un test de vraie
   independance rejete au niveau 5 % ; mesure : 15/20 seeds canoniques
   a 0.05, 20/20 a 0.01).

Fonctions exposees
------------------

- ``generer_donnees_decouverte(n, bruit, seed)`` -- monde DGP-connu a 5
  variables (C, X, M, Y, Z) : confondeur C, traitement X, mediateur M,
  resultat Y, descendant Z. ``bruit="gaussien"`` -> PC/GES rendent un
  CPDAG ; ``bruit="non_gaussien"`` (exponentiel centre) -> LiNGAM
  recouvre le DAG exact.
- ``executer_pc(donnees, alpha)`` -- PC de causal-learn (Fisher-z),
  rend les aretes orientees et non orientees.
- ``executer_ges(donnees)`` -- GES (BIC), meme sortie.
- ``executer_lingam(donnees, seuil_coef)`` -- DirectLiNGAM : matrice
  d'adjacence W (convention ``W[i, j] != 0`` => ``j -> i``), ordre
  causal, aretes.
- ``v_structures(aretes)`` -- les triples ``a -> b <- c`` non brides
  d'un DAG donne.
- ``enumerer_extensions_acycliques(resultat)`` -- les DAGs valides
  derriere un CPDAG : acycliques ET memes v-structures.
- ``verdict_cpdag(resultat)`` -- le verdict honnete : ``CPDAG_AMBIGU``
  (l'ambiguite est un resultat) ou ``DAG_ORIENTE`` (l'orientation vient
  des hypotheses, pas des donnees seules).
- ``comparer_au_dag_vrai(resultat)`` -- squelette / orientations correctes
  / inverses / parasites / manquantes contre ``ARETES_DAG_VRAI``.
- ``effet_backdoor_depuis_aretes(donnees, aretes, traitement, resultat)``
  -- le pont dowhy : identifie + estime l'effet backdoor sur le DAG
  fourni (decouvert ou suppose), expose l'ensemble d'ajustement choisi.

Doctrine de parametrisation (cf. ``dowhy_organs.py``, ``dowhy_iv_organs.py``) :
RandomState LOCAL par fonction, constantes en module documentees.

References
----------

- Notebook consommateur : ``DoWhy-3-Decouverte-de-Structure.ipynb``.
- PC : Spirtes & Glymour, « An Algorithm for Fast Recovery of Sparse
  Causal Graphs », Social Science Computer Review 9 (1991).
- GES : Chickering, « Optimal Structure Identification With Greedy
  Search », JMLR 3 (2002).
- DirectLiNGAM : Shimizu et al., « DirectLiNGAM », AISTATS 2011 ;
  identifiabilite DARM : Shimizu et al. 2006.
- Classes d'equivalence : Verma & Pearl, « Equivalence and Synthesis of
  Causal Models », UAI 1990.
- API causal-learn : ``causallearn.search.ConstraintBased.PC.pc``,
  ``causallearn.search.ScoreBased.GES.ges``,
  ``causallearn.search.FCMBased.lingam.direct_lingam.DirectLiNGAM``.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from itertools import combinations, product
from typing import Dict, List, Optional, Tuple

import networkx as nx
import numpy as np
import pandas as pd

# ---------------------------------------------------------------------------
# Constantes par defaut -- l'unique verite du simulateur
# ---------------------------------------------------------------------------
# Monde DGP (5 variables, tous bruits independants) :
#     C ~ Bruit(1.0)
#     X = COEF_C_X * C + Bruit(0.5)
#     M = COEF_X_M * X + Bruit(0.5)
#     Y = COEF_M_Y * M + COEF_C_Y * C + Bruit(0.5)
#     Z = COEF_Y_Z * Y + Bruit(0.5)
ARETES_DAG_VRAI: List[Tuple[str, str]] = [
    ("C", "X"),
    ("X", "M"),
    ("M", "Y"),
    ("C", "Y"),
    ("Y", "Z"),
]
ORDRE_COLONNES: List[str] = ["C", "X", "M", "Y", "Z"]
COEF_C_X: float = 1.0
COEF_X_M: float = 1.0
COEF_M_Y: float = 0.8
# COEF_C_Y = 0.3 et non 0.6 : a 0.6, la covariance partielle (C, M | Y)
# s'annule presque exactement (le chemin C->X->M compense l'ouverture du
# collisionneur C->Y<-M) -- monde quasi-infidele ou {Y} devient un sepset
# legitime pour PC, qui perd la v-structure 18 fois sur 20 (mesure
# 2026-09-13). A 0.3, corr partielle (C, M | Y) ~ 0.27 : collisionneur
# detectable 20/20 a alpha = 0.01.
COEF_C_Y: float = 0.3
COEF_Y_Z: float = 1.0
BRUIT_C: float = 1.0
BRUIT_X: float = 0.5
BRUIT_M: float = 0.5
BRUIT_Y: float = 0.5
BRUIT_Z: float = 0.5
# alpha par defaut de PC : le standard causal-learn. Sur CE monde, la
# v-structure est fragile a 0.05 (15/20 seeds canoniques) et robuste a
# 0.01 (20/20) -- le notebook motive le choix, l'exercice 2 le mesure.
ALPHA_PC_DEFAUT: float = 0.05
SEUIL_COEF_LINGAM: float = 0.1


# ---------------------------------------------------------------------------
# Generateur du monde
# ---------------------------------------------------------------------------
def generer_donnees_decouverte(
    n: int = 2000,
    bruit: str = "gaussien",
    seed: int = 42,
) -> pd.DataFrame:
    """Monde DGP a 5 variables, DAG connu (``ARETES_DAG_VRAI``).

    Mecanisme (lineaire, bruits independants) :
        C ~ Bruit(1.0)
        X = 1.0 * C  + Bruit(0.5)
        M = 1.0 * X  + Bruit(0.5)
        Y = 0.8 * M  + 0.3 * C + Bruit(0.5)
        Z = 1.0 * Y  + Bruit(0.5)

    Semantique : C confondeur observe, X traitement, M mediateur,
    Y resultat, Z descendant de Y (capteur). Le DAG vrai porte une seule
    v-structure non bridee : ``C -> Y <- M``.

    Parametrisation
    ---------------
    n : int, default 2000
        Taille de l'echantillon.
    bruit : str, default "gaussien"
        ``"gaussien"`` : N(0, sigma) -- PC et GES rendent le CPDAG
        (C--X et X--M non orientees), LiNGAM n'a aucune raison d'etre
        juste. ``"non_gaussien"`` : exponentiel centre et rescale
        (variance identique au gaussien) -- LiNGAM recouvre le DAG
        exact ; PC, qui n'utilise pas la forme du bruit, reste CPDAG.
    seed : int, default 42
        RandomState LOCAL (doctrine module).

    Return
    ------
    pd.DataFrame de shape ``(n, 5)`` -- colonnes ``C``, ``X``, ``M``,
    ``Y``, ``Z`` dans cet ordre.
    """
    if bruit not in ("gaussien", "non_gaussien"):
        raise ValueError(f"bruit doit etre 'gaussien' ou 'non_gaussien', recu {bruit!r}")
    rng = np.random.RandomState(seed)

    def tirage(sigma: float) -> np.ndarray:
        if bruit == "gaussien":
            return rng.normal(0.0, sigma, n)
        # Exponentiel centre : E=1, Var=1 -> centre puis rescale a sigma
        # (meme variance que le gaussien, seul change le kurtosis).
        return sigma * (rng.exponential(1.0, n) - 1.0)

    c = tirage(BRUIT_C)
    x = COEF_C_X * c + tirage(BRUIT_X)
    m = COEF_X_M * x + tirage(BRUIT_M)
    y = COEF_M_Y * m + COEF_C_Y * c + tirage(BRUIT_Y)
    z = COEF_Y_Z * y + tirage(BRUIT_Z)
    return pd.DataFrame({"C": c, "X": x, "M": m, "Y": y, "Z": z})


# ---------------------------------------------------------------------------
# Resultat structure commun
# ---------------------------------------------------------------------------
@dataclass
class ResultatDecouverte:
    """Sortie structuree des executeurs (PC, GES, LiNGAM).

    Champs :
        methode : str -- "PC", "GES" ou "LiNGAM".
        aretes_orientees : list[tuple[str, str]] -- aretes (u, v) lues
            u -> v par l'algorithme.
        aretes_non_orientees : list[tuple[str, str]] -- aretes du CPDAG
            que la donnee ne tranche pas (u - v), stockees triees.
        matrice_adjacence : ndarray ou None -- W de LiNGAM (convention
            ``W[i, j] != 0`` => ``j -> i``), None pour PC/GES.
        ordre_causal : list[str] ou None -- ordre causal estime par
            LiNGAM (cause -> effet), None pour PC/GES.
        n : int -- taille de l'echantillon.
        details : dict -- parametres de l'algorithme (alpha, score,
            seuil...).
    """

    methode: str
    aretes_orientees: List[Tuple[str, str]] = field(default_factory=list)
    aretes_non_orientees: List[Tuple[str, str]] = field(default_factory=list)
    matrice_adjacence: Optional[np.ndarray] = None
    ordre_causal: Optional[List[str]] = None
    n: int = 0
    details: Dict[str, object] = field(default_factory=dict)


def _aretes_depuis_generalgraph(graphe, labels: List[str]):
    """Convertit un GeneralGraph causal-learn en (orienteess, non_orientees).

    Conventions d'endpoints causal-learn : (TAIL, ARROW) => u -> v ;
    (ARROW, TAIL) => v -> u ; toute autre combinaison (TAIL/TAIL, CIRCLE)
    est une arete que la donnee ne tranche pas.
    """
    from causallearn.graph.Endpoint import Endpoint

    orientees: List[Tuple[str, str]] = []
    non_orientees: List[Tuple[str, str]] = []
    for e in graphe.get_graph_edges():
        u, v = e.node1.name, e.node2.name
        if e.endpoint1 == Endpoint.TAIL and e.endpoint2 == Endpoint.ARROW:
            orientees.append((u, v))
        elif e.endpoint1 == Endpoint.ARROW and e.endpoint2 == Endpoint.TAIL:
            orientees.append((v, u))
        else:
            non_orientees.append(tuple(sorted((u, v))))
    return sorted(orientees), sorted(set(non_orientees))


def executer_pc(
    donnees: pd.DataFrame,
    alpha: float = ALPHA_PC_DEFAUT,
    labels: Optional[List[str]] = None,
) -> ResultatDecouverte:
    """PC (Spirtes-Glymour) via causal-learn : tests Fisher-z + v-structures.

    Parametrisation
    ---------------
    donnees : pd.DataFrame
        Les colonnes utilisees sont ``labels`` (defaut : ``ORDRE_COLONNES``).
    alpha : float, default 0.05
        Seuil des tests d'independance. Compromis mesure sur le monde
        par defaut : 0.05 -> v-structure perdue ~1 seed sur 4 ;
        0.01 -> 20/20 canonique (au prix de la puissance sur signaux
        faibles -- il n'y a pas d'alpha gratuit).
    labels : list[str], optional
        Noms de colonnes dans l'ordre de la matrice passee a PC.

    Return
    ------
    ResultatDecouverte(methode="PC") -- les aretes non orientees sont le
    resultat honnete, pas un echec de convergence.
    """
    from causallearn.search.ConstraintBased.PC import pc

    cols = list(labels) if labels is not None else ORDRE_COLONNES
    cg = pc(donnees[cols].values, alpha=alpha, node_names=cols, show_progress=False)
    orientees, non_orientees = _aretes_depuis_generalgraph(cg.G, cols)
    return ResultatDecouverte(
        methode="PC",
        aretes_orientees=orientees,
        aretes_non_orientees=non_orientees,
        n=len(donnees),
        details={"alpha": alpha, "test_independance": "fisherz"},
    )


def executer_ges(
    donnees: pd.DataFrame,
    labels: Optional[List[str]] = None,
) -> ResultatDecouverte:
    """GES (Chickering) via causal-learn : recherche gloutonne BIC.

    GES cherche directement sur l'espace des CLASSES d'equivalence (pas
    des DAGs individuels) : son output est nativement un CPDAG.

    Parametrisation
    ---------------
    donnees : pd.DataFrame
        Les colonnes utilisees sont ``labels`` (defaut : ``ORDRE_COLONNES``).
    labels : list[str], optional
        Noms de colonnes dans l'ordre de la matrice.

    Return
    ------
    ResultatDecouverte(methode="GES").
    """
    from causallearn.search.ScoreBased.GES import ges

    cols = list(labels) if labels is not None else ORDRE_COLONNES
    resultat = ges(donnees[cols].values, score_func="local_score_BIC", node_names=cols)
    orientees, non_orientees = _aretes_depuis_generalgraph(resultat["G"], cols)
    return ResultatDecouverte(
        methode="GES",
        aretes_orientees=orientees,
        aretes_non_orientees=non_orientees,
        n=len(donnees),
        details={"score": "local_score_BIC"},
    )


def executer_lingam(
    donnees: pd.DataFrame,
    seuil_coef: float = SEUIL_COEF_LINGAM,
    labels: Optional[List[str]] = None,
) -> ResultatDecouverte:
    """DirectLiNGAM via causal-learn : DAG complet sous non-gaussianite.

    LiNGAM exploite une hypothese que PC/GES ignorent : bruit exogene
    NON GAUSSIEN + relations lineaires => l'ordre causal est identifiable
    (DARM). En contrepartie, sur bruit gaussien, l'hypothese n'est pas
    tenue et DirectLiNGAM rend quand meme un DAG complet -- faux, sans
    erreur ni avertissement (verifie : deux seeds gaussiens rendent deux
    DAGs faux differents).

    Parametrisation
    ---------------
    donnees : pd.DataFrame
        Les colonnes utilisees sont ``labels`` (defaut : ``ORDRE_COLONNES``).
    seuil_coef : float, default 0.1
        Les coefficients |W| sous ce seuil sont consideres nuls (les
        vrais coefficients du monde par defaut sont >= 0.3).
    labels : list[str], optional
        Noms de colonnes dans l'ordre de la matrice.

    Return
    ------
    ResultatDecouverte(methode="LiNGAM") avec ``matrice_adjacence`` = W
    (convention ``W[i, j] != 0`` => ``j -> i``, verifiee sur DGP connu)
    et ``ordre_causal`` = ordre cause -> effet estime.
    """
    from causallearn.search.FCMBased.lingam.direct_lingam import DirectLiNGAM

    cols = list(labels) if labels is not None else ORDRE_COLONNES
    modele = DirectLiNGAM()
    modele.fit(donnees[cols].values)
    w = np.asarray(modele.adjacency_matrix_, dtype=float)
    aretes = [
        (cols[j], cols[i])
        for i in range(len(cols))
        for j in range(len(cols))
        if abs(w[i, j]) > seuil_coef
    ]
    ordre = [cols[k] for k in np.asarray(modele.causal_order_).ravel().tolist()]
    return ResultatDecouverte(
        methode="LiNGAM",
        aretes_orientees=sorted(aretes),
        aretes_non_orientees=[],
        matrice_adjacence=w,
        ordre_causal=ordre,
        n=len(donnees),
        details={"seuil_coef": seuil_coef},
    )


# ---------------------------------------------------------------------------
# Classes d'equivalence
# ---------------------------------------------------------------------------
def v_structures(aretes) -> List[Tuple[str, str, str]]:
    """V-structures non brides d'un ensemble d'aretes orientees.

    Une v-structure ``a -> b <- c`` est non bridee quand ``a`` et ``c``
    ne sont pas adjacents (aucune arete dans un sens ni dans l'autre) :
    c'est la seule configuration locale que deux DAGs equivalents ne
    peuvent PAS partager differemment (Verma & Pearl 1990 : meme
    squelette + memes v-structures <=> meme classe de Markov).

    Parametrisation
    ---------------
    aretes : iterable de tuples (u, v) lus u -> v.

    Return
    ------
    Liste triee de tuples (a, b, c) : a -> b <- c.
    """
    g = nx.DiGraph(list(aretes))
    out: List[Tuple[str, str, str]] = []
    for b in sorted(g.nodes):
        parents = sorted(g.predecessors(b))
        for a, c in combinations(parents, 2):
            if not g.has_edge(a, c) and not g.has_edge(c, a):
                out.append((a, b, c))
    return sorted(out)


def enumerer_extensions_acycliques(
    resultat: ResultatDecouverte,
) -> List[List[Tuple[str, str]]]:
    """Les DAGs valides derriere un CPDAG : 3, pas 2^k.

    Une extension d'un CPDAG est valide ssi (a) le DAG obtenu en
    orientant chaque arete ambigue est acyclique, ET (b) il porte
    EXACTEMENT les memes v-structures que le CPDAG. Le critere (b)
    exclut des orientations acycliques pourtant invalides : dans notre
    monde, orienter ``C -> X`` et ``M -> X`` cree une v-structure
    ``C -> X <- M`` que la donnee exclut -- 3 extensions valides, et
    non 4 (= 2^2 aretes ambigues).

    Les v-structures de reference se lisent sur les aretes DEJA orientees
    du CPDAG : les fleches d'une v-structure sont toujours compelled
    (meme orientation dans tous les membres de la classe).

    Parametrisation
    ---------------
    resultat : ResultatDecouverte
        Sortie de ``executer_pc`` ou ``executer_ges``.

    Return
    ------
    Liste triee d'extensions valides, chacune une liste triee d'aretes
    (u, v) orientees formant un DAG de la classe.
    """
    fixes = [tuple(e) for e in resultat.aretes_orientees]
    ambigues = [tuple(e) for e in resultat.aretes_non_orientees]

    # Adjacence complete (oriente + non orientee) pour le test "non bride".
    adjacence = nx.Graph(fixes + [tuple(sorted(e)) for e in ambigues])

    # V-structures de reference : parents deja orientes, non adjacents.
    parents_de: Dict[str, List[str]] = {}
    for u, v in fixes:
        parents_de.setdefault(v, []).append(u)
    v_ref = set()
    for b, parents in parents_de.items():
        for a, c in combinations(sorted(parents), 2):
            if not adjacence.has_edge(a, c):
                v_ref.add((a, b, c))

    extensions_valides: List[List[Tuple[str, str]]] = []
    if not ambigues:
        g = nx.DiGraph(fixes)
        if nx.is_directed_acyclic_graph(g):
            return [sorted(fixes)]
        return []
    for choix in product(*[[(u, v), (v, u)] for (u, v) in ambigues]):
        candidat = fixes + list(choix)
        g = nx.DiGraph(candidat)
        if not nx.is_directed_acyclic_graph(g):
            continue
        if set(v_structures(candidat)) != v_ref:
            continue
        extensions_valides.append(sorted(candidat))
    return sorted(extensions_valides)


# ---------------------------------------------------------------------------
# Verdicts
# ---------------------------------------------------------------------------
def verdict_cpdag(resultat: ResultatDecouverte) -> Dict[str, object]:
    """Le verdict honnete sur la forme du graphe decouvert.

    - ``CPDAG_AMBIGU`` : la methode rend des aretes non orientees. Ce
      n'est PAS un echec d'algorithme : c'est la classe d'equivalence
      de Markov, la borne exacte de ce que CES donnees (avec les
      hypotheses de CETTE methode) peuvent trancher.
    - ``DAG_ORIENTE`` : la methode rend un DAG complet. L'orientation
      ne vient PAS des donnees seules mais des hypotheses fonctionnelles
      de la methode (LiNGAM : non-gaussianite du bruit). Sans cette
      hypothese, rien ne distingue ce DAG des autres membres de sa
      classe -- sur bruit gaussien, le meme appel rend un DAG faux,
      sans avertissement.

    Parametrisation
    ---------------
    resultat : ResultatDecouverte
        Sortie d'un executeur.

    Return
    ------
    Dict avec cles ``verdict``, ``n_aretes_non_orientees``,
    ``aretes_non_orientees``, ``methode``, ``message``.
    """
    n_amb = len(resultat.aretes_non_orientees)
    if n_amb > 0:
        verdict = "CPDAG_AMBIGU"
        message = (
            f"{n_amb} arete(s) non orientee(s) : classe d'equivalence de Markov. "
            "L'ambiguite est un RESULTAT -- aucun n plus grand ne la tranche "
            "(donnees gaussiennes). Chaque extension valide donne un estimand "
            "potentiellement different (cf. effet_backdoor_depuis_aretes)."
        )
    else:
        verdict = "DAG_ORIENTE"
        message = (
            "Orientation complete : elle vient des HYPOTHESES de la methode "
            "(LiNGAM : bruit non gaussien), pas des donnees seules. Sur bruit "
            "gaussien le meme appel rend un DAG faux sans avertissement -- "
            "verifier l'hypothese (kurtosis, stabilite inter-seeds) avant de "
            "faire parler l'orientation."
        )
    return {
        "verdict": verdict,
        "n_aretes_non_orientees": n_amb,
        "aretes_non_orientees": [tuple(e) for e in resultat.aretes_non_orientees],
        "methode": resultat.methode,
        "message": message,
    }


def comparer_au_dag_vrai(
    resultat: ResultatDecouverte,
    aretes_vraies: Optional[List[Tuple[str, str]]] = None,
) -> Dict[str, object]:
    """Confronte un resultat de decouverte au DAG vrai du simulateur.

    Parametrisation
    ---------------
    resultat : ResultatDecouverte
        Sortie d'un executeur.
    aretes_vraies : list[tuple[str, str]], optional
        Defaut : ``ARETES_DAG_VRAI``.

    Return
    ------
    Dict avec cles :
        ``squelette_trouvees`` -- "k/K" aretes vraies presentes (orientees
        ou non) ;
        ``oriente_comme_vrai`` -- arets orientees dans le bon sens ;
        ``oriente_inverse`` -- aretes orientees a l'envers du DAG vrai ;
        ``non_orientees_parmi_vraies`` -- vraies arets laissees ambigues ;
        ``parasites`` -- aretes detectees absentes du DAG vrai ;
        ``manquantes`` -- vraies aretes absentes du resultat.
    """
    vraies = {tuple(e) for e in (aretes_vraies or ARETES_DAG_VRAI)}
    orientees = {tuple(e) for e in resultat.aretes_orientees}
    non_orientees = {tuple(sorted(e)) for e in resultat.aretes_non_orientees}

    squelette_detecte = {
        tuple(sorted(e)) for e in orientees
    } | non_orientees

    oriente_comme_vrai = sorted(orientees & vraies)
    # une arete orientee "inverse" = (v, u) avec (u, v) vraie
    inversees = sorted(
        (v, u) for (u, v) in vraies if (v, u) in orientees
    )
    non_or_vraies = sorted(
        tuple(sorted(e)) for e in vraies if tuple(sorted(e)) in non_orientees
    )
    vraies_skel = {tuple(sorted(e)) for e in vraies}
    parasites = sorted(squelette_detecte - vraies_skel)
    manquantes = sorted(vraies_skel - squelette_detecte)
    return {
        "squelette_trouvees": f"{len(vraies_skel) - len(manquantes)}/{len(vraies_skel)}",
        "oriente_comme_vrai": oriente_comme_vrai,
        "oriente_inverse": inversees,
        "non_orientees_parmi_vraies": non_or_vraies,
        "parasites": parasites,
        "manquantes": manquantes,
    }


# ---------------------------------------------------------------------------
# Pont dowhy : du graphe decouvert a l'estimand
# ---------------------------------------------------------------------------
@dataclass
class DowhyBackdoorResult:
    """Sortie structuree du wrapper ``effet_backdoor_depuis_aretes``.

    Champs :
        estimate_value : float -- effet estime (backdoor.linear_regression).
        ensemble_ajustement : list[str] -- variables d'ajustement
            retenues par dowhy pour cet ensemble d'aretes.
        estimand_texte : str -- estimand identifie (texte dowhy).
    """

    estimate_value: float
    ensemble_ajustement: List[str] = field(default_factory=list)
    estimand_texte: str = ""


def effet_backdoor_depuis_aretes(
    donnees: pd.DataFrame,
    aretes,
    traitement: str = "X",
    resultat: str = "Y",
) -> DowhyBackdoorResult:
    """Identifie et estime l'effet backdoor sur un ensemble d'aretes donne.

    C'est le pont entre la decouverte (ce module) et l'identification
    (dowhy, DoWhy-1) : le DAG decouvert -- ou n'importe quelle extension
    d'un CPDAG -- alimente le pipeline dowhy. Le point pedagogique :
    les differentes extensions valides du MEME CPDAG, sur les MEMES
    donnees, donnent des ensembles d'ajustement et des estimands
    DIFFERENTS (mesure sur le monde par defaut : 0.81 / 1.05 / 0.22 pour
    un effet total vrai de 0.8). L'ambiguite de la decouverte ne s'arrete
    pas au dessin : elle se propage au chiffre.

    Parametrisation
    ---------------
    donnees : pd.DataFrame
        Doit porter toutes les variables du graphe.
    aretes : iterable de tuples (u, v) lus u -> v
        Le DAG a tester (decouvert par LiNGAM, extension d'un CPDAG,
        ou suppose par expertise -- meme pipeline).
    traitement, resultat : str
        Noms du traitement et de l'outcome (defaut X et Y).

    Return
    ------
    DowhyBackdoorResult -- voir la dataclass.

    Raises
    ------
    RuntimeError
        Si dowhy ne peut pas identifier d'ensemble backdoor pour ce
        graphe (l'exception remonte au notebook, qui la commente).
    """
    from dowhy import CausalModel

    graphe = nx.DiGraph([tuple(e) for e in aretes])
    modele = CausalModel(
        data=donnees,
        treatment=traitement,
        outcome=resultat,
        graph=graphe,
    )
    estimand = modele.identify_effect()
    effet = modele.estimate_effect(
        estimand, method_name="backdoor.linear_regression"
    )
    backdoor_vars = getattr(estimand, "backdoor_variables", None)
    if isinstance(backdoor_vars, dict):
        ensemble = sorted(backdoor_vars.get("backdoor", []))
    elif backdoor_vars:
        ensemble = sorted(backdoor_vars)
    else:
        ensemble = []
    return DowhyBackdoorResult(
        estimate_value=float(effet.value),
        ensemble_ajustement=ensemble,
        estimand_texte=str(estimand),
    )
