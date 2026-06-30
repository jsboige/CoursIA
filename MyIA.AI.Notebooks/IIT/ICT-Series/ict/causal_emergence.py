"""Causal Emergence 2.0 : quantifier la complexite emergente multi-echelles.

Reimplementation pedagogique inspiree de :

    Erik Hoel, "Causal Emergence 2.0: Quantifying emergent complexity",
    arXiv:2503.13395, 2025.

ainsi que de la construction canonique de macro-echelle (coarse-graining sous
intervention) de :

    Hoel, Albantakis & Tononi, "Quantifying causal emergence shows that macro
    can beat micro", PNAS 2013 ;
    Erik Hoel, "When the map is better than the territory", Entropy 2017.

Note de provenance / licence
----------------------------
Le depot de reference https://github.com/jessescool/Causal-Emergence-2.0
(implementation accompagnant l'article) ne porte AUCUNE licence : son code
n'est donc pas reutilisable. Ce module est une reimplementation INDEPENDANTE,
ecrite a partir des equations de l'article et de la litterature canonique de
l'emergence causale (et non a partir de ce code). Le depot est cite ici comme
implementation de reference, a des fins de comparaison pedagogique uniquement.

Place dans la serie ICT
-----------------------
La serie ICT est passee de la *photographie* (Phi a un instant, ICT-1) au
*film* (trajectoires causales, ICT-2/3) puis a l'emergence causale canonique
par coarse-graining maximisant une mesure causale (ICT-5, via ``pyphi.macro``).
Le present module apporte l'outillage *moderne* du second pilier de la serie :
au lieu de chercher l'unique macro-echelle qui maximise une mesure causale, on
**apportionne** la causalite le long d'un *chemin* d'echelles (micro -> macro)
et l'on mesure a quel point le travail causal d'un systeme est *distribue*
entre ses echelles -- la "complexite emergente" EC de l'article.

Contrairement a PyPhi (limite en pratique a ~6 noeuds), ce module n'opere que
sur une matrice de transition etat-a-etat (n x n, numpy) : il passe donc a
l'echelle sur des systemes que PyPhi ne peut pas traiter (interet direct pour
ICT-6, ou l'on branche les trajectoires de tri-morphogenese d'ICT-2 via
``ict.tpm_estimation``).

Format des TPM
--------------
Ici une TPM est une matrice **etat-a-etat** ``(n, n)``, ligne-stochastique :
``tpm[i, j]`` = P(etat suivant = j | etat courant = i). C'est le format naturel
d'une chaine de Markov sur n macro-etats, distinct du format state-by-node de
PyPhi utilise par ``ict.trajectories`` (voir ``ict.tpm_estimation`` pour le
pont entre les deux representations).

Definitions (article + litterature canonique)
----------------------------------------------
Sous une intervention uniforme sur les n etats (le ``do`` de Hoel) :
  - determinisme (suffisance)   : det = 1 - <H(E|c)> / log2(n)
  - degenerescence              : deg = 1 - H(E|C) / log2(n)
  - specificite (necessite)     : spec = 1 - deg
  - effectiveness (normalisee)  : eff = det - deg                  (dans [0, 1])
  - information effective (bits): EI  = eff * log2(n)
ou E|c est la ligne de la TPM pour l'etat-cause c, et E|C la distribution
d'effet marginale (moyenne des lignes sous intervention uniforme).

Dependances : bibliotheque standard + numpy.
Reference : ICT-0 (cadrage de la serie), Epic #4588.
"""

from __future__ import annotations

from typing import Callable

import numpy as np


# --------------------------------------------------------------- validation
def validate_tpm(tpm, tol: float = 1e-6) -> np.ndarray:
    """Verifie qu'une matrice est une TPM etat-a-etat valide et la retourne.

    Conditions : carree ``(n, n)``, sans valeur negative, chaque ligne sommant
    a 1 (a ``tol`` pres). Leve ``ValueError`` sinon.
    """
    m = np.asarray(tpm, dtype=float)
    if m.ndim != 2 or m.shape[0] != m.shape[1]:
        raise ValueError(f"TPM doit etre carree (n, n), recu {m.shape}")
    if np.any(m < -tol):
        raise ValueError("TPM contient des probabilites negatives")
    sums = m.sum(axis=1)
    if not np.allclose(sums, 1.0, atol=max(tol, 1e-9)):
        raise ValueError(f"lignes non normalisees a 1 : sommes = {sums}")
    return m


# --------------------------------------------------------------- entropie
def _entropy_bits(p) -> float:
    """Entropie de Shannon en bits d'une distribution, avec 0*log2(0) = 0."""
    p = np.asarray(p, dtype=float)
    nz = p[p > 0]
    if nz.size == 0:
        return 0.0
    return float(-np.sum(nz * np.log2(nz)))


# --------------------------------------------------------------- primitives causales
def determinism(tpm) -> float:
    """Determinisme (suffisance) : ``1 - <H(E|c)> / log2(n)``.

    Mesure a quel point chaque etat-cause determine son effet : 1.0 si chaque
    ligne de la TPM est un Dirac (transition certaine), plus bas si les
    transitions sont bruitees. La moyenne est prise sous intervention uniforme.
    """
    m = validate_tpm(tpm)
    n = m.shape[0]
    if n < 2:
        return 1.0
    mean_row_entropy = float(np.mean([_entropy_bits(m[i]) for i in range(n)]))
    return 1.0 - mean_row_entropy / np.log2(n)


def degeneracy(tpm) -> float:
    """Degenerescence : ``1 - H(E|C) / log2(n)``.

    ``E|C`` est la distribution d'effet *marginale* sous intervention uniforme
    (moyenne des lignes de la TPM). Elevee quand des causes differentes
    convergent vers les memes effets (l'effet renseigne peu sur la cause).
    """
    m = validate_tpm(tpm)
    n = m.shape[0]
    if n < 2:
        return 0.0
    marginal = m.mean(axis=0)
    return 1.0 - _entropy_bits(marginal) / np.log2(n)


def specificity(tpm) -> float:
    """Specificite (necessite) : ``1 - degeneracy``. Voir ``degeneracy``."""
    return 1.0 - degeneracy(tpm)


def effectiveness(tpm) -> float:
    """Effectiveness normalisee : ``determinism - degeneracy`` (dans [0, 1]).

    Quantite causale *scale-free* (independante du nombre d'etats) : c'est la
    primitive naturellement apportionnee le long d'un chemin d'echelles, car
    elle n'est pas penalisee par le retrecissement de ``log2(n)`` au
    coarse-graining (contrairement a l'EI en bits).
    """
    m = validate_tpm(tpm)
    return determinism(m) - degeneracy(m)


def effective_information(tpm) -> float:
    """Information effective ``EI = effectiveness * log2(n)`` (en bits).

    Mesure causale canonique (Hoel/Tononi) : equivaut a la divergence KL
    moyenne entre la ligne de chaque etat et la distribution d'effet marginale,
    sous intervention uniforme (``EI = H(E|C) - <H(E|c)>``).
    """
    m = validate_tpm(tpm)
    n = m.shape[0]
    if n < 2:
        return 0.0
    return effectiveness(m) * np.log2(n)


def causal_profile(tpm) -> dict:
    """Profil causal complet d'une TPM (toutes les primitives de l'article)."""
    m = validate_tpm(tpm)
    n = int(m.shape[0])
    det = determinism(m)
    deg = degeneracy(m)
    eff = det - deg
    return {
        "n": n,
        "determinism": det,
        "degeneracy": deg,
        "specificity": 1.0 - deg,
        "effectiveness": eff,
        "effective_information": eff * np.log2(n) if n > 1 else 0.0,
    }


# --------------------------------------------------------------- coarse-graining
def initial_labels(n: int) -> list:
    """Etiquettes initiales : chaque macro-etat contient un seul micro-etat."""
    return [(k,) for k in range(n)]


def merge_labels(labels: list, i: int, j: int) -> list:
    """Met a jour les etiquettes apres fusion des positions ``i`` et ``j``.

    Le macro-etat resultant herite des deux ensembles de micro-etats ; il prend
    la position ``min(i, j)``, l'autre position est retiree.
    """
    a, b = sorted((i, j))
    new = list(labels)
    new[a] = tuple(sorted(set(new[a]) | set(new[b])))
    del new[b]
    return new


def merge_states(tpm, i: int, j: int) -> np.ndarray:
    """Fusionne les etats ``i`` et ``j`` en un macro-etat (coarse-graining).

    Construction canonique de l'emergence causale (Hoel 2013) sous intervention
    uniforme :

      1. fusion des COLONNES : la probabilite d'arriver dans le macro-etat est
         la SOMME des colonnes des deux micro-etats (arriver dans ``i`` OU dans
         ``j``) ;
      2. fusion des LIGNES : l'effet du macro-etat est la MOYENNE des lignes des
         deux micro-etats (l'intervention sur le macro tire uniformement parmi
         ses micro-constituants) ;
      3. renormalisation defensive des lignes.

    Retourne une TPM ``(n-1, n-1)``. Le macro-etat occupe la position
    ``min(i, j)``.
    """
    m = validate_tpm(tpm)
    n = m.shape[0]
    if not (0 <= i < n and 0 <= j < n) or i == j:
        raise ValueError(f"indices invalides pour fusion : i={i}, j={j}, n={n}")
    a, b = sorted((i, j))
    # 1) fusion des colonnes : P(arriver dans le macro) = P(->a) + P(->b)
    cols = m.copy()
    cols[:, a] = m[:, a] + m[:, b]
    cols = np.delete(cols, b, axis=1)
    # 2) fusion des lignes : effet du macro = moyenne des deux micro-effets
    cols[a] = 0.5 * (cols[a] + cols[b])
    macro = np.delete(cols, b, axis=0)
    # 3) renormalisation defensive (les lignes doivent deja sommer a 1)
    row_sums = macro.sum(axis=1, keepdims=True)
    row_sums[row_sums == 0] = 1.0
    return macro / row_sums


# --------------------------------------------------------------- apportionment glouton
def greedy_apportionment(tpm, primitive: Callable = effectiveness,
                         eps: float = 1e-9) -> dict:
    """Construit un chemin d'echelles micro -> macro par fusion gloutonne.

    A chaque pas, on essaie toutes les fusions de paires d'etats et l'on retient
    celle qui MAXIMISE la primitive causale (``effectiveness`` par defaut) a
    l'echelle plus grossiere. On enregistre la valeur de la primitive et le gain
    ``delta_cp`` par rapport a l'echelle precedente. On s'arrete des qu'aucune
    fusion n'ameliore la primitive (gain < ``eps``), ou qu'il ne reste qu'un
    etat.

    NB methodologique (honnete). L'article construit la trajectoire d'echelles
    valides de facon plus rigoureuse (recherche d'un point d'arrivee a gain
    total maximal, puis plus long chemin consistant). La variante GLOUTONNE
    implementee ici est la forme pratique usuelle ; elle ne garantit PAS
    l'optimalite globale du chemin. La primitive par defaut est l'effectiveness
    normalisee (la grandeur "scale-free" derriere les primitives causales de
    l'article), et non l'EI en bits qui, penalisee par ``log2(n)``, masque
    souvent l'emergence sous coarse-graining.

    Retourne un dict :
      - ``scales`` : liste de pas, chacun ``{size, value, determinism,
        specificity, effectiveness, effective_information, labels, merged,
        delta_cp}``. Le premier pas est la micro-echelle (``merged`` et
        ``delta_cp`` valent None) ;
      - ``deltas`` : liste des ``delta_cp`` positifs le long du chemin ;
      - ``emergent_complexity`` : EC calculee sur ``deltas`` (cf
        ``emergent_complexity``).
    """
    m = validate_tpm(tpm)
    n = m.shape[0]
    labels = initial_labels(n)

    def _step(matrix, merged, delta):
        prof = causal_profile(matrix)
        return {
            "size": prof["n"],
            "value": float(primitive(matrix)),
            "determinism": prof["determinism"],
            "specificity": prof["specificity"],
            "effectiveness": prof["effectiveness"],
            "effective_information": prof["effective_information"],
            "labels": list(labels),
            "merged": merged,
            "delta_cp": delta,
        }

    scales = [_step(m, None, None)]
    deltas: list = []
    cur = m
    cur_val = float(primitive(m))

    while cur.shape[0] > 1:
        sz = cur.shape[0]
        best = None  # (value, i, j, macro_tpm)
        for i in range(sz):
            for j in range(i + 1, sz):
                cand = merge_states(cur, i, j)
                val = float(primitive(cand))
                if best is None or val > best[0]:
                    best = (val, i, j, cand)
        val, i, j, cand = best
        delta = val - cur_val
        if delta < eps:
            break  # plus aucune fusion n'ameliore : on s'arrete (emergence epuisee)
        labels = merge_labels(labels, i, j)
        scales.append(_step(cand, (i, j), delta))
        deltas.append(delta)
        cur, cur_val = cand, val

    return {
        "scales": scales,
        "deltas": deltas,
        "emergent_complexity": emergent_complexity(deltas),
    }


# --------------------------------------------------------------- complexite emergente
def emergent_complexity(deltas) -> float:
    """Complexite emergente ``EC = log2(L) - sum_i p_i log2(p_i)`` (Hoel 2025).

    ``deltas`` = gains de primitive causale (``delta_cp`` positifs) le long du
    chemin d'echelles ; ``p_i = delta_i / sum(delta)`` est la contribution
    relative de chaque transition d'echelle, ``L`` le nombre de transitions.

    Equivaut a ``log2(L) + H(p)`` ou ``H(p)`` est l'entropie des contributions :
    EC est donc maximale quand le travail causal est *largement distribue* entre
    les echelles (cf l'abstract de Hoel 2025), et nulle si une seule echelle
    porte tout le gain (``L <= 1``).
    """
    d = np.asarray([float(x) for x in deltas if x > 0], dtype=float)
    L = int(d.size)
    if L <= 1:
        return 0.0
    p = d / d.sum()
    return float(np.log2(L) - np.sum(p * np.log2(p)))


# --------------------------------------------------------------- presentation
def apportionment_table(result: dict) -> list:
    """Reduit un resultat d'apportionment a un tableau lisible (pour notebook).

    Chaque ligne : ``(taille, effectiveness, EI_bits, det, spec, delta_cp)``,
    arrondie a 4 decimales. Utile pour un affichage tabulaire dans ICT-6/ICT-7.
    """
    rows = []
    for s in result["scales"]:
        rows.append((
            s["size"],
            round(s["effectiveness"], 4),
            round(s["effective_information"], 4),
            round(s["determinism"], 4),
            round(s["specificity"], 4),
            None if s["delta_cp"] is None else round(s["delta_cp"], 4),
        ))
    return rows
