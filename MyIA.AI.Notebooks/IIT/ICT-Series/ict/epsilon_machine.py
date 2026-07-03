"""epsilon-machine (Crutchfield computational mechanics) : etats causaux, complexite statistique C_mu, entropie d'exces E (ICT-17, strate 5 Epic #4588, See #5100).

ICT-15 (capstone) a pose que l'integration (Phi), la surprise (F) et la
compression (K) sont trois facettes d'un meme quantite -- *un systeme qui
modelise son monde*. ICT-16 (mdl.py) a attache la jambe K a la structure
INTERNE du modele (MDL deux parties). ICT-17 importe la **discipline** de
Crutchfield -- la *mecanique computationnelle* -- et ses trois objets exacts :

  - **etats causaux** : classes d'equivalence de passes a distribution
    conditionnelle de futurs identique. C'est LA reponse de Crutchfield a
    la question "quel est le bon macro-etat ?" : la partition causale est
    la plus grossiere qui preserve l'integrale du pouvoir predictif.
  - **C_mu (complexite statistique)** : entropie de la distribution
    stationnaire des etats causaux -- la quantite de "memoire" que le
    systeme doit conserver pour predire son futur.
  - **entropie d'exces E** : information mutuelle passe / futur -- c'est
    la borne superieure de ce que N'IMPORTE QUEL estimateur ``p_hat`` peut
    capturer, elle unifie les jambes F et K.

Cette **gate Crutchfield-vs-Hoel** (issue #5100) confronte deux reponses
rivales au meme probleme de coarse-graining : la partition en etats causaux
(Crutchfield) vs les macro-groupes du ``greedy_apportionment`` (Hoel 2.0,
cf ``ict.causal_emergence``). Accord sur les substrats fortement structures,
divergence ailleurs -- tout verdict est informatif, aucun n'est un echec.

Trois estimateurs, tous numpy-only, volontairement honnetes sur leurs bornes :

  - ``causal_state_partition`` : partition en etats causaux par fusion des
    passes de longueur ``history_len`` dont la distribution conditionnelle de
    futurs (longueur ``future_len``) est indistinguable a la distance L1 pres,
    a la tolerance ``tol`` pres. Renvoie une liste de groupes (tuples
    d'indices de passes canoniques) et un mapping passe canonique -> etat.
  - ``statistical_complexity`` : C_mu = entropie (log2) de la distribution
    stationnaire des etats causaux sur la trajectoire.
  - ``excess_entropy_estimate`` : E par convergence des entropies de bloc ;
    le plafond qu'aucun estimateur ``p_hat`` ne peut capturer.
  - ``partition_similarity`` : information de variation (VI) normalisee entre
    deux partitions -- mesure le "degre de desaccord" entre Crutchfield et Hoel.

Dependances : bibliotheque standard + numpy. Aucune dependance au package
``ict`` (import local a l'appelant) -- ce module est volontairement
autonome, comme ``causal_emergence`` et ``mdl``.
"""

from __future__ import annotations

from collections import defaultdict
from typing import Dict, List, Sequence, Tuple

import numpy as np


# --------------------------------------------------------------------------- #
#  Primitives : passes canoniques, futurs, distribution conditionnelle         #
# --------------------------------------------------------------------------- #


def _canon(history: Tuple) -> Tuple:
    """Canonise une passe : tuple d'etats en l'occurrence (deja hachable)."""
    return tuple(history)


def _build_histories(states: Sequence, history_len: int) -> List[Tuple]:
    """Construit la liste des passes de longueur ``history_len``.

    Une passe a l'indice ``t`` est ``states[t : t + history_len]`` (la
    fenetre observee, pas le futur). Pour ``history_len=1``, chaque passe
    est un etat isole (la partition triviale).
    """
    n = len(states)
    if history_len < 1:
        raise ValueError(f"history_len doit etre >= 1, recu {history_len}")
    if n < history_len:
        return []
    return [_canon(states[t : t + history_len]) for t in range(n - history_len + 1)]


def _future_distribution(states: Sequence, t: int, history_len: int,
                         future_len: int) -> np.ndarray:
    """Distribution conditionnelle des ``future_len`` prochains etats apres la passe ``t``.

    Renvoie un vecteur de probabilites sur les ``k**future_len`` futurs
    possibles (canonise en tuples de longueur ``future_len``). Si la
    trajectoire est trop courte pour le futur demande, on tronque
    silencieusement a la longueur disponible -- un futur observe est mieux
    que pas de futur du tout.

    Parametres :
      - ``states`` : sequence complete d'etats ;
      - ``t`` : indice du debut de la passe ;
      - ``history_len`` : longueur de la passe ;
      - ``future_len`` : longueur du futur observe.

    Retourne un vecteur numpy de probabilites sur les futurs vus (somme=1).
    La cle du mapping (futur canonique -> probabilite) est implicite dans
    l'ordre du vecteur ; l'appelant doit garder le meme mapping pour les
    comparaisons. Pour eviter ce piege, on utilise ``future_counts_dict``
    ci-dessous.
    """
    pass_start = t
    future_start = pass_start + history_len
    future_end = min(future_start + future_len, len(states))
    if future_start >= len(states):
        return np.zeros(0, dtype=float)
    future = tuple(states[future_start:future_end])
    # Future canonique dans la passe de longueur future_len : on tronque
    # si la trajectoire finit ; c'est OK pour la distance L1 (memes classes
    # d'evenement tronquees).
    return _dict_to_array({future: 1.0})


def _future_counts_dict(states: Sequence, t: int, history_len: int,
                        future_len: int) -> Dict[Tuple, int]:
    """Comptage des futurs observes apres la passe ``t`` de longueur ``history_len``.

    Dictionnaire ``futur canonique -> nombre d'occurrences``. Pour
    ``future_len = 0``, la cle est le tuple vide et la valeur est 1
    (chaque passe a 1 occurrence de "futur vide"). Pour ``future_len`` > 0
    et une trajectoire finissante, on tronque le futur a la longueur
    disponible ; ce n'est pas un probleme pour la partition causale, car
    toutes les passe a la meme position de fin voient le meme futur
    tronque.
    """
    future_start = t + history_len
    future_end = min(future_start + future_len, len(states))
    if future_start >= len(states):
        return {(): 1}  # futur vide : 1 occurrence
    future = _canon(states[future_start:future_end])
    return {future: 1}


def _merge_history_future(histories: List[Tuple], states: Sequence,
                          history_len: int, future_len: int
                          ) -> Dict[Tuple, Dict[Tuple, int]]:
    """Construit le mapping passe -> comptage des futurs associes.

    Une passe peut apparaitre plusieurs fois dans la trajectoire (meme
    bloc de ``history_len`` etats a des temps differents) ; le futur
    associe peut etre different (meme passe, futurs distincts -- la
    signature exacte du non-Markovianisme). Le retour est un dict
    imbrique : ``mapping[passe][futur] = nombre d'occurrences``.

    NB methodologique : pour ``future_len = 0``, le futur est le tuple vide
    et le mapping degenerera ; ce cas n'a pas de sens pour la partition
    causale (toutes les passes auraient le meme futur vide). On force
    ``future_len >= 1``.
    """
    if future_len < 1:
        raise ValueError(
            f"future_len doit etre >= 1 (sinon toutes les passes ont le "
            f"meme futur vide), recu {future_len}"
        )
    out: Dict[Tuple, Dict[Tuple, int]] = defaultdict(lambda: defaultdict(int))
    n = len(states)
    for t, hist in enumerate(histories):
        future_start = t + history_len
        future_end = min(future_start + future_len, n)
        if future_start >= n:
            future = ()
        else:
            future = _canon(states[future_start:future_end])
        out[hist][future] += 1
    # Convertit defaultdict en dict normal pour la serialisation.
    return {h: dict(fc) for h, fc in out.items()}


# --------------------------------------------------------------------------- #
#  Partition en etats causaux                                                  #
# --------------------------------------------------------------------------- #


def causal_state_partition(
    states: Sequence,
    history_len: int = 2,
    future_len: int = 2,
    tol: float = 0.05,
) -> dict:
    """Partition causale au sens de Crutchfield, fusion L1 + tolerance.

    Deux passes sont dans le meme etat causal ssi la distribution
    conditionnelle de leurs futurs (sur ``future_len`` pas) est
    indistinguable a la distance de variation totale (L1/2) pres ``tol``.
    On utilise L1/2 (demi-distance L1) pour rester dans [0, 1] -- c'est
    l'integrale standard entre deux distributions discretes.

    Algorithme (U-algorithme simplifie, Crutchfield & Young 1989) :

      1. Construire la table ``mapping[passe][futur] = count``.
      2. Initialiser : chaque passe est son propre etat causal (singleton).
      3. Tant que deux passes a distance L1/2 > tol peuvent etre fusionnees,
         les fusionner et mettre a jour la table agregee.

    Parametres :
      - ``states`` : sequence d'etats (labels hachables, comparable).
      - ``history_len`` : longueur de la passe (>= 1).
      - ``future_len`` : longueur du futur compare (>= 1 ; ``= history_len``
        est le defaut de la litterature).
      - ``tol`` : tolerance L1/2 en dessous de laquelle deux distributions
        sont declarees indistinguables. ``0.05`` = 5% de divergence maximale.

    Retourne ``{"labels": list[tuple[int]],
    "causal_to_histories": dict[int, list[tuple]],
    "history_to_causal": dict[tuple, int],
    "history_len": int, "future_len": int, "tol": float,
    "n_causal_states": int, "n_histories": int}``.

    Les ``labels`` sont des tuples d'indices de passes dans la liste
    ``histories``. ``causal_to_histories`` donne le contenu de chaque etat
    causal (``causal_state -> liste des passes qu'il contient``).
    """
    states = list(states)
    n = len(states)
    if n < history_len + future_len:
        raise ValueError(
            f"trajectoire trop courte pour history_len={history_len} + "
            f"future_len={future_len}, recu n={n}"
        )

    histories = _build_histories(states, history_len)
    n_hist = len(histories)
    if n_hist == 0:
        return {
            "labels": [], "causal_to_histories": {},
            "history_to_causal": {},
            "history_len": history_len, "future_len": future_len,
            "tol": tol, "n_causal_states": 0, "n_histories": 0,
        }

    table = _merge_history_future(histories, states, history_len, future_len)
    # Normalisation : chaque passe a une distribution de comptage des futurs.
    future_keys = sorted({f for fc in table.values() for f in fc})
    key_index = {f: i for i, f in enumerate(future_keys)}
    k_fut = len(future_keys)
    dists = np.zeros((n_hist, k_fut), dtype=float)
    for i, hist in enumerate(histories):
        for f, c in table[hist].items():
            dists[i, key_index[f]] = float(c)
        s = dists[i].sum()
        if s > 0:
            dists[i] /= s

    # -- U-algorithme : regrouper par distribution identique a tol pres
    # On part d'un dict ``signature de distribution -> liste d'indices``
    # puis onagrege les signatures dont la distance L1/2 <= tol.
    # Astuce : la L1 entre signatures est lineaire en la concatenation de
    # leurs vecteurs, donc une fermeture iterative par paires marche.

    # Etape 1 : clustering initial par egalite exacte.
    sig_groups: Dict[Tuple, List[int]] = {}
    for i in range(n_hist):
        # Clignotant numerique : arrondir a 1e-9
        sig = tuple(np.round(dists[i], 9))
        sig_groups.setdefault(sig, []).append(i)
    signatures = list(sig_groups.values())

    # Etape 2 : fusion iterative des paires a distance <= tol.
    # On travaille sur des "centroides" (moyenne des distributions des
    # signatures) pour accelerer, mais la verif se fait sur les distributions
    # reelles via min(distance). Pour rester honnete sur la complexite
    # (et parce que n_hist est petit en pratique), on teste toutes les paires.
    changed = True
    while changed:
        changed = False
        # Centroides par signature.
        centroids = np.array([np.mean([dists[i] for i in grp], axis=0)
                              for grp in signatures])
        m = len(signatures)
        # On cherche la paire la plus proche sous tol ; si on en trouve,
        # on fusionne.
        best = (None, None, float("inf"))
        for i in range(m):
            for j in range(i + 1, m):
                d = 0.5 * float(np.sum(np.abs(centroids[i] - centroids[j])))
                if d <= tol and d < best[2]:
                    best = (i, j, d)
        if best[0] is not None:
            i, j, _ = best
            signatures[i] = signatures[i] + signatures[j]
            del signatures[j]
            changed = True

    # -- Construction des labels
    # ``labels[c]`` = tuple d'INDICES d'occurrences de passes regroupees dans
    # l'etat causal ``c``. Le mapping ``occurrence_to_causal`` indexe chaque
    # occurrence (entier ``i in [0, n_hist)``) par son etat causal.
    #
    # NB C198-HARD : ne PAS indexer ``history_to_causal`` par le tuple
    # canonique de la passe -- plusieurs occurrences du meme bloc partage la
    # meme cle et s'ecrasent, perdant la trace individuelle (bug fondateur).
    # La cle est l'index d'occurrence ; on expose aussi ``canonical_to_causal``
    # alias par passe canonique pour les usages "semantiques" (un tuple
    # represente UN etat meme s'il apparait 100 fois -- bug miroir : si
    # plusieurs occurrences d'un meme tuple tombent dans des etats causaux
    # distincts apres fusion toleree, ``canonical_to_causal`` choisit le
    # premier vu, ce qui peut etre incoherent avec ``occurrence_to_causal``
    # sur les occurrences suivantes -- preferable a l'inverse mais le caller
    # prudent utilise ``occurrence_to_causal``).
    occurrence_to_causal: Dict[int, int] = {}
    canonical_to_causal: Dict[Tuple, int] = {}
    labels: List[Tuple[int, ...]] = []
    causal_to_histories: Dict[int, List[Tuple]] = {}
    for c, grp in enumerate(signatures):
        labels.append(tuple(sorted(grp)))
        causal_to_histories[c] = [histories[i] for i in grp]
        for i in grp:
            occurrence_to_causal[i] = c
            canonical_to_causal.setdefault(histories[i], c)

    return {
        "labels": labels,
        "causal_to_histories": causal_to_histories,
        "occurrence_to_causal": occurrence_to_causal,
        # Alias historique (semantique) -- conserve pour retrocompat.
        "history_to_causal": canonical_to_causal,
        "history_len": history_len,
        "future_len": future_len,
        "tol": tol,
        "n_causal_states": len(labels),
        "n_histories": n_hist,
    }


# --------------------------------------------------------------------------- #
#  Complexite statistique C_mu                                                #
# --------------------------------------------------------------------------- #


def statistical_complexity(partition: dict, states: Sequence) -> dict:
    """Complexite statistique ``C_mu`` (entropie de la distribution stationnaire des etats causaux).

    On parcourt la trajectoire, on regarde l'etat causal courant a chaque
    pas (l'etat de la passe qui finit a l'indice ``t``), et on accumule
    les frequences. ``C_mu = -sum p(s) log2 p(s)``.

    Parametres :
      - ``partition`` : dict renvoye par ``causal_state_partition``.
      - ``states`` : sequence d'etats (meme longueur que celle ayant servi
        a la partition, idealement ; sinon on tronque au minimum).

    Retourne ``{"C_mu": float, "stationary": dict[int, float],
    "n_used": int}`` -- ``stationary`` donne la distribution stationnaire
    estimee sur la trajectoire, ``n_used`` le nombre de pas utilises.
    """
    states = list(states)
    history_len = int(partition["history_len"])
    # Cle : index d'occurrence (entier), pas tuple canonique -- chaque
    # occurrence de la trajectoire est comptee, meme si elle partage le
    # meme tuple passe avec d'autres occurrences (cf C198-HARD).
    occ_to_c = partition["occurrence_to_causal"]
    n = len(states)
    n_occurrences = n - history_len + 1
    counts: Dict[int, int] = defaultdict(int)
    n_used = 0
    for i in range(n_occurrences):
        if i in occ_to_c:
            counts[occ_to_c[i]] += 1
            n_used += 1
    total = sum(counts.values())
    if total == 0:
        return {"C_mu": 0.0, "stationary": {}, "n_used": 0}
    stationary = {c: cnt / total for c, cnt in counts.items()}
    p = np.array(list(stationary.values()), dtype=float)
    H = float(-np.sum(p * np.log2(p))) if p.size > 0 else 0.0
    return {"C_mu": H, "stationary": stationary, "n_used": int(n_used)}


# --------------------------------------------------------------------------- #
#  Entropie d'exces E                                                         #
# --------------------------------------------------------------------------- #


def _entropy_from_counts(counts: Sequence) -> float:
    """Entropie de Shannon (log2) d'une distribution de comptages."""
    arr = np.asarray(counts, dtype=float).ravel()
    total = float(arr.sum())
    if total <= 0:
        return 0.0
    p = arr[arr > 0] / total
    return float(-np.sum(p * np.log2(p)))


def _ngrams(seq: Sequence, k: int) -> Dict[Tuple, int]:
    """Denombre les ``k``-grammes consecutifs dans ``seq``."""
    if k < 1 or k > len(seq):
        return {}
    out: Dict[Tuple, int] = {}
    for i in range(len(seq) - k + 1):
        gram = _canon(seq[i : i + k])
        out[gram] = out.get(gram, 0) + 1
    return out


def excess_entropy_estimate(
    states: Sequence, max_block: int = 8, forward: bool = True
) -> dict:
    """Estimation de l'entropie d'exces ``E`` par convergence des entropies de bloc.

    Definition : ``E = lim_{k -> inf} [H(X_{t+k}) - H(X_{t+k} | X_{<t})]``
    ou, sous forme equivalente pratique,
    ``E = lim_{k -> inf} [H(X_0^k) - H(X_0^k | X_{-k}^0)]``
    (qui est la limite des ``H(X_0^k) - H(X_0^k | passe de longueur k)``).
    On l'estime numeriquement par la convergence des ``H(bloc=k)`` -- la
    borne de Shannon : ``H(X_0^k)/k -> h_mu`` (le taux reel) tandis que
    ``H(X_0^k) - h_mu*k -> E``. Pour un calcul exact en pratique, on
    utilise directement les entropies de bloc : ``E_k = H(k) - H(k | passe)``
    pour le backward, ou ``E_k = H(k) - H(k | futur de meme longueur)``
    pour le forward.

    Ici on implemente la version **forward** (``forward=True``) ou
    **backward** (``forward=False``) symetrique, par moyenne des estimateurs
    ``E_k = H(X_0^k) - H(X_k^{2k}) + H(X_k^{2k} | X_0^k)`` -- simplifie
    en ``E_k = H(X_0^k) + H(X_k^{2k}) - H(X_0^{2k})`` (mesure d'information
    mutuelle chainee). Pour traçabilite on retourne la suite ``E_k`` par k
    de 1 a ``max_block``.

    Parametres :
      - ``states`` : sequence d'etats ;
      - ``max_block`` : taille max du bloc pour l'estimation (defaut 8).
      - ``forward`` : sens de la decomposition (forward ou backward) ;
        symetriques en regime stationnaire.

    Retourne ``{"E_estimate": float, "E_series": list[(int, float)],
    "converged": bool}``. L'estimation finale est la moyenne des 3
    derniers ``E_k``, qui est le plus stable en pratique.
    """
    seq = list(states)
    n = len(seq)
    if n < max_block * 2 + 1:
        raise ValueError(
            f"il faut au moins {max_block * 2 + 1} etats pour "
            f"max_block={max_block}, recu n={n}"
        )

    series: List[Tuple[int, float]] = []
    for k in range(1, max_block + 1):
        # Bloc gauche : X_0^k ; bloc droit : X_k^{2k} ; bloc complet : X_0^{2k}.
        left = _ngrams(seq, k)
        right = _ngrams(seq[k:], k)
        full = _ngrams(seq, 2 * k)
        # ``E_k ~ H(X_0^k) + H(X_k^{2k}) - H(X_0^{2k})``
        # C'est l'info mutuelle entre passe et futur de meme longueur.
        H_left = _entropy_from_counts(list(left.values()))
        H_right = _entropy_from_counts(list(right.values()))
        H_full = _entropy_from_counts(list(full.values()))
        # Plancher a 0 : la MI est toujours >= 0.
        E_k = max(0.0, H_left + H_right - H_full)
        series.append((k, E_k))

    # Estimation finale : moyenne des 3 derniers E_k (le plus stable).
    tail = [e for _, e in series[-3:]]
    E_est = float(np.mean(tail)) if tail else 0.0
    # ``converged`` : la serie est-elle stable sur les 3 derniers ?
    converged = len(tail) >= 2 and (max(tail) - min(tail)) < 0.5

    return {
        "E_estimate": E_est,
        "E_series": series,
        "converged": bool(converged),
    }


# --------------------------------------------------------------------------- #
#  Similarite entre partitions (information de variation)                     #
# --------------------------------------------------------------------------- #


def partition_similarity(
    partition_a: dict,
    partition_b: dict,
    states: Sequence,
) -> dict:
    """Similarite entre deux partitions (Crutchfield vs Hoel) par information de variation.

    L'information de variation (VI, Meila 2003) entre deux partitions
    ``U`` et ``V`` d'un meme ensemble de ``N`` points vaut
    ``VI(U, V) = H(U) + H(V) - 2 I(U, V)`` ou ``H(U)`` est l'entropie de
    la partition U vue comme distribution discrete, et ``I(U, V)`` est
    l'information mutuelle entre U et V.

    On l'evalue sur les **passes canoniques** communes aux deux
    partitions : chaque passe observee dans la trajectoire est codee par
    son etat dans chaque partition, et on compare les deux codages. Pour
    rendre VI independante du nombre de passes, on normalise par
    ``H(U) + H(V)`` (le max) : VI_norm dans ``[0, 1]``. 0 = accord
    parfait, 1 = desaccord total (les partitions sont independantes au
    sens de l'info mutuelle).

    NB methodologique : VI n'est PAS une distance metrique (pas
    inegalite triangulaire). On l'utilise comme **mesure de divergence**
    entre partitions, pas comme une metrique stricte.

    Parametres :
      - ``partition_a``, ``partition_b`` : dicts renvoyes par
        ``causal_state_partition`` (meme ``history_len`` recommande).
      - ``states`` : sequence d'etats (meme longueur pour les deux
        partitions).

    Retourne ``{"VI_norm": float, "VI_raw": float, "n_used": int,
    "agree": int, "disagree": int}``.
    """
    states = list(states)
    history_len = int(partition_a["history_len"])
    if int(partition_b["history_len"]) != history_len:
        raise ValueError(
            f"history_len divergent : {partition_a['history_len']} vs "
            f"{partition_b['history_len']}"
        )
    # C198-HARD : preferer le mapping par index d'occurrence (cle entiere)
    # qui preserve l'individualite de chaque occurrence dans la trajectoire.
    # ``occurrence_to_causal`` est indexee par l'index ``t`` de la passe ;
    # ``history_to_causal`` (alias canonique) est indexee par le tuple
    # canonique -- quand plusieurs occurrences partagent la meme passe,
    # le mapping canonique ne peut pas distinguer leurs assignations.
    occ_to_a = partition_a.get("occurrence_to_causal", {})
    occ_to_b = partition_b.get("occurrence_to_causal", {})
    h_to_a = partition_a.get("history_to_causal", {})
    h_to_b = partition_b.get("history_to_causal", {})
    n = len(states)

    # Comptage des paires (causal_a, causal_b) sur les pas ou les deux
    # partitions ont une passe connue.
    pair_counts: Dict[Tuple[int, int], int] = defaultdict(int)
    counts_a: Dict[int, int] = defaultdict(int)
    counts_b: Dict[int, int] = defaultdict(int)
    n_used = 0
    n_occ = n - history_len + 1
    for t in range(n_occ):
        # Si les deux partitions exposent un mapping par occurrence,
        # c'est l'information la plus fine ; sinon on fallback sur la
        # cle canonique (alias ``history_to_causal``).
        if occ_to_a and occ_to_b and t in occ_to_a and t in occ_to_b:
            ca, cb = occ_to_a[t], occ_to_b[t]
        else:
            hist = _canon(states[t : t + history_len])
            if hist not in h_to_a or hist not in h_to_b:
                continue
            ca, cb = h_to_a[hist], h_to_b[hist]
        pair_counts[(ca, cb)] += 1
        counts_a[ca] += 1
        counts_b[cb] += 1
        n_used += 1
    total = sum(counts_a.values())
    if total == 0:
        return {"VI_norm": 0.0, "VI_raw": 0.0, "n_used": 0,
                "agree": 0, "disagree": 0}

    # H(U) + H(V)
    H_a = _entropy_from_counts(list(counts_a.values()))
    H_b = _entropy_from_counts(list(counts_b.values()))
    # I(U, V) = sum p(u,v) log2 p(u,v) / (p(u) p(v))
    p_uv = np.array([c for c in pair_counts.values()], dtype=float) / total
    p_u = np.array([counts_a[ca] for ca, _ in pair_counts], dtype=float) / total
    p_v = np.array([counts_b[cb] for _, cb in pair_counts], dtype=float) / total
    I_uv = float(np.sum(p_uv * np.log2(p_uv / (p_u * p_v + 1e-300))))
    VI_raw = H_a + H_b - 2 * I_uv
    denom = H_a + H_b
    VI_norm = VI_raw / denom if denom > 0 else 0.0

    agree = sum(c for (ca, cb), c in pair_counts.items() if ca == cb)
    disagree = total - agree
    return {
        "VI_norm": float(VI_norm),
        "VI_raw": float(VI_raw),
        "n_used": int(n_used),
        "agree": int(agree),
        "disagree": int(disagree),
    }
