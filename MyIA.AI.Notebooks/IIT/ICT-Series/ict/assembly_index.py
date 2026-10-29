"""L'assembly index exact sur les chaines (case 20, veille #8182).

Banc pre-enregistre : ``docs/ict/assembly-theory-pre-enregistrement.md`` (scelle
par le commit parent -- la relation de parente des commits porte l'anteriorite).
Source primaire : Sharma et al., *Nature* 622:321 (2023). Contre-claim :
Abrahao et al., *PLOS Complex Systems* 1(1):e0000014 (2024, arXiv:2403.06629v6).

Le modele (scelle, section 4 du pre-enregistrement) : l'assembly index d'une
chaine ``x`` est le nombre minimal de jointures pour produire ``x`` a partir des
caracteres le prenant pour alphabet, ou **les objets formes retournent au pool
et peuvent resservir** (Sharma et al., p. 322). Le pool est un ensemble d'objets
**distingues par leur contenu** : construire une fois ``"01"`` le rend
disponible partout ou cette chaine sert -- une lecture par positions
surestimerait (deux occurrences du meme contenu ne se construisent qu'une fois).

Deux solveurs independants, pour la porte G1 :

- :func:`exact_ai` -- recherche iterative (IDA*) sur des etats ``frozenset`` de
  pieces (indices de bits), enumeration des jointures par masques de suiveurs,
  borne de doublement ``ai >= ceil(log2 n)``, memo des echecs par (pool, reste).
- :func:`brute_force_ai` -- seconde implementation : etats **multiensemble**
  (la multiplicite est permise, jamais dedupliquee), enumeration par double
  boucle sur toutes les paires, profondeur croissante depuis 0, memo propre.
  Sert de temoin croise : un desaccord sur une seule chaine declare
  l'instrument NON_CONCLUSIF.

Proxys LZ (definitions scellees) : :func:`zlib_len` (zlib niveau 9),
:func:`lz76_count` (factorisation de Lempel-Ziv 1976 : phrase = plus longue
amorce reproductible depuis l'historique, augmentee d'un caractere),
:func:`lz78_count` (dictionnaire Lempel-Ziv 1978). Entropies : :func:`h0`,
:func:`h_block`.

Tout est deterministe. Dependances : bibliotheque standard + numpy (ajustements
log-log et Spearman). ``z3`` n'est PAS une dependance du module -- la
corroboration z3 du pre-enregistrement est un script de mesure local, hors CI.
"""

from __future__ import annotations

import math
import zlib
from typing import Dict, List, Optional, Sequence, Tuple

import numpy as np


# --------------------------------------------------------------------------- #
#  petites briques
# --------------------------------------------------------------------------- #


def ceil_log2(n: int) -> int:
    """``ceil(log2 n)`` entier, sans flottant (n >= 1)."""
    if n <= 1:
        return 0
    return (n - 1).bit_length()


def h0(x: str) -> float:
    """Entropie de Shannon (bits) de la distribution des symboles de ``x``."""
    if not x:
        return 0.0
    counts: Dict[str, int] = {}
    for ch in x:
        counts[ch] = counts.get(ch, 0) + 1
    n = len(x)
    return float(-sum((c / n) * math.log2(c / n) for c in counts.values()))


def h_block(x: str, k: int = 2) -> float:
    """Entropie de Shannon (bits par symbole) de la distribution des blocs de
    longueur ``k`` (blocs comptes par fenetre glissante)."""
    if len(x) < k:
        return 0.0
    counts: Dict[str, int] = {}
    for i in range(len(x) - k + 1):
        b = x[i : i + k]
        counts[b] = counts.get(b, 0) + 1
    total = len(x) - k + 1
    ent = -sum((c / total) * math.log2(c / total) for c in counts.values())
    return float(ent / k)


# --------------------------------------------------------------------------- #
#  proxys LZ (definitions scellees)
# --------------------------------------------------------------------------- #


def zlib_len(x: str, level: int = 9) -> int:
    """Longueur en octets de ``zlib.compress(x.encode(), level)``."""
    return len(zlib.compress(x.encode("ascii"), level))


def lz76_count(x: str) -> int:
    """Complexite de Lempel-Ziv 1976 : nombre de phrases.

    La phrase courante est la plus courte amorce du reste **non reproductible**
    depuis l'historique (i.e. n'apparaissant pas dans ``x[:i]``) ; si toutes les
    amorces sont reproductibles (fin de chaine periodique), la phrase est le
    reste. Le predicat de reproductibilite est monotone en la longueur
    (tronquer une occurrence reste une occurrence), donc la longueur de phrase
    se cherche par dichotomie.
    """
    n = len(x)
    if n == 0:
        return 0
    count = 0
    i = 0
    while i < n:
        # plus longue amorce reproductible depuis x[:i]
        lo, hi = 0, n - i
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if x.find(x[i : i + mid], 0, i) != -1:
                lo = mid
            else:
                hi = mid - 1
        if lo >= n - i:
            # le reste entier est reproductible : la phrase est le reste
            count += 1
            break
        i += lo + 1
        count += 1
    return count


def lz78_count(x: str) -> int:
    """Complexite de Lempel-Ziv 1978 : nombre de phrases du dictionnaire.

    A chaque pas, on prolonge le plus long mot du dictionnaire prefixant le
    reste par le symbole suivant ; la phrase (mot + symbole) entre au
    dictionnaire. Une phrase ne se prolonge jamais par un mot entier deja vu
    (le dictionnaire n'ajoute qu'un mot par phrase), donc la recherche lineaire
    du plus long prefixe est O(phrase).
    """
    n = len(x)
    if n == 0:
        return 0
    dictionnaire = {""}
    count = 0
    i = 0
    while i < n:
        L = 0
        while i + L + 1 <= n and x[i : i + L + 1] in dictionnaire:
            L += 1
        # la phrase x[i:i+L+1] est nouvelle (ou la derniere, si la prolongation
        # depasse la chaine : on prend alors le reste)
        if i + L + 1 <= n:
            dictionnaire.add(x[i : i + L + 1])
            i += L + 1
        else:
            i += L
        count += 1
    return count


# --------------------------------------------------------------------------- #
#  corpus (familles et classes scellees)
# --------------------------------------------------------------------------- #


def periodic(n: int) -> str:
    """``(01)^k`` tronque a ``n`` : "0101..."."""
    return ("01" * ((n + 1) // 2))[:n]


def fibonacci_string(j: int) -> str:
    """Mot de Fibonacci ``f_j`` : f_1 = "0", f_2 = "01", f_j = f_{j-1} f_{j-2}."""
    if j < 1:
        raise ValueError("j >= 1 requis")
    a, b = "0", "01"
    if j == 1:
        return a
    for _ in range(2, j):
        a, b = b, b + a
    return b


def thue_morse(j: int) -> str:
    """Thue-Morse ``tau_j`` : tau_0 = "0", tau_j = tau_{j-1} + complement."""
    t = "0"
    for _ in range(j):
        t = t + "".join("1" if c == "0" else "0" for c in t)
    return t


def half_ones(n: int, ones: int, seed: int) -> str:
    """Chaine de longueur ``n`` avec exactement ``ones`` symboles "1".

    Tirage deterministe (``np.random.default_rng(seed)``) : les positions des
    "1" sont un echantillon sans remise de ``ones`` positions parmi ``n``.
    """
    rng = np.random.default_rng(seed)
    pos = np.zeros(n, dtype=np.int8)
    pos[rng.choice(n, size=ones, replace=False)] = 1
    return "".join("1" if v else "0" for v in pos)


def zero_one_block(m: int) -> str:
    """``0^m 1^m`` (le membre a deux blocs de la classe a comptes fixes)."""
    return "0" * m + "1" * m


# --------------------------------------------------------------------------- #
#  solveur exact (modele ensemble de pieces, contenu)
# --------------------------------------------------------------------------- #


class _Universe:
    """Univers de pieces d'une chaine : sous-chaines distinctes + caracteres.

    ``free_mask`` : les caracteres (pieces de longueur 1) sont toujours
    disponibles, sans cout. ``comp[a][b]`` : indice de ``a+b`` s'il est
    lui-meme une sous-chaine de ``x`` (sinon -1) -- une piece qui n'est pas une
    sous-chaine de ``x`` ne peut appartenir a aucune derivation de ``x``.
    """

    def __init__(self, x: str) -> None:
        self.x = x
        self.n = len(x)
        substrings = {
            x[i:j] for i in range(self.n) for j in range(i + 1, self.n + 1)
        }
        self.pieces: List[str] = sorted(substrings)
        self.index: Dict[str, int] = {p: k for k, p in enumerate(self.pieces)}
        self.npcs = len(self.pieces)
        self.free_mask = 0
        self.freq: List[int] = []
        for k, p in enumerate(self.pieces):
            if len(p) == 1:
                self.free_mask |= 1 << k
            self.freq.append(x.count(p))
        # table de composition et masques de suiveurs
        self.comp: List[List[int]] = [
            [-1] * self.npcs for _ in range(self.npcs)
        ]
        self.follow: List[int] = [0] * self.npcs
        for a in range(self.npcs):
            pa = self.pieces[a]
            row = self.comp[a]
            mask = 0
            for b in range(self.npcs):
                c = self.index.get(pa + self.pieces[b])
                if c is not None:
                    row[b] = c
                    mask |= 1 << b
            self.follow[a] = mask
        self.x_bit = 1 << self.index[x] if self.n >= 1 else 0


def _bit_indices(mask: int):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def _candidates(uni: _Universe, pool: int) -> List[int]:
    """Bits des pieces joignables en une jointure depuis ``pool`` (non dedupe)."""
    avail = pool | uni.free_mask
    out: List[int] = []
    for a in _bit_indices(avail):
        partners = uni.follow[a] & avail
        if not partners:
            continue
        row = uni.comp[a]
        for b in _bit_indices(partners):
            c = row[b]
            if c >= 0 and not (pool >> c) & 1:
                out.append(c)
    return out


def exact_ai(
    x: str,
    state_budget: int = 2_000_000,
    ub_cap: Optional[int] = None,
) -> dict:
    """Assembly index exact de ``x`` (solveur principal, porte G1).

    Recherche iterative : pour chaque cout ``k`` depuis ``ceil(log2 n)``
    (borne de doublement) jusqu'a la borne superieure gloutonne, un DFS avec
    memoire des echecs ``(pool, reste)``. La premiere profondeur ou une
    solution est trouvee EST l'optimum. Budget d'etats declare : au-dela,
    ``reach_exceeded = True`` et ``ai = None`` -- jamais d'approximation
    silencieuse (porte G3).

    Retourne ``ai``, ``lb``, ``ub`` (glouton), ``states``, ``reach_exceeded``
    et ``witness`` (les pieces construites dans l'ordre, si trouve).
    """
    n = len(x)
    lb = ceil_log2(n)
    if n <= 1:
        return {
            "ai": 0, "lb": 0, "ub": 0, "states": 0,
            "reach_exceeded": False, "witness": [],
        }
    uni = _Universe(x)
    ub = _greedy_ub(uni)
    if ub_cap is not None:
        ub = min(ub, ub_cap)
    states = 0
    memo: Dict[int, int] = {}

    def dfs(pool: int, cost: int, k: int, maxlen: int,
            path: List[int]) -> Optional[List[int]]:
        nonlocal states
        if pool & uni.x_bit:
            return list(path)
        remaining = k - cost
        if maxlen << remaining < n:
            return None  # borne de doublement : ne peut plus atteindre n
        prev = memo.get(pool)
        if prev is not None and prev >= remaining:
            return None
        states += 1
        if states > state_budget:
            raise _ReachExceeded
        cands = _candidates(uni, pool)
        if not cands:
            memo[pool] = remaining
            return None
        # les pieces longues d'abord : trouve vite quand une solution existe
        cands = sorted(set(cands), key=lambda c: -len(uni.pieces[c]))
        for c in cands:
            got = dfs(pool | (1 << c), cost + 1, k,
                      max(maxlen, len(uni.pieces[c])), path + [c])
            if got is not None:
                return got
        memo[pool] = remaining
        return None

    try:
        for k in range(lb, ub + 1):
            got = dfs(uni.free_mask, 0, k, 1, [])
            if got is not None:
                return {
                    "ai": k, "lb": lb, "ub": ub, "states": states,
                    "reach_exceeded": False,
                    "witness": [uni.pieces[c] for c in got],
                }
    except _ReachExceeded:
        return {
            "ai": None, "lb": lb, "ub": ub, "states": states,
            "reach_exceeded": True, "witness": [],
        }
    # inatteignable en pratique : la route gloutonne est une derivation valide
    return {
        "ai": ub, "lb": lb, "ub": ub, "states": states,
        "reach_exceeded": False,
        "witness": _greedy_path(uni),
    }


class _ReachExceeded(Exception):
    pass


def _greedy_ub(uni: _Universe) -> int:
    """Borne superieure gloutonne : a chaque pas, la jointure qui produit la
    piece la plus longue (departage par la frequence dans x)."""
    pool = uni.free_mask
    maxlen = 1
    cost = 0
    while not pool & uni.x_bit:
        cands = set(_candidates(uni, pool))
        if not cands:
            raise RuntimeError("aucune jointure possible -- univers incoherent")
        best = max(
            cands, key=lambda c: (len(uni.pieces[c]), uni.freq[c])
        )
        pool |= 1 << best
        maxlen = max(maxlen, len(uni.pieces[best]))
        cost += 1
        if cost > uni.n:
            raise RuntimeError("borne gloutonne absurde (> n)")
    return cost


def _greedy_path(uni: _Universe) -> List[str]:
    pool = uni.free_mask
    out: List[str] = []
    while not pool & uni.x_bit:
        cands = set(_candidates(uni, pool))
        best = max(cands, key=lambda c: (len(uni.pieces[c]), uni.freq[c]))
        pool |= 1 << best
        out.append(uni.pieces[best])
    return out


# --------------------------------------------------------------------------- #
#  second solveur independant (multiensemble, enumerate exhaustif)
# --------------------------------------------------------------------------- #


def brute_force_ai(x: str, state_budget: int = 2_000_000) -> dict:
    """Assembly index par enumeration exhaustive sur des **multiplicites**.

    Espace d'etats volontairement different : un multiensemble de pieces (la
    repetition est permise et jamais dedupliquee), enumere par double boucle sur
    toutes les paires disponibles, profondeur croissante depuis 0, memoire
    propre. Ne partage ni les masques, ni la memoire, ni l'ordre
    d'exploration du solveur principal. Les pieces produites restent des
    sous-chaines de ``x`` (une piece hors de ``x`` ne peut appartenir a aucune
    derivation de ``x`` -- meme argument que pour le solveur principal).
    """
    n = len(x)
    if n <= 1:
        return {"ai": 0, "states": 0, "reach_exceeded": False}
    substring_set = {
        x[i:j] for i in range(n) for j in range(i + 1, n + 1)
    }
    chars = tuple(sorted(set(x)))  # toujours disponibles, en copies illimitees
    states = 0

    for k in range(0, n):
        memo: set = set()

        def dfs(state: Tuple[str, ...], left: int) -> bool:
            """Etat = multiensemble trie de pieces (multiplicite permise)."""
            nonlocal states
            if x in state:
                return True
            if left == 0:
                return False
            maxlen = max((len(p) for p in state), default=1)
            if maxlen << left < n:
                return False
            key = (state, left)
            if key in memo:
                return False
            states += 1
            if states > state_budget:
                raise _ReachExceeded
            avail = state + chars
            for a in avail:
                for b in avail:
                    r = a + b
                    if r in substring_set:
                        if dfs(tuple(sorted(state + (r,))), left - 1):
                            return True
            memo.add(key)
            return False

        try:
            if dfs((), k):
                return {"ai": k, "states": states, "reach_exceeded": False}
        except _ReachExceeded:
            return {"ai": None, "states": states, "reach_exceeded": True}
    return {"ai": None, "states": states, "reach_exceeded": True}


# --------------------------------------------------------------------------- #
#  ajustements et correlations (mesures du banc)
# --------------------------------------------------------------------------- #


def loglog_fit(xs: Sequence[float], ys: Sequence[float]) -> dict:
    """Ajustement lineaire de ``log(y)`` sur ``log(x)`` (pente, ordonnee, R2).

    Une serie constante a une pente 0 et un R2 conventionnel de 1.0 (variance
    nulle : l'ajustement est exact), ce qui est le cas du zlib constant
    attendu sur l'echelle periodique.
    """
    xs = np.asarray(xs, dtype=float)
    ys = np.asarray(ys, dtype=float)
    lx = np.log(xs)
    ly = np.log(ys)
    slope, intercept = np.polyfit(lx, ly, 1)
    resid = ly - (slope * lx + intercept)
    ss_tot = float(np.sum((ly - ly.mean()) ** 2))
    if ss_tot == 0.0:
        r2 = 1.0
    else:
        r2 = float(1.0 - np.sum(resid ** 2) / ss_tot)
    return {
        "slope": float(slope),
        "intercept": float(intercept),
        "r2": r2,
    }


def _ranks(v: Sequence[float]) -> np.ndarray:
    v = np.asarray(v, dtype=float)
    order = np.argsort(v, kind="mergesort")
    ranks = np.empty(len(v), dtype=float)
    sv = v[order]
    i = 0
    while i < len(v):
        j = i
        while j + 1 < len(v) and sv[j + 1] == sv[i]:
            j += 1
        ranks[order[i : j + 1]] = (i + j) / 2.0 + 1.0
        i = j + 1
    return ranks


def spearman(a: Sequence[float], b: Sequence[float]) -> float:
    """Rho de Spearman (rangs moyens en cas d'ex aequo)."""
    ra, rb = _ranks(a), _ranks(b)
    ra = ra - ra.mean()
    rb = rb - rb.mean()
    denom = math.sqrt(float((ra ** 2).sum()) * float((rb ** 2).sum()))
    if denom == 0.0:
        return 0.0
    return float((ra * rb).sum() / denom)


# --------------------------------------------------------------------------- #
#  le banc : corpus scelles, portes, verdicts (sections 4-5 du pre-enregistrement)
# --------------------------------------------------------------------------- #

SEEDS = (0, 1, 7, 42, 99)

VERDICT_CONFIRMEE = "CONFIRMÉE"
VERDICT_FALSIFIEE = "FALSIFIÉE"
VERDICT_PARTIELLE = "PARTIELLE"
VERDICT_NON_CONCLUSIF = "NON_CONCLUSIF_INSTRUMENT"


def corpus_h1() -> Dict[str, List[Tuple[str, str]]]:
    """Les deux classes a comptes fixes de H1 (h0 = 1.000 bit exactement)."""
    classes: Dict[str, List[Tuple[str, str]]] = {}
    for n, ones in ((12, 6), (16, 8)):
        name = f"n={n} ({ones} uns)"
        members: List[Tuple[str, str]] = [
            (f"(01)^{n // 2}", periodic(n)),
            (f"0^{n // 2} 1^{n // 2}", zero_one_block(n // 2)),
        ]
        members += [
            (f"aleatoire s{seed}", half_ones(n, ones, seed)) for seed in SEEDS
        ]
        classes[name] = members
    return classes


def corpus_ladders() -> Dict[str, List[dict]]:
    """Les trois echelles de H2, avec bornes certifiees par construction.

    L'enveloppe est ``[ceil(log2 n), UB construit]`` : pour la famille
    periodique la construction de doublement et la borne inferieure coincident
    (``ai = log2 n`` exactement, certifie des deux cotes) ; pour Fibonacci et
    Thue-Morse, la construction par morphisme donne un UB
    (``j-1`` pour ``f_j`` ; ``2j-1`` pour ``tau_j``, qui exige d'entretenir
    aussi le complement) superieur a la borne de doublement.
    """
    familles: Dict[str, List[dict]] = {"P": [], "F": [], "TM": []}
    for j in range(5, 15):
        n = 2 ** j
        familles["P"].append({
            "label": f"P n=2^{j}", "x": periodic(n),
            "lb_cert": j, "ub_cert": j, "certified": True,
        })
    for j in range(12, 22):
        s = fibonacci_string(j)
        familles["F"].append({
            "label": f"F f_{j}", "x": s,
            "lb_cert": ceil_log2(len(s)), "ub_cert": j - 1, "certified": False,
        })
    for j in range(6, 16):
        s = thue_morse(j)
        familles["TM"].append({
            "label": f"TM tau_{j}", "x": s,
            "lb_cert": ceil_log2(len(s)), "ub_cert": 2 * j - 1, "certified": False,
        })
    return familles


def corpus_mixed() -> List[Tuple[str, str]]:
    """La batterie mixte de H3 (objets a ai exactement calculable)."""
    items: List[Tuple[str, str]] = []
    for n in range(2, 21, 2):
        items.append((f"periodique n={n}", periodic(n)))
    for j in (3, 4, 5, 6):
        items.append((f"fibonacci f_{j}", fibonacci_string(j)))
    for j in (1, 2, 3, 4):
        items.append((f"thue-morse tau_{j}", thue_morse(j)))
    for m in range(1, 11):
        items.append((f"0^{m} 1^{m}", zero_one_block(m)))
    for members in corpus_h1().values():
        items.extend(members)
    items.append(("ABRACADABRA", "ABRACADABRA"))
    items.append(("BANANA", "BANANA"))
    return items


def validate_witness(x: str, witness: Sequence[str]) -> bool:
    """Rejoue un temoin : chaque piece se joint a deux pieces deja au pool.

    Le pool initial est l'alphabet de ``x`` (copies illimitees). Verifie aussi
    que la derniere piece construite est exactement ``x``.
    """
    pool = set(x)
    for piece in witness:
        if not any(
            piece[:i] in pool and piece[i:] in pool for i in range(1, len(piece))
        ):
            return False
        pool.add(piece)
    return x in pool


def measure_object(x: str, label: str = "", budget: int = 2_000_000) -> dict:
    """Mesure complete d'un objet : solveur exact + proxys LZ + entropies."""
    res = exact_ai(x, state_budget=budget)
    return {
        "label": label or x,
        "n": len(x),
        "ai": res["ai"],
        "lb_doublement": res["lb"],
        "ub_glouton": res["ub"],
        "states": res["states"],
        "reach_exceeded": res["reach_exceeded"],
        "temoin_valide": (
            validate_witness(x, res["witness"]) if res["ai"] is not None else None
        ),
        "zlib": zlib_len(x),
        "lz76": lz76_count(x),
        "lz78": lz78_count(x),
        "h0": h0(x),
        "h_block2": h_block(x, 2),
    }


def g1_gate(
    n_max: int = 10, n_samples: int = 200, budget: int = 2_000_000
) -> dict:
    """Porte G1 : accord des deux solveurs sur tout le petit espace + tirage.

    Toutes les chaines binaires de ``n <= n_max`` (2 046 chaines pour 10), plus
    ``n_samples`` chaines tirees a ``n in {11, 12}`` (une seule graine de
    tirage : ``default_rng(0)``, indices 0..n_samples-1). Tout desaccord est
    rapporte (liste bornee a 20 entrees).
    """
    import itertools

    mismatches: List[dict] = []
    checked = 0
    for n in range(1, n_max + 1):
        for bits in itertools.product("01", repeat=n):
            s = "".join(bits)
            a = exact_ai(s, state_budget=budget)
            b = brute_force_ai(s, state_budget=budget)
            checked += 1
            if a["ai"] != b["ai"] or a["reach_exceeded"] or b["reach_exceeded"]:
                if len(mismatches) < 20:
                    mismatches.append({
                        "x": s, "exact_ai": a["ai"], "brute_force_ai": b["ai"],
                        "reach_exact": a["reach_exceeded"],
                        "reach_brute": b["reach_exceeded"],
                    })
    for k in range(n_samples):
        n = 11 + (k % 2)
        s = half_ones(n, n // 2, k)
        a = exact_ai(s, state_budget=budget)
        b = brute_force_ai(s, state_budget=budget)
        checked += 1
        if a["ai"] != b["ai"] or a["reach_exceeded"] or b["reach_exceeded"]:
            if len(mismatches) < 20:
                mismatches.append({
                    "x": s, "exact_ai": a["ai"], "brute_force_ai": b["ai"],
                    "reach_exact": a["reach_exceeded"],
                    "reach_brute": b["reach_exceeded"],
                })
    return {
        "checked": checked,
        "n_max": n_max,
        "n_samples": n_samples,
        "mismatches": mismatches,
        "passed": not mismatches,
    }


def _ladder_rows(familles: Dict[str, List[dict]], budget: int) -> Dict[str, List[dict]]:
    rows: Dict[str, List[dict]] = {}
    for fam, lignes in familles.items():
        out = []
        for ligne in lignes:
            x = ligne["x"]
            out.append({
                "label": ligne["label"],
                "n": len(x),
                "lb_cert": ligne["lb_cert"],
                "ub_cert": ligne["ub_cert"],
                "certified": ligne["certified"],
                "zlib": zlib_len(x),
                "lz76": lz76_count(x),
                "lz78": lz78_count(x),
                "h0": h0(x),
                "h_block2": h_block(x, 2),
            })
        rows[fam] = out
    return rows


def _h2b_fits(rows: Dict[str, List[dict]]) -> dict:
    """Pentes log-log par famille et regle de refutation scellee (seuil 0.30).

    Pour P, ``ai`` est exact (log2 n). Pour F et TM, il n'est certifie que par
    enveloppe : la refutation exige alors un ecart de pente >= 0.30 **aux deux
    bornes** de l'enveloppe (lecture conservatrice -- elle ne relache jamais le
    critere scelle, elle en exige davantage).
    """
    seuil = 0.30
    out: Dict[str, dict] = {}
    for fam, lignes in rows.items():
        ns = [r["n"] for r in lignes]
        fits: Dict[str, dict] = {}
        for key in ("zlib", "lz76", "lz78"):
            fits[key] = loglog_fit(ns, [r[key] for r in lignes])
        if fam == "P":
            fits["ai"] = loglog_fit(ns, [math.log2(r["n"]) for r in lignes])
            refutes = [
                k for k in ("zlib", "lz76", "lz78")
                if abs(fits[k]["slope"] - fits["ai"]["slope"]) >= seuil
                and fits[k]["r2"] >= 0.98 and fits["ai"]["r2"] >= 0.98
            ]
        else:
            fits["ai_lb"] = loglog_fit(ns, [r["lb_cert"] for r in lignes])
            fits["ai_ub"] = loglog_fit(ns, [r["ub_cert"] for r in lignes])
            refutes = [
                k for k in ("zlib", "lz76", "lz78")
                if abs(fits[k]["slope"] - fits["ai_lb"]["slope"]) >= seuil
                and abs(fits[k]["slope"] - fits["ai_ub"]["slope"]) >= seuil
                and fits[k]["r2"] >= 0.98 and fits["ai_lb"]["r2"] >= 0.98
                and fits["ai_ub"]["r2"] >= 0.98
            ]
        out[fam] = {"fits": fits, "refutes": refutes}
    return out


def run_battery(
    budget_solver: int = 2_000_000,
    budget_brute: int = 2_000_000,
    g1: bool = True,
) -> dict:
    """Execute le banc scelle et rend les mesures brutes + verdicts bornes.

    Structure : ``meta`` (horodatage de run et notes d'interpretation du
    scelle), ``gates`` (G1/G2), ``h1`` (classes a comptes fixes), ``ladders``
    (lignes brutes), ``h2`` (fits et refutations), ``h3`` (correlation),
    ``controls`` (permutations, pont, batterie mixte), ``verdicts``.
    """
    notes = [
        "Le scelle decrit TM 'j = 6..14' en annoncant 10 lignes : les deux ne "
        "vont pas ensemble (9 valeurs). Le banc prend j = 6..15 (64 -> 32768) "
        "-- l'extension va vers le haut, aucune bande scellee n'est touchee.",
        "Fibonacci : f_j pour j = 12..21 (233 -> 17711, '~ 16384' au sommet).",
        "F et TM : ai n'est certifie que par enveloppe [lb, ub] ; la refutation "
        "H2b exige 0.30 d'ecart aux DEUX bornes (lecture conservatrice).",
        "Le pool est un ensemble d'objets distingues par leur contenu (la "
        "reutilisation est celle du pool du primaire) ; une lecture par "
        "positions surestimerait et n'est pas celle du banc.",
    ]

    gates: Dict[str, dict] = {}
    if g1:
        gates["G1"] = g1_gate(budget=budget_brute)

    # --- H1 : classes a comptes fixes ---
    cache: Dict[str, dict] = {}

    def mes(x: str, label: str) -> dict:
        if x not in cache:
            cache[x] = measure_object(x, label, budget=budget_solver)
        got = dict(cache[x])
        got["label"] = label
        return got

    h1: Dict[str, dict] = {}
    for name, members in corpus_h1().items():
        rows = [mes(x, lab) for lab, x in members]
        vals = [r["ai"] for r in rows if r["ai"] is not None]
        h1[name] = {
            "h0_commun": rows[0]["h0"] if rows else None,
            "rows": rows,
            "max_ai": max(vals) if vals else None,
            "min_ai": min(vals) if vals else None,
            "gap": (max(vals) - min(vals)) if vals else None,
            "exclus_reach": [r["label"] for r in rows if r["ai"] is None],
        }

    # --- H2a : echelle periodique (ai croit, zlib constant) ---
    familles = corpus_ladders()
    lignes = _ladder_rows(familles, budget_solver)
    P = lignes["P"]
    violations = 0
    for i in range(1, len(P)):
        ai_i = math.log2(P[i]["n"])
        if not (ai_i > math.log2(P[i - 1]["n"]) and P[i]["zlib"] <= P[i - 1]["zlib"]):
            violations += 1
    h2a = {
        "lignes": len(P),
        "paires": len(P) - 1,
        "violations": violations,
        "zlib_max": max(r["zlib"] for r in P),
        "criterion": "violations <= 2 (>= 8/10 lignes)",
        "verdict": VERDICT_CONFIRMEE if violations <= 2 else VERDICT_FALSIFIEE,
    }

    # --- H2b : pentes par famille ---
    h2b = _h2b_fits(lignes)
    familles_refutees = [f for f, d in h2b.items() if d["refutes"]]
    h2b_verdict = (
        VERDICT_CONFIRMEE if familles_refutees else VERDICT_FALSIFIEE
    )

    # --- H3 : correlation globale sur la batterie mixte ---
    mixed_rows = [mes(x, lab) for lab, x in corpus_mixed()]
    exact_rows = [r for r in mixed_rows if r["ai"] is not None]
    rho = spearman([r["ai"] for r in exact_rows], [r["zlib"] for r in exact_rows])
    h3 = {
        "n_objets": len(exact_rows),
        "exclus_reach": [r["label"] for r in mixed_rows if r["ai"] is None],
        "rho_spearman_ai_zlib": rho,
        "verdict": VERDICT_CONFIRMEE if rho >= 0 else VERDICT_FALSIFIEE,
    }

    # --- controles : permutations et pont ---
    perm_rows = []
    for name, n in (("n=12", 12), ("n=16", 16)):
        base = periodic(n)
        for seed in SEEDS:
            rng = np.random.default_rng(seed)
            perm = "".join(rng.permutation(list(base)))
            perm_rows.append({
                "classe": name,
                "seed": seed,
                "ai_base": mes(base, f"(01)^[{name}]")["ai"],
                "ai_permute": mes(perm, f"permute s{seed} [{name}]")["ai"],
            })
    pont_rows = [
        mes(x, lab) for lab, x in (("ABRACADABRA", "ABRACADABRA"), ("BANANA", "BANANA"))
    ]

    # --- porte G2 : bornes et temoins sur toutes les mesures exactes ---
    g2_pool = list(exact_rows) + [
        r for d in h1.values() for r in d["rows"] if r["ai"] is not None
    ]
    g2_violations = [
        r["label"] for r in g2_pool
        if r["ai"] < r["lb_doublement"] or r["temoin_valide"] is not True
    ]
    gates["G2"] = {
        "checked": len(g2_pool),
        "violations": g2_violations,
        "passed": not g2_violations,
    }

    # --- verdicts ---
    if (g1 and not gates["G1"]["passed"]) or not gates["G2"]["passed"]:
        verdict_global = VERDICT_NON_CONCLUSIF
    else:
        h1_gaps = [d["gap"] for d in h1.values() if d["gap"] is not None]
        h1_ok = bool(h1_gaps) and all(g >= 2 for g in h1_gaps)
        if h1_ok and h2a["verdict"] == VERDICT_CONFIRMEE and h2b_verdict == VERDICT_CONFIRMEE \
                and h3["verdict"] == VERDICT_CONFIRMEE:
            verdict_global = "CONFIRMÉ"
        elif h1_ok or h2a["verdict"] == VERDICT_CONFIRMEE or h3["verdict"] == VERDICT_CONFIRMEE:
            verdict_global = "PARTIEL"
        else:
            verdict_global = "FALSIFIÉ"

    verdicts = {
        "H1": VERDICT_CONFIRMEE if (
            h1["n=12 (6 uns)"]["gap"] is not None
            and h1["n=16 (8 uns)"]["gap"] is not None
            and h1["n=12 (6 uns)"]["gap"] >= 2
            and h1["n=16 (8 uns)"]["gap"] >= 2
        ) else VERDICT_FALSIFIEE,
        "H2a": h2a["verdict"],
        "H2b": h2b_verdict,
        "H3": h3["verdict"],
        "global": verdict_global,
    }
    if (g1 and not gates["G1"]["passed"]) or not gates["G2"]["passed"]:
        verdicts["H1"] = verdicts["H2a"] = verdicts["H2b"] = verdicts["H3"] = (
            VERDICT_NON_CONCLUSIF
        )

    return {
        "meta": {"notes_scelle": notes, "seeds": list(SEEDS)},
        "gates": gates,
        "ladders": lignes,
        "h1": h1,
        "h2": {"H2a": h2a, "H2b": h2b},
        "h3": h3,
        "controls": {"permutations": perm_rows, "pont": pont_rows},
        "mixed": exact_rows,
        "verdicts": verdicts,
    }