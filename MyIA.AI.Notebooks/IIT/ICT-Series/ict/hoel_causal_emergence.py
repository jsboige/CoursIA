"""Case 25 de la veille ICT (#8182) : le renversement EI-macro de Hoel 2013.

Banc de mesure preregistre (docs/ict/hoel-causal-emergence-pre-enregistrement.md,
scelle 2026-11-21 AVANT l'ecriture de ce module) pour la source primaire :

    Erik P. Hoel, Larissa Albantakis, Giulio Tononi, "Quantifying causal
    emergence shows that macro can beat micro", PNAS 110(49):19790-19795, 2013,
    DOI 10.1073/pnas.1314922110 (OA PMC3856819).

Organ-first : la semantique EI (determinisme, degenerescence, effectiveness,
information effective) et le coarse-graining canonique (perturbation macro =
moyenne uniforme intra-groupe + sommation des colonnes) sont INVOQUES depuis
l'organe natif ``ict.causal_emergence`` (``causal_profile`` + ``partition_profile``).
Ce module apporte ce que l'organe n'a pas :

  1. des constructeurs de systemes a elements binaires (portes AND/COPY +
     bruit intrinseque) produisant la TPM etat-a-etat ;
  2. la garde de legalite des regroupements (relation produit + invariance
     sous permutation des micro-elements groupes -- [[00,01,10],[11]] legal,
     [[00,01],[10,11]] rejete, p. 19792) ;
  3. la contre-verification independante ``ei_mi`` (forme information mutuel,
     p. 19791) pour la porte G1 du prereg ;
  4. le calibrage G3 : reconstruction des cablages des Fig. 2/4/5 par recherche
     bornee sur les valeurs IMPRIMEES dans le texte (les schemas vectoriels
     sont illisibles depuis le siege de mesure -- declare au prereg) ;
  5. les hypotheses H1-H4 avec temoin negatif H4, verdicts bornes.

Instrument exact : toutes les mesures viennent de TPM enumerees, aucun
Monte-Carlo (``stochastic: false`` dans le JSON de resultats).

Conventions d'indexation : etat d'un systeme a k elements = entier dont le bit
de poids fort est l'element 0 (big-endian) ; ``groups`` de
``causal_emergence.partition_profile`` = partition exhaustive de ``range(2**k)``.

Dependances : numpy (via l'organe), bibliotheque standard.
"""

from __future__ import annotations

from itertools import permutations, product

import numpy as np

from ict.causal_emergence import causal_profile, partition_profile, validate_tpm

#: tolerances de calibrage G3 (prereg : +/-0.06 bit sur EI, +/-0.03 sur Eff/det/deg)
CAL_TOL_BITS = 0.06
CAL_TOL_COEF = 0.03

#: grille de bruit bornee (prereg §4 : cablages et bruits de la classe)
NOISE_GRID = [round(0.05 * i, 2) for i in range(1, 9)]

#: valeurs imprimees dans le texte de Hoel 2013 (pages 19792-19794) ; la
#: cible ne porte que les valeurs attestees dans le texte extrait
PRINTED = {
    "fig2": {
        "micro": {"EI": 1.15, "eff": 0.29, "det": 0.34, "deg": 0.05},
        "macro": {"EI": 1.55, "eff": 0.78, "det": 0.78, "deg": 0.006},
    },
    "fig4": {
        "micro": {"EI": 2.43, "eff": 0.4, "det": 1.0, "deg": 0.6},
        "macro": {"EI": 3.0, "eff": 1.0},
    },
    "fig5": {
        # imprime p. 19793 : "EI(Sm) = 0.16 bits; Eff(Sm) = 0.03"
        "one_step": {"EI": 0.16, "eff": 0.03},
        "two_step": {"EI": 1.38, "eff": 0.34},
        "macro": {"EI": 2.0, "eff": 1.0},
    },
}


# ------------------------------------------------------------------ G1 : contre-verification
def ei_mi(tpm) -> float:
    """Information effective, forme information mutuel (p. 19791).

    ``EI = MI(UC ; UE)`` entre causes uniformes et effets induits, calculee
    depuis la loi JOINTE ``P(cause=i, effet=j) = TPM[i, j] / n`` par entropies
    -- chemin de code independant de la forme determinisme/degenerescence de
    l'organe (porte G1 du prereg).
    """
    m = validate_tpm(tpm)
    n = m.shape[0]
    joint = m / n  # lignes = causes uniformes
    p_c = joint.sum(axis=1)
    p_e = joint.sum(axis=0)
    nz = joint[joint > 0]
    h_joint = float(-(nz * np.log2(nz)).sum())
    h_c = float(-(p_c[p_c > 0] * np.log2(p_c[p_c > 0])).sum())
    h_e = float(-(p_e[p_e > 0] * np.log2(p_e[p_e > 0])).sum())
    return h_c + h_e - h_joint


# ------------------------------------------------------------------ constructeurs
def bits_of(state: int, k: int) -> tuple:
    """Bits big-endian de l'etat : element 0 = poids fort."""
    return tuple((state >> (k - 1 - i)) & 1 for i in range(k))


def tpm_from_gates(k: int, gates: dict, noise: float = 0.0,
                   mech: str = "and", noise_site: str = "output") -> np.ndarray:
    """TPM etat-a-etat d'un systeme de k elements binaires a portes logiques.

    ``gates[i]`` = couple d'indices d'elements ENTRANT dans la porte de
    l'element i (pas d'auto-connexion, verifie ; deux entrees distinctes).
    Mecanisme ``and`` : sortie = AND des deux entrees ; ``copy`` : sortie =
    copie de la premiere entree. Bruit intrinseque symetrique ``noise`` :
    chaque bit vise est inverse avec cette probabilite, independamment --
    site ``output`` (bit de sortie) ou ``input`` (chaque bit d'ENTREE avant
    la porte ; la porte reste alors deterministe sur les entrees observees,
    les sorties des portes sont independantes entre elles). Le texte de
    Hoel 2013 dit seulement "operating over some intrinsic noise" : les deux
    sites sont enumeres par le calibrage G3.
    """
    if not 0.0 <= noise <= 1.0:
        raise ValueError(f"noise doit etre dans [0, 1], recu {noise}")
    if noise_site not in ("output", "input"):
        raise ValueError(f"noise_site inconnu : {noise_site}")
    for i, ins in gates.items():
        if (len(set(ins)) != 2 or i in ins
                or any(not 0 <= j < k for j in ins)):
            raise ValueError(f"porte invalide pour l'element {i} : {ins}")
    n = 2 ** k
    tpm = np.zeros((n, n))
    for s in range(n):
        cur = bits_of(s, k)
        if noise_site == "input":
            # par porte : chaque entree bruitee est Ber(q), la sortie de la
            # porte est deterministe sur les entrees observees -> P(out=1)
            # = q1*q2 (AND) et les sorties des portes sont independantes
            q_one = []
            for i in range(k):
                i1, i2 = gates[i]
                q1 = cur[i1] * (1.0 - noise) + (1 - cur[i1]) * noise
                q2 = cur[i2] * (1.0 - noise) + (1 - cur[i2]) * noise
                q_one.append(q1 * q2 if mech == "and" else q1)
            for t in range(n):
                nxt = bits_of(t, k)
                p = 1.0
                for i in range(k):
                    p *= q_one[i] if nxt[i] == 1 else (1.0 - q_one[i])
                tpm[s, t] = p
        else:
            base = [int(all(cur[j] for j in gates[i])) if mech == "and"
                    else cur[gates[i][0]] for i in range(k)]
            for t in range(n):
                nxt = bits_of(t, k)
                p = 1.0
                for i in range(k):
                    p *= (1.0 - noise) if nxt[i] == base[i] else noise
                tpm[s, t] = p
    return validate_tpm(tpm)


# ------------------------------------------------------------------ G4 : garde de legalite
def _local_tuple(state: int, macro_elements: list) -> tuple:
    """Vues locales (une par macro-element) d'un micro-etat, big-endian."""
    k = sum(len(g) for g in macro_elements)
    b = bits_of(state, k)
    return tuple(int("".join(str(b[e]) for e in g), 2) for g in macro_elements)


def _state_from_local(loc: tuple, macro_elements: list) -> int:
    """Reconstruction du micro-etat depuis ses vues locales (bijection)."""
    k = sum(len(g) for g in macro_elements)
    b = [0] * k
    for gi, g in enumerate(macro_elements):
        bits_loc = bin(loc[gi])[2:].zfill(len(g))
        for pos, e in enumerate(g):
            b[e] = int(bits_loc[pos])
    return int("".join(map(str, b)), 2)


def is_legal_grouping(groups: list, macro_elements: list) -> bool:
    """Legalite d'un regroupement au sens de Hoel 2013 (p. 19792).

    Conditions : (1) ``macro_elements`` partitionne les micro-elements
    (exhaustif, disjonctif) ; (2) ``groups`` partitionne ``range(2**k)`` ;
    (3) la relation "meme groupe" est un PRODUIT de relations locales (fermee
    sous melange coordonnee par coordonnee) ; (4) la partition locale de
    chaque macro-element est INVARIANTE sous permutation de ses micro-elements
    -- l'identite des micro-elements est perdue. Le regroupement
    ``[[00,01],[10,11]]`` viole (4) : distinguer 01 de 10 exigerait de savoir
    quel element est lequel.
    """
    k = sum(len(g) for g in macro_elements)
    n = 2 ** k
    flat = [e for g in macro_elements for e in g]
    if sorted(flat) != list(range(k)):
        return False
    if sorted(s for g in groups for s in g) != list(range(n)):
        return False
    assign: dict = {}
    for gi, g in enumerate(groups):
        for s in g:
            assign[s] = gi
    nm = len(macro_elements)
    # (3) fermeture produit : deux etats d'un meme groupe restent dans ce
    # groupe si l'on remplace, coordonnee locale par coordonnee locale, la
    # vue de l'un par celle de l'autre
    for a in range(n):
        va = _local_tuple(a, macro_elements)
        for b in range(a + 1, n):
            if assign[a] != assign[b]:
                continue
            vb = _local_tuple(b, macro_elements)
            for gi in range(nm):
                mixed = list(va)
                mixed[gi] = vb[gi]
                m_state = _state_from_local(tuple(mixed), macro_elements)
                if assign[m_state] != assign[a]:
                    return False
    # (4) perte d'identite : classes locales via etats de reference (valides
    # car la relation est deja produit), puis stabilite sous permutation
    for gi in range(nm):
        m = len(macro_elements[gi])
        ref = [0] * nm
        classes: dict = {}
        for bv in range(2 ** m):
            loc = list(ref)
            loc[gi] = bv
            s_ref = _state_from_local(tuple(loc), macro_elements)
            classes.setdefault(assign[s_ref], set()).add(bv)
        parts = {frozenset(c) for c in classes.values()}
        for perm in permutations(range(m)):
            for part in parts:
                moved = set()
                for bv in part:
                    bits_loc = bin(bv)[2:].zfill(m)
                    moved.add(
                        int("".join(bits_loc[perm[i]] for i in range(m)), 2))
                if frozenset(moved) not in parts:
                    return False
    return True


def element_pair_groups(k: int, element_pairs: list) -> list:
    """Groupes d'etats pour des macro-elements = paires d'elements, mapping
    [[00,01,10],[11]] (off/on) par paire. Partition de ``range(2**k)`` au
    format de ``partition_profile`` : un groupe par etat macro.
    """
    nm = len(element_pairs)
    groups: dict = {i: [] for i in range(2 ** nm)}
    for s in range(2 ** k):
        b = bits_of(s, k)
        idx = 0
        for (e1, e2) in element_pairs:
            idx = (idx << 1) | (1 if (b[e1] == 1 and b[e2] == 1) else 0)
        groups[idx].append(s)
    return [groups[i] for i in range(2 ** nm)]


# ------------------------------------------------------------------ G3 : calibrage
def _match(profile: dict, target: dict) -> bool:
    """Concordance d'un profil mesure aux valeurs imprimees (tolerances G3)."""
    if abs(profile["effective_information"] - target["EI"]) > CAL_TOL_BITS:
        return False
    if "eff" in target and abs(profile["effectiveness"] - target["eff"]) > CAL_TOL_COEF:
        return False
    if "det" in target and abs(profile["determinism"] - target["det"]) > CAL_TOL_COEF:
        return False
    if "deg" in target and abs(profile["degeneracy"] - target["deg"]) > CAL_TOL_COEF:
        return False
    return True


def _fig2_wirings():
    """Classe bornee Fig. 2 : chaque element = AND de 2 entrees distinctes
    prises parmi les 3 AUTRES elements (9^4 = 6561 cablages bornes)."""
    per_elem = []
    for i in range(4):
        others = [j for j in range(4) if j != i]
        per_elem.append([(a, b) for a in others for b in others if a != b])
    for wiring in product(*per_elem):
        yield {i: wiring[i] for i in range(4)}


def calibrate_fig2() -> dict | None:
    """Recherche bornee du systeme Fig. 2 (4 AND bruites, emergence spatiale).

    Cablages de la classe scellee, bruit p dans ``NOISE_GRID``, site de bruit
    parmi {sortie, entree} (le texte dit seulement "operating over some
    intrinsic noise"). Cible : valeurs imprimees micro (EI 1.15, Eff 0.29,
    det 0.34, deg 0.05) PUIS macro (EI 1.55, Eff 0.78, det 0.78, deg 0.006)
    sous le regroupement [[00,01,10],[11]] par paire {A,B},{C,D}.
    """
    for site in ("output", "input"):
        for gates in _fig2_wirings():
            for p in NOISE_GRID:
                tpm = tpm_from_gates(4, gates, noise=p, noise_site=site)
                micro = causal_profile(tpm)
                if not _match(micro, PRINTED["fig2"]["micro"]):
                    continue
                groups = element_pair_groups(4, [(0, 1), (2, 3)])
                macro = partition_profile(tpm, groups)
                if _match(macro, PRINTED["fig2"]["macro"]):
                    return {"gates": gates, "noise": p, "noise_site": site,
                            "micro": micro, "macro": macro, "exhaustive": True}
    return None


def fig2_exclusion_note() -> dict:
    """Diagnostic d'exclusion Fig. 2 : impossibilite structurelle, demontree.

    Sous bruit symetrique de SORTIE, chaque bit de sortie a une entropie
    H(p) exactement (q = p ou 1-p selon la base), d'ou det = 1 - H(p) pour
    TOUT cablage ; et chaque bit marginal a P(1) = 1/4 + p/2, d'ou
    deg >= 1 - H(1/4 + p/2). Sous bruit d'ENTREE, P(bit=1) = 1/4 est
    preserve, d'ou deg >= 1 - H(1/4) pour tout p. Les valeurs imprimees
    (det 0.34, deg 0.05 +/- tolerances) sont donc inatteignables dans la
    classe scellee : le "bruit intrinseque" du texte ne peut pas etre un
    flip symetrique sur un mecanisme AND (il est asymetrique, ou le
    mecanisme differe). Ce diagnostic EXPLIQUE l'exclusion G3, il ne reouvre
    aucune bande.
    """
    def h(x):
        z = np.array([x, 1 - x])
        nz = z[z > 0]
        return float(-(nz * np.log2(nz)).sum())

    grid = [0.01 * i for i in range(1, 51)]
    # site sortie : det = 1 - H(p) ; p* minimisant l'ecart a det imprime
    target_det = PRINTED["fig2"]["micro"]["det"]
    target_deg = PRINTED["fig2"]["micro"]["deg"]
    best = min(grid, key=lambda p: abs((1 - h(p)) - target_det))
    det_out = 1 - h(best)
    deg_lb_out = 1 - h(0.25 + best / 2)  # borne : H(joint) <= 4 H(bit)
    return {
        "impossible": True,
        "output_site": {
            "p_star": round(best, 2),
            "det_at_p_star": round(det_out, 4),
            "degeneracy_lower_bound": round(deg_lb_out, 4),
            "target_deg": target_deg,
            "unreachable": deg_lb_out > target_deg + CAL_TOL_COEF,
        },
        "input_site": {
            "degeneracy_lower_bound": round(1 - h(0.25), 4),
            "target_deg": target_deg,
            "unreachable": (1 - h(0.25)) > target_deg + CAL_TOL_COEF,
        },
        "conclusion": ("bruit symetrique (sortie ou entree) incompatible avec "
                       "det=0.34 ET deg=0.05 imprimes sur mecanisme AND"),
    }


def _fig4_wirings():
    """Classe bornee Fig. 4 : "cycle de 6 AND deterministes" (texte p. 19793).

    Deux lectures fideles : (a) cycles a decalages -- l'element i = AND de
    (i+d1) et (i+d2) mod 6 ; (b) cycles de PAIRES DUPLIQUEES -- les deux
    elements d'une paire lisent la meme paire voisine (A=B=AND(C,D) etc.),
    lecture que le macro "3 COPY par paires" rend naturelle. Le texte ne
    fixe pas les entrees element par element : les deux familles sont
    enumerees, le calibrage G3 tranche.
    """
    wirings = []
    # (a) decalages
    for d1 in range(1, 5):
        for d2 in range(d1 + 1, 6):
            wirings.append(("decalages",
                            {i: ((i + d1) % 6, (i + d2) % 6) for i in range(6)}))
    # (b) paires dupliquees : cycle sur les 3 paires, 2 directions
    pairs = [(0, 1), (2, 3), (4, 5)]
    for direction in (1, 2):
        gates = {}
        for pi, (e1, e2) in enumerate(pairs):
            src = pairs[(pi + direction) % 3]
            gates[e1] = src
            gates[e2] = src
        wirings.append((f"paires-dupliquees-dir{direction}", gates))
    return wirings


def calibrate_fig4() -> dict | None:
    """Recherche bornee du systeme Fig. 4 (cycle de 6 AND deterministes).

    Cible : micro EI 2.43 / Eff 0.4 / det 1 / deg 0.6, macro (3 COPY par
    paires adjacentes) EI 3.0 / Eff 1.0.
    """
    for family, gates in _fig4_wirings():
        tpm = tpm_from_gates(6, gates, noise=0.0)
        micro = causal_profile(tpm)
        if not _match(micro, PRINTED["fig4"]["micro"]):
            continue
        groups = element_pair_groups(6, [(0, 1), (2, 3), (4, 5)])
        macro = partition_profile(tpm, groups)
        if _match(macro, PRINTED["fig4"]["macro"]):
            return {"gates": gates, "family": family, "noise": 0.0,
                    "micro": micro, "macro": macro, "exhaustive": True}
    return None


#: regles ``else`` bornees pour Fig. 5 (reponse hors burst)
_FIG5_ELSE = ("quiet", "copy", "count", "uniform")


def _fig5_out_dist(in_self: int, in_other: int, else_rule: str,
                   noise: float) -> dict:
    """Distribution de la fenetre de sortie d'un element Fig. 5.

    Burst de l'entree (fenetre 11) -> burst de sortie (11) ; sinon regle
    ``else`` (quiet : 00 ; copy : propre fenetre ; count : 01 si l'entree
    porte un spike isole, 00 sinon ; uniform : uniforme). Bruit symetrique :
    la reponse attendue a lieu w.p. 1-noise, sinon tirage uniforme.
    """
    if in_other == 0b11:
        base = {0b11: 1.0}
    elif else_rule == "quiet":
        base = {0b00: 1.0}
    elif else_rule == "copy":
        base = {in_self: 1.0}
    elif else_rule == "count":
        spikes = bin(in_other).count("1")
        base = {0b01: 1.0} if spikes == 1 else {0b00: 1.0}
    else:  # uniform
        base = {w: 0.25 for w in range(4)}
    if noise <= 0.0:
        return base
    out = {w: noise * 0.25 for w in range(4)}
    for w, pr in base.items():
        out[w] += (1.0 - noise) * pr
    return out


def fig5_tpms(else_rule: str = "quiet", noise: float = 0.0) -> dict:
    """Systeme Fig. 5 : deux elements Markov d'ordre 2 (burst -> burst).

    Fenetre de 2 pas : la fenetre (t+1, t+2) de A = burst ssi la fenetre de B
    en (t-1, t) = burst, regle ``else`` sinon (cf ``_fig5_out_dist``). Renvoie
    la TPM 2 pas (16 etats = couple de fenetres, exacte), la TPM 1 pas
    (etat = (A_t, B_t), histoire t-1 marginalisee uniformement) et le
    regroupement temporel [[00,01,10],[11]] par element.
    """
    # TPM 2 pas : etat = (fenA, fenB), fenA = bits de poids fort
    t2 = np.zeros((16, 16))
    for s in range(16):
        fa, fb = (s >> 2) & 3, s & 3
        da = _fig5_out_dist(fa, fb, else_rule, noise)
        db = _fig5_out_dist(fb, fa, else_rule, noise)
        for na, pa in da.items():
            for nb, pb in db.items():
                t2[s, (na << 2) | nb] += pa * pb
    # TPM 1 pas : etat = (A_t, B_t) ; l'historique (t-1) est uniforme et le
    # bit observe A_{t+1} est le PREMIER bit de la fenetre de sortie
    t1 = np.zeros((4, 4))
    for s in range(4):
        a, b = (s >> 1) & 1, s & 1
        for h_a in (0, 1):
            for h_b in (0, 1):
                fa, fb = (h_a << 1) | a, (h_b << 1) | b
                da = _fig5_out_dist(fa, fb, else_rule, noise)
                db = _fig5_out_dist(fb, fa, else_rule, noise)
                for na, pa in da.items():
                    for nb, pb in db.items():
                        nxt = (((na >> 1) & 1) << 1) | ((nb >> 1) & 1)
                        t1[s, nxt] += 0.25 * pa * pb
    # regroupement temporel [[00,01,10],[11]] par element (fenetre -> on/off)
    groups = []
    for macro_idx in range(4):
        ma, mb = (macro_idx >> 1) & 1, macro_idx & 1
        groups.append([
            s for s in range(16)
            if (1 if ((s >> 2) & 3) == 3 else 0) == ma
            and (1 if (s & 3) == 3 else 0) == mb
        ])
    return {"one_step": t1, "two_step": t2, "groups": groups}


def calibrate_fig5() -> dict | None:
    """Calibrage Fig. 5 : regles ``else`` bornees x bruit de la grille contre
    les valeurs imprimees (1 pas EI 0.16 ; 2 pas 1.38/0.34 ; macro 2.0/1.0)."""
    for rule in _FIG5_ELSE:
        for noise in NOISE_GRID:
            tp = fig5_tpms(rule, noise)
            p1 = causal_profile(tp["one_step"])
            p2 = causal_profile(tp["two_step"])
            pm = partition_profile(tp["two_step"], tp["groups"])
            if (_match(p1, PRINTED["fig5"]["one_step"])
                    and _match(p2, PRINTED["fig5"]["two_step"])
                    and _match(pm, PRINTED["fig5"]["macro"])):
                return {"else_rule": rule, "noise": noise,
                        "one_step": p1, "two_step": p2, "macro": pm,
                        "exhaustive": True}
    return None


# ------------------------------------------------------------------ H4 : temoin negatif
def _self_copy_tpm(k: int, noise: float) -> np.ndarray:
    """TPM de k elements independants, chacun x <- x bruite (autoregression)."""
    n = 2 ** k
    tpm = np.zeros((n, n))
    for s in range(n):
        b = bits_of(s, k)
        for t in range(n):
            nb = bits_of(t, k)
            p = 1.0
            for i in range(k):
                p *= (1.0 - noise) if nb[i] == b[i] else noise
            tpm[s, t] = p
    return validate_tpm(tpm)


def legal_groupings_4ind() -> list:
    """Regroupements legaux non triviaux du temoin H4 (4 elements) : les 3
    appariements en paires [[00,01,10],[11]] et le macro unique on/off sur
    les 4 elements (on = 1111)."""
    out = []
    for pairs in ([(0, 1), (2, 3)], [(0, 2), (1, 3)], [(0, 3), (1, 2)]):
        out.append((f"paires-{pairs[0][0]}{pairs[0][1]}-{pairs[1][0]}{pairs[1][1]}",
                    element_pair_groups(4, pairs)))
    out.append(("total-4", [[s for s in range(16) if s != 15], [15]]))
    return out


def witness_h4(noise: float = 0.1) -> dict:
    """Temoin negatif H4 : 4 elements COPY d'eux-memes, bruits, independants.

    Prediction scellee : CE <= 0 sur CHAQUE regroupement legal non trivial
    (micro deja efficace, sans structure de groupe : le coarse-graining perd
    de la taille sans gain d'efficacite -- lignes directrices (i)/(ii),
    p. 19795).
    """
    tpm = _self_copy_tpm(4, noise)
    micro = causal_profile(tpm)
    rows = []
    for label, groups in legal_groupings_4ind():
        macro = partition_profile(tpm, groups)
        rows.append({
            "label": label,
            "EI_macro": macro["effective_information"],
            "CE": macro["effective_information"] - micro["effective_information"],
        })
    return {"micro": micro, "rows": rows,
            "verdict": "CONFIRMEE" if all(r["CE"] <= 1e-9 for r in rows)
            else "FALSIFIEE"}


# ------------------------------------------------------------------ batterie complete
def _h1_share(micro: dict, macro: dict) -> float:
    """Part du gain de determinisme dans le delta d'effectivite (H1)."""
    d_eff = macro["effectiveness"] - micro["effectiveness"]
    if d_eff <= 1e-12:
        return 0.0
    return (macro["determinism"] - micro["determinism"]) / d_eff


def run_all() -> dict:
    """Batterie preregistree complete : portes G1/G2/G4, calibrages G3,
    hypotheses H1-H4, verdict global borne. Sortie = JSON de resultats."""
    # ---- G2 : cas analytiques sur l'organe
    copy2 = np.eye(2)               # COPY parfait : Eff 1, EI 1
    noisy2 = np.full((2, 2), 0.5)   # bruit total : EI 0
    degen3 = np.tile([1.0, 0.0, 0.0], (3, 1))  # lignes identiques : Eff 0
    prof_c, prof_n, prof_d = (causal_profile(m) for m in (copy2, noisy2, degen3))
    g2 = (abs(prof_c["effectiveness"] - 1.0) < 1e-9
          and abs(prof_c["effective_information"] - 1.0) < 1e-9
          and abs(prof_n["effective_information"]) < 1e-9
          and abs(prof_d["effectiveness"]) < 1e-9)
    gates_out: dict = {"G2_analytic": {"ok": bool(g2), "copy": prof_c,
                                       "noisy": prof_n, "degenerate": prof_d}}

    # ---- G3 : calibrages (avant G1, pour mesurer aussi les systemes reconstruits)
    cal2, cal4, cal5 = calibrate_fig2(), calibrate_fig4(), calibrate_fig5()

    # ---- G1 : organe (det - deg) contre ei_mi (joint) sur toutes les TPM
    g1_mats = [copy2, noisy2, degen3]
    if cal2:
        g1_mats.append(tpm_from_gates(4, cal2["gates"], noise=cal2["noise"]))
        g1_mats.append(cal2["macro"]["macro_tpm"])
    if cal4:
        g1_mats.append(tpm_from_gates(6, cal4["gates"]))
        g1_mats.append(cal4["macro"]["macro_tpm"])
    if cal5:
        tp5 = fig5_tpms(cal5["else_rule"], cal5["noise"])
        g1_mats += [tp5["one_step"], tp5["two_step"],
                    cal5["macro"]["macro_tpm"]]
    diffs = [abs(ei_mi(m) - causal_profile(m)["effective_information"])
             for m in g1_mats]
    gates_out["G1_dual_impl"] = {
        "ok": bool(diffs and max(diffs) < 1e-9),
        "max_abs_diff": max(diffs) if diffs else None,
        "n_matrices": len(g1_mats),
    }

    # ---- G4 : garde de legalite
    legal_map = element_pair_groups(4, [(0, 1), (2, 3)])
    illegal = [[0, 1], [2, 3]]  # [[00,01],[10,11]] : distingue 01 de 10
    g4 = (is_legal_grouping(legal_map, [(0, 1), (2, 3)])
          and not is_legal_grouping(illegal, [(0, 1)]))
    gates_out["G4_legality"] = {"ok": bool(g4)}

    gates_ok = all(v["ok"] for v in gates_out.values())

    # ---- hypotheses (evaluees seulement si les portes instrumentales passent)
    hyps: dict = {}
    if gates_ok:
        if cal2 and cal2.get("exhaustive"):
            micro, macro = cal2["micro"], cal2["macro"]
            ce = macro["effective_information"] - micro["effective_information"]
            share = _h1_share(micro, macro)
            hyps["H1"] = {
                "CE": ce, "band": [0.2, 0.6], "det_share": share,
                "micro": micro, "macro": macro,
                "verdict": ("CONFIRMEE" if (ce > 0 and 0.2 <= ce <= 0.6
                                            and share >= 0.8)
                            else ("FALSIFIEE" if ce <= 0 else "PARTIEL")),
            }
        else:
            hyps["H1"] = {"verdict": "NON_CONCLUSIF",
                          "reason": "calibrage G3 Fig. 2 non atteint",
                          "exclusion": fig2_exclusion_note()}
        if cal4 and cal4.get("exhaustive"):
            micro, macro = cal4["micro"], cal4["macro"]
            ce = macro["effective_information"] - micro["effective_information"]
            hyps["H2"] = {
                "CE": ce, "band": [0.3, 0.8],
                "macro_eff": macro["effectiveness"],
                "micro_det": micro["determinism"],
                "micro": micro, "macro": macro,
                "verdict": ("CONFIRMEE" if (ce > 0 and 0.3 <= ce <= 0.8
                                            and macro["effectiveness"] > 1 - 1e-9
                                            and micro["determinism"] > 1 - 1e-9)
                            else ("FALSIFIEE" if ce <= 0 else "PARTIEL")),
            }
        else:
            hyps["H2"] = {"verdict": "NON_CONCLUSIF",
                          "reason": "calibrage G3 Fig. 4 non atteint"}
        if cal5 and cal5.get("exhaustive"):
            e1 = cal5["one_step"]["effective_information"]
            e2 = cal5["two_step"]["effective_information"]
            em = cal5["macro"]["effective_information"]
            ce = em - e2
            hyps["H3"] = {
                "EI_1": e1, "EI_2": e2, "EI_macro": em,
                "CE": ce, "band": [0.3, 0.9],
                "verdict": ("CONFIRMEE" if (e1 < e2 < em and 0.3 <= ce <= 0.9)
                            else ("FALSIFIEE" if not (e1 < e2 < em)
                                  else "PARTIEL")),
            }
        else:
            hyps["H3"] = {"verdict": "NON_CONCLUSIF",
                          "reason": "calibrage G3 Fig. 5 non atteint"}
        hyps["H4"] = witness_h4()
    else:
        hyps = {h: {"verdict": "NON_CONCLUSIF",
                    "reason": "porte instrumentale G* declenchee"}
                for h in ("H1", "H2", "H3", "H4")}

    # ---- verdict global borne (prereg §6 : NON_CONCLUSIF reserve aux portes
    # G1/G2/G4 ou a l'exclusion G3 de TOUTES les figures ; melange sans
    # falsification = PARTIEL)
    verdicts = [hyps[h]["verdict"] for h in ("H1", "H2", "H3", "H4")]
    all_h_figs_non_concl = all(hyps[h]["verdict"] == "NON_CONCLUSIF"
                               for h in ("H1", "H2", "H3"))
    if not gates_ok or all_h_figs_non_concl:
        global_verdict = "NON_CONCLUSIF"
    elif any(v == "FALSIFIEE" for v in verdicts):
        global_verdict = "REFUTE"
    elif all(v == "CONFIRMEE" for v in verdicts):
        global_verdict = "SOUTENU"
    else:
        global_verdict = "PARTIEL"

    return {
        "case": "25-hoel-causal-emergence",
        "source": ("Hoel, Albantakis, Tononi 2013, PNAS 110(49):19790-19795, "
                   "10.1073/pnas.1314922110"),
        "organ": "ict.causal_emergence (causal_profile + partition_profile), invoque",
        "stochastic": False,
        "gates": gates_out,
        "calibration": {
            "fig2": ({"gates": cal2["gates"], "noise": cal2["noise"],
                      "noise_site": cal2.get("noise_site"),
                      "exhaustive": cal2.get("exhaustive", False)}
                     if cal2 else None),
            "fig4": ({"gates": cal4["gates"], "family": cal4.get("family"),
                      "noise": cal4["noise"],
                      "exhaustive": cal4.get("exhaustive", False)}
                     if cal4 else None),
            "fig5": ({"else_rule": cal5["else_rule"], "noise": cal5["noise"],
                      "exhaustive": cal5.get("exhaustive", False)}
                     if cal5 else None),
        },
        "hypotheses": hyps,
        "global_verdict": global_verdict,
    }


def _json_default(obj):
    """Convertisseur JSON : tableaux numpy -> listes, scalaires -> float."""
    if isinstance(obj, np.ndarray):
        return obj.tolist()
    return float(obj)


if __name__ == "__main__":
    import json

    print(json.dumps(run_all(), indent=2, default=_json_default))
