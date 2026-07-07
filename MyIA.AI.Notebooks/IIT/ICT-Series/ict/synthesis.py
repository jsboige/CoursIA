"""Synthese cross-substrat de la serie ICT (capstone, Epic #4588, voir #4946).

Le fil unificateur de la serie ICT : chaque substrat -- tri auto-organise (S1),
paysage bistable / reaction-diffusion (S2), replicateur strategique (S3) --
produit une **trajectoire**. On estime une TPM etat-a-etat depuis cette
trajectoire propre (le pont tri->TPM d'ICT-6, generalise via
``ict.tpm_estimation``) puis on lui applique la MEME batterie d'emergence
causale (``ict.causal_emergence``). C'est le seul appareil de mesure de la
serie applique a l'identique a des substrats radicalement differents.

Ce module reste **generique** : il opere sur des suites d'etats deja
discretisees (labels hachables), sans rien connaitre des substrats. La
discretisation substrat-specifique (coarse-graining d'un champ 2D, binning
d'un scalaire, symbolisation d'un vecteur de frequences strategiques) vit dans
le notebook ICT-Synthese, ou elle est un choix documente et mesure -- pas une
constante cachee dans la librairie. Ce choix doit rester **grossier** : le
chemin d'echelles de ``causal_emergence.greedy_apportionment`` explore toutes
les paires d'etats a chaque pas (cout ~O(k^2) par echelle, k = nombre d'etats
distincts), donc une trajectoire de tri brute (``tuple(config)``) explose vite
alors que sa version macro (niveau d'inversions) tient en une dizaine d'etats.

Gate falsifiable central : *un scalaire d'integration transfere-t-il entre
substrats ?* Les aides ``cross_substrate_summary`` et ``rank_consistency``
permettent de le tester. L'attendu (a confirmer par execution dans le
notebook) est **non** : le classement des substrats change selon la mesure
choisie (EI brute vs gain d'emergence), et aucun nombre unique ne les ordonne
tous. L'invariant de la serie n'est pas un scalaire universel mais une
*methode* : une emergence n'est creditee que **contrastee a son propre controle
degenere**.

Sans complaisance : ``shuffled_baseline`` casse la structure temporelle de la
trajectoire tout en conservant exactement les frequences marginales d'etats.
Si l'emergence "reelle" ne depasse pas ce controle, elle n'est qu'un artefact
du reservoir d'etats visites (des degres de liberte), pas de la dynamique.

Dependances : numpy + ``ict.tpm_estimation`` + ``ict.causal_emergence``.
Reference : ICT-0 (cadrage + feuille de route synthese), Epic #4588.
"""

from __future__ import annotations

from typing import Dict, List, Sequence

import numpy as np

from . import causal_emergence as CE
from . import tpm_estimation as TE


# --------------------------------------------------------------- batterie sur une TPM
def emergence_battery(tpm) -> dict:
    """Batterie d'emergence causale sur une TPM etat-a-etat.

    Combine le profil causal (``causal_emergence.causal_profile``) et le chemin
    d'echelles glouton (``greedy_apportionment``). Retourne un dict plat :
    ``n``, ``effective_information`` (bits, micro), ``determinism``,
    ``degeneracy``, ``effectiveness``, ``emergent_complexity`` (EC sur le chemin
    d'echelles), ``n_scales`` (longueur du chemin micro -> macro).
    """
    prof = CE.causal_profile(tpm)
    appo = CE.greedy_apportionment(tpm)
    return {
        "n": prof["n"],
        "effective_information": prof["effective_information"],
        "determinism": prof["determinism"],
        "degeneracy": prof["degeneracy"],
        "effectiveness": prof["effectiveness"],
        "emergent_complexity": appo["emergent_complexity"],
        "n_scales": len(appo["scales"]),
    }


# --------------------------------------------------------------- trajectoire -> batterie
def trajectory_battery(states: Sequence, unseen: str = "self") -> dict:
    """Estime la TPM d'une trajectoire discrete puis calcule la batterie.

    ``states`` : suite d'etats consecutifs (labels hachables). Ajoute au
    resultat de ``emergence_battery`` deux champs de contexte : ``n_states``
    (nombre d'etats distincts observes) et ``n_transitions``.
    """
    seq = list(states)
    tpm, mapping = TE.tpm_from_trajectory(seq, unseen=unseen)
    out = emergence_battery(tpm)
    out["n_states"] = len(mapping)
    out["n_transitions"] = max(0, len(seq) - 1)
    return out


# --------------------------------------------------------------- controle degenere
def shuffle_states(states: Sequence, rng: np.random.Generator) -> List:
    """Permute la suite d'etats (casse la structure temporelle).

    Conserve exactement le multi-ensemble d'etats : le controle isole la part
    d'emergence qui vient de l'ORDRE (la dynamique) plutot que du simple
    reservoir d'etats visites.
    """
    seq = list(states)
    idx = rng.permutation(len(seq))
    return [seq[i] for i in idx]


def shuffled_baseline(states: Sequence, rng: np.random.Generator,
                      n_shuffles: int = 20, unseen: str = "self") -> dict:
    """Batterie moyenne sur ``n_shuffles`` permutations de la trajectoire.

    Retourne la moyenne (et l'ecart-type sous ``*_std``) de
    ``effective_information`` et ``emergent_complexity`` sur les permutations.
    C'est le controle *sans complaisance* : la valeur a battre pour crediter une
    emergence reelle.
    """
    eis, ecs = [], []
    for _ in range(int(n_shuffles)):
        b = trajectory_battery(shuffle_states(states, rng), unseen=unseen)
        eis.append(b["effective_information"])
        ecs.append(b["emergent_complexity"])
    return {
        "effective_information": float(np.mean(eis)),
        "effective_information_std": float(np.std(eis)),
        "emergent_complexity": float(np.mean(ecs)),
        "emergent_complexity_std": float(np.std(ecs)),
        "n_shuffles": int(n_shuffles),
    }


def emergence_gain(states: Sequence, rng: np.random.Generator,
                   n_shuffles: int = 20, unseen: str = "self") -> dict:
    """Gain d'emergence : mesure reelle - controle shuffle (le signal credite).

    Retourne les valeurs reelles, les valeurs du controle et le gain pour EI et
    EC, plus un booleen ``credited`` : True quand le gain d'EC depasse
    l'ecart-type du controle (signal au-dessus du bruit du reservoir d'etats).

    Capstone ICT-15 (#5090) : enrichi (retro-compatible) des deux autres
    facettes de la theorie fondatrice -- la surprise transitionnelle ``fe_gain``
    (jambe F, ``free_energy.surprise_gain``) et la compression ``k_gain`` (jambe
    K, ``compression.compression_gain``). Les trois scalaires partagent le MEME
    controle shuffle, condition necessaire au gate de convergence Gate 4
    (τ de Kendall par paire sur {ec_gain, fe_gain, k_gain}). Les anciennes cles
    sont preservees : les tests Synthese existants restent verts sans modif.
    """
    from . import compression as CMP
    from . import free_energy as FE

    real = trajectory_battery(states, unseen=unseen)
    base = shuffled_baseline(states, rng, n_shuffles=n_shuffles, unseen=unseen)
    ec_gain = real["emergent_complexity"] - base["emergent_complexity"]
    ei_gain = real["effective_information"] - base["effective_information"]
    credited = ec_gain > base["emergent_complexity_std"] + 1e-12
    fe = FE.surprise_gain(states, rng, n_shuffles=n_shuffles)
    kp = CMP.compression_gain(states, rng, n_shuffles=n_shuffles)
    return {
        "ei_real": real["effective_information"],
        "ei_shuffled": base["effective_information"],
        "ei_gain": ei_gain,
        "ec_real": real["emergent_complexity"],
        "ec_shuffled": base["emergent_complexity"],
        "ec_gain": ec_gain,
        "credited": bool(credited),
        "n_states": real["n_states"],
        # capstone ICT-15 : les deux autres facettes (retro-compatibles)
        "fe_gain": fe["fe_gain"],
        "k_gain": kp["k_gain"],
    }


# --------------------------------------------------------------- comparaison inter-substrat
def cross_substrate_summary(named_trajectories: Dict[str, Sequence],
                            rng: np.random.Generator,
                            n_shuffles: int = 20, unseen: str = "self") -> dict:
    """Applique la batterie + le controle a chaque substrat nomme.

    ``named_trajectories`` : ``{nom_substrat: suite d'etats}``. Retourne
    ``{nom: emergence_gain(...)}`` -- la table brute pour le gate inter-substrat.
    """
    return {
        name: emergence_gain(states, rng, n_shuffles=n_shuffles, unseen=unseen)
        for name, states in named_trajectories.items()
    }


def _kendall_tau(x: Sequence[float], y: Sequence[float]) -> float:
    """Tau de Kendall (concordance de rangs), implementation directe O(n^2).

    Compte les paires concordantes/discordantes, sans dependance a scipy. Les
    paires a egalite (sur x ou y) sont ignorees. Retourne 0.0 s'il y a moins de
    deux elements ou aucune paire departageable.
    """
    xs = list(x)
    ys = list(y)
    n = len(xs)
    if n < 2:
        return 0.0
    conc = disc = 0
    for i in range(n):
        for j in range(i + 1, n):
            sx = np.sign(xs[i] - xs[j])
            sy = np.sign(ys[i] - ys[j])
            if sx == 0 or sy == 0:
                continue
            if sx == sy:
                conc += 1
            else:
                disc += 1
    total = conc + disc
    if total == 0:
        return 0.0
    return float((conc - disc) / total)


def rank_consistency(summary: dict, key_a: str = "ei_real",
                     key_b: str = "ec_gain") -> dict:
    """Teste si deux mesures classent les substrats dans le MEME ordre.

    Coeur du gate falsifiable : si un "scalaire d'integration" transferait entre
    substrats, le classement selon ``key_a`` et selon ``key_b`` coinciderait.
    Retourne l'ordre (decroissant) selon chaque cle, le tau de Kendall entre les
    deux (dans ``[-1, 1]`` : +1 = ordres identiques, -1 = inverses, ~0 = pas de
    transfert) et un booleen ``consistent`` (tau ~ +1).
    """
    names = list(summary)
    va = [summary[n][key_a] for n in names]
    vb = [summary[n][key_b] for n in names]
    order_a = [names[i] for i in np.argsort(va)[::-1]]
    order_b = [names[i] for i in np.argsort(vb)[::-1]]
    tau = _kendall_tau(va, vb)
    return {
        "order_by_" + key_a: order_a,
        "order_by_" + key_b: order_b,
        "kendall_tau": tau,
        "consistent": bool(tau > 0.999),
    }


# --------------------------------------------------------------- substrat S4 (LLM, ICT-22)
def sae_substrate_states(npz_path, feature_ids, sets=None, q: float = 0.5):
    """Trajectoire d'etats discrets du substrat S4 (LLM, traces SAE ICT-21).

    Quatrieme substrat du banc cross-substrat (ICT-22, #5102) : un transformer
    traitant du texte. On consomme les traces SAE top-k committers (GPU-free,
    produites par ``scripts/extract_sae_traces.py`` au sens d'ICT-21) -- un
    ``.npz`` par variante (``trained``, ``control``).

    Le pipeline, identique a ICT-21 : on materialise le panel dense pour les
    ``feature_ids`` donnees (typiquement les features differentielles de
    ``sae_traces.differential_features``, selectionnees sur la variante
    ``trained`` PUIS gerees figees pour le controle ``control`` -- le meme
    capteur pour les deux variantes), on binarise au quantile ``q`` des valeurs
    positives, et on encode chaque pas de temps (token) en un etat entier par
    bit-packing (``sae_traces.states_from_panel``). La trajectoire concatenee
    sur tous les jeux de prompts (ou sur ``sets`` restreints -- utile pour le
    multi-jeux de Gate 12) est directement consommable par
    ``cross_substrate_summary`` / ``emergence_gain``.

    Le choix de la taille du panel doit rester **grossier** (cf. docstring du
    module) : ``greedy_apportionment`` coute ~O(k^2) par echelle ou k est le
    nombre d'etats distincts observes, et le bit-packing sur K features engendre
    jusqu'a 2^K etats possibles. Un panel de ~8-10 features differentielles
    tient l'espace d'etats observé dans la dizaine/la centaine (tractable),
    comme les coarse-grainings de S1/S2/S3.

    Retro-compatible : fonction additive, ``cross_substrate_summary`` et les
    tests existants sont inchanges. Les imports ``sae_traces`` sont locaux pour
    ne pas creer de dependance dur quand le substrat S4 n'est pas utilise.

    Parametres
    ----------
    npz_path : str | Path
        Chemin vers un ``.npz`` de traces SAE (schema ICT-21).
    feature_ids : array-like d'entiers
        Features du panel (communes a toutes les variantes comparees).
    sets : sequence de str | None
        Jeux de prompts a concatener (defaut : tous, dans l'ordre lexicographique).
    q : float
        Quantile de binarisation des valeurs positives (defaut 0.5).

    Retourne
    --------
    list[int]
        Suite d'etats consecutifs (un par token), labels entiers hachables.
    """
    from pathlib import Path

    from . import sae_traces as ST

    tr = ST.load_traces(Path(npz_path))
    feature_ids = np.asarray(feature_ids)
    panels = ST.acts_topk_panels(tr, feature_ids)
    all_sets = sorted({s for s, _ in tr["prompts"]})
    keep = list(sets) if sets is not None else all_sets
    chunks = []
    for s in keep:
        idxs = sorted(i for (ss, i) in tr["prompts"] if ss == s)
        for i in idxs:
            chunks.append(panels[(s, i)])
    if not chunks:
        raise ValueError(f"Aucun panel pour sets={keep} dans {npz_path}")
    dense = np.concatenate(chunks, axis=0)
    bits = ST.binarize_quantile(dense, q=q)
    return [int(v) for v in ST.states_from_panel(bits)]
