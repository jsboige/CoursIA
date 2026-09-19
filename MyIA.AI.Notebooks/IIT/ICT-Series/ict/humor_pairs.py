# -*- coding: utf-8 -*-
"""Couche d'acces au corpus humour consolide (CORPUS_DUR) pour #14035.

Reproduit le geste du pilote ICT-35 : les cellules code [0..10] de
``GameTheory-24b-Humour-Banc-Dur.ipynb`` sont executees dans un namespace
isole, sans editer le notebook source, et ``CORPUS_DUR`` en est extrait.
La source de verite reste le notebook GT-24b, jamais copie.
"""
from __future__ import annotations

import json
import os
from collections import Counter

import numpy as np
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Iterator

# Taxonomie de labels du banc consolide (GT-24b, verifiee sur le pilote ICT-35).
LABELS: tuple[str, ...] = (
    "humour_reussi",
    "rire_sans_recadrage",
    "recadrage_sans_rire",
    "offensif_compris_non_partage",
    "rien",
)

# Derniere cellule code de GT-24b a executer : CORPUS_DUR est construit dans
# la cellule 10 (mesure firsthand sur le notebook source).
_CORPUS_CELL_END = 10

# Champs du contrat d'instance (GT-24b cellule 10, verbe du banc).
_REQUIRED_FIELDS = ("id", "texte", "features", "label", "justification", "source")


def gt24b_path() -> Path:
    """Chemin canonique du banc humour consolide, resolu depuis ce module."""
    return (
        Path(__file__).resolve().parents[3]
        / "GameTheory"
        / "GameTheory-24b-Humour-Banc-Dur.ipynb"
    )


def _corpus_cwd() -> Path:
    """Repertoire d'execution reproduisant le cwd du pilote ICT-35.

    La cellule 4 de GT-24b resout son cache Argumentum en chemin RELATIF
    (``Path("argumentum_scenarii.csv")``) : selon le cwd, elle fait un hit
    cache ou declenche un fetch GitHub raw. Le cache du pilote vit dans le
    dossier ICT-Series ; a defaut on retombe sur le dossier du notebook
    (comportement natif du banc, fetch documente dans sa cellule 4).
    """
    for d in (Path(__file__).resolve().parent, gt24b_path().parent):
        if (d / "argumentum_scenarii.csv").exists():
            return d
    return gt24b_path().parent


@contextmanager
def _cwd(path: Path) -> Iterator[None]:
    prev = Path.cwd()
    os.chdir(path)
    try:
        yield
    finally:
        os.chdir(prev)


def load_corpus_dur(path: Path | None = None) -> list[dict[str, Any]]:
    """Charge ``CORPUS_DUR`` en executant les cellules de GT-24b.

    Reproduction deterministe (``random.seed(42)`` est pose par GT-24b
    lui-meme dans la cellule 10) ; le notebook source n'est jamais modifie.
    L'exec se fait dans le cwd portant le cache Argumentum (cf :func:`_corpus_cwd`)
    pour ne pas dependre du repertoire appelant.
    """
    nb_path = path or gt24b_path()
    nb = json.loads(nb_path.read_text(encoding="utf-8"))
    ns: dict[str, Any] = {}
    with _cwd(_corpus_cwd()):
        for i, cell in enumerate(nb["cells"]):
            if cell["cell_type"] == "code" and i <= _CORPUS_CELL_END:
                exec("".join(cell["source"]), ns)  # noqa: S102 - reproduction, motif du pilote ICT-35 cell[3]
    corpus = ns["CORPUS_DUR"]
    validate_corpus(corpus)
    return corpus


def validate_corpus(corpus: list[dict[str, Any]], *, min_size: int = 100) -> None:
    """Verifie le contrat du corpus : taille, champs, taxonomie, unicite des ids."""
    assert isinstance(corpus, list) and len(corpus) >= min_size, (
        f"CORPUS_DUR attendu >= {min_size} instances, recu {len(corpus)}"
    )
    ids = [inst["id"] for inst in corpus]
    assert len(set(ids)) == len(ids), "ids dupliques dans CORPUS_DUR"
    for inst in corpus:
        for field in _REQUIRED_FIELDS:
            assert field in inst, f"champ {field} manquant sur {inst.get('id')}"
        assert inst["label"] in LABELS, (
            f"label hors taxonomie : {inst['label']!r} sur {inst['id']}"
        )


def label_distribution(corpus: list[dict[str, Any]]) -> Counter:
    """Effectifs par label, pour le controle de stratification des tranches."""
    return Counter(inst["label"] for inst in corpus)


# --------------------------------------------------------------------------- #
# Paires minimales humour -> unfun (#14035 tranche 1, phase observationnelle)
# --------------------------------------------------------------------------- #

# Edits main : (setup verbatim, punchline verbatim, punchline_neutre, controle).
# - setup + punchline = le texte COMMITTE de l'instance (source de verite GT-24b),
#   re-verifie au chargement (span unique, suffixe exact).
# - punchline_neutre : continuation coherente attendue — tue l'incongruite,
#   conserve le lexique du registre, taille comparable.
# - controle : AUTRE continuation coherente non-humorale de taille comparable —
#   controle de distance d'edition (l'effet est-il specifique a la perte
#   d'incongruite, ou a toute edition de cette taille ?).
# joke-p01 (texte corpus tronque : punchline absente) et joke-p17 (saut de ligne
# inline malformé) sont EXCLUS — 28 paires, complement >=30 via les instances
# Argumentum au cycle suivant.
_PAIR_EDITS: dict[str, tuple[str, str, str, str]] = {
    "joke-p02": ("Pourquoi les développeurs confondent Halloween et Noël ? ", "Parce que Oct 31 == Dec 25.", "Parce que les deux tombent en fin d'année.", "Parce que les deux sont des jours fériés."),
    "joke-p03": ("Il y a 10 types de personnes au monde : ", "ceux qui comprennent le binaire et ceux qui ne le comprennent pas.", "ceux qui parlent anglais et ceux qui parlent une autre langue.", "ceux qui habitent en ville et ceux qui habitent à la campagne."),
    "joke-p04": ("Un SQL entre dans un bar, voit deux tables et leur dit : ", "'SELECT * FROM...'", "'Bonjour, je voudrais réserver.'", "'Excusez-moi, il y a de la place ?'"),
    "joke-p05": ("Combien d'ingénieurs faut-il pour changer une ampoule ? ", "Aucun, c'est un problème hardware.", "Un seul, avec un escabeau.", "Deux, pour tenir l'escabeau."),
    "joke-p06": ("Je suis tombé amoureuse d'une fonction quadratique. ", "Mais elle avait deux racines.", "Mais elle était déjà définie.", "Mais elle vivait dans un autre espace."),
    "joke-p07": ("Un null et un undefined entrent dans un bar. ", "Le barman dit 'On accepte pas les non-définis ici'.", "Le barman leur sert deux bières.", "Le barman leur demande leur carte."),
    "joke-p08": ("Je voulais te raconter une blague sur UDP... ", "mais je sais si elle arrive.", "mais je ne suis pas sûr qu'elle est drôle.", "mais elle est un peu longue."),
    "joke-p09": ("Le père Noël a-t-il déjà eu un problème de pile ? ", "Non, il a toujours des piles neuves.", "Non, il change ses piles chaque année.", "Non, il utilise des piles rechargeables."),
    "joke-p10": ("Pourquoi le café est-il si bon au travail ? ", "Parce qu'il est fraîchement moulu par l'échéance.", "Parce que la machine est réglée le matin.", "Parce que tout le monde le boit noir."),
    "joke-p11": ("J'ai essayé d'écrire une blague sur les coroutines, mais ", "je n'arrive pas à la yield.", "je n'arrive pas à la terminer.", "je n'arrive pas à la faire tenir."),
    "joke-p12": ("Docker, Kubernetes, Prometheus, Grafana. On m'a dit que c'était simple, alors ", "je stack.", "j'installe tout.", "je retire tout."),
    "joke-p13": ("Mon compilateur et moi on a une relation stable : ", "il compile, je pleure.", "il compile, je relis.", "il plante, je redémarre."),
    "joke-p14": ("J'ai un ami palindrome. ", "On ne peut pas se différencier.", "Son prénom se lit pareil dans les deux sens.", "Son prénom est très difficile à prononcer."),
    "joke-p15": ("Les regex sont comme des licornes : ", "tout le monde en parle, personne les a vues.", "elles sont très difficiles à écrire.", "elles servent à chercher du texte."),
    "joke-p16": ("Un physicien, un biologiste et un chimiste voient 2 bâtiments. ", "L'un entre, l'autre sort. 'Tiens, ils ont échangé.'", "Ils regardent les deux bâtiments.", "Ils entrent dans le même bâtiment."),
    "joke-p18": ("Si Dieu existe, il est Objective-C : ", "tout est message.", "tout est objet.", "rien n'est simple."),
    "joke-p19": ("Le temps est une illusion. ", "Le décalage horaire, doublement.", "Le décalage horaire, aussi.", "Le décalage horaire, surtout."),
    "joke-p20": ("Un photon entre dans un bar et commande une bière. ", "Le barman dit 'Pour vous, c'est gratuit, on vous voit pas partir'.", "Le barman lui sert la bière aussitôt.", "Le barman lui demande de payer d'avance."),
    "joke-p21": ("J'ai une blague sur les matrices, mais ", "c'est hors de portée du public.", "elle est trop longue à raconter.", "elle n'est pas encore au point."),
    "joke-p22": ("Un chat roux dans une salle de serveurs est dangereux : ", "il pourrait activer l'incident majeur.", "il pourrait débrancher un câble.", "il pourrait se cacher derrière une baie."),
    "joke-p23": ("Pourquoi les plongeurs plongent-ils toujours en arrière et jamais en avant ? ", "Parce que sinon ils tomberaient dans le bateau.", "Parce que le bateau est derrière eux.", "Parce que leurs bouteilles sont dans le dos."),
    "joke-p24": ("Le HTML n'est pas un langage de programmation. ", "Et le plus dur, c'est de le dire à mon patron.", "Et tout le monde est d'accord là-dessus.", "Et le débat recommence chaque année."),
    "joke-p25": ("Si vous pensez que personne ne s'intéresse à votre vie, ", "regardez vos logs Git.", "regardez vos statistiques de navigation.", "regardez le nombre de vos abonnés."),
    "joke-p26": ("Comment debug-on un avion ? ", "On retire les composants un par un jusqu'à ce qu'il ne plante plus.", "On relit le manuel de maintenance.", "On appelle un mécanicien qualifié."),
    "joke-p27": ("Mieux vaut avoir un git pull que ", "deux tu l'auras.", "rien du tout.", "un git push raté."),
    "joke-p28": ("Mon chat a appris Python. ", "Maintenant il chasse les exceptions au lieu des souris.", "Maintenant il connaît trois commandes.", "Maintenant il ignore les souris."),
    "joke-p29": ("Les submodules Git, c'est comme les voisins : ", "mieux vaut ne pas les déranger.", "on les voit rarement.", "ils prennent de la place."),
    "joke-p30": ("Il était une fois un UTF-8 qui ne savait pas où était la fin. ", "Il était perdu dans un BOM.", "Il attendait son dernier octet.", "Il cherchait son marqueur de fin."),
    # Top-up a >=30 : les instances Argumentum sont TRONQUEES a ~150 c. par le
    # banc GT-24b (punchline jamais committée) — inutilisables. Les one-liners
    # edge-04/05 (label recadrage_sans_rire : incongruite vive, annotateur n'a
    # pas ri) completent — heterogeneite de label documentée, l'incongruite
    # portee par le texte est le critere du pairing.
    "edge-04": ("'I told my wife she was drawing her eyebrows too high. ", "She seemed surprised.' (Graham Chapman)", "She looked in the mirror.' (Graham Chapman)", "She asked him why.' (Graham Chapman)"),
    "edge-05": ("'I'm on a whiskey diet. ", "I've lost three days already.' (Tommy Cooper)", "It has been three weeks already.' (Tommy Cooper)", "I have not started yet.' (Tommy Cooper)"),
}


def build_pairs(corpus: list[dict[str, Any]]) -> list[dict[str, str]]:
    """Construit les paires minimales humour/unfun/controle depuis la table d'edits.

    Chaque paire porte : le texte original (humour), sa version punchline
    neutralisee (unfun), et le controle de distance d'edition. La zone d'edition
    (punchline) est disjoncte du prefixe commun (setup) par construction.
    """
    by_id = {inst["id"]: inst["texte"] for inst in corpus}
    pairs = []
    for jid, (setup, punch, unfun, ctrl) in _PAIR_EDITS.items():
        texte = by_id[jid]
        assert texte.count(punch) == 1, f"{jid}: punchline absente ou non unique"
        assert texte.endswith(punch) and texte.startswith(setup), (
            f"{jid}: le texte commite ne se coupe pas setup|punchline comme declare"
        )
        pairs.append({
            "id": jid,
            "setup": setup,
            "humour": texte,
            "unfun": setup + unfun,
            "ctrl_edit": setup + ctrl,
        })
    return pairs


def validate_pairs(pairs: list[dict[str, str]], *, min_pairs: int = 30) -> None:
    """Contrat des paires : nombre, unicite, prefixe commun exact."""
    assert len(pairs) >= min_pairs, f"{len(pairs)} paires < {min_pairs} requises"
    ids = [p["id"] for p in pairs]
    assert len(set(ids)) == len(ids), "ids de paires dupliques"
    for p in pairs:
        for variant in ("unfun", "ctrl_edit"):
            assert p[variant].startswith(p["setup"]), (
                f"{p['id']}/{variant}: le setup n'est pas prefixe commun exact"
            )
        assert p["unfun"] != p["humour"] and p["ctrl_edit"] != p["humour"]


def build_prompts_json(pairs: list[dict[str, str]]) -> dict[str, list[str]]:
    """Serialise les paires au contrat ``extract_sae_traces.py --prompts-json``.

    Contrat (validateur du script, ligne 663) : dict non vide
    ``{set_name: [textes non vides]}`` — un texte par paire, ordre stable.
    """
    return {
        "humour": [p["humour"] for p in pairs],
        "unfun": [p["unfun"] for p in pairs],
        "ctrl_edit": [p["ctrl_edit"] for p in pairs],
    }


# --------------------------------------------------------------------------- #
# Mesure differentielle sur traces SAE (verdict pre-registre c.5743321902,
# ecart null corrigé c.5743498870 — numpy uniquement, discipline ict/)
# --------------------------------------------------------------------------- #

def _common_prefix_len(toks_a, toks_b) -> int:
    """Longueur du prefixe token commun exact (limite de zone d'edition)."""
    n = 0
    for a, b in zip(toks_a, toks_b):
        if a != b:
            break
        n += 1
    return n


def _zone_vec(entry: dict, start: int, d_sae: int) -> np.ndarray:
    """Vecteur moyen dense (d_sae,) des activations des tokens de zone."""
    ids = entry["ids"][start:]
    vals = entry["vals"][start:]
    assert ids.shape[0] > 0, "zone d'edition vide (prefixe commun = texte entier)"
    v = np.zeros(d_sae, dtype=np.float64)
    np.add.at(v, ids.ravel(), vals.ravel())
    return v / ids.shape[0]


def measure_humor_differential(
    traces_path: str | Path,
    pairs: list[dict[str, str]],
    *,
    n_draws: int = 2048,
    seed: int = 42,
) -> dict[str, Any]:
    """Mesure pre-registree : delta_pair vs null croise + delta_ctrl + z features.

    Verdict (critères figés c.5743321902, null corrigé c.5743498870) :
    FEATURE_CANDIDATE ssi delta_pair > p99(null croise) ET delta_pair >
    1.5*delta_ctrl ET >= 3 features |z| > 3 du meme cote ; SURFACE_SEULE si
    delta_pair dépasse le null mais <= 1.5*delta_ctrl ; INCONCLUSIVE sinon.
    """
    from .sae_traces import load_traces

    tr = load_traces(traces_path)
    d_sae = int(tr["meta"]["d_sae"])
    n = len(pairs)
    zones = {"humour": [], "unfun": [], "ctrl_edit": []}
    for i in range(n):
        eh = tr["prompts"][("humour", i)]
        eu = tr["prompts"][("unfun", i)]
        ec = tr["prompts"][("ctrl_edit", i)]
        k_hu = _common_prefix_len(eh["tokens"], eu["tokens"])
        k_hc = _common_prefix_len(eh["tokens"], ec["tokens"])
        zones["humour"].append(_zone_vec(eh, k_hu, d_sae))
        zones["unfun"].append(_zone_vec(eu, k_hu, d_sae))
        zones["ctrl_edit"].append(_zone_vec(ec, k_hc, d_sae))
    H = np.stack(zones["humour"])       # [n, d_sae]
    U = np.stack(zones["unfun"])
    C = np.stack(zones["ctrl_edit"])

    delta_pair = float(np.mean(np.abs(H - U).sum(axis=1)))
    delta_ctrl = float(np.mean(np.abs(H - C).sum(axis=1)))

    rng = np.random.default_rng(seed)
    # Null croise (c.5743498870) : sigma brasse les unfun ENTRE paires.
    null_deltas = np.empty(n_draws)
    for d in range(n_draws):
        sigma = rng.permutation(n)
        null_deltas[d] = np.mean(np.abs(H - U[sigma]).sum(axis=1))
    p99 = float(np.quantile(null_deltas, 0.99))

    # z features : flip de signe intra-paire (null valide au niveau feature).
    diffs = H - U                                  # [n, d_sae]
    observed = diffs.mean(axis=0)
    null_means = np.empty((n_draws, d_sae))
    for d in range(n_draws):
        s = rng.choice(np.array([-1.0, 1.0]), size=(n, 1))
        null_means[d] = (diffs * s).mean(axis=0)
    z = observed / (null_means.std(axis=0) + 1e-12)
    over = np.where(np.abs(z) > 3)[0]
    pos = sum(1 for f in over if z[f] > 0)
    neg = len(over) - pos
    same_side = max(pos, neg) >= 3

    if delta_pair > p99 and delta_pair > 1.5 * delta_ctrl and same_side:
        verdict = "FEATURE_CANDIDATE"
    elif delta_pair > p99:
        verdict = "SURFACE_SEULE"
    else:
        verdict = "INCONCLUSIVE"
    return {
        "delta_pair": delta_pair,
        "delta_ctrl": delta_ctrl,
        "null_p99": p99,
        "ratio_vs_ctrl": delta_pair / max(delta_ctrl, 1e-12),
        "n_features_over3": int(len(over)),
        "n_over3_positive": int(pos),
        "n_over3_negative": int(neg),
        "top_features": sorted(
            ((int(f), float(z[f])) for f in np.argsort(np.abs(z))[::-1][:10]),
            key=lambda x: -abs(x[1]),
        ),
        "verdict": verdict,
    }
