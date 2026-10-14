"""Tests du protocole Sona-like de RAG-02 §7 (issue #19521).

Contrat sur le notebook committé + propriete mathematique de la pseudo-replication.
Aucun modele, aucun reseau : le test verifie l'ARTEFACT (sources + sorties committes)
et l'arithmetique du test DM, pas une re-execution.

Corrige les defaults suivants (tous confirmes par reproduction, voir #19521) :
1. boucle "5 seeds" sans effet sur des configs deterministes -> 25 pseudo-replicats ;
2. DM compte n=25 alors que 5 observations independantes existent (t gonfle de sqrt(6)) ;
3. prose "MLP simple" sur des poids fixes [1.0, 0.1, 0.5] ;
4. HyDE+Rerank == Rerank par construction (top_k=10 > catalogue de 6) ;
5. reference arXiv fausse (2509.14471 = colloides Janus) + auteurs fabriques.
"""

import json
import math
from pathlib import Path

import numpy as np
import pytest
from scipy.stats import t as student_t

NB = Path(__file__).resolve().parents[1] / (
    "MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/02-Retrieval-Avance.ipynb"
)

pytestmark = pytest.mark.filterwarnings("ignore")


def _notebook():
    return json.loads(NB.read_text(encoding="utf-8"))


def _cells_of(nb, cell_type=None, containing=None):
    out = []
    for i, c in enumerate(nb["cells"]):
        if cell_type and c["cell_type"] != cell_type:
            continue
        src = "".join(c["source"])
        if containing and containing not in src:
            continue
        out.append((i, c, src))
    return out


def _stream_text(cell):
    return "".join(
        "".join(o.get("text", []))
        for o in cell.get("outputs", [])
        if o.get("output_type") == "stream"
    )


def _dm(e1, e2):
    """Replique fidele de diebold_mariano_ndcg du notebook (perte 1 - ndcg)."""
    a, b = np.asarray(e1, dtype=float), np.asarray(e2, dtype=float)
    d = (1 - a) - (1 - b)
    s_d = float(np.std(d, ddof=1))
    if s_d == 0:
        return 0.0, 1.0
    dm = float(np.mean(d)) / (s_d / math.sqrt(len(d)))
    p = 2 * (1 - student_t.cdf(abs(dm), df=len(d) - 1))
    return dm, p


# ---------------------------------------------------------------- math DM ---

def test_dm_pseudoreplication_inflation_is_sqrt6():
    """Recopier k=5 fois chaque observation gonfle le t d'un facteur exact sqrt(6).

    5 valeurs distinctes dupliquees 5x : meme moyenne, variance ddof=1 multipliee
    par 5/6, n multiplie par 5 -> t multiplie par sqrt(5 / (5/6)) = sqrt(6).
    """
    rng = np.random.default_rng(42)
    sona5 = rng.uniform(0.2, 0.5, 5)
    casc5 = sona5 + rng.uniform(-0.3, 0.4, 5)
    dm5, _ = _dm(sona5, casc5)
    dm25, _ = _dm(np.repeat(sona5, 5), np.repeat(casc5, 5))
    assert dm25 == pytest.approx(dm5 * math.sqrt(6), rel=1e-10)


def test_dm_on_5_users_is_inconclusive_at_alpha_5():
    """Sur les valeurs par utilisateur committes, p > 0.05 -> INCONCLUSIF.

    Valeurs lues dans la sortie fraiche de la cellule benchmark (deterministes :
    inf-CPU, reproductibles a l'identique d'une execution a l'autre).
    """
    sona5 = [0.2641, 0.3836, 0.2372, 0.4776, 0.3836]
    casc5 = [0.5013, 0.3836, 0.3066, 0.6797, 0.3836]
    dm, p = _dm(sona5, casc5)
    assert dm == pytest.approx(2.0312, abs=1e-3)
    assert p > 0.05  # 0.1121 : estimation ponctuelle pour la cascade, non significatif


def test_dm_on_pseudo_replicates_reproduces_old_beats_number():
    """Le dm=+4.9755 publie avant correction est exactement l'artefact sqrt(6)."""
    sona5 = [0.2641, 0.3836, 0.2372, 0.4776, 0.3836]
    casc5 = [0.5013, 0.3836, 0.3066, 0.6797, 0.3836]
    dm25, p25 = _dm(np.repeat(sona5, 5), np.repeat(casc5, 5))
    assert dm25 == pytest.approx(4.9755, abs=1e-3)
    assert p25 < 0.001  # l'ancien "p < 0.0001" n'etait PAS de l'information nouvelle


# ------------------------------------------------- contrat sur le notebook ---

def test_no_seed_loop_in_section7_benchmark():
    nb = _notebook()
    hits = _cells_of(nb, "code", containing="results_music")
    assert hits, "cellule benchmark §7 introuvable"
    _, _, src = hits[0]
    assert "for seed in SEEDS" not in src, "la boucle pseudo-replicative est de retour"
    assert "np.random.seed(seed)" not in src
    assert "torch.manual_seed(SEED)" in src  # seul alea (HyDE) explicitement fixe


def test_benchmark_output_reports_5_independent_observations():
    nb = _notebook()
    _, cell, _ = _cells_of(nb, "code", containing="results_music")[0]
    out = _stream_text(cell)
    assert "5 observations independantes" in out
    for user in ["Alice", "Bob", "Charlie", "Diana", "Eve"]:
        assert user in out
    # HyDE+Rerank == Rerank par utilisateur (visible dans la sortie par utilisateur)
    for line in out.splitlines():
        if "Rerank=" in line and "HyDE+Rerank=" in line:
            rk = float(line.split("Rerank=")[1].split()[0])
            hr = float(line.split("HyDE+Rerank=")[1].split()[0])
            assert rk == pytest.approx(hr, abs=1e-9)


def test_dm_cell_counts_users_not_pseudo_replicates():
    nb = _notebook()
    hits = _cells_of(nb, "code", containing="diebold_mariano_ndcg")
    assert hits
    _, cell, src = hits[0]
    out = _stream_text(cell)
    assert "verdict = INCONCLUSIVE" in out
    assert "n=5 utilisateurs" in out
    assert "df=4" in out or "df = 4" in src
    # le controle pedagogique nomme la pseudo-replication pour ce qu'elle est
    assert "pseudo-replication" in out
    assert "np.repeat(sona_vals, 5)" in src


def test_no_beats_cascade_anywhere():
    nb = _notebook()
    for c in nb["cells"]:
        blob = "".join(c["source"]) + _stream_text(c)
        assert "BEATS_CASCADE" not in blob, (
            f"verdict infonde BEATS_CASCADE dans cellule {nb['cells'].index(c)}"
        )


def test_sona_head_declared_fixed_weights_not_mlp():
    nb = _notebook()
    _, _, src = _cells_of(nb, "code", containing="def music_sona_like")[0]
    assert "POIDS FIXES" in src.upper()
    assert "weights = np.array([1.0, 0.1, 0.5])" in src  # comportement inchange
    intro = _cells_of(nb, "markdown", containing="Pont vers le catalogue musical")[0][2]
    assert "poids fixes" in intro
    assert "MLP" not in intro.replace("MLP réel de Sona est appris", "")


def test_arxiv_reference_is_sona_technical_report():
    nb = _notebook()
    intro = _cells_of(nb, "markdown", containing="Pont vers le catalogue musical")[0][2]
    assert "arXiv:2608.11015" in intro
    assert "2509.14471" not in intro  # colloides Janus, pas Sona
    assert "Udeneev" in intro
    # les auteurs fabriques de l'ancienne version ne doivent plus y figurer
    for fake in ["Miasnikov", "Ershov", "Gorodnichy"]:
        assert fake not in intro, f"auteur fabrique encore cite : {fake}"
    assert "Bibliographie IA\\MachineLearning" in intro  # chemin reel du gisement


def test_lecture_cell_names_limits_honestly():
    nb = _notebook()
    hits = _cells_of(nb, "markdown", containing="panel trop petit")
    assert hits, "cellule Lecture §7 introuvable"
    src = hits[0][2]
    assert "INCONCLUSIVE" in src
    assert "inter-utilisateurs" in src  # le sigma n'est plus vendu comme inter-seed
    # HyDE+Rerank == Rerank nomme explicitement
    assert "≡" in src or "==" in src
    assert "Rerank" in src
