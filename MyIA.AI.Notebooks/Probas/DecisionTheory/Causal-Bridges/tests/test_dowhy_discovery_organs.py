"""Tests pytest pour dowhy_discovery_organs.py -- grain DoWhy-3 de l'issue #14049.

Issue #14049, acceptance 4 : « chaque notebook de la serie DoWhy expose
un organe importable des sa livraison, et les tests verifient la sortie
du module contre la valeur attendue ». Ce fichier EST le consommateur
externe de l'organe (avec le notebook).

Strategie de test (meme convention que test_dowhy_iv_organs.py) : on
**execute reellement** les algorithmes de causal-learn (pas de mock,
H.1) et on verifie que :

(a) ``generer_donnees_decouverte`` respecte la RandomState LOCALE et
    produit un bruit gaussien ou non gaussien selon le mode (kurtosis) ;
(b) ``ARETES_DAG_VRAI`` est bien un DAG 5 aretes a une seule
    v-structure C -> Y <- M ;
(c) PC (alpha=0.01) et GES rendent le CPDAG canonique sur donnees
    gaussiennes : squelette 5/5, v-structure orientee, C--X et X--M
    ambigues -- le verdict CPDAG_AMBIGU est un RESULTAT ;
(d) PC reste ambigu sur donnees NON gaussiennes (PC ne consomme pas la
    forme du bruit -- c'est le coeur du contraste avec LiNGAM) ;
(e) LiNGAM recouvre le DAG EXACT sur bruit non gaussien (5/5, ordre
    causal correct) et se trompe sur bruit gaussien (DAG faux rendu
    quand meme -- l'echec honnete documente) ;
(f) ``enumerer_extensions_acycliques`` rend exactement 3 extensions
    (pas 4) : l'orientation C->X + M->X est exclue car elle cree une
    v-structure a X que la donnee exclut ;
(g) ``effet_backdoor_depuis_aretes`` : les extensions valides du meme
    CPDAG donnent des estimands dowhy DIFFERENTS -- l'ambiguite se
    propage au chiffre ;
(h) anti-derive : la cellule DGP du notebook consomme l'organe et
    produit la meme DataFrame que l'appel direct du module.

Les tolerances sont celles de la serie : le monde est DGP-connu, les
coefficients sont forts (>= 0.3), n=2000 -- les resultats ci-dessus sont
stables sur 20/20 seeds (PC a alpha=0.01, GES) et 10/10 (LiNGAM non
gaussien), mesures avant l'ecriture de ces tests.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

# Import direct sans packaging : on ajoute le dossier parent
# (Probas/DecisionTheory/Causal-Bridges/) au sys.path.
_PARENT_DIR = Path(__file__).resolve().parent.parent
if str(_PARENT_DIR) not in sys.path:
    sys.path.insert(0, str(_PARENT_DIR))

import dowhy_discovery_organs as ddo

# Chemin du notebook consommateur (relatif a ce test).
NB_PATH = _PARENT_DIR / "DoWhy-3-Decouverte-de-Structure.ipynb"

# Le CPDAG canonique du monde par defaut (mesure, 20/20 seeds a alpha=0.01).
# Convention du module : les aretes non orientees sont rendues en tuple TRIE.
ORIENTEES_CANON = {("C", "Y"), ("M", "Y"), ("Y", "Z")}
AMBIGUES_CANON = {("C", "X"), ("M", "X")}


# ---------------------------------------------------------------------------
# (a) generer_donnees_decouverte
# ---------------------------------------------------------------------------
def test_generer_forme_et_colonnes():
    """Dimensions par defaut : n=2000 x 5 colonnes (C, X, M, Y, Z)."""
    df = ddo.generer_donnees_decouverte()
    assert isinstance(df, pd.DataFrame)
    assert df.shape == (2000, 5)
    assert list(df.columns) == ddo.ORDRE_COLONNES


def test_generer_seed_reproductible():
    """RandomState LOCAL : deux appels meme seed -> DataFrame egale."""
    pd.testing.assert_frame_equal(
        ddo.generer_donnees_decouverte(seed=42),
        ddo.generer_donnees_decouverte(seed=42),
    )


def test_generer_seed_change_impacte():
    """Deux seeds differentes -> deux DataFrames differentes."""
    assert not ddo.generer_donnees_decouverte(seed=42).equals(
        ddo.generer_donnees_decouverte(seed=43)
    )


def test_generer_bruit_non_gaussien_est_non_gaussien():
    """Mode non_gaussien : kurtosis excess >> 0 (exponentiel ~ 3)."""
    from scipy import stats as sps

    df_g = ddo.generer_donnees_decouverte(bruit="gaussien", seed=42)
    df_ng = ddo.generer_donnees_decouverte(bruit="non_gaussien", seed=42)
    k_g = sps.kurtosis(df_g["C"].values, fisher=True)
    k_ng = sps.kurtosis(df_ng["C"].values, fisher=True)
    assert abs(k_g) < 0.5, f"kurtosis gaussien attendu ~0, recu {k_g:.2f}"
    assert k_ng > 1.5, f"kurtosis exponentiel attendu ~3, recu {k_ng:.2f}"


def test_generer_meme_variance_entre_modes():
    """Les deux modes portent la meme variance de bruit (seul le kurtosis change)."""
    for col in ddo.ORDRE_COLONNES:
        v_g = ddo.generer_donnees_decouverte(bruit="gaussien", seed=42)[col].var()
        v_ng = ddo.generer_donnees_decouverte(bruit="non_gaussien", seed=42)[col].var()
        assert abs(v_g - v_ng) < 0.15 * v_g, (
            f"variance {col} : gaussien {v_g:.2f} vs non_gaussien {v_ng:.2f}"
        )


def test_generer_mode_invalide_leve():
    """Un mode de bruit inconnu est refuse explicitement."""
    with pytest.raises(ValueError):
        ddo.generer_donnees_decouverte(bruit="poissonien")


# ---------------------------------------------------------------------------
# (b) Le DAG vrai du simulateur
# ---------------------------------------------------------------------------
def test_aretes_dag_vrai_est_un_dag_acyclique():
    """5 aretes, acyclique, une seule v-structure C -> Y <- M."""
    import networkx as nx

    g = nx.DiGraph(ddo.ARETES_DAG_VRAI)
    assert g.number_of_edges() == 5
    assert nx.is_directed_acyclic_graph(g)
    assert ddo.v_structures(ddo.ARETES_DAG_VRAI) == [("C", "Y", "M")]


# ---------------------------------------------------------------------------
# (c) PC et GES : le CPDAG canonique sur donnees gaussiennes
# ---------------------------------------------------------------------------
def test_pc_alpha_001_cpdag_canonique():
    """PC : squelette 5/5, v-structure orientee, C--X et X--M ambigues."""
    df = ddo.generer_donnees_decouverte(seed=42)
    res = ddo.executer_pc(df, alpha=0.01)
    assert res.methode == "PC"
    assert set(res.aretes_orientees) == ORIENTEES_CANON
    assert set(res.aretes_non_orientees) == AMBIGUES_CANON
    comp = ddo.comparer_au_dag_vrai(res)
    assert comp["squelette_trouvees"] == "5/5"
    assert comp["parasites"] == []
    assert comp["manquantes"] == []
    assert set(comp["non_orientees_parmi_vraies"]) == AMBIGUES_CANON


def test_ges_cpdag_canonique():
    """GES rend le meme CPDAG que PC sur ce monde (20/20 seeds mesures)."""
    df = ddo.generer_donnees_decouverte(seed=42)
    res = ddo.executer_ges(df)
    assert res.methode == "GES"
    assert set(res.aretes_orientees) == ORIENTEES_CANON
    assert set(res.aretes_non_orientees) == AMBIGUES_CANON


def test_pc_sur_non_gaussien_reste_ambigu():
    """Point cle : PC ignore la forme du bruit -- l'ambiguite survit."""
    df_ng = ddo.generer_donnees_decouverte(bruit="non_gaussien", seed=42)
    res = ddo.executer_pc(df_ng, alpha=0.01)
    assert len(res.aretes_non_orientees) >= 1, (
        "PC ne doit pas trancher C--X meme sur bruit non gaussien "
        "(il ne consomme pas l'information de forme)"
    )


# ---------------------------------------------------------------------------
# (d) LiNGAM : exact sous non-gaussianite, faux-confiant sous gaussianite
# ---------------------------------------------------------------------------
def test_lingam_non_gaussien_recouvre_le_dag_exact():
    """LiNGAM : les 5 aretes exactes, ordre causal correct (10/10 seeds)."""
    df_ng = ddo.generer_donnees_decouverte(bruit="non_gaussien", seed=42)
    res = ddo.executer_lingam(df_ng)
    assert res.methode == "LiNGAM"
    assert res.aretes_non_orientees == []
    assert set(res.aretes_orientees) == set(ddo.ARETES_DAG_VRAI)
    assert res.ordre_causal == ["C", "X", "M", "Y", "Z"]
    comp = ddo.comparer_au_dag_vrai(res)
    assert comp["squelette_trouvees"] == "5/5"
    assert comp["oriente_inverse"] == []
    assert comp["parasites"] == []


def test_lingam_gaussien_rend_un_dag_faux():
    """L'echec honnete : sur bruit gaussien LiNGAM rend un DAG complet faux.

    Verifie sur seed=42 : 7 aretes dont 2 parasites et des inversions.
    Le module ne masque pas cet echec -- il l'expose (verdict DAG_ORIENTE
    + message de prudence).
    """
    df_g = ddo.generer_donnees_decouverte(seed=42)
    res = ddo.executer_lingam(df_g)
    assert res.aretes_non_orientees == []
    assert set(res.aretes_orientees) != set(ddo.ARETES_DAG_VRAI), (
        "sur bruit gaussien LiNGAM ne doit pas (par chance structurelle) "
        "rendre le DAG exact -- si c'est le cas, changer le seed du test"
    )
    v = ddo.verdict_cpdag(res)
    assert v["verdict"] == "DAG_ORIENTE"
    assert "HYPOTHESES" in v["message"]


# ---------------------------------------------------------------------------
# (e) Verdicts
# ---------------------------------------------------------------------------
def test_verdict_cpdag_ambigu_est_un_resultat():
    """PC -> CPDAG_AMBIGU : l'ambiguite est enseignee comme resultat."""
    res = ddo.executer_pc(ddo.generer_donnees_decouverte(seed=42), alpha=0.01)
    v = ddo.verdict_cpdag(res)
    assert v["verdict"] == "CPDAG_AMBIGU"
    assert v["n_aretes_non_orientees"] == 2
    assert set(v["aretes_non_orientees"]) == AMBIGUES_CANON
    assert "RESULTAT" in v["message"]


def test_verdict_cpdag_oriente_vient_des_hypotheses():
    """LiNGAM -> DAG_ORIENTE : l'orientation vient des hypotheses, message clair."""
    res = ddo.executer_lingam(
        ddo.generer_donnees_decouverte(bruit="non_gaussien", seed=42)
    )
    v = ddo.verdict_cpdag(res)
    assert v["verdict"] == "DAG_ORIENTE"
    assert v["n_aretes_non_orientees"] == 0


# ---------------------------------------------------------------------------
# (f) Classe d'equivalence : 3 extensions, pas 4
# ---------------------------------------------------------------------------
def test_extensions_acycliques_exactement_trois():
    """Le CPDAG canonique a 2 aretes ambigues mais SEULEMENT 3 extensions valides.

    L'orientation C->X + M->X est exclue : elle cree la v-structure
    C -> X <- M, absente des v-structures de reference du CPDAG.
    """
    res = ddo.executer_pc(ddo.generer_donnees_decouverte(seed=42), alpha=0.01)
    exts = ddo.enumerer_extensions_acycliques(res)
    assert len(exts) == 3, f"3 extensions attendues, {len(exts)} rendues : {exts}"
    assert sorted(ddo.ARETES_DAG_VRAI) in exts
    for ext in exts:
        assert ("C", "X") not in ext or ("M", "X") not in ext, (
            f"l'orientation C->X + M->X (v-structure exclue) est presente : {ext}"
        )


def test_extensions_lingam_est_lui_meme():
    """Sans aretes ambigues : l'unique extension est le DAG lui-meme."""
    res = ddo.executer_lingam(
        ddo.generer_donnees_decouverte(bruit="non_gaussien", seed=42)
    )
    exts = ddo.enumerer_extensions_acycliques(res)
    assert exts == [sorted(ddo.ARETES_DAG_VRAI)]


# ---------------------------------------------------------------------------
# (g) Pont dowhy : l'ambiguite se propage a l'estimand
# ---------------------------------------------------------------------------
def test_effet_backdoor_estimations_differentes_par_extension():
    """Meme CPDAG, memes donnees : 3 extensions -> 3 estimands differents.

    Valeurs mesurees (seed=42, delta=0.3) : vrai ~0.81 (ajustement {C}),
    extension sans confondeur ~1.05 (pas d'ajustement), extension qui
    ajuste le mediateur ~0.22 (ecrase l'effet). L'effet total vrai
    vaut beta_x_m * gamma_m_y = 0.8.
    """
    df = ddo.generer_donnees_decouverte(seed=42)
    res_pc = ddo.executer_pc(df, alpha=0.01)
    exts = ddo.enumerer_extensions_acycliques(res_pc)

    estimands = []
    for ext in exts:
        r = ddo.effet_backdoor_depuis_aretes(df, ext)
        estimands.append((r.ensemble_ajustement, r.estimate_value))
        assert -0.5 < r.estimate_value < 2.0

    valeurs = sorted(round(v, 3) for _, v in estimands)
    assert len(set(valeurs)) == 3, f"3 estimands distincts attendus : {valeurs}"

    r_vrai = ddo.effet_backdoor_depuis_aretes(df, ddo.ARETES_DAG_VRAI)
    assert r_vrai.ensemble_ajustement == ["C"]
    assert abs(r_vrai.estimate_value - 0.8) < 0.15, (
        f"estimand du DAG vrai ~0.8 attendu, recu {r_vrai.estimate_value:.3f}"
    )


# ---------------------------------------------------------------------------
# (h) Anti-derive : le notebook consomme l'organe
# ---------------------------------------------------------------------------
def _lire_cellule(nb_path: Path, cell_index: int) -> str:
    nb = json.load(open(nb_path, encoding="utf-8"))
    return "".join(nb["cells"][cell_index]["source"])


def test_notebook_cellule_dgp_byte_identique_module():
    """La cellule DGP (index 3) du notebook consomme l'organe, sans redefinition.

    Anti-derive (acceptance 4) : si quelqu'un recopiait la generation
    dans une fonction locale du notebook, ce test rougirait -- le
    notebook DOIT produire la meme DataFrame que l'appel canonique.
    """
    src = _lire_cellule(NB_PATH, 3)
    assert "ddo.generer_donnees_decouverte" in src, (
        "la cellule DGP du notebook doit appeler ddo.generer_donnees_decouverte"
    )
    g: dict = {"ddo": ddo}
    exec(compile(src, "<cellule-dgp>", "exec"), g)
    df_nb = g["df_monde"]
    pd.testing.assert_frame_equal(
        df_nb, ddo.generer_donnees_decouverte(n=2000, bruit="gaussien", seed=42)
    )


def test_notebook_cellule_pc_consomme_lorgane():
    """La cellule PC (index 6) reference ddo.executer_pc."""
    src = _lire_cellule(NB_PATH, 6)
    assert "ddo.executer_pc" in src
    assert "alpha=0.01" in src, (
        "le notebook motive alpha=0.01 pour PC (v-structure robuste 20/20)"
    )
