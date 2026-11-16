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
# (Probas/Causalite/) au sys.path.
_PARENT_DIR = Path(__file__).resolve().parent.parent
if str(_PARENT_DIR) not in sys.path:
    sys.path.insert(0, str(_PARENT_DIR))

import dowhy_discovery_organs as ddo

# Chemin du notebook consommateur (relatif a ce test).
NB_PATH = _PARENT_DIR / "Causalite-04-DoWhy-Decouverte-Structure-Python.ipynb"

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


def _cellule_contenant(nb_path: Path, marqueur: str) -> str:
    """Source de la premiere cellule CODE contenant le marqueur.

    Robuste aux enrichissements markdown : retrouver une cellule par son
    appel d'organe ne casse pas quand une cellule pedagogique s'insere.
    """
    nb = json.load(open(nb_path, encoding="utf-8"))
    for cell in nb["cells"]:
        if cell["cell_type"] == "code" and marqueur in "".join(cell["source"]):
            return "".join(cell["source"])
    raise AssertionError(f"aucune cellule code ne contient {marqueur!r}")


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
    """La cellule PC reference ddo.executer_pc.

    La cellule est retrouvee par contenu (appel de l'organe), pas par index
    fige : sous enrichissement markdown pedagogique, l'index a deja glisse
    deux fois (7 puis 6) et cassait le test a chaque fois.
    """
    src = _cellule_contenant(NB_PATH, "ddo.executer_pc")
    assert "alpha=0.01" in src, (
        "le notebook motive alpha=0.01 pour PC (v-structure robuste 20/20)"
    )


# ---------------------------------------------------------------------------
# (i) Metrique d'erreur commune et baselines triviales
# ---------------------------------------------------------------------------
# Ces tests couvrent l'apport de l'issue #24301 : un contre-resultat
# (LiNGAM faux sous bruit gaussien) n'est lisible que compare a des
# baselines triviales mesurees sur la MEME metrique (SHD).
#
# Les valeurs attendues sont celles mesurees par probe_baselines.py sur
# ce monde (n=2000) :
#   baseline "ordre chronologique" (chaine)  SHD 1  (4/5 de squelette)
#   baseline "ordre inverse" (chaine)         SHD 5  (4 inverses + 1 manquante)
#   baseline "DAG complet"                    SHD 5  (5 parasites)
#   tirage aleatoire (DAG complet, 200)       SHD min 5, moyenne 7.5
#   LiNGAM seed=42 sur bruit GAUSSIEN         SHD 4  (3 correctes, 2 inverses, 2 parasites)
#   LiNGAM seed=42 sur bruit NON gaussien     SHD 0  (DAG exact)


def test_distance_structurelle_dag_exact_vaut_zero():
    """Le DAG vrai lui-meme a un SHD de 0 : la metrique est bien calibration."""
    exact = ddo.ResultatDecouverte(
        methode="TEST",
        aretes_orientees=sorted(ddo.ARETES_DAG_VRAI),
        aretes_non_orientees=[],
        ordre_causal=list(ddo.ORDRE_COLONNES),
    )
    d = ddo.distance_structurelle(exact)
    assert d["shd"] == 0
    assert d["squelette"] == 5, "le compte du squelette est un entier"
    assert d["squelette_texte"] == "5/5", "la forme textuelle est portee a part"
    assert d["orientees_correctes"] == 5
    assert d["inverses"] == []
    assert d["parasites"] == []
    assert d["manquantes"] == []


def test_distance_structurelle_compte_chaque_categorie_une_fois():
    """SHD = inverses + ambigues + parasites + manquantes (chacune une fois)."""
    df_g = ddo.generer_donnees_decouverte(seed=42)
    res = ddo.executer_lingam(df_g)
    d = ddo.distance_structurelle(res)
    total = (len(d["inverses"]) + len(d["ambigues"])
             + len(d["parasites"]) + len(d["manquantes"]))
    assert d["shd"] == total, (
        f"SHD {d['shd']} incoherent avec les categories {total}"
    )
    assert d["shd"] == 4, f"SHD mesure de LiNGAM gaussien seed=42 attendu 4, recu {d['shd']}"


def test_baseline_ordre_chaine_vaut_moins_que_lingam_gaussien():
    """La baseline "ordre chronologique" (chaine) : SHD 1, il manque (C, Y)."""
    res = ddo.baseline_ordre(ddo.ORDRE_COLONNES)
    d = ddo.distance_structurelle(res)
    assert res.methode == "BASELINE_ORDRE"
    assert len(res.aretes_orientees) == 4
    assert d["shd"] == 1
    assert d["squelette"] == 4
    assert d["squelette_texte"] == "4/5"
    assert d["manquantes"] == [("C", "Y")]
    assert d["parasites"] == []


def test_baseline_ordre_inverse_compte_les_inversions():
    """La chaine inverse : 4 aretes a l'envers + 1 vraie arete manquante."""
    res = ddo.baseline_ordre(list(reversed(ddo.ORDRE_COLONNES)))
    d = ddo.distance_structurelle(res)
    assert d["shd"] == 5
    assert len(d["inverses"]) == 4
    assert len(d["manquantes"]) == 1
    assert d["parasites"] == []


def test_baseline_ordre_complet_rend_le_dag_complet():
    """Le DAG complet : 10 aretes, dont 5 parasites -> SHD 5."""
    res = ddo.baseline_ordre(ddo.ORDRE_COLONNES, complet=True)
    d = ddo.distance_structurelle(res)
    assert len(res.aretes_orientees) == 10
    assert d["shd"] == 5
    assert len(d["parasites"]) == 5
    assert d["manquantes"] == []
    assert d["inverses"] == []


def test_baseline_aleatoire_est_reproductible():
    """Meme seed -> meme suite de tirages (RandomState locale)."""
    a = ddo.baseline_aleatoire(n_tirages=10, seed=0)
    b = ddo.baseline_aleatoire(n_tirages=10, seed=0)
    assert [r.aretes_orientees for r in a] == [r.aretes_orientees for r in b]


def test_baseline_aleatoire_ne_peut_pas_faire_mieux_que_le_complet():
    """Un DAG complet tire au sort porte 10 aretes : SHD >= 5 toujours.

    Borne deterministe (pas une mesure de moyenne) : sur 5 noeuds, un
    graphe complet contient 10 aretes ; le pire cas est 10/5 vraies
    presentes -> 0 parasite et 0 manquante... mais il faut qu'il contienne
    les 5 vraies, ce qui donne SHD 5 (les 5 autres sont parasites). Le
    minimum atteignable est donc 5.
    """
    tirages = ddo.baseline_aleatoire(n_tirages=30, seed=0, complet=True)
    shds = [ddo.distance_structurelle(t)["shd"] for t in tirages]
    assert min(shds) >= 5, f"SHD {min(shds)} sous la borne 5"
    assert all(t.methode == "BASELINE_ALEATOIRE" for t in tirages)


def test_classer_par_shd_est_trie_et_deterministe():
    """Le classement est trie par SHD croissant, et l'egalite est Alphabetique."""
    cands = {
        "DAG complet": ddo.baseline_ordre(ddo.ORDRE_COLONNES, complet=True),
        "ordre chronologique (chaine)": ddo.baseline_ordre(ddo.ORDRE_COLONNES),
        "ordre inverse (chaine)": ddo.baseline_ordre(list(reversed(ddo.ORDRE_COLONNES))),
    }
    classement = ddo.classer_par_shd(cands)
    shds = [d["shd"] for _, d in classement]
    assert shds == sorted(shds)
    assert classement[0][0] == "ordre chronologique (chaine)", (
        f"la baseline triviale doit venir en tete du classement, "
        f"recu {classement[0][0]}"
    )
    # egalite -> ordre alphabetique (determinisme)
    classement2 = ddo.classer_par_shd(dict(reversed(list(cands.items()))))
    assert [n for n, _ in classement] == [n for n, _ in classement2]


def test_classer_par_shd_lingam_non_gaussien_devance_tout():
    """Regime TENU : LiNGAM est exact (SHD 0) et passe devant toutes les baselines."""
    df_ng = ddo.generer_donnees_decouverte(bruit="non_gaussien", seed=42)
    cands = {
        "LiNGAM (seed=42)": ddo.executer_lingam(df_ng),
        "ordre chronologique (chaine)": ddo.baseline_ordre(ddo.ORDRE_COLONNES),
        "ordre inverse (chaine)": ddo.baseline_ordre(list(reversed(ddo.ORDRE_COLONNES))),
        "DAG complet": ddo.baseline_ordre(ddo.ORDRE_COLONNES, complet=True),
    }
    classement = ddo.classer_par_shd(cands)
    assert classement[0][0] == "LiNGAM (seed=42)"
    assert classement[0][1]["shd"] == 0
    assert classement[1][1]["shd"] >= 1


def test_classer_par_shd_baseline_triviale_devance_lingam_gaussien():
    """Regime VIOLE : la baseline triviale passe devant LiNGAM.

    C'est le resultat central de l'issue #24301 : le contre-resultat de
    la section 6 n'est pas « le moteur est inutile » mais « le moteur
    est moins bon qu'une hypothese qu'un praticien pose sans regarder les
    donnees ».
    """
    df_g = ddo.generer_donnees_decouverte(seed=42)
    cands = {
        "LiNGAM (seed=42)": ddo.executer_lingam(df_g),
        "ordre chronologique (chaine)": ddo.baseline_ordre(ddo.ORDRE_COLONNES),
    }
    classement = ddo.classer_par_shd(cands)
    assert classement[0][0] == "ordre chronologique (chaine)", (
        f"la baseline triviale doit devancer LiNGAM en regime viole, "
        f"classement = {[(n, d['shd']) for n, d in classement]}"
    )
    assert classement[0][1]["shd"] == 1
    assert classement[1][1]["shd"] == 4


def test_tableau_classement_contient_entete_et_methodes():
    """Le tableau rendu est lisible : entete, une ligne par methode, SHD trie."""
    cands = {
        "LiNGAM (seed=42)": ddo.executer_lingam(ddo.generer_donnees_decouverte(seed=42)),
        "ordre chronologique (chaine)": ddo.baseline_ordre(ddo.ORDRE_COLONNES),
    }
    txt = ddo.tableau_classement(cands, titre="REGIME 1 -- test")
    assert txt.startswith("REGIME 1 -- test")
    assert "SHD" in txt and "aretes" in txt and "parasites" in txt
    assert "LiNGAM (seed=42)" in txt
    assert "ordre chronologique (chaine)" in txt
    lignes = [l for l in txt.splitlines() if l.startswith("LiNGAM")
              or l.startswith("ordre chronologique")]
    assert len(lignes) == 2
    # colonnes a largeur fixe : le nom occupe 38 caracteres, puis un espace,
    # puis le SHD sur 4 caracteres (le nom contient des espaces -- un split()
    # serait trompeur)
    assert lignes[0][:38].strip() == "ordre chronologique (chaine)"
    assert lignes[0][39:43].strip() == "1"
    assert lignes[1][:38].strip() == "LiNGAM (seed=42)"
    assert lignes[1][39:43].strip() == "4"


def test_notebook_cellules_baselines_consomment_lorgane():
    """Anti-derive : les cellules de baselines du notebook consomment l'organe.

    Le notebook ne redéfinit ni la metrique (SHD) ni les baselines : il
    appelle les fonctions canoniques du module.
    """
    for marqueur in ("ddo.baseline_ordre", "ddo.distance_structurelle",
                     "ddo.tableau_classement"):
        src = _cellule_contenant(NB_PATH, marqueur)
        assert marqueur in src
    # le notebook ne redéfinit pas la métrique localement
    nb = json.load(open(NB_PATH, encoding="utf-8"))
    for cell in nb["cells"]:
        if cell["cell_type"] != "code":
            continue
        src = "".join(cell["source"])
        assert "def distance_structurelle" not in src, (
            "la métrique SHD ne doit pas être redéfinie dans le notebook"
        )
        assert "def baseline_ordre" not in src, (
            "les baselines ne doivent pas être redéfinies dans le notebook"
        )
        assert "def baseline_aleatoire" not in src, (
            "la baseline aléatoire ne doit pas être redéfinie dans le notebook"
        )
        assert "def tableau_classement" not in src, (
            "le tableau de classement ne doit pas être redéfini dans le notebook"
        )

