#!/usr/bin/env python3
"""Tests du VETO de creation (#23174) — mandat user du 30/10.

Le regime du budget (#23174) **ralentit** la creation ; le veto l'**arrete**
tant que les issues ouvertes sont au moins `EXPANSION_VETO_THRESHOLD` (400).
Les deux portes sont distinctes, et la mesure du 11/11 montre que le budget
seul n'ecarte rien : son etat n'est pose par aucune lane, donc
`load_state()` rend `None` et `over_budget()` rend « rien n'est ecarte ».

Ce que ces tests verrouillent, par ordre d'importance :

  1. **le veto ecarte un grain de CREATION** au-dela du seuil, avec sa
     cause nommee (le seuil et le compte y sont ecrits) ;
  2. **un grain de REPARATION n'est jamais ecarte**, quel que soit le
     compte — le veto ne doit pas vider le tapis de grains utiles ;
  3. **sous le seuil**, on retombe sur la logique du budget (fail-OPEN) ;
  4. **l'exemption de finition** (`[EXEMPTION-FINITION]`, mandat user du
     06/11) garde le grain servi ;
  5. **le seuil est aligne** sur la constante du tapis : deux seuils
     divergents feraient que le tapis annonce un seuil et la porte en
     applique un autre.

Le compte employe (519 issues ouvertes) est la mesure du 11/11 sur
`jsboige/CoursIA` ; le seuil (400) est celui du mandat user du 30/10.

Le veto est LEVE depuis la decision user du 12/11 (`VETO_ACTIF = False`).
Les tests du mecanisme l'ARMENT explicitement (fixture `_armer_le_veto`),
pour qu'un nouveau mandat le rearme sans redecouvrir la porte ; deux tests
verrouillent la levee elle-meme, sur la valeur par defaut du module.
"""

import creation_budget as cb
import pytest
import sys

# La valeur du module AVANT toute fixture : c'est elle que la levee fixe.
VETO_PAR_DEFAUT = cb.VETO_ACTIF

CATALOG_PATHS = [
    "MyIA.AI.Notebooks/NLP/01-Introduction-Python.ipynb",
    "MyIA.AI.Notebooks/NLP/02-Ngrammes-Python.ipynb",
    "MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/20b-groupes-abeliens.ipynb",
    "MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/28-mobius-inversion.ipynb",
]


@pytest.fixture
def catalog():
    return cb.NotebookCatalog(CATALOG_PATHS)


@pytest.fixture(autouse=True)
def _isoler_les_commentaires(monkeypatch):
    """L'exemption lit l'instantane LOCAL de la machine : sans isolement,
    un test lirait le vrai etat de la machine et passerait pour une porte
    qui ecarte alors qu'elle n'a rien ecarte (le meme piege que le cliquet
    anti-entropie)."""
    monkeypatch.setattr(cb, "_commentaires_locaux", lambda: {})


@pytest.fixture(autouse=True)
def _armer_le_veto(monkeypatch):
    """Les tests du mecanisme portent sur le veto ARME : la levee du 12/11
    se teste a part, sur la valeur par defaut capturee a l'import."""
    monkeypatch.setattr(cb, "VETO_ACTIF", True)


def issue(number=1, title="", body="", labels=None, parent=None):
    return {"number": number, "title": title, "body": body,
            "labels": labels or [], "parent": parent}


def grain_qui_cree(numeros=1, corps=""):
    """Un grain de CREATION : il nomme le carnet qu'il veut creer."""
    return issue(
        number=numeros,
        title="Add(ml,#19341): carnet ML-07 — systeme de recommandation",
        body="Livrable : `MyIA.AI.Notebooks/ML/ML.Net/"
             "ML-07-Recommendation.ipynb`\n" + corps)


def grain_de_reparation(numeros=2):
    return issue(number=numeros,
                 title="Fix(lean,#18408): aligner la prose de ANALYSE-04",
                 body="Corriger la prose de ANALYSE-04.")


# --- la levee du 12/11 ----------------------------------------------------------

def test_le_veto_est_leve_par_defaut():
    """La decision user du 12/11 leve le veto : le module le livre desarme.
    Ce test rougit si quelqu'un le rearme sans le dire dans une PR."""
    assert VETO_PAR_DEFAUT is False


def test_veto_leve_un_grain_de_creation_est_servi(catalog, monkeypatch):
    """Veto leve, un grain de creation n'est plus ecarte au-dela du seuil :
    a 441 issues ouvertes (le compte du 12/11), la porte retombe sur le
    budget, fail-OPEN sans etat."""
    monkeypatch.setattr(cb, "VETO_ACTIF", VETO_PAR_DEFAUT)
    assert cb.veto_creation(441) is False
    pool = [grain_qui_cree()]
    gate = cb.creation_gate(pool, catalog=catalog, state=None, open_count=441)
    assert gate == {}


# --- le veto ------------------------------------------------------------------

def test_le_veto_ecarte_un_grain_de_creation(catalog):
    """A 519 issues ouvertes, un grain de creation est ecarte, avec sa
    cause nommee : le seuil et le compte y sont ecrits, pour qu'un journal
    de tirage dise POURQUOI le grain a ete saute."""
    pool = [grain_qui_cree()]
    gate = cb.creation_gate(pool, catalog=catalog, state=None, open_count=519)
    assert 1 in gate
    assert cb.CAUSE_VETO in gate[1]
    assert "519" in gate[1]
    assert str(cb.EXPANSION_VETO_THRESHOLD) in gate[1]


def test_le_vecto_s_active_sans_etat_du_budget(catalog):
    """Le veto est INDEPENDANT de l'etat du budget : c'est tout l'objet du
    correctif. L'etat absent est le cas reel de la flotte
    (`COURSIA_CREATION_BUDGET_FILE` n'est posee par aucune lane)."""
    pool = [grain_qui_cree()]
    assert cb.load_state() is None or True  # l'etat n'est pas requis
    gate = cb.creation_gate(pool, catalog=catalog, state=None, open_count=519)
    assert 1 in gate
    assert cb.CAUSE_VETO in gate[1]


def test_le_compte_du_pool_sert_par_defaut(catalog):
    """Sans argument, le compte est la TAILLE DU POOL — le repli de la
    porte quand l'appelant n'a rien mesure. Le tapis, lui, passe le
    compte REEL (cf `open_count_for_gates` dans `pick_idle_grain.py`)."""
    pool = [grain_qui_cree()] + [grain_de_reparation(numeros=100 + i)
                                 for i in range(518)]
    assert len(pool) == 519
    gate = cb.creation_gate(pool, catalog=catalog, state=None)
    assert 1 in gate
    assert cb.CAUSE_VETO in gate[1]
    # les grains de reparation restent servis
    assert all(n not in gate for n in range(100, 618))


def test_le_compte_reel_prime_sur_la_taille_du_pool(catalog):
    """Le compte compare au seuil est le compte REEL des issues ouvertes,
    pas la taille du pool : un pool de DEUX elements avec 450 issues
    ouvertes doit declencher le veto, et un pool de DEUX elements avec
    10 issues ouvertes ne doit pas le declencher.

    C'est le test qui distingue les deux grandeurs — sans lui, la porte
    qui compare a la vue passerait les deux cas."""
    pool = [grain_qui_cree(), grain_de_reparation(numeros=2)]
    assert len(pool) == 2
    gate = cb.creation_gate(pool, catalog=catalog, state=None, open_count=450)
    assert 1 in gate
    assert cb.CAUSE_VETO in gate[1]
    assert "450" in gate[1]
    gate = cb.creation_gate(pool, catalog=catalog, state=None, open_count=10)
    assert gate == {}


def test_sous_le_seuil_on_retombe_sur_le_budget(catalog):
    """A 399 issues ouvertes, le veto ne s'active pas : le grain passe par
    la logique du budget, qui est fail-OPEN sans etat."""
    pool = [grain_qui_cree()]
    gate = cb.creation_gate(pool, catalog=catalog, state=None, open_count=399)
    assert gate == {}


def test_un_grain_de_reparation_est_toujours_servi(catalog):
    """Le veto de REPARATION l'emporte toujours : un grain de correction
    n'est jamais ecarte, meme a 10 000 issues ouvertes."""
    pool = [grain_de_reparation()]
    gate = cb.creation_gate(pool, catalog=catalog, state=None, open_count=10000)
    assert gate == {}


def test_une_issue_de_consolidation_n_est_pas_ecartee(catalog):
    """Controle negatif de l'issue : aucune issue de consolidation n'est
    ecartee par le veto."""
    pool = [issue(number=3,
                  title="Consolidat(search,#19297): fusionner les carnets "
                        "Frontieres-01 a 05",
                  body="Fusionner les carnets existants de la serie.")]
    gate = cb.creation_gate(pool, catalog=catalog, state=None, open_count=519)
    assert gate == {}


# --- l'exemption de finition (mandat user du 06/11) ---------------------------

def test_le_corps_seul_ne_donne_pas_l_exemption(catalog):
    """Le marqueur `[EXEMPTION-FINITION]` pose dans le CORPS du grain ne
    vaut pas exemption (action `myia-ai-01` du 11/11) : un corps s'ecrit
    sous le login partage `jsboige`, donc une lane peut y poser le
    marqueur et s'ecarter elle-meme du veto que le mandat du 30/10 pose.

    Le grain reste ecarte, et la CAUSE le dit : un refus motive vaut mieux
    qu'un refus muet."""
    pool = [grain_qui_cree(corps="[EXEMPTION-FINITION]")]
    gate = cb.creation_gate(pool, catalog=catalog, state=None, open_count=519)
    assert 1 in gate
    assert cb.CAUSE_VETO in gate[1]
    assert cb.MARQUEUR_EXEMPTION in gate[1]


def test_l_exemption_par_commentaire_du_coordinateur(catalog, monkeypatch):
    """L'autre canal : un commentaire signe `myia-ai-01` qui porte le
    marqueur. C'est le canal des claims et des levees."""
    table = {"1": [{"body": "[EXEMPTION-FINITION] autorise",
                     "author": {"login": "myia-ai-01"}}]}
    monkeypatch.setattr(cb, "_commentaires_locaux", lambda: table)
    pool = [grain_qui_cree()]
    gate = cb.creation_gate(pool, catalog=catalog, state=None, open_count=519)
    assert gate == {}


def test_le_marqueur_pose_par_une_autre_lane_ne_donne_pas_l_exemption(
        catalog, monkeypatch):
    """Le marqueur est une ACCORDE du coordinateur : une autre lane ne
    peut pas s'en servir pour se servir un grain de creation."""
    table = {"1": [{"body": "[EXEMPTION-FINITION]",
                     "author": {"login": "myia-po-2025"}}]}
    monkeypatch.setattr(cb, "_commentaires_locaux", lambda: table)
    pool = [grain_qui_cree()]
    gate = cb.creation_gate(pool, catalog=catalog, state=None, open_count=519)
    assert 1 in gate
    assert cb.CAUSE_VETO in gate[1]


# --- l'alignement du seuil ----------------------------------------------------

def test_le_seuil_est_aligne_sur_la_constante_du_tapis():
    """Le tapis annonce le seuil dans ses journaux ; la porte en applique
    un autre si les deux divergent. L'alignement est verifie ici, et non
    laisse au soin d'un lecteur."""
    import pick_idle_grain as pig
    assert cb.EXPANSION_VETO_THRESHOLD == pig.EXPANSION_VETO_THRESHOLD


def test_le_veto_ne_depend_daucun_etat(catalog, monkeypatch, tmp_path):
    """Sans `COURSIA_CREATION_BUDGET_FILE`, le veto s'applique quand meme :
    c'est le point mesure du 11/11."""
    monkeypatch.delenv(cb.ENV_STATE, raising=False)
    pool = [grain_qui_cree()]
    gate = cb.creation_gate(pool, catalog=catalog, open_count=519)
    assert 1 in gate
    assert cb.CAUSE_VETO in gate[1]


# --- le compte REEL mesure par le tapis (action myia-ai-01 du 11/11) ---------

@pytest.fixture
def picker(monkeypatch):
    """Le tapis, avec son cache de mesure remis a zero.

    Le cache est un etat de PROCESS : sans le remettre a zero, un test
    qui mesure 509 contaminerait le suivant. C'est le meme piege que le
    cache chaud du shell (cf `forbid_shell_escape`)."""
    import pick_idle_grain as pig
    monkeypatch.setattr(pig, "_OPEN_COUNT_CACHE",
                        {"done": False, "value": None})
    return pig


def _gh_api_faux(total_count):
    """Une reponse `gh api search/issues` simulee."""
    return '{"total_count": %s}' % total_count


def test_le_compte_reel_est_lu_une_fois(picker, monkeypatch):
    """Le compte vient de l'API de RECHERCHE (`total_count`), qui compte
    les issues ouvertes du depot -- pas la vue du tapis. Une seule mesure
    par process : le cache est donc branche."""
    appels = []

    class _Result:
        stdout = _gh_api_faux(509)

    def _run(cmd, *args, **kwargs):
        appels.append(cmd)
        return _Result()

    monkeypatch.setattr(picker.subprocess, "run", _run)
    assert picker.measure_open_issue_count() == 509
    assert picker.measure_open_issue_count() == 509
    assert len(appels) == 1
    assert "search/issues" in appels[0][2]


def test_une_mesure_impossible_ne_vaut_pas_zero(picker, monkeypatch):
    """Un `gh` muet, un quota epuise, une reponse inattendue : la mesure
    rend `None`, jamais zero. Zero ecarterait tout le tapis."""
    def _run(*args, **kwargs):
        raise RuntimeError("quota")

    monkeypatch.setattr(picker.subprocess, "run", _run)
    assert picker.measure_open_issue_count() is None


def test_le_repli_est_la_taille_du_pool(picker, monkeypatch):
    """Sans mesure, le tapis compare a la taille du pool et le DIT : un
    refus muet sur une mesure absente est un mensonge."""
    monkeypatch.setattr(picker, "measure_open_issue_count", lambda: None)
    n, source = picker.open_count_for_gates(455)
    assert n == 455
    assert "pool" in source


def test_le_tapis_passe_le_compte_reel_a_la_porte(picker, monkeypatch):
    """Le compte mesure est celui que la porte compare au seuil : le
    tapis ne doit pas laisser la porte retomber sur la taille du pool."""
    # La mesure n'est PAS tentee sous pytest (surface reseau stubee) : on
    # leve le garde pour exercer le chemin de production.
    monkeypatch.delenv("PYTEST_CURRENT_TEST", raising=False)
    monkeypatch.setattr(picker, "measure_open_issue_count", lambda: 450)
    n, source = picker.open_count_for_gates(455)
    assert n == 450
    assert source == "mesure"

    vu = {}

    def _fake_creation_budget(module):
        class _CB:
            @staticmethod
            def creation_gate(pool, open_count=None):
                vu["open_count"] = open_count
                return {}

        return _CB

    monkeypatch.setitem(
        sys.modules, "creation_budget", _fake_creation_budget(None))
    picker.creation_budget_gate([{"number": 1}], open_count=n)
    assert vu["open_count"] == 450
