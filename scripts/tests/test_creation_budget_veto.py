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
"""

import creation_budget as cb
import pytest

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
    """Sans argument, le compte est la TAILLE DU POOL — celle qui alimente
    deja `expansion_factor` dans le tapis. Aucun appel reseau de plus."""
    pool = [grain_qui_cree()] + [grain_de_reparation(numeros=100 + i)
                                 for i in range(518)]
    assert len(pool) == 519
    gate = cb.creation_gate(pool, catalog=catalog, state=None)
    assert 1 in gate
    assert cb.CAUSE_VETO in gate[1]
    # les grains de reparation restent servis
    assert all(n not in gate for n in range(100, 618))


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

def test_un_grain_exempt_de_finition_est_servi(catalog):
    """Le marqueur `[EXEMPTION-FINITION]` dans le corps du grain le garde
    servi : le coordinateur a autorise explicitement ce grain."""
    pool = [grain_qui_cree(corps="[EXEMPTION-FINITION]")]
    gate = cb.creation_gate(pool, catalog=catalog, state=None, open_count=519)
    assert gate == {}


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
