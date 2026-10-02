"""Tests for scripts/notebook_tools/auto_evaluation.py.

Couvre le contrat observe par l'organe `check_auto_evaluation_presence.py` :

- API publique : `question(enonce, choix, bonne, explication, moment)` + `bilan_session` + `MOMENTS`
- Moments valides : `avant` / `pendant` / `apres`
- Mode non-interactif (sans kernel Jupyter) : la fonction ne leve pas, rend
  `{"repondu": False, "bon": None}` -- conforme C.1 (pas d'erreur volontaire)
- Validation des arguments : moment invalide / choix vide / bonne absente
- Format de retour : dict avec les 6 champs attendus
- Comptage par moment via `bilan_session`
- Module importable avec la forme `from auto_evaluation import question`
  (cf regex de l'organe)
"""

import importlib.util
import sys
from pathlib import Path

# Charge explicitement `scripts/notebook_tools/auto_evaluation.py` par son
# path absolu. La CI Scripts Tests (CPU) ajoute `scripts/notebook_tools/tests`
# a sys.path, ce qui ferait resolver `import auto_evaluation` vers un fichier
# homonyme d'une autre serie (ex. MyIA.AI.Notebooks/ML/DataScienceWithAgents/
# auto_evaluation.py) et masquerait le nouveau module. Le chargement par
# fichier rend la resolution certaine, peu importe l'ordre de sys.path.
_MODULE_PATH = Path(__file__).resolve().parent.parent / "auto_evaluation.py"
_SPEC = importlib.util.spec_from_file_location("auto_evaluation", _MODULE_PATH)
auto_evaluation = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(auto_evaluation)
sys.modules["auto_evaluation"] = auto_evaluation

import pytest

MOMENTS = auto_evaluation.MOMENTS
bilan_session = auto_evaluation.bilan_session
question = auto_evaluation.question


# -----------------------------------------------------------------------------
# Tests de l'API publique et de la forme
# -----------------------------------------------------------------------------


def test_module_exposes_expected_names():
    """Le module exporte bien question, bilan_session, MOMENTS."""
    assert hasattr(auto_evaluation, "question")
    assert hasattr(auto_evaluation, "bilan_session")
    assert hasattr(auto_evaluation, "MOMENTS")
    assert "question" in auto_evaluation.__all__
    assert "bilan_session" in auto_evaluation.__all__
    assert "MOMENTS" in auto_evaluation.__all__


def test_moments_constant_matches_spec():
    """MOMENTS contient exactement les 3 moments reconnus par l'organe."""
    assert MOMENTS == ("avant", "pendant", "apres")


def test_module_importable_via_from_import():
    """Le contrat de l'organe est `from auto_evaluation import question`."""
    exec("from auto_evaluation import question", {})
    # Si on arrive ici sans ImportError, le contrat est respecte.


# -----------------------------------------------------------------------------
# Tests des arguments de `question`
# -----------------------------------------------------------------------------


def test_question_rejects_unknown_moment():
    with pytest.raises(ValueError, match="moment doit etre l'un de"):
        question(
            enonce="Q ?",
            choix=["a", "b"],
            bonne="a",
            explication="...",
            moment="pendant_la_cours",  # invalide
        )


def test_question_rejects_empty_choix():
    with pytest.raises(ValueError, match="choix ne peut pas etre vide"):
        question(
            enonce="Q ?",
            choix=[],
            bonne="a",
            explication="...",
            moment="avant",
        )


def test_question_rejects_bonne_not_in_choix():
    with pytest.raises(ValueError, match="ne se resout pas dans choix"):
        question(
            enonce="Q ?",
            choix=["a", "b"],
            bonne="z",
            explication="...",
            moment="avant",
        )


# -----------------------------------------------------------------------------
# Tests de la resolution par lettre (cas pedagogique des carnets)
# -----------------------------------------------------------------------------


def test_question_bonne_lettre_resolved_to_choix():
    """``bonne="B"`` se resout vers le 2e choix."""
    res = question(
        enonce="Q ?",
        choix=["alpha", "beta", "gamma"],
        bonne="B",
        explication="...",
        moment="avant",
        reponse="B",  # reponse par lettre
    )
    assert res["bon"] is True
    assert res["repondu"] is True


def test_question_bonne_texte_exact_accepte():
    """``bonne="beta"`` (texte exact) reste fonctionnel."""
    res = question(
        enonce="Q ?",
        choix=["alpha", "beta", "gamma"],
        bonne="beta",
        explication="...",
        moment="pendant",
        reponse="beta",
    )
    assert res["bon"] is True


def test_question_reponse_lettre_mauvaise():
    """Une reponse par lettre fausse est detectee comme incorrecte."""
    res = question(
        enonce="Q ?",
        choix=["alpha", "beta", "gamma"],
        bonne="A",
        explication="...",
        moment="apres",
        reponse="C",
    )
    assert res["bon"] is False
    assert res["reponse"] == "C"


def test_question_reponse_pre_remplie_skip_raw_input(monkeypatch):
    """Si ``reponse`` est fournie, on n'appelle PAS raw_input."""
    appels = []

    class _BoomIPython:
        kernel = True

        def raw_input(self, prompt):
            appels.append(prompt)
            raise AssertionError(
                "raw_input ne doit pas etre appele si reponse est fournie"
            )

    monkeypatch.setattr(
        auto_evaluation, "get_ipython", lambda: _BoomIPython(), raising=False
    )

    res = question(
        enonce="Q ?",
        choix=["a", "b"],
        bonne="a",
        explication="...",
        moment="pendant",
        reponse="a",
    )
    assert res["bon"] is True
    assert appels == []


def test_question_casse_lettre_minuscule_acceptee():
    """``reponse="b"`` (minuscule) est equivalent a ``reponse="B"``."""
    res = question(
        enonce="Q ?",
        choix=["alpha", "beta"],
        bonne="B",
        explication="...",
        moment="avant",
        reponse="b",
    )
    assert res["bon"] is True


# -----------------------------------------------------------------------------
# Tests du mode non-interactif (Papermill / kernel sans raw_input)
# -----------------------------------------------------------------------------


def test_question_non_interactive_does_not_raise():
    """Sans IPython kernel, question() rend sans lever (C.1, Papermill-safe)."""
    res = question(
        enonce="Test sans reponse",
        choix=["a", "b"],
        bonne="a",
        explication="explication",
        moment="avant",
    )
    assert isinstance(res, dict)


def test_question_non_interactive_returns_correct_shape():
    res = question(
        enonce="Test",
        choix=["a", "b"],
        bonne="a",
        explication="...",
        moment="pendant",
    )
    # Les 7 champs annonces dans la docstring doivent tous etre presents.
    assert set(res.keys()) == {
        "moment",
        "repondu",
        "bon",
        "reponse",
        "choix",
        "enonce",
        "explication",
    }
    assert res["moment"] == "pendant"
    assert res["enonce"] == "Test"
    assert res["choix"] == ["a", "b"]
    assert res["explication"] == "..."
    # En non-interactif, repondu=False, bon=None
    assert res["repondu"] is False
    assert res["bon"] is None
    assert res["reponse"] is None


def test_question_non_interactive_all_three_moments():
    """Les 3 moments sont acceptes en mode non-interactif sans lever."""
    for moment in MOMENTS:
        res = question(
            enonce=f"Q {moment}",
            choix=["x", "y"],
            bonne="x",
            explication="...",
            moment=moment,
        )
        assert res["moment"] == moment
        assert res["repondu"] is False


# -----------------------------------------------------------------------------
# Tests du mode interactif (simulation avec mock de get_ipython)
# -----------------------------------------------------------------------------


class _FakeKernel:
    """Simule un IPython kernel pour tester le mode interactif."""


class _FakeIPython:
    """Simule un IPython avec raw_input et un kernel."""

    def __init__(self, reponse: str) -> None:
        self.kernel = _FakeKernel()
        self._reponse = reponse
        self.calls: list[str] = []

    def raw_input(self, prompt: str) -> str:
        self.calls.append(prompt)
        return self._reponse


def _set_get_ipython(monkeypatch, ip):
    """`get_ipython` est injecte par IPython dans le namespace du module qui
    l'appelle au runtime. On l'injecte dans le namespace du module teste
    (meme technique que IPython lui-meme) -- `raising=False` car l'attribut
    n'existe pas en dehors d'un kernel IPython actif."""
    monkeypatch.setattr(auto_evaluation, "get_ipython", lambda: ip, raising=False)


def test_question_interactive_bonne_reponse(monkeypatch):
    """Si l'apprenant repond correctement, bon=True et repondu=True."""
    ip = _FakeIPython("a")
    _set_get_ipython(monkeypatch, ip)

    res = question(
        enonce="Q ?",
        choix=["a", "b"],
        bonne="a",
        explication="...",
        moment="pendant",
    )
    assert res["repondu"] is True
    assert res["bon"] is True
    assert res["reponse"] == "a"
    assert len(ip.calls) == 1


def test_question_interactive_mauvaise_reponse(monkeypatch):
    """Si l'apprenant repond mal, bon=False et repondu=True."""
    ip = _FakeIPython("b")
    _set_get_ipython(monkeypatch, ip)

    res = question(
        enonce="Q ?",
        choix=["a", "b"],
        bonne="a",
        explication="...",
        moment="apres",
    )
    assert res["repondu"] is True
    assert res["bon"] is False
    assert res["reponse"] == "b"


def test_question_interactive_normalisation_casse(monkeypatch):
    """La comparaison de la reponse est insensible a la casse et aux espaces."""
    ip = _FakeIPython("  A  ")
    _set_get_ipython(monkeypatch, ip)

    res = question(
        enonce="Q ?",
        choix=["a", "b"],
        bonne="a",
        explication="...",
        moment="avant",
    )
    assert res["bon"] is True


def test_question_interactive_input_vide(monkeypatch):
    """Entree vide -> raw_input rend "" -> repondu=True mais bon=False
    (ce n'est pas la meme chose que mode non-interactif). Le contrat du
    module : "" est une reponse valide qui se compare a "" -- un apprenant
    qui ne repond pas explicitement voit la correction."""
    ip = _FakeIPython("")
    _set_get_ipython(monkeypatch, ip)

    res = question(
        enonce="Q ?",
        choix=["a", "b"],
        bonne="a",
        explication="...",
        moment="pendant",
    )
    assert res["repondu"] is True
    assert res["bon"] is False
    assert res["reponse"] == ""


# -----------------------------------------------------------------------------
# Tests de bilan_session
# -----------------------------------------------------------------------------


def test_bilan_session_initial_vide():
    """bilan_session() demarre a 0 pour les 3 moments."""
    # Le registre interne est partage -- on documente l'etat apres
    # l'initialisation du module ; d'autres tests peuvent l'avoir peuple.
    comptes = bilan_session()
    assert set(comptes.keys()) == set(MOMENTS)
    for moment in MOMENTS:
        assert comptes[moment] >= 0


def test_bilan_session_compte_les_moments(monkeypatch):
    """bilan_session() cumule les questions par moment."""
    # On vide l'etat partage en rechargeant le module via le meme chemin
    # que l'init -- spec_from_file_location rend le reload possible.
    import importlib

    spec = importlib.util.spec_from_file_location("auto_evaluation", _MODULE_PATH)
    fresh = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(fresh)
    sys.modules["auto_evaluation"] = fresh
    # Mise a jour des noms du module global pour les asserts ci-dessous.
    globals()["question"] = fresh.question
    globals()["bilan_session"] = fresh.bilan_session
    globals()["MOMENTS"] = fresh.MOMENTS
    globals()["auto_evaluation"] = fresh

    # Mode non-interactif : on injecte un get_ipython qui rend None
    # dans le namespace du module (equivalent Papermill).
    monkeypatch.setattr(fresh, "get_ipython", lambda: None, raising=False)

    for moment in ("avant", "pendant", "apres", "avant"):
        question(
            enonce=f"Q {moment}",
            choix=["a", "b"],
            bonne="a",
            explication="...",
            moment=moment,
        )

    comptes = bilan_session()
    assert comptes["avant"] == 2
    assert comptes["pendant"] == 1
    assert comptes["apres"] == 1
