"""Tests gh_etag -- lectures REST conditionnelles persistees (#26260 extension).

Hermetiques : `subprocess.run` de gh_etag est remplace par un faux ; le cache
vit dans tmp_path via COURSIA_GH_ETAG_DIR. Les invariants testes sont ceux du
corps de gh_etag.py : un 304 sert le corps certifie inchange, tout echec
non-304 reste un echec, un cache corrompu coute un 200 (jamais un verdict).

Le faux reproduit la mesure #26260 : `gh api -i` sort en rc=1 sur un 304
(stdout `HTTP/2.0 304 Not Modified`, stderr `gh: HTTP 304`).
"""
import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent


def _charger(nom: str):
    """Charge un module de scripts/ par son fichier (patron des tests B.0 :
    scripts/ n'est pas un package depuis n'importe quel cwd). #13737 tranche 2 :
    gh_etag vit dans scripts/ci/, les autres candidats restent a la racine."""
    candidats = [HERE.parent / f"{nom}.py", HERE.parent / "ci" / f"{nom}.py"]
    chemin = next((c for c in candidats if c.exists()), None)
    assert chemin is not None, f"module introuvable pour les tests : {nom}"
    spec = importlib.util.spec_from_file_location(nom, chemin)
    module = importlib.util.module_from_spec(spec)
    sys.modules[nom] = module
    spec.loader.exec_module(module)
    return module


gh_etag = _charger("gh_etag")


class FauxGh:
    """200 (avec Etag) sans `If-None-Match`, 304 (rc=1, mesure #26260) avec.
    Enregistre chaque argv emis."""

    def __init__(self, etag: str, corps: dict):
        self.etag, self.corps = etag, corps
        self.argv_emis: list[list[str]] = []

    def __call__(self, cmd, **kwargs):
        self.argv_emis.append(list(cmd))
        assert cmd[:2] == ["gh", "api"]
        argv = [str(a) for a in cmd]
        if any(a.startswith("If-None-Match:") for a in argv):
            return subprocess.CompletedProcess(
                cmd, 1, stdout="HTTP/2.0 304 Not Modified\n\n",
                stderr="gh: HTTP 304")
        texte = json.dumps(self.corps)
        return subprocess.CompletedProcess(
            cmd, 0, stdout=f"HTTP/2.0 200 OK\nEtag: {self.etag}\n\n{texte}",
            stderr="")


@pytest.fixture(autouse=True)
def cache_isole(tmp_path, monkeypatch):
    """Cache dans tmp_path, store memoire et compteurs remis a zero.

    Re-active EXPLICITEMENT l'ETag : le conftest de scripts/tests le
    desactive pour tout test (filet #26631), et ce fichier teste precisement
    le chemin conditionnel -- son autouse conftest court avant celui-ci.
    """
    monkeypatch.setenv("COURSIA_GH_ETAG", "1")
    monkeypatch.setenv("COURSIA_GH_ETAG_DIR", str(tmp_path / "etag"))
    gh_etag.reset_for_tests()
    yield
    gh_etag.reset_for_tests()


def _lancer(monkeypatch, faux):
    monkeypatch.setattr(gh_etag.subprocess, "run", faux)
    return gh_etag.conditional_get("repos/jsboige/CoursIA/issues/42")


def test_200_frais_est_servi_et_stocke(tmp_path, monkeypatch):
    corps = {"number": 42, "body": "x"}
    faux = FauxGh('W/"abc"', corps)
    lu, servi_304 = _lancer(monkeypatch, faux)
    assert (lu, servi_304) == (corps, False)
    # Aucun If-None-Match au premier appel : rien en cache.
    assert not any(str(a).startswith("If-None-Match:") for a in faux.argv_emis[0])
    # Le store persiste l'assoc (etag, corps).
    ecrit = json.loads((tmp_path / "etag" / "cache.json").read_text(encoding="utf-8"))
    assert ecrit["repos/jsboige/CoursIA/issues/42"] == ['W/"abc"', corps]


def test_304_reutilise_le_corps_en_cache(tmp_path, monkeypatch):
    corps = {"number": 42, "body": "x"}
    faux = FauxGh('W/"abc"', corps)
    _lancer(monkeypatch, faux)  # amorce le store
    lu, servi_304 = _lancer(monkeypatch, faux)
    assert servi_304 is True
    assert lu == corps
    # L'etag stocke a bien ete renvoye en If-None-Match.
    assert any(a == 'If-None-Match: W/"abc"' for a in faux.argv_emis[1])
    assert gh_etag.HITS_304 == 1


def test_controle_negatif_502_avec_corps_en_cache_reste_un_echec(
        tmp_path, monkeypatch):
    """Le controle negatif du mandat : un etat d'erreur ne reutilise JAMAIS
    le corps cache -- sinon un etat perime produirait un verdict de merge."""
    corps = {"number": 42}
    faux = FauxGh('W/"abc"', corps)
    _lancer(monkeypatch, faux)  # amorce le store

    def _502(cmd, **kwargs):
        return subprocess.CompletedProcess(
            cmd, 1, stdout="HTTP/2.0 502 Bad Gateway\n\n",
            stderr="gh: HTTP 502")

    monkeypatch.setattr(gh_etag.subprocess, "run", _502)
    with pytest.raises(subprocess.CalledProcessError):
        gh_etag.conditional_get("repos/jsboige/CoursIA/issues/42")
    assert gh_etag.HITS_304 == 0


def test_controle_negatif_cache_corrompu_lecture_directe(tmp_path, monkeypatch):
    """Un cache.json illisible n'est PAS un verdict : lecture non
    conditionnelle (le faux sert son 200), le store est re-ecrit propre."""
    dossier = tmp_path / "etag"
    dossier.mkdir()
    (dossier / "cache.json").write_text("{corrompu", encoding="utf-8")
    corps = {"number": 42}
    faux = FauxGh('W/"n"', corps)
    lu, servi_304 = _lancer(monkeypatch, faux)
    assert (lu, servi_304) == (corps, False)
    assert not any(str(a).startswith("If-None-Match:") for a in faux.argv_emis[0])
    ecrit = json.loads((dossier / "cache.json").read_text(encoding="utf-8"))
    assert "repos/jsboige/CoursIA/issues/42" in ecrit


def test_controle_negatif_304_sans_corps_en_cache_est_bruyant(monkeypatch):
    """Le serveur certifie un etat que le store ne peut plus produire :
    erreur NON AVALEE, jamais un corps fabrique."""

    def _304_nu(cmd, **kwargs):
        return subprocess.CompletedProcess(
            cmd, 1, stdout="HTTP/2.0 304 Not Modified\n\n",
            stderr="gh: HTTP 304")

    monkeypatch.setattr(gh_etag.subprocess, "run", _304_nu)
    with pytest.raises(subprocess.CalledProcessError):
        gh_etag.conditional_get("repos/jsboige/CoursIA/issues/42")


def test_le_corps_servi_est_un_deepcopy(tmp_path, monkeypatch):
    corps = {"number": 42, "liste": [1, 2]}
    faux = FauxGh('W/"abc"', corps)
    _lancer(monkeypatch, faux)
    lu, _ = _lancer(monkeypatch, faux)  # servi par 304
    lu["liste"].append(3)
    # Le store n'a pas ete mute par l'appelant.
    ecrit = json.loads((tmp_path / "etag" / "cache.json").read_text(encoding="utf-8"))
    assert ecrit["repos/jsboige/CoursIA/issues/42"][1]["liste"] == [1, 2]


def test_desactivation_et_redirection_par_env(monkeypatch):
    monkeypatch.setenv("COURSIA_GH_ETAG", "0")
    assert gh_etag.cache_dir() is None
    monkeypatch.setenv("COURSIA_GH_ETAG", "off")
    assert gh_etag.cache_dir() is None
    monkeypatch.delenv("COURSIA_GH_ETAG")
    monkeypatch.setenv("COURSIA_GH_ETAG_DIR", "/quelque/part")
    assert gh_etag.cache_dir() == Path("/quelque/part")


def test_plafond_entrees_eviction_ancienne(tmp_path, monkeypatch):
    """Au-dela de MAX_ENTRIES, la plus ancienne insertion part : une entree
    evictee ne coute qu'un 200, jamais un verdict."""
    for i in range(gh_etag.MAX_ENTRIES + 5):
        monkeypatch.setattr(
            gh_etag.subprocess, "run", FauxGh(f'W/"e{i}"', {"i": i}))
        gh_etag.conditional_get(f"repos/jsboige/CoursIA/issues/{i}")
    ecrit = json.loads((tmp_path / "etag" / "cache.json").read_text(encoding="utf-8"))
    assert len(ecrit) == gh_etag.MAX_ENTRIES
    assert "repos/jsboige/CoursIA/issues/0" not in ecrit
    assert f"repos/jsboige/CoursIA/issues/{gh_etag.MAX_ENTRIES + 4}" in ecrit


def test_corps_trop_gros_servi_mais_non_stocke(tmp_path, monkeypatch):
    """Un blob base64 geant ne doit pas faire du cache le plus gros objet de
    la machine : servi (200 frais), jamais stocke -- la lecture suivante
    reste non conditionnelle."""
    gros = {"number": 42, "blob": "x" * (gh_etag.BODY_MAX_BYTES + 10)}
    faux = FauxGh('W/"gros"', gros)
    lu, servi_304 = _lancer(monkeypatch, faux)
    assert lu == gros and servi_304 is False
    assert not (tmp_path / "etag" / "cache.json").exists()
    # Deuxieme lecture : aucun If-None-Match (rien en stock).
    _lancer(monkeypatch, faux)
    assert not any(str(a).startswith("If-None-Match:")
                   for a in faux.argv_emis[1])


def test_sans_cache_le_chemin_d_origine_est_pris(monkeypatch):
    """#26631 (CR coordinateur), geste 1 : sans dossier de cache --
    COURSIA_GH_ETAG=0, ou machine sans LOCALAPPDATA/APPDATA (runner Linux)
    -- `etag_applicable` rend None et l'appelant reste sur son chemin
    d'origine OCTET POUR OCTET. Le conditionnel ne doit jamais changer la
    forme de l'appel quand il n'y a rien a revalider."""
    ok = ["api", "repos/jsboige/CoursIA/issues/42"]
    monkeypatch.setenv("COURSIA_GH_ETAG", "0")
    assert gh_etag.cache_dir() is None
    assert gh_etag.etag_applicable(ok) is None
    # Meme verdict sans variable de desactivation, base locale absente
    # (le cas du runner Linux du run 43651006619).
    monkeypatch.delenv("COURSIA_GH_ETAG")
    monkeypatch.delenv("COURSIA_GH_ETAG_DIR")
    monkeypatch.delenv("LOCALAPPDATA", raising=False)
    monkeypatch.delenv("APPDATA", raising=False)
    assert gh_etag.cache_dir() is None
    assert gh_etag.etag_applicable(ok) is None


def test_etag_applicable_filtre_les_argv():
    """Seul `api repos/...` nu est conditionnable : --paginate (pages
    internes a la CLI), --jq (corps transforme), graphql (pas d'ETag) et
    `pr view` restent sur le chemin d'origine."""
    ok = ["api", "repos/jsboige/CoursIA/issues/42"]
    assert gh_etag.etag_applicable(ok) == "repos/jsboige/CoursIA/issues/42"
    assert gh_etag.etag_applicable(
        ["api", "repos/x/y/pulls/7/reviews", "--paginate"]) is None
    assert gh_etag.etag_applicable(
        ["api", "repos/x/y/commits/a/check-runs?per_page=100",
         "--paginate", "--jq", ".x"]) is None
    assert gh_etag.etag_applicable(
        ["api", "graphql", "-f", "query=x"]) is None
    assert gh_etag.etag_applicable(
        ["pr", "view", "7", "--json", "state"]) is None
    assert gh_etag.etag_applicable(["api", "user"]) is None


def test_b0_gh_json_route_le_rest_conditionnable(monkeypatch):
    """B.0 : le funnel `gh_json` sert un 304 par gh_etag, compte `rest_304`,
    et la projection du payload s'applique AUSSI au corps servi par 304."""
    nits = _charger("check_unaddressed_nits")

    def _cond(path, timeout=None):
        return ({"number": 42, "title": "T", "body": "B", "state": "open"}, True)

    monkeypatch.setattr(nits.gh_etag, "conditional_get", _cond)
    monkeypatch.setattr(nits.gh_etag, "etag_applicable",
                        lambda args: "repos/jsboige/CoursIA/issues/42"
                        if args[:2] == ["api", "repos/jsboige/CoursIA/issues/42"]
                        else None)
    nits.API_USAGE["rest_304"] = 0
    lu = nits.gh_json(["api", "repos/jsboige/CoursIA/issues/42"])
    # La projection issues/{n} s'applique AU corps servi par 304 : les quatre
    # champs lus passent, `number` (jamais lu) est projete dehors.
    assert lu == {"title": "T", "body": "B", "state": "open"}
    assert nits.API_USAGE["rest_304"] == 1

    # Un argv non applicable ne touche pas gh_etag : chemin subprocess d'origine.
    def _boom(*a, **k):
        raise AssertionError("gh_etag ne doit pas etre appele")

    monkeypatch.setattr(nits.gh_etag, "conditional_get", _boom)
    monkeypatch.setattr(
        nits.subprocess, "run",
        lambda cmd, **k: subprocess.CompletedProcess(
            cmd, 0,
            stdout=json.dumps([{"id": 7, "user": {"login": "jsboige"},
                                "body": "bruit"}]),
            stderr=""))
    lu = nits.gh_json(["api", "repos/jsboige/CoursIA/pulls/7/reviews",
                       "--paginate"])
    # La projection B.0 des reviews garde (id, user.login) et omet le bruit.
    assert lu == [{"id": 7, "user": {"login": "jsboige"}}]


def test_check_run_state_run_gh_sert_le_304(monkeypatch):
    """check_run_state : `_run_gh` rend toujours du texte JSON ; un 304 y
    passe sans changer le contrat (str), un echec reste un RuntimeError."""
    m = _charger("check_run_state")
    monkeypatch.setattr(
        m.gh_etag, "conditional_get",
        lambda path, timeout=None: ({"head": {"sha": "ab"}}, True))
    texte = m._run_gh(["api", "repos/jsboige/CoursIA/pulls/7"])
    assert json.loads(texte)["head"]["sha"] == "ab"

    def _echec(path, timeout=None):
        raise subprocess.CalledProcessError(1, ["gh"], stderr="gh: HTTP 502")

    monkeypatch.setattr(m.gh_etag, "conditional_get", _echec)
    with pytest.raises(RuntimeError):
        m._run_gh(["api", "repos/jsboige/CoursIA/pulls/7"])
