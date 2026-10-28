"""Tests de l'instantane local partage (#22630) et de la voie en processus.

Acceptance (issue #22630, body) :
- l'instantane est un cache **par issue** : frais pour une issue dont les
  commentaires viennent d'etre lus, perime pour une autre -- `serves()`
  distingue les deux ;
- une entree fraiche ne declenche **aucun** appel gh (passe chaude) ;
- le seam du lecteur de claims rend le payload de l'instantane **sans
  sous-processus**, et l'etat d'une PR sans `gh pr view` ;
- la voie en processus du tapis rend les memes codes de verdict que la voie
  historique -- meme fonction, memes arguments, par construction ;
- un lecteur introuvable rend None, et le tapis retombe sur la voie
  historique.

Aucun test ne touche le reseau : `_gh_api` est remplace par un faux, et la
racine de l'instantane est redirigee vers `tmp_path` (jamais le
`%LOCALAPPDATA%` reel de la machine).
"""

import json
import sys
import time
import types
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "coordination"))

import check_lane_claim as clc
import gh_snapshot as gs
import pick_idle_grain as pig


@pytest.fixture(autouse=True)
def _snapshot_root_isole(tmp_path, monkeypatch):
    """Racine de l'instantane redirigee : jamais le LOCALAPPDATA reel."""
    def _racine():
        return tmp_path / "gh-snapshot"

    monkeypatch.setattr(gs, "snapshot_root", _racine)
    # Le picker importe le module sous son nom de package
    # (`coordination.gh_snapshot`) alors que ce fichier l'importe en
    # top-level (`gh_snapshot`) : deux instances du meme fichier peuvent
    # sieger dans sys.modules. Si l'instance package existe, sa racine doit
    # etre isolee aussi -- sinon tout appel y passant (ex.
    # `_flush_repair_snapshot`) lirait ou ecrirait le %LOCALAPPDATA% reel
    # de la machine.
    instance_package = sys.modules.get("coordination.gh_snapshot")
    if instance_package is not None and instance_package is not gs:
        monkeypatch.setattr(instance_package, "snapshot_root", _racine)
    # Le lecteur ne doit garder aucun instantane entre deux tests.
    yield
    clc.set_snapshot(None)
    pig._PASS_SNAPSHOT = None
    pig._BELT_SNAPSHOT = None


def _redirige_gh_snapshot(monkeypatch, cible):
    """Redirige `from coordination import gh_snapshot` vers ``cible``.

    Le seul ``setitem(sys.modules, 'coordination.gh_snapshot', ...)`` est
    insuffisant : des qu'un test precedent a importe REELLEMENT le package,
    l'attribut ``gh_snapshot`` du module ``coordination`` est pose, et
    ``from coordination import gh_snapshot`` le lit SANS consulter
    ``sys.modules['coordination.gh_snapshot']`` -- le module reel (racine
    non isolee) reprend alors la main, avec ses appels gh et son
    ``%LOCALAPPDATA%``. On patche donc les DEUX surfaces : l'entree
    ``sys.modules`` ET l'attribut du package.
    """
    monkeypatch.setitem(sys.modules, "coordination.gh_snapshot", cible)
    package = sys.modules.setdefault(
        "coordination", types.ModuleType("coordination"))
    package.__path__ = getattr(package, "__path__", [])
    monkeypatch.setattr(package, "gh_snapshot", cible, raising=False)


def _faux_gh_api(responses):
    """Remplace `_gh_api` : rend les reponses fixees et COMPTE les appels."""
    counter = {"n": 0}

    def fake(path, *, params=""):
        counter["n"] += 1
        if path in responses:
            value = responses[path]
            if callable(value):
                return value(params)
            return value
        raise RuntimeError(f"appel gh inattendu: {path} {params}")

    return fake, counter


def test_normalise_comment_rend_la_forme_du_lecteur():
    raw = {
        "body": "[CLAIMED] lane x:y -- test",
        "created_at": "2026-10-26T07:00:00Z",
        "updated_at": "2026-10-26T07:00:00Z",
        "user": {"login": "jsboige"},
        "html_url": "https://github.com/o/r/issues/1#comment",
    }
    norm = gs.normalise_comment(raw)
    assert norm["createdAt"] == "2026-10-26T07:00:00Z"
    assert norm["author"]["login"] == "jsboige"
    assert norm["url"].endswith("#comment")
    assert norm["body"].startswith("[CLAIMED]")


def test_load_snapshot_vide_sur_dossier_absent():
    snap = gs.load_snapshot("jsboige/CoursIA")
    assert snap["issues"] == {} and snap["comments"] == {}
    assert snap["prs"] == {} and snap["checks"] == {}
    assert snap["meta"] == {}


def test_round_trip_save_load():
    snap = {
        "issues": {"1": {"number": 1, "title": "T", "labels": ["consolidation"]}},
        "comments": {"1": [{"body": "x", "createdAt": "c",
                            "author": {"login": "a"}, "url": "u"}]},
        "prs": {"2": {"state": "OPEN"}},
        "checks": {},
        "meta": {"version": gs.SNAPSHOT_VERSION, "refreshed_at": "x"},
    }
    gs.save_snapshot("jsboige/CoursIA", snap)
    back = gs.load_snapshot("jsboige/CoursIA")
    assert back["issues"]["1"]["labels"] == ["consolidation"]
    assert back["prs"]["2"]["state"] == "OPEN"
    assert back["meta"]["version"] == gs.SNAPSHOT_VERSION


def test_serves_est_frais_par_issue():
    import time as _time
    now = _time.time()
    snap = {
        "issues": {"1": {}, "2": {}},
        "comments": {"1": [], "2": []},
        "prs": {}, "checks": {},
        "meta": {"comment_stamps": {"1": now, "2": now - 3600},
                 "refreshed_at": "2026-10-26T00:00:00Z"},
    }
    # Issue 1 fraiche, issue 2 perimee (1 h) : la paire n'est pas servie.
    assert gs.serves(snap, [1], 600) is True
    assert gs.serves(snap, [2], 600) is False
    assert gs.serves(snap, [1, 2], 600) is False


def test_entree_fraiche_ne_declenche_aucun_appel_gh(monkeypatch):
    import time as _time
    fake, counter = _faux_gh_api({})
    monkeypatch.setattr(gs, "_gh_api", fake)
    now = _time.time()
    snap = {
        "issues": {"7": {"number": 7}},
        "comments": {"7": []},
        "prs": {}, "checks": {},
        "meta": {"comment_stamps": {"7": now}},
    }
    _, calls = gs.ensure_issue_payloads("jsboige/CoursIA", [7], snap, 600)
    assert calls == 0
    assert counter["n"] == 0


def test_entree_manquante_est_recuperee_par_rest(monkeypatch):
    fake, counter = _faux_gh_api({
        "repos/jsboige/CoursIA/issues/8":
            {"number": 8, "title": "T", "labels": [{"name": "bug"}],
             "updated_at": "u", "state": "open"},
        "repos/jsboige/CoursIA/issues/8/comments":
            [{"body": "b", "created_at": "c", "updated_at": "c",
              "user": {"login": "l"}, "html_url": "u"}],
    })
    monkeypatch.setattr(gs, "_gh_api", fake)
    snap = {"issues": {}, "comments": {}, "prs": {}, "checks": {}, "meta": {}}
    out, calls = gs.ensure_issue_payloads("jsboige/CoursIA", [8], snap, 600)
    assert calls == 2
    assert out["issues"]["8"]["labels"] == ["bug"]
    assert out["comments"]["8"][0]["author"]["login"] == "l"
    assert counter["n"] == 2


def test_sweep_comments_est_retire():
    """#22684 (review ai-01 2026-10-27, point 3) : `sweep_comments` est RETIREE.

    Sa construction d'argv etait invalide -- `params=f"--paginate&since={since}"`
    devient UN argument (`gh api <path> --paginate&since=...`), que `gh`
    refuse -- et elle n'avait **aucun** appelant en production : le
    rafraichissement reel passe par `ensure_issue_payloads`, issue par issue.
    La garde est structurelle : la fonction ne doit pas revenir sans appelant
    et sans forme d'argv valide.
    """
    assert not hasattr(gs, "sweep_comments")
    assert "sweep_comments" not in gs.__all__


def test_le_verrou_est_partage_et_le_second_passe_sert_le_premier(monkeypatch):
    responses = {
        "repos/jsboige/CoursIA/issues/9":
            {"number": 9, "title": "T", "labels": [], "updated_at": "u",
             "state": "open"},
        "repos/jsboige/CoursIA/issues/9/comments": [],
    }
    fake, counter = _faux_gh_api(responses)
    monkeypatch.setattr(gs, "_gh_api", fake)
    first = gs.refresh("jsboige/CoursIA", issue_numbers=[9])
    assert gs.serves(first, [9], 600) is True
    calls_after_first = counter["n"]
    second = gs.refresh("jsboige/CoursIA", issue_numbers=[9])
    assert counter["n"] == calls_after_first  # 0 appel de plus : passe chaude
    assert second["comments"]["9"] == []


def test_gh_api_est_borne_et_le_timeout_fait_fail_open(monkeypatch):
    """#22684 : chaque appel `gh` porte une borne, et un `gh` qui ne repond
    pas est une lecture impossible (fail-open), jamais un pend.

    Mesure fondatrice (sans reseau, surface stubee) : a froid, le priming
    du tapis emet 2 appels par candidat -- 140 pour une fenetre de 70 -- et
    `_gh_api` n'avait AUCUNE borne : un seul `gh` lent pendant une
    saturation du pool GitHub pendait la passe entiere du picker (rc=124,
    sortie vide, le JSON n'etant imprime qu'en fin de passe).
    """
    import subprocess as _sp
    seen: dict = {}

    def fake_run(argv, **kwargs):
        seen["timeout"] = kwargs.get("timeout")
        raise _sp.TimeoutExpired(cmd="gh", timeout=kwargs.get("timeout"))

    monkeypatch.setattr(gs.subprocess, "run", fake_run)
    snap = {"issues": {}, "comments": {}, "prs": {}, "checks": {}, "meta": {}}
    out, calls = gs.ensure_issue_payloads("jsboige/CoursIA", [15], snap, 600)
    # La borne est bien transmise au subprocess (valeur finie, raisonnable).
    assert isinstance(seen.get("timeout"), (int, float))
    assert 0 < seen["timeout"] <= 60
    # L'echec est NOMME, pas leve : l'issue est signalee en fetch_failures
    # et la passe continue sans verdict suppose (0 appel abouti).
    assert calls == 0
    assert "15" in out["meta"]["fetch_failures"]
    assert out["issues"] == {} and out["comments"] == {}


def test_verrou_expire_ne_laisse_pas_ecrire_sans_exclusion(monkeypatch):
    lock = gs.snapshot_dir("jsboige/CoursIA") / "refresh.lock"
    lock.parent.mkdir(parents=True, exist_ok=True)
    lock.write_text("autre lane", encoding="utf-8")
    monkeypatch.setattr(gs.time, "monotonic", iter([0, 2]).__next__)
    with (pytest.raises(gs.SnapshotLockTimeout),
          gs.snapshot_lock("jsboige/CoursIA", timeout=1)):
        pytest.fail("le bloc ne doit jamais s'executer sans verrou")
    assert lock.read_text(encoding="utf-8") == "autre lane"


def test_seam_du_lecteur_rend_le_payload_sans_sous_processus(monkeypatch):
    def _refuse(*a, **k):  # pragma: no cover - ne doit jamais etre atteint
        raise AssertionError("aucun sous-processus ne doit etre lance")
    monkeypatch.setattr(clc.subprocess, "run", _refuse)
    payload = {"number": 5, "title": "T", "labels": [],
               "comments": [{"body": "[CLAIMED] lane a:b -- x",
                             "createdAt": "2026-10-26T06:00:00Z",
                             "author": {"login": "jsboige"}, "url": "u"}]}
    clc.set_snapshot({"issues": {"5": payload}, "prs": {}})
    assert clc._gh_issue_comments("5") is payload
    assert clc._gh_issue_comments(5) is payload


def test_seam_rend_l_etat_de_pr_sans_gh(monkeypatch):
    def _refuse(*a, **k):  # pragma: no cover
        raise AssertionError("aucun gh pr view ne doit etre lance")
    monkeypatch.setattr(clc.subprocess, "run", _refuse)
    clc.set_snapshot({"issues": {}, "prs": {"77": {"state": "MERGED"}}})
    assert clc._fetch_pr_state(77) == ("MERGED", None)


def test_retire_l_instantane_retablit_la_lecture_reseau(monkeypatch):
    clc.set_snapshot({"issues": {"5": {"number": 5}}, "prs": {}})
    clc.set_snapshot(None)
    assert clc._snapshot_issue_payload("5") is None


def test_check_issues_batch_rend_le_dict_sans_imprimer(capsys):
    out = clc.check_issues_batch(["5"], "myia-ai-01:CoursIA-2",
                                 from_json=None)
    # Issue 5 introuvable dans l'instantane et gh absent -> ERROR, pas crash.
    assert isinstance(out, dict)
    assert out["mode"] == "batch"
    assert out["results"]["5"]["code"] in ("ERROR", "FREE", "BLOCKED",
                                           "IMPLICIT")
    captured = capsys.readouterr()
    assert captured.out == ""   # rien sur stdout : le rendu est dans le dict


def test_run_check_batch_imprime_le_json_sur_stdout(capsys, monkeypatch):
    payload = {"number": 5, "title": "T", "labels": [],
               "comments": [{"body": "prose sans marqueur",
                             "createdAt": "2026-10-26T06:00:00Z",
                             "author": {"login": "jsboige"}, "url": "u"}]}
    clc.set_snapshot({"issues": {"5": payload}, "prs": {}})
    monkeypatch.setattr(clc, "_OPEN_PRS_MEMO", [])
    rc = clc._run_check_batch(["5"], "myia-ai-01:CoursIA-2")
    assert rc == 0
    printed = json.loads(capsys.readouterr().out)
    assert printed["mode"] == "batch"
    assert printed["results"]["5"]["code"] == "FREE"


def _payload_sans_claim(n: int) -> dict:
    return {"number": n, "title": f"T{n}", "labels": [],
            "comments": []}


def _payload_claime_par_autre_lane(n: int) -> dict:
    recent = (datetime.now(UTC)
              - timedelta(hours=1)).strftime("%Y-%m-%dT%H:%M:%SZ")
    return {"number": n, "title": f"T{n}", "labels": [],
            "comments": [{"body": "[CLAIMED] lane my-po-2023:CoursIA -- x",
                          "createdAt": recent,
                          "author": {"login": "jsboige"}, "url": "u"}]}


# --- #22684 : la forme FABRIQUEE par la production doit servir les claims -----


def _production_snapshot_avec_claim_autre_lane(monkeypatch, n: int) -> dict:
    """Instantane construit par la voie de PRODUCTION (#22684).

    `ensure_issue_payloads` -- exactement comme `refresh()` l'appelle --
    range l'issue dans `issues[n]` (metadonnees seules) et ses commentaires
    dans `comments[n]` : DEUX cles separees. C'est la seule forme que la
    production fabrique ; les injections directes de payloads complets dans
    `issues[n]` ne la reproduisent pas (defaut fondateur : les tests
    passaient alors que la voie en processus lisait tout comme libre).
    """
    recent = (datetime.now(UTC)
              - timedelta(hours=1)).strftime("%Y-%m-%dT%H:%M:%SZ")
    fake, _ = _faux_gh_api({
        f"repos/jsboige/CoursIA/issues/{n}":
            {"number": n, "title": f"T{n}", "labels": [],
             "updated_at": recent, "state": "open"},
        f"repos/jsboige/CoursIA/issues/{n}/comments":
            [{"body": "[CLAIMED] lane myia-po-2099:CoursIA -- paths: x/**",
              "created_at": recent, "updated_at": recent,
              "user": {"login": "jsboige"}, "html_url": "u"}],
    })
    monkeypatch.setattr(gs, "_gh_api", fake)
    snap = {"issues": {}, "comments": {}, "prs": {}, "checks": {}, "meta": {}}
    snap, _calls = gs.ensure_issue_payloads("jsboige/CoursIA", [n], snap, 600)
    return snap


def test_voie_en_processus_forme_production_voit_le_claim_d_une_autre_lane(
        monkeypatch):
    """#22684 -- reproduction du defaut de production (review ai-01
    2026-10-27T04:38Z) : via la forme FABRIQUEE par `ensure_issue_payloads`,
    un `[CLAIMED]` d'une AUTRE lane doit etre VU, jamais FREE.

    Avant le correctif, `issues[n]` ne portait pas `comments` et le lecteur
    servait l'entree telle quelle : `_sort_events` voyait zero evenement de
    claim et le verdict etait `FREE | CLEAR: no other lane claims ...` pour
    toute issue claimee -- le claim d'une autre lane devenait invisible.
    """
    import contextlib
    import io

    n = 424242
    snap = _production_snapshot_avec_claim_autre_lane(monkeypatch, n)
    # La forme est bien celle de la production : deux cles separees.
    assert "comments" not in snap["issues"][str(n)]
    assert len(snap["comments"][str(n)]) == 1

    clc.set_snapshot(snap)
    monkeypatch.setattr(clc, "_OPEN_PRS_MEMO", [])

    # (a) Voie BATCH en processus (celle de `_claims_in_process` a N >= 2) :
    # le verdict n'est PAS FREE. Un appel sans `--paths` devant des
    # bloqueurs rend le NOT_SCOPED historique (exit 2, #12322) -- la queue
    # de son message dans stderr_tail prouve que le claim d'une autre lane
    # est VU (le NOT_SCOPED n'est emis que dans la branche `if others:` ;
    # l'en-tete "NOT_SCOPED:" peut etre tronque par la limite a 200 chars,
    # la queue du message est stable).
    out = clc.check_issues_batch([str(n)], "myia-ai-01:CoursIA-2",
                                 from_json=None)
    result = out["results"][str(n)]
    assert result["code"] != "FREE"
    assert result["exit"] == 2
    assert "branch on the verdict" in result["stderr_tail"]

    # (b) Voie SOLO (celle de `_claims_in_process` a N = 1) : le JSON de
    # synthese porte le bloqueur -- c'est `blocking_lanes` que
    # `_summarize_claim` lit pour rendre BLOCKED au tapis.
    buf_out = io.StringIO()
    with contextlib.redirect_stdout(buf_out):
        payload = clc._gh_issue_comments(str(n))
        clc._run_check(payload, "myia-ai-01:CoursIA-2", stale_threshold=48.0,
                       my_paths=None, check_open_pr_paths=True)
    summary_text = buf_out.getvalue()
    brace = summary_text.find("{")
    data, _ = json.JSONDecoder().raw_decode(summary_text[brace:])
    assert data["blocked"] is True
    assert "myia-po-2099:CoursIA" in data["blocking_lanes"]


def test_les_deux_formes_d_instantane_rendent_le_meme_verdict(monkeypatch):
    """Le seam doit servir la meme semantique aux deux formes : fusionnee
    (payload complet injecte dans `issues[n]`) et separee (production).
    Verdicts identiques par `check_issues_batch`, claim d'une autre lane."""
    n = 424242
    snap = _production_snapshot_avec_claim_autre_lane(monkeypatch, n)
    entry = snap["issues"][str(n)]
    fusionnee = {"issues": {str(n): dict(entry, comments=snap["comments"][str(n)])},
                 "prs": {}}

    verdicts = {}
    for form_name, installed in (("separee", snap), ("fusionnee", fusionnee)):
        clc.set_snapshot(installed)
        monkeypatch.setattr(clc, "_OPEN_PRS_MEMO", [])
        out = clc.check_issues_batch([str(n)], "myia-ai-01:CoursIA-2",
                                     from_json=None)
        verdicts[form_name] = out["results"][str(n)]
    assert verdicts["separee"]["code"] != "FREE"
    assert verdicts["separee"]["exit"] == verdicts["fusionnee"]["exit"]
    assert verdicts["separee"]["human"] == verdicts["fusionnee"]["human"]
    assert verdicts["separee"]["stderr_tail"] == \
        verdicts["fusionnee"]["stderr_tail"]


def test_le_seam_fusionne_les_commentaires_de_la_forme_separee():
    """Le seam lui-meme : entree separee -> payload servi AVEC commentaires ;
    entree fusionnee -> servie telle quelle (identite preservee)."""
    payload_complet = {"number": 5, "title": "T", "labels": [], "comments": []}
    clc.set_snapshot({"issues": {"5": payload_complet}, "prs": {}})
    assert clc._snapshot_issue_payload("5") is payload_complet

    clc.set_snapshot({"issues": {"6": {"number": 6, "title": "T", "labels": []}},
                      "comments": {"6": [{"body": "x"}]},
                      "prs": {}})
    served = clc._snapshot_issue_payload("6")
    assert served is not None
    assert served["comments"] == [{"body": "x"}]
    # La fusion ne mute pas l'entree d'origine de l'instantane.
    assert "comments" not in clc._SNAPSHOT["issues"]["6"]


def test_entree_sans_commentaires_n_est_pas_servie():
    """Fail-closed : une entree `issues[n]` sans cle `comments` et sans liste
    dans `comments[n]` n'etablit PAS l'absence de commentaires -- la servir
    telle quelle fabriquerait un FREE de zero lu (#22684). Le seam rend None :
    le lecteur retombe sur la voie reseau."""
    clc.set_snapshot({"issues": {"7": {"number": 7, "title": "T", "labels": []}},
                      "prs": {}})
    assert clc._snapshot_issue_payload("7") is None


def test_voie_en_processus_rend_les_memes_codes_que_la_voie_cli(monkeypatch):
    """La voie tapis (#22630) appelle les MEMES fonctions que la CLI.

    Une issue sans marqueur rend FREE ; une issue claimée par une AUTRE lane
    depuis 1 h rend BLOCKED -- les deux par `_run_check`, exactement comme la
    CLI mono-issue, sans aucun sous-processus ni appel gh.
    """
    snap = {"issues": {"101": _payload_sans_claim(101),
                       "202": _payload_claime_par_autre_lane(202)},
            "prs": {}}
    fake = types.ModuleType("coordination.gh_snapshot")
    fake.refresh = lambda repo, issue_numbers=None, ttl_seconds=600: snap
    _redirige_gh_snapshot(monkeypatch, fake)
    monkeypatch.setattr(clc, "_OPEN_PRS_MEMO", [])
    monkeypatch.setattr(pig, "_build_open_prs_cache_for_belt",
                        lambda lane: None)

    verdicts = pig._claims_in_process([101, 202],
                                      "myia-ai-01:CoursIA-2")
    assert verdicts is not None
    assert verdicts[101][0] == pig.CLAIM_CODE_FREE
    # La voie CLI mono-issue lit `blocking_lanes` dans le JSON de synthese :
    # un claim d'une AUTRE lane, appelant sans --paths, rend BLOCKED.
    solo = pig._claims_in_process([202], "myia-ai-01:CoursIA-2")
    assert solo is not None
    assert solo[202][0] == pig.CLAIM_CODE_BLOCKED
    # #22983 -- CONTRAT CHANGE ICI, et non contourne (revue Hermes,
    # point 5a). Le mode batch mappe desormais `exit 2` + `blocking_lanes`
    # non vide sur BLOCKED, le verdict de la voie historique du picker : le
    # resume JSON nomme les lanes bloquantes, alors que `NOT_SCOPED:` part
    # sur stderr et n'a jamais ete lisible sur stdout. La version precedente
    # de cette assertion affirmait ERROR -- le comportement HISTORIQUE du
    # mode batch, qui rendait un grain tenu par une autre lane *servable*
    # par le tapis (fail-open) : exactement la collision que la jambe
    # IMPLICIT (#14300) existe pour empecher.
    # Le contrat #22630 tient toujours : la voie en processus et la voie CLI
    # rendent le MEME code, et cette assertion mesure la premiere tandis que
    # celle du dessus (mono-issue) mesure deja BLOCKED sur la meme situation.
    assert verdicts[202][0] == pig.CLAIM_CODE_BLOCKED


def test_voie_en_processus_rend_none_si_le_lecteur_manque(monkeypatch):
    def _absent():
        raise RuntimeError("lecteur introuvable")
    monkeypatch.setattr(pig, "_claim_reader_module", _absent)
    assert pig._claims_in_process([1], "lane") is None


def test_check_claims_retombe_sur_la_voie_historique_si_none(monkeypatch):
    """Si la voie en processus rend None, `check_claims` garde son chemin."""
    monkeypatch.setattr(pig, "_claims_in_process",
                        lambda numbers, lane, cache=None: None)
    captured: dict = {}

    def _legacy(numbers, lane):
        captured["numbers"] = list(numbers)
        return {n: (pig.CLAIM_CODE_ERROR, "legacy") for n in numbers}

    # On shunte le sous-processus reel : on veut seulement verifier que le
    # chemin historique est PRIS, pas qu'il reussit.
    monkeypatch.setattr(pig, "_build_open_prs_cache_for_belt",
                        lambda lane: None)
    monkeypatch.setattr(pig, "_run_bounded",
                        lambda cmd, timeout=None, env=None: types.SimpleNamespace(
                            returncode=0,
                            stdout=json.dumps(
                                {"results": {str(n): {"code": "ERROR",
                                                      "human": "legacy"}
                                             for n in cmd[-2:]}}),
                            stderr=""))
    verdicts = pig.check_claims([301, 302], "lane")
    assert verdicts[301][1] == "legacy"


def test_check_claims_en_processus_quand_le_cache_de_passe_est_actif(monkeypatch):
    """Controle positif du gate : cache active => voie en processus, zero
    sous-processus.

    Sans cache de passe (`_PASS_SNAPSHOT` a None), `check_claims` garde le
    transport historique -- c'est le seam que simulent les appelants directs
    (cf. le test precedent et les trois tests mono-issue du fichier belt).
    Avec cache, la voie en processus doit reprendre, sinon le correctif
    d'hermeticite aurait simplement supprime l'optimisation en production.
    """
    _active_repair(monkeypatch)
    snap = {"issues": {"101": _payload_sans_claim(101)}, "prs": {}}
    fake = types.ModuleType("coordination.gh_snapshot")
    fake.refresh = lambda repo, issue_numbers=None, ttl_seconds=600: snap
    monkeypatch.setitem(sys.modules, "coordination.gh_snapshot", fake)
    monkeypatch.setattr(clc, "_OPEN_PRS_MEMO", [])
    monkeypatch.setattr(pig, "_build_open_prs_cache_for_belt", lambda lane: None)

    def refuse_gh(cmd, *a, **k):
        joined = " ".join(str(p) for p in (cmd if isinstance(cmd, (list, tuple))
                                           else [cmd]))
        if "check_lane_claim.py" in joined or " gh " in f" {joined} ":
            pytest.fail(f"voie historique atteinte : {joined[:80]}")
        # Les lectures locales (git tracked files) restent permises : elles
        # ne sortent pas sur le reseau et font partie de `_run_check`.
        return types.SimpleNamespace(returncode=0, stdout="", stderr="")

    monkeypatch.setattr(pig.subprocess, "run", refuse_gh)

    verdicts = pig.check_claims([101], "myia-ai-01:CoursIA-2")

    assert verdicts[101][0] == pig.CLAIM_CODE_FREE


# --- file de reparation : meme instantane, invalidation par updatedAt ---------


def _repair_pr(n=41, updated="2026-10-26T08:00:00Z"):
    return {"number": n, "title": "PR", "body": "Grain: MED/guard -- lane a:b",
            "createdAt": "2026-10-20T00:00:00Z", "updatedAt": updated,
            "isDraft": False, "author": {"login": "jsboige"},
            "headRefName": "feature/x"}


def _active_repair(monkeypatch, prs=None):
    snap = gs.load_snapshot("jsboige/CoursIA")
    if prs is not None:
        snap["repair"] = {"open_prs": {
            "fetched_at": time.time(), "prs": prs}}
    monkeypatch.setattr(pig, "_PASS_SNAPSHOT", snap)
    return snap


def _fake_state_transport(monkeypatch, states):
    calls = []

    def fake(cmd, *, timeout, env=None):
        calls.append(cmd)
        query = next(x[len("query="):] for x in cmd if x.startswith("query="))
        repo = {}
        for n, state in states.items():
            if f"pullRequest(number:{n})" in query:
                repo[f"p{n}"] = state
        return types.SimpleNamespace(
            returncode=0,
            stdout=json.dumps({"data": {"repository": repo}}), stderr="")

    monkeypatch.setattr(pig, "_run_bounded", fake)
    return calls


def test_reparation_chaude_liste_etats_et_nits_sans_aucun_fetch(monkeypatch):
    """Controle negatif de l'ancienne voie : trois familles, zero appel."""
    prs = [_repair_pr()]
    snap = _active_repair(monkeypatch, prs)
    now = time.time()
    state = {"number": 41, "mergeable": "MERGEABLE", "reviews": {"nodes": []}}
    info = {"blocking": [], "blocked": False, "budget_exhausted": False,
            "verdict": None, "verdict_surface": None}
    snap["repair"]["states"] = {"41": {
        "updatedAt": prs[0]["updatedAt"], "fetched_at": now, "value": state}}
    snap["repair"]["nits"] = {"41": {
        "updatedAt": prs[0]["updatedAt"], "fetched_at": now, "value": info}}
    monkeypatch.setattr(pig, "_run_bounded",
                        lambda *a, **k: pytest.fail("aucun fetch a chaud"))

    import check_unaddressed_nits as nits
    monkeypatch.setattr(nits, "analyse_pr",
                        lambda n: pytest.fail("aucun organe B.0 a chaud"))
    assert pig.fetch_open_prs() == prs
    assert pig.fetch_pr_states([41]) == {41: state}
    assert pig._nits_blocking_entries(41) == info
    detail = pig.unaddressed_review_points_detail([41])
    assert detail[41]["count"] == 0


def test_reparation_verdict_annexe_est_reutilise(monkeypatch):
    prs = [_repair_pr()]
    snap = _active_repair(monkeypatch, prs)
    info = {"blocking": [{"author": "a"}], "blocked": True,
            "budget_exhausted": False, "verdict": "CONCERNS",
            "verdict_surface": "review-body"}
    snap["repair"]["nits"] = {"41": {
        "updatedAt": prs[0]["updatedAt"], "fetched_at": time.time(),
        "value": info}}
    import pool_review_verdicts as verdicts
    monkeypatch.setattr(verdicts, "fetch_prs",
                        lambda *a: pytest.fail("verdict deja mesure"))
    assert pig.unaddressed_review_points_detail([41])[41]["verdict"] == "CONCERNS"


def test_panne_verdict_annexe_est_relue_a_la_passe_suivante(monkeypatch):
    snap = _active_repair(monkeypatch, [_repair_pr()])
    import check_unaddressed_nits as nits
    import pool_review_verdicts as verdicts
    monkeypatch.setattr(nits, "analyse_pr", lambda n: {
        "blocking": [{"author": "a"}], "blocked": True})
    calls = []
    monkeypatch.setattr(verdicts, "fetch_prs", lambda repo, numbers: (
        calls.append(numbers), {})[1])
    assert pig.unaddressed_review_points_detail([41])[41]["count"] == 1
    assert "verdict" not in snap["repair"]["nits"]["41"]["value"]
    assert pig.unaddressed_review_points_detail([41])[41]["count"] == 1
    assert calls == [[41], [41]], "une panne annexe ne gèle pas son retry"


def test_reparation_liste_expiree_est_relue(monkeypatch):
    now = time.time()
    prs = [_repair_pr()]
    snap = _active_repair(monkeypatch, [dict(prs[0], title="ancienne")])
    snap["repair"]["open_prs"]["fetched_at"] = now - 601
    calls = _fake_state_transport(monkeypatch, {})
    # La commande de listing passe par le meme transport borne que les etats.
    def fake(cmd, *, timeout, env=None):
        if cmd[:3] == ["gh", "pr", "list"]:
            calls.append(cmd)
            assert "updatedAt" in cmd[cmd.index("--json") + 1]
            return types.SimpleNamespace(returncode=0, stdout=json.dumps(prs),
                                         stderr="")
        return pytest.fail(f"fetch inattendu: {cmd}")
    monkeypatch.setattr(pig, "_run_bounded", fake)
    assert pig.fetch_open_prs() == prs
    assert len(calls) == 1
    assert snap["repair"]["open_prs"]["prs"] == prs


def test_reparation_updated_at_change_relit_etat_et_nits(monkeypatch):
    prs = [_repair_pr(updated="2026-10-26T09:00:00Z")]
    snap = _active_repair(monkeypatch, prs)
    now = time.time()
    for namespace, value in (("states", {"number": 41, "old": True}),
                             ("nits", {"blocking": [], "blocked": False})):
        snap["repair"][namespace] = {"41": {
            "updatedAt": "2026-10-26T08:00:00Z", "fetched_at": now,
            "value": value}}
    new_state = {"number": 41, "mergeable": "CONFLICTING"}
    calls = _fake_state_transport(monkeypatch, {41: new_state})
    import check_unaddressed_nits as nits
    analysed = []
    monkeypatch.setattr(nits, "analyse_pr", lambda n: (
        analysed.append(n) or {"blocking": [{"author": "a"}], "blocked": True}))

    assert pig.fetch_pr_states([41]) == {41: new_state}
    assert len(calls) == 1
    info = pig._nits_blocking_entries(41)
    assert analysed == [41] and info["blocking"] == [{"author": "a"}]
    assert snap["repair"]["states"]["41"]["updatedAt"] == prs[0]["updatedAt"]
    assert snap["repair"]["nits"]["41"]["updatedAt"] == prs[0]["updatedAt"]


def test_reparation_entree_expiree_relit_etat_et_nits(monkeypatch):
    prs = [_repair_pr()]
    snap = _active_repair(monkeypatch, prs)
    # Age derive de la constante (arbitrage #22684 : TTL cron de 1800 s) --
    # le litterel 901 de l'ancien TTL aurait casse au prochain arbitrage.
    old = time.time() - (pig.PR_STATE_SNAPSHOT_TTL_S + 1)
    for namespace, value in (("states", {"number": 41, "old": True}),
                             ("nits", {"blocking": [], "blocked": False})):
        snap["repair"][namespace] = {"41": {
            "updatedAt": prs[0]["updatedAt"], "fetched_at": old, "value": value}}
    new_state = {"number": 41, "mergeable": "MERGEABLE"}
    calls = _fake_state_transport(monkeypatch, {41: new_state})
    import check_unaddressed_nits as nits
    monkeypatch.setattr(nits, "analyse_pr",
                        lambda n: {"blocking": [], "blocked": False})
    assert pig.fetch_pr_states([41]) == {41: new_state}
    assert pig._nits_blocking_entries(41)["blocking"] == []
    assert len(calls) == 1


def test_annotations_check_run_sont_partagees_et_echec_non_cache(monkeypatch):
    _active_repair(monkeypatch)
    calls = []

    def fake(cmd, **kwargs):
        calls.append(cmd)
        return types.SimpleNamespace(stdout=json.dumps([
            {"message": "::error::Organes bloquants en echec : un autre"}]))

    monkeypatch.setattr(pig.subprocess, "run", fake)
    assert pig.fetch_check_organs(77) == ["un", "autre"]
    assert pig.fetch_check_organs(77) == ["un", "autre"]
    assert len(calls) == 1
    monkeypatch.setattr(pig, "_repair_read_annotation", lambda n: [])
    assert pig.fetch_check_organs(77) == []
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **k: (_ for _ in ()).throw(RuntimeError("down")))
    monkeypatch.setattr(pig, "_repair_read_annotation", lambda n: None)
    assert pig.fetch_check_organs(88) == []
    assert "88" not in (pig._repair_cache().get("annotations") or {})


def test_main_probe_est_serialise_en_listes(monkeypatch):
    _active_repair(monkeypatch)
    contexts = [{"name": "a", "conclusion": "FAILURE", "databaseId": 1}]
    payload = {"data": {"repository": {"defaultBranchRef": {"target": {
        "oid": "s", "statusCheckRollup": {"contexts": {"nodes": contexts}}}}}}}
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **k: types.SimpleNamespace(
                            stdout=json.dumps(payload)))
    monkeypatch.setattr(pig, "_enrich_probe_with_workflow_runs", lambda p: p)
    assert pig.fetch_main_head_probe()["red_keys"] == {"a"}
    stored = pig._repair_cache()["main_probe"]["value"]
    assert stored["red_keys"] == ["a"]
    _redirige_gh_snapshot(monkeypatch, gs)
    pig._flush_repair_snapshot()
    back = gs.load_snapshot("jsboige/CoursIA")
    assert back["repair"]["main_probe"]["value"]["red_keys"] == ["a"]


def test_main_probe_reutilise_ses_ensembles_sans_relire(monkeypatch):
    snap = _active_repair(monkeypatch)
    snap["repair"]["main_probe"] = {
        "fetched_at": time.time(), "value": {
            "sha": "s", "red_keys": ["a"], "names": ["a", "b"]}}
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **k: pytest.fail("probe deja fraiche"))
    assert pig.fetch_main_head_probe()["red_keys"] == {"a"}


def test_check_runs_hors_du_cache_long(monkeypatch):
    """Arbitrage #22684 (cycle cron) : l'etat des check-runs (annotations de
    runs, sonde de main) reste au TTL court -- un check ne bouge pas
    l'updatedAt de la PR, un etat vieux de ~30 min serait servi indement."""
    snap = _active_repair(monkeypatch)
    age = pig.PR_STATE_SNAPSHOT_TTL_S - 1    # encore frais pour les etats...
    assert age > pig.CHECKS_SNAPSHOT_TTL_S   # ...perime pour les check-runs
    snap["repair"]["annotations"] = {"77": {
        "fetched_at": time.time() - age, "value": ["::error vieux"]}}
    snap["repair"]["main_probe"] = {
        "fetched_at": time.time() - age, "value": {"sha": "s", "red_keys": []}}
    assert pig._repair_read_annotation(77) is None
    assert pig._repair_cached_main_probe() is None


def test_commentaires_servis_au_dela_du_ttl_des_index(monkeypatch):
    """Arbitrage #22684 : les payloads claims/commentaires vivent au TTL long
    -- un stamp de 1200 s, perime pour l'index des PRs ouvertes, sert encore
    la sonde de commentaires sans aucune requete."""
    stamp = time.time() - (pig.OPEN_PRS_SNAPSHOT_TTL_S + 600)
    assert stamp > time.time() - pig.COMMENT_SNAPSHOT_TTL_S  # encore frais
    snap = {"comments": {"41": [{"body": "[CLAIMED] lane x"}]},
            "meta": {"comment_stamps": {"41": stamp}}}
    monkeypatch.setattr(pig, "_BELT_SNAPSHOT", None)
    monkeypatch.setattr(pig, "_PASS_SNAPSHOT", snap)
    assert pig._snapshot_comments(41) == [{"body": "[CLAIMED] lane x"}]


def test_reparation_pr_absente_du_fingerprint_ne_sert_pas_un_vieux_vert(monkeypatch):
    snap = _active_repair(monkeypatch, [])
    snap["repair"]["states"] = {"41": {
        "updatedAt": "u", "fetched_at": time.time(),
        "value": {"number": 41, "mergeable": "MERGEABLE"}}}
    _fake_state_transport(monkeypatch, {})
    assert pig.fetch_pr_states([41]) == {}


def test_echec_b0_n_est_jamais_cache_comme_un_zero(monkeypatch):
    prs = [_repair_pr()]
    snap = _active_repair(monkeypatch, prs)
    import check_unaddressed_nits as nits
    monkeypatch.setattr(nits, "analyse_pr",
                        lambda n: (_ for _ in ()).throw(RuntimeError("gh down")))
    assert pig._nits_blocking_entries(41) is None
    assert "nits" not in snap["repair"]
    monkeypatch.setattr(nits, "analyse_pr",
                        lambda n: {"blocking": [], "blocked": False})
    assert pig._nits_blocking_entries(41)["blocking"] == []


def test_budget_b0_epuise_n_est_pas_cache(monkeypatch):
    prs = [_repair_pr()]
    snap = _active_repair(monkeypatch, prs)
    import check_unaddressed_nits as nits
    monkeypatch.setattr(nits, "analyse_pr",
                        lambda n: {"budget_exhausted": True})
    assert pig._nits_blocking_entries(41) is None
    assert "nits" not in snap["repair"]


def test_derive_contrat_b0_se_propage_meme_avec_snapshot(monkeypatch):
    _active_repair(monkeypatch, [_repair_pr()])
    import check_unaddressed_nits as nits
    monkeypatch.setattr(nits, "analyse_pr",
                        lambda n: (_ for _ in ()).throw(TypeError("contrat")))
    with pytest.raises(TypeError, match="contrat"):
        pig._nits_blocking_entries(41)


def test_flush_reparation_preserve_les_autres_namespaces(monkeypatch):
    snap = _active_repair(monkeypatch)
    disk = gs.load_snapshot("jsboige/CoursIA")
    disk["comments"] = {"22630": [{"body": "claim d'une autre lane"}]}
    disk["prs"] = {"99": {"state": "OPEN"}}
    disk["repair"] = {"nits": {"41": {
        "fetched_at": 200.0, "updatedAt": "recent", "value": {"blocked": False}}}}
    gs.save_snapshot("jsboige/CoursIA", disk)
    snap["repair"] = {"nits": {"41": {
        "fetched_at": 100.0, "updatedAt": "ancien", "value": {"blocked": True}}}}

    _redirige_gh_snapshot(monkeypatch, gs)
    pig._flush_repair_snapshot()
    back = gs.load_snapshot("jsboige/CoursIA")
    assert back["comments"] == disk["comments"]
    assert back["prs"] == disk["prs"]
    assert back["repair"]["nits"]["41"]["updatedAt"] == "recent"


def test_hit_reparation_ne_prolonge_pas_son_ttl(monkeypatch):
    prs = [_repair_pr()]
    snap = _active_repair(monkeypatch, prs)
    old = time.time() - 850
    info = {"blocking": [], "blocked": False}
    snap["repair"]["nits"] = {"41": {
        "updatedAt": prs[0]["updatedAt"], "fetched_at": old, "value": info}}
    assert pig._nits_blocking_entries(41) == info
    assert snap["repair"]["nits"]["41"]["fetched_at"] == old
    monkeypatch.setattr(pig, "_PASS_SNAPSHOT", None)
    pig._activate_pass_snapshot("jsboige/CoursIA")
    assert pig._PASS_SNAPSHOT is None, "pytest ne charge pas l'etat machine"


def test_fetchers_directs_sans_main_ne_lisent_pas_le_snapshot(monkeypatch):
    """Le cache est opt-in par main : la voie historique directe est inchangee."""
    monkeypatch.setattr(pig, "_PASS_SNAPSHOT", None)
    calls = []

    def fake(cmd, **kwargs):
        calls.append(cmd)
        kwargs["stdout"].write("[]")
        return types.SimpleNamespace(returncode=0, stdout="", stderr="")

    monkeypatch.setattr(pig.subprocess, "run", fake)
    assert pig.fetch_open_prs() == []
    assert len(calls) == 1


def _marker_snapshot(number: int, fresh: bool = True,
                     body="[INFO] candidate-delivered -- x") -> dict:
    stamp = time.time() if fresh else time.time() - 3600
    return {"comments": {str(number): [{"body": body,
                                       "createdAt": "2026-10-26T06:00:00Z",
                                       "author": {"login": "jsboige"},
                                       "url": "u"}]},
            "issues": {str(number): {"number": number}},
            "meta": {"comment_stamps": {str(number): stamp}}}


def test_sonde_delivered_marker_lit_l_instantane_sans_gh(monkeypatch):
    """La sonde de marqueur partage l'instantane : memes corps, zero requete."""
    monkeypatch.setattr(pig, "_BELT_SNAPSHOT", _marker_snapshot(7423))
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **k: pytest.fail("instantane deja la"))
    assert pig._has_delivered_marker(7423) is True


def test_instantane_de_passe_sert_les_commentaires_frais(monkeypatch):
    monkeypatch.setattr(pig, "_PASS_SNAPSHOT", _marker_snapshot(7423))
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **k: pytest.fail("commentaire frais en cache"))
    assert pig._has_delivered_marker(7423) is True


def test_instantane_de_passe_perime_retombe_sur_le_reseau(monkeypatch):
    monkeypatch.setattr(pig, "_PASS_SNAPSHOT", _marker_snapshot(7423, fresh=False))
    calls = []
    monkeypatch.setattr(pig.subprocess, "run", lambda cmd, **k: (
        calls.append(cmd), types.SimpleNamespace(
            stdout=json.dumps({"comments": []}), returncode=0, stderr=""))[1])
    assert pig._has_delivered_marker(7423) is False
    assert len(calls) == 1


# --- #22684 point 2 : la source 1 est soumise au meme controle d'age ----------


def test_source_1_perimee_n_est_pas_servie(monkeypatch):
    """La source 1 ne sert plus une entree au-dela de `COMMENT_SNAPSHOT_TTL_S`.

    Defaut fondateur (review ai-01 2026-10-27, point 2) : `_BELT_SNAPSHOT`
    etait servi SANS controle d'age, au motif qu'il est « frais par
    construction ». Faux -- `refresh()` ne relit que les candidats de la
    fenetre ; le reste de l'instantane vient du disque, ecrit par une passe
    anterieure ou par une autre lane, et peut dater de plusieurs jours. Un
    remplacement tire au-dela de la fenetre lisait alors un fil perime.
    """
    monkeypatch.setattr(pig, "_BELT_SNAPSHOT", _marker_snapshot(7423, fresh=False))
    monkeypatch.setattr(pig, "_PASS_SNAPSHOT", None)
    assert pig._snapshot_comments(7423) is None


def test_source_1_perimee_retombe_sur_le_reseau(monkeypatch):
    """Meme consequence observable que pour la source 2 : le transport
    historique reprend, et le marqueur perime n'est PAS le verdict."""
    monkeypatch.setattr(pig, "_BELT_SNAPSHOT", _marker_snapshot(7423, fresh=False))
    monkeypatch.setattr(pig, "_PASS_SNAPSHOT", None)
    calls = []
    monkeypatch.setattr(pig.subprocess, "run", lambda cmd, **k: (
        calls.append(cmd), types.SimpleNamespace(
            stdout=json.dumps({"comments": []}), returncode=0, stderr=""))[1])
    assert pig._has_delivered_marker(7423) is False
    assert len(calls) == 1


def test_source_1_fraiche_reste_servie_sans_gh(monkeypatch):
    """Controle positif : le controle d'age ne coupe pas le chemin chaud."""
    monkeypatch.setattr(pig, "_BELT_SNAPSHOT", _marker_snapshot(7423))
    monkeypatch.setattr(pig, "_PASS_SNAPSHOT", None)
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **k: pytest.fail("entree fraiche en cache"))
    assert pig._snapshot_comments(7423) == [
        {"body": "[INFO] candidate-delivered -- x",
         "createdAt": "2026-10-26T06:00:00Z",
         "author": {"login": "jsboige"}, "url": "u"}]


def test_source_1_sans_horodatage_n_est_pas_servie(monkeypatch):
    """Fail-closed : une entree sans stamp n'etablit pas sa fraicheur.

    L'instantane peut venir d'une version anterieure (`meta.comment_stamps`
    absent) : servir l'entree reviendrait a supposer sa fraicheur, exactement
    le defaut corrige.
    """
    monkeypatch.setattr(pig, "_BELT_SNAPSHOT", {
        "comments": {"7423": [{"body": "[CLAIMED] lane x:y -- z"}]},
        "meta": {},
    })
    monkeypatch.setattr(pig, "_PASS_SNAPSHOT", None)
    assert pig._snapshot_comments(7423) is None


def test_transport_b0_est_reutilise_a_updated_at_constant(monkeypatch):
    """Le funnel `gh_json` de l'organe B.0 est memoise par (PR, updatedAt)."""
    prs = [_repair_pr()]
    snap = _active_repair(monkeypatch, prs)
    import check_unaddressed_nits as nits
    transport_calls = []

    def fake_gh(args):
        transport_calls.append(list(args))
        return {"sha": "abc"}

    monkeypatch.setattr(nits, "gh_json", fake_gh)
    monkeypatch.setattr(nits, "analyse_pr", lambda n: {
        "blocking": [{"author": nits.gh_json(["api", "commits/abc"])["sha"]}],
        "blocked": True})
    _redirige_gh_snapshot(monkeypatch, gs)
    assert pig._nits_blocking_entries(41)["blocking"]
    assert len(transport_calls) == 1
    snap["repair"]["nits"].clear()          # force un nouveau calcul du verdict
    assert pig._nits_blocking_entries(41)["blocking"]
    assert len(transport_calls) == 1, "PR inchangee : transport deja mesure"


def test_panne_b0_ne_persiste_pas_le_transport(monkeypatch):
    _active_repair(monkeypatch, [_repair_pr()])
    import check_unaddressed_nits as nits
    monkeypatch.setattr(nits, "gh_json", lambda args: {"x": 1})
    monkeypatch.setattr(nits, "analyse_pr",
                        lambda n: (_ for _ in ()).throw(RuntimeError("down")))
    assert pig._nits_blocking_entries(41) is None
    assert "b0" not in pig._repair_cache()


def test_budget_b0_epuise_ne_persiste_pas_le_transport(monkeypatch):
    _active_repair(monkeypatch, [_repair_pr()])
    import check_unaddressed_nits as nits
    monkeypatch.setattr(nits, "gh_json", lambda args: {"x": 1})
    monkeypatch.setattr(nits, "analyse_pr", lambda n: {"budget_exhausted": True})
    assert pig._nits_blocking_entries(41) is None
    assert "b0" not in pig._repair_cache()


def _pool_item(number=7):
    return {"number": number, "title": "T", "labels": [], "body": "",
            "createdAt": "2026-10-20T00:00:00Z",
            "updatedAt": "2026-10-25T00:00:00Z"}


def test_pool_est_servi_par_l_instantane_pendant_son_ttl(monkeypatch):
    snap = _active_repair(monkeypatch)
    snap["repair"]["pool"] = {"fetched_at": time.time(),
                              "issues": [_pool_item()]}
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **k: pytest.fail("pool deja lu"))
    pool, err = pig.fetch_pool(cache_mode="off")
    assert err is None
    assert [p["number"] for p in pool] == [7]


def test_pool_perime_est_relu(monkeypatch):
    snap = _active_repair(monkeypatch)
    snap["repair"]["pool"] = {"fetched_at": time.time() - 91,
                              "issues": [_pool_item(999)]}
    calls = []

    def fake(cmd, **kwargs):
        calls.append(cmd)
        return types.SimpleNamespace(stdout=json.dumps([_pool_item()]),
                                     returncode=0, stderr="")

    monkeypatch.setattr(pig.subprocess, "run", fake)
    pool, err = pig.fetch_pool(cache_mode="off")
    assert err is None
    assert [p["number"] for p in pool] == [7]
    assert len(calls) == 1
    assert snap["repair"]["pool"]["issues"][0]["number"] == 7


def test_enumeration_claims_est_servie_par_l_instantane(monkeypatch):
    snap = _active_repair(monkeypatch)
    snap["repair"]["claims_open_prs"] = {"fetched_at": time.time(),
                                        "prs": [{"number": 1}]}
    monkeypatch.setattr(pig, "_OPEN_PRS_ENUM_MEMO", None)
    monkeypatch.setattr(pig, "_claim_reader_module",
                        lambda: pytest.fail("enumeration deja faite"))
    assert pig._complete_open_prs() == [{"number": 1}]
