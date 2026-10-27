"""Balayage incremental de l'instantane : la phase reseau du tapis (#22983).

Le tapis ne doit plus interroger GitHub pendant le tirage. Cette PR rend la
**phase reseau** (la lecture des commentaires des candidats) incrémentale et
bornee :

- un **balayage** du depot (`repos/<repo>/issues/comments?since=`) lit les
  commentaires modifies depuis la derniere lecture, en UN appel ;
- les issues que le balayage ne couvre pas sont lues une par une ;
- les metadonnees (titre, labels) viennent d'UN balayage des issues
  ouvertes, pas d'une lecture par issue.

Aucun test ne touche le reseau : `_gh_api` est remplace par un faux, et la
racine de l'instantane est redirigee vers `tmp_path`.
"""

import datetime as dt
import json
import os
import re
import subprocess
import sys
import time
import types
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "coordination"))

import gh_snapshot as gs
import pick_idle_grain as pig


@pytest.fixture(autouse=True)
def _snapshot_root_isole(tmp_path, monkeypatch):
    """Racine de l'instantane redirigee : jamais le LOCALAPPDATA reel."""
    def _racine():
        return tmp_path / "gh-snapshot"

    monkeypatch.setattr(gs, "snapshot_root", _racine)
    instance_package = sys.modules.get("coordination.gh_snapshot")
    if instance_package is not None and instance_package is not gs:
        monkeypatch.setattr(instance_package, "snapshot_root", _racine)
    yield
    pig._PASS_SNAPSHOT = None
    pig._BELT_SNAPSHOT = None
    pig._BELT_PRIMED_WINDOW = set()


def _commentaire(issue, body="[CLAIMED] lane a:b -- x", created="2026-10-27T10:00:00Z"):
    """Commentaire REST normalise, pret pour le faux `gh api`."""
    return {
        "body": body,
        "created_at": created,
        "updated_at": created,
        "user": {"login": "jsboige"},
        "html_url": f"https://github.com/o/r/issues/{issue}#c",
        "issue_url": f"https://api.github.com/repos/o/r/issues/{issue}",
    }


def _commentaire_pr(pr, body="x", created="2026-10-27T10:00:00Z"):
    """Commentaire de PULL REQUEST : l'`issue_url` porte `/pulls/`."""
    return {
        "body": body,
        "created_at": created,
        "updated_at": created,
        "user": {"login": "jsboige"},
        "html_url": f"https://github.com/o/r/pull/{pr}#c",
        "issue_url": f"https://api.github.com/repos/o/r/pulls/{pr}",
    }


# --- le balayage -------------------------------------------------------------


def test_le_balayage_exclut_les_pr_et_classe_par_issue(monkeypatch):
    monkeypatch.setattr(gs, "_gh_api", lambda path, **kw: [
        _commentaire(7), _commentaire(9), _commentaire_pr(1234)])
    grouped = gs.fetch_repo_comments_since("o/r")
    assert set(grouped) == {7, 9}
    assert grouped[7][0]["body"].startswith("[CLAIMED]")
    assert grouped[9][0]["author"]["login"] == "jsboige"


def test_le_balayage_fusionne_sans_dupliquer_et_avance_les_stamps(monkeypatch):
    deja = {"body": "ancien", "createdAt": "2026-10-20T00:00:00Z",
            "author": {"login": "x"}, "url": "u1"}
    snapshot = {
        "comments": {"7": [deja]},
        "meta": {"comment_stamps": {"7": 1000.0}},
    }
    monkeypatch.setattr(gs, "_gh_api", lambda path, **kw: [
        _commentaire(7, body="nouveau"),
        _commentaire(7, body="ancien", created="2026-10-20T00:00:00Z"),
    ])
    out, calls = gs.sweep_repo_comments("o/r", snapshot, since="2026-10-01T00:00:00Z")
    assert calls == 1
    bodies = [c["body"] for c in out["comments"]["7"]]
    assert "nouveau" in bodies and "ancien" in bodies
    # Le meme commentaire (meme url) n'est pas duplique.
    assert len(out["comments"]["7"]) == 2
    stamp = out["meta"]["comment_stamps"]["7"]
    assert stamp > 1000.0


def test_l_argv_du_balayage_est_valide(monkeypatch):
    """Le defaut qui avait fait RETIRER la precedente balayage.

    La forme `params=f"--paginate&since={since}"` devenait UN argument que
    `gh` refuse. Ici, les parametres sont une LISTE d'arguments.
    """
    captures = []

    def faux_run(cmd, **kw):
        captures.append(list(cmd))
        return types.SimpleNamespace(returncode=0, stdout="[]", stderr="")

    monkeypatch.setattr(gs.subprocess, "run", faux_run)
    gs.fetch_repo_comments_since("o/r", since="2026-10-01T00:00:00Z")
    assert captures, "aucun appel gh"
    cmd = captures[0]
    assert cmd[:3] == ["gh", "api", "repos/o/r/issues/comments"]
    assert "--paginate" in cmd
    assert "-f since=2026-10-01T00:00:00Z" in cmd
    # Aucun argument ne contient un `&` : c'est le defaut exact du retrait.
    assert not any("&" in part for part in cmd)


def test_le_balayage_annonce_la_methode_GET(monkeypatch):
    """`gh api` bascule en POST des qu'un champ `-f` est present.

    Un POST sur un point d'entree de LISTE rend `404 Not Found` : c'est
    exactement ce qui est arrive au premier balayage (mesure du 27/10 :
    `gh: Not Found (HTTP 404)`, le balayage entier etait mort, et tout le
    rafraichissement de l'instantane echouait derriere). `-X GET` est donc
    OBLIGATOIRE des qu'un `-f` est present.
    """
    captures = []

    def faux_run(cmd, **kw):
        captures.append(list(cmd))
        return types.SimpleNamespace(returncode=0, stdout="[]", stderr="")

    monkeypatch.setattr(gs.subprocess, "run", faux_run)
    gs.fetch_repo_comments_since("o/r", since="2026-10-01T00:00:00Z")
    cmd = captures[0]
    assert "GET" in cmd, f"la methode HTTP n'est pas annoncee : {cmd}"
    assert cmd.index("GET") == cmd.index("-X") + 1


def test_la_methode_GET_est_annoncee_pour_les_issues_ouvertes(monkeypatch):
    """Meme cause, autre point d'entree : `repos/<repo>/issues?state=open`.

    Sans `-X GET`, `gh api` poste le champ `state` comme un corps de
    requete et GitHub repond `422 -- "title" wasn't supplied`.
    """
    captures = []

    def faux_run(cmd, **kw):
        captures.append(list(cmd))
        return types.SimpleNamespace(returncode=0, stdout="[]", stderr="")

    monkeypatch.setattr(gs.subprocess, "run", faux_run)
    gs.fetch_open_issues("o/r")
    cmd = captures[0]
    assert cmd[:3] == ["gh", "api", "repos/o/r/issues"]
    assert "GET" in cmd, f"la methode HTTP n'est pas annoncee : {cmd}"
    assert "state=open" in cmd


# --- ensure_comments --------------------------------------------------------


def test_ensure_comments_balaiage_borne_puis_lecture_par_issue(monkeypatch):
    """Le balayage couvre ce qui est borne ; le reste est lu par issue.

    Le balayage n'est possible que si un horodatage de lecture est connu :
    c'est lui qui borne la lecture. 7 a un horodatage (le balayage le
    couvre) ; 9 n'en a pas (le balayage ne peut pas le borner) -> il est
    lu par issue.
    """
    appels = []

    def faux_gh_api(path, *, params="", timeout=30.0):
        appels.append(path)
        if path.endswith("/issues/comments"):
            return [_commentaire(7)]
        if path.endswith("/issues"):
            return [{"number": 7, "title": "T", "labels": [],
                     "updated_at": "u", "state": "open"}]
        if path.endswith("/issues/9/comments"):
            return [_commentaire(9)]
        if path.endswith("/issues/7/comments"):
            return [_commentaire(7)]
        raise AssertionError(f"appel inattendu: {path}")

    monkeypatch.setattr(gs, "_gh_api", faux_gh_api)
    snapshot = {"comments": {}, "issues": {}, "meta": {
        "comment_stamps": {"7": time.time() - 600}}}
    out, calls, stats = gs.ensure_comments("o/r", [7, 9], snapshot)
    # 7 est couvert par le balayage ; 9 n'a pas d'horodatage connu, donc
    # le balayage ne peut pas le borner : il est lu par issue.
    assert stats["lus"] == 1
    assert out["comments"]["7"][0]["body"].startswith("[CLAIMED]")
    assert out["comments"]["9"][0]["body"].startswith("[CLAIMED]")
    assert "repos/o/r/issues/9/comments" in appels


def test_ensure_comments_sans_balayage_possible_va_directement_par_issue(monkeypatch):
    """Aucun horodatage connu => le balayage n'est pas borne => lecture par issue."""
    appels = []

    def faux_gh_api(path, *, params="", timeout=30.0):
        appels.append(path)
        if path.endswith("/issues/comments"):
            return [_commentaire(7)]
        if path.endswith("/issues"):
            return []
        if path.endswith("/issues/7/comments"):
            return [_commentaire(7)]
        raise AssertionError(f"appel inattendu: {path}")

    monkeypatch.setattr(gs, "_gh_api", faux_gh_api)
    out, calls, stats = gs.ensure_comments("o/r", [7], {"comments": {}, "issues": {}, "meta": {}})
    assert stats["lus"] == 1
    assert "repos/o/r/issues/7/comments" in appels


def test_ensure_comments_lit_les_metadonnees_en_un_balaiage(monkeypatch):
    """Les metadonnees de TOUTES les issues ouvertes : un appel, pas N."""
    appels = []

    def faux_gh_api(path, *, params="", timeout=30.0):
        appels.append(path)
        if path.endswith("/issues/comments"):
            return []
        if path.endswith("/issues"):
            return [{"number": n, "title": f"T{n}", "labels": ["x"],
                     "updated_at": "u", "state": "open"} for n in (7, 9)]
        if path.endswith("/issues/7/comments"):
            return []
        if path.endswith("/issues/9/comments"):
            return []
        raise AssertionError(f"appel inattendu: {path}")

    monkeypatch.setattr(gs, "_gh_api", faux_gh_api)
    out, calls, stats = gs.ensure_comments("o/r", [7, 9], {"comments": {}, "issues": {}, "meta": {}})
    assert stats["meta_balayees"] == 2
    assert out["issues"]["7"]["labels"] == ["x"]
    # UN appel pour les metadonnees des deux issues.
    assert len([a for a in appels if a.endswith("/issues")]) == 1


def test_ensure_comments_sur_entrees_fraiches_ne_bloque_aucun_appel(monkeypatch):
    """Chemin chaud : tout est frais, aucun appel gh."""
    monkeypatch.setattr(gs, "_gh_api", lambda path, **kw: (_ for _ in ()).throw(
        AssertionError(f"appel inattendu: {path}")))
    now = time.time()
    snapshot = {
        "comments": {"7": [_commentaire(7)]},
        "issues": {"7": {"number": 7, "title": "T", "labels": []}},
        "meta": {"comment_stamps": {"7": now}},
    }
    out, calls, stats = gs.ensure_comments("o/r", [7], snapshot)
    assert calls == 0
    assert stats["perimes"] == 0


def test_le_balaiage_est_borne_par_la_fenetre_maximale(monkeypatch):
    """Le balayage ne lit jamais plus de `MAX_SWEEP_LOOKBACK_SECONDS`.

    Son cout croit avec la FENETRE lue, pas avec le nombre d'issues
    visees : un horodatage tres ancien le ferait relire des jours de
    commentaires du depot. Au-dela de la borne, les issues trop anciennes
    sont lues une par une.
    """
    captures = []

    def faux_gh_api(path, *, params="", timeout=30.0):
        captures.append(params)
        if path.endswith("/issues/comments"):
            return []
        if path.endswith("/issues"):
            return []
        raise AssertionError(f"appel inattendu: {path}")

    monkeypatch.setattr(gs, "_gh_api", faux_gh_api)
    vieux = time.time() - 30 * 24 * 3600
    snapshot = {"comments": {}, "issues": {}, "meta": {
        "comment_stamps": {"7": vieux, "9": vieux}}}
    out, calls, stats = gs.ensure_comments("o/r", [7, 9], snapshot)
    sweep_params = [p for p in captures if "since=" in str(p)]
    assert sweep_params, "aucun balayage"
    joined = " ".join(str(p) for p in sweep_params)
    match = re.search(r"since=([0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9:]+Z)", joined)
    assert match, f"aucun horodatage de balayage dans {joined}"
    since = match.group(1)
    # `mktime` lit l'horodatage en HEURE LOCALE : l'ecart de fuseau
    # (UTC+1 sur ce siege) gonflerait la fenetre mesuree d'une heure.
    parsed = dt.datetime.fromisoformat(since.replace("Z", "+00:00")).timestamp()
    age_s = time.time() - parsed
    assert age_s <= gs.MAX_SWEEP_LOOKBACK_SECONDS + 60, (
        f"la fenetre du balayage n'est pas bornee : {age_s / 3600:.1f} h")


def test_une_issue_trop_ancienne_est_lue_a_part(monkeypatch):
    """Ce que le balayage ne couvre pas est lu par issue (jamais suppose lu)."""
    appels = []

    def faux_gh_api(path, *, params="", timeout=30.0):
        appels.append(path)
        if path.endswith("/issues/comments"):
            return []
        if path.endswith("/issues"):
            return [{"number": 7, "title": "T", "labels": [],
                     "updated_at": "u", "state": "open"}]
        if path.endswith("/issues/7/comments"):
            return [_commentaire(7)]
        raise AssertionError(f"appel inattendu: {path}")

    monkeypatch.setattr(gs, "_gh_api", faux_gh_api)
    snapshot = {"comments": {}, "issues": {}, "meta": {
        "comment_stamps": {"7": time.time() - 30 * 24 * 3600}}}
    out, calls, stats = gs.ensure_comments("o/r", [7], snapshot)
    assert stats["lus"] == 1
    assert "repos/o/r/issues/7/comments" in appels


def test_une_issue_illisible_n_interrompt_pas_la_lecture_par_issue(monkeypatch):
    """La lecture parallele isole les echecs : une issue illisible ne fait
    pas tomber les autres, et l'echec est NOMME."""
    appels = []

    def faux_gh_api(path, *, params="", timeout=30.0):
        appels.append(path)
        if path.endswith("/issues/comments"):
            return []
        if path.endswith("/issues"):
            return [{"number": n, "title": "T", "labels": [],
                     "updated_at": "u", "state": "open"} for n in (7, 9)]
        if path.endswith("/issues/7/comments"):
            return [_commentaire(7)]
        if path.endswith("/issues/9/comments"):
            raise RuntimeError("404")
        raise AssertionError(f"appel inattendu: {path}")

    monkeypatch.setattr(gs, "_gh_api", faux_gh_api)
    snapshot = {"comments": {}, "issues": {}, "meta": {}}
    out, calls, stats = gs.ensure_comments("o/r", [7, 9], snapshot)
    assert stats["lus"] == 1
    assert out["comments"]["7"]
    assert "9" not in out["comments"]
    failures = (out.get("meta") or {}).get("fetch_failures") or {}
    assert "9" in failures, "l'echec n'est pas nomme"


def test_un_balaiage_mort_laisse_la_lecture_par_issue_prendre_le_relais(monkeypatch):
    """Le balayage peut echouer (fenetre trop large, quota) : la passe doit
    continuer par la lecture par issue, et le dire."""
    appels = []

    def faux_gh_api(path, *, params="", timeout=30.0):
        appels.append(path)
        if path.endswith("/issues/comments"):
            raise RuntimeError("balayage indisponible")
        if path.endswith("/issues"):
            return [{"number": 7, "title": "T", "labels": [],
                     "updated_at": "u", "state": "open"}]
        if path.endswith("/issues/7/comments"):
            return [_commentaire(7)]
        raise AssertionError(f"appel inattendu: {path}")

    monkeypatch.setattr(gs, "_gh_api", faux_gh_api)
    snapshot = {"comments": {}, "issues": {}, "meta": {
        "comment_stamps": {"7": time.time() - 300}}}
    out, calls, stats = gs.ensure_comments("o/r", [7], snapshot)
    assert stats["lus"] == 1
    assert stats.get("balayage_echoue"), "l'echec du balayage n'est pas dit"
    assert out["comments"]["7"][0]["body"].startswith("[CLAIMED]")


def test_un_verrou_tenu_par_un_processus_mort_est_casse(monkeypatch,
                                                          tmp_path):
    """Un processus tue laisse le verrou derriere lui.

    Mesure du 27/10 : un tirage interrompu a laisse le fichier de verrou,
    et toutes les lanes de la machine ont attendu `LOCK_STALE_SECONDS`
    (15 min) avant de pouvoir rafraichir. Un verrou dont le **pid est
    mort** est casse immediatement.
    """
    monkeypatch.setattr(gs, "snapshot_root", lambda: tmp_path / "snap")
    monkeypatch.setattr(gs, "LOCK_STALE_SECONDS", 900)
    directory = gs.snapshot_dir("jsboige/CoursIA")
    directory.mkdir(parents=True, exist_ok=True)
    lock = directory / "refresh.lock"
    lock.write_text("999999999", encoding="utf-8")   # pid mort
    with gs.snapshot_lock("jsboige/CoursIA", timeout=5):
        assert lock.read_text(encoding="utf-8") == str(os.getpid())
    assert not lock.exists()


# --- les stamps servis par l'instantane --------------------------------------


def _instantane_frais(pig_module=pig):
    """Pose un instantane qui sert l'issue 7 (commentaires frais)."""
    now = time.time()
    pig_module._BELT_SNAPSHOT = {
        "comments": {"7": [_commentaire(7, body="[CLAIMED] lane a:b -- x")]},
        "meta": {"comment_stamps": {"7": now}},
    }
    pig_module._PASS_SNAPSHOT = None


def test_les_stamps_viennent_de_l_instantane_et_les_non_servis_sont_separes():
    _instantane_frais()
    served, missing = pig._claim_stamps_from_snapshot([7, 9])
    assert missing == [9]
    assert 7 in served
    # Un stamp `None` est une MESURE (aucun marqueur), pas une absence.
    assert served[7] is None or isinstance(served[7], str)


def test_un_stamp_absent_de_l_instantane_n_est_jamais_fabrique():
    """Aucun instantane : tout est non servi, aucun stamp invente."""
    pig._BELT_SNAPSHOT = None
    pig._PASS_SNAPSHOT = None
    served, missing = pig._claim_stamps_from_snapshot([7])
    assert served == {}
    assert missing == [7]


def test_le_balaiage_est_servi_par_le_meme_reducteur_que_la_voie_reseau():
    """Le stamp calcule en memoire vaut celui de la voie reseau.

    La reduction est la meme (`_claim_stamp_from_comments`), donc le
    resultat ne peut pas diverger : le test compare les deux formes.
    """
    comments = [
        {"body": "[INFO] candidate-delivered lane a:b -- x",
         "createdAt": "2026-10-27T10:00:00Z", "author": {"login": "a"},
         "url": "u1"},
        {"body": "[CLAIMED] lane c:d -- y",
         "createdAt": "2026-10-26T10:00:00Z", "author": {"login": "c"},
         "url": "u2"},
    ]
    assert pig._claim_stamp_from_comments(comments) == "2026-10-27T10:00:00Z"


def test_l_evenement_de_livraison_vient_de_l_instantane():
    """La sonde d'evenement (#22500) lit l'instantane, sans requete.

    Elle rend le meme triplet que la voie historique -- le reducteur est
    partage, donc la divergence est impossible par construction.
    """
    comments = [
        {"body": "[DELIVERED] lane a:b -- PR #1",
         "createdAt": "2026-10-27T10:00:00Z", "author": {"login": "a"},
         "url": "u1"},
    ]
    assert pig._delivery_event_from_comments(comments) == (
        True, True, "2026-10-27T10:00:00Z")
    assert pig._delivery_event_from_comments([]) == (False, False, None)


def test_l_evenement_de_livraison_est_serve_par_l_instantane(monkeypatch):
    """Le transport historique ne doit PAS etre appele quand l'instantane
    sert l'issue."""
    instantane = {
        "comments": {"7": [{"body": "[FROZEN] lane a:b",
                            "createdAt": "2026-10-27T10:00:00Z",
                            "author": {"login": "a"}, "url": "u1"}]},
        "meta": {"comment_stamps": {"7": time.time()}},
    }
    monkeypatch.setattr(pig, "_BELT_SNAPSHOT", instantane)
    monkeypatch.setattr(pig, "_PASS_SNAPSHOT", None)

    def faux_run(*a, **kw):
        raise AssertionError("appel reseau inattendu")

    monkeypatch.setattr(pig.subprocess, "run", faux_run)
    verdict = pig.delivery_event(7)
    assert verdict[0] is True
    assert verdict[2] == "2026-10-27T10:00:00Z"


def test_m_le_batch_sert_le_payload_depuis_l_instantane(monkeypatch):
    """Le mode batch de `check_lane_claim` doit lire l'instantane.

    Regression mesuree le 27/10 : la voie EN PROCESSUS du tapis installe
    l'instantane puis appelle `check_issues_batch`, qui relisait chaque
    issue par `gh issue view` -- 1,19 s par issue, soit 179 s pour les 150
    numeros de la fenetre de service. Le batch doit donc servir le payload
    depuis l'instantane, et ne jamais appeler le transport historique
    quand l'instantane couvre l'issue.
    """
    clc = pig._claim_reader_module()
    instantane = {
        "issues": {"7": {"number": 7, "title": "Un titre", "labels": []}},
        "comments": {"7": [{"body": "[CLAIMED] lane autre:lane -- x",
                            "created_at": "2026-10-27T10:00:00Z",
                            "updated_at": "2026-10-27T10:00:00Z",
                            "user": {"login": "autre"},
                            "html_url": "u1",
                            "issue_url": "i1"}]},
    }
    clc.set_snapshot(instantane)
    try:
        def faux_gh(issue):
            raise AssertionError(f"transport historique appele pour {issue}")

        payloads = []

        def faux_run_check(payload, lane, **kw):
            payloads.append(payload)
            return 0

        monkeypatch.setattr(clc, "_gh_issue_comments", faux_gh)
        monkeypatch.setattr(clc, "_run_check", faux_run_check)
        resultat = clc.check_issues_batch(["7"], "ma:lane")
    finally:
        clc.set_snapshot(None)

    assert payloads, "le batch n'a rien evalue"
    assert payloads[0]["number"] == 7
    assert payloads[0]["comments"], "les commentaires de l'instantane sont absents"
    assert resultat["results"]["7"]["code"] == "FREE"


def test_m_le_batch_retombe_sur_le_reseau_sans_instantane(monkeypatch):
    """Sans instantane (ou pour une issue non couverte), le batch lit le
    reseau : le repli doit rester en place, jamais un verdict fabrique."""
    clc = pig._claim_reader_module()
    clc.set_snapshot(None)
    appels = []

    def faux_gh(issue):
        appels.append(issue)
        return {"number": int(issue), "title": "t", "labels": [],
                "comments": []}

    def faux_run_check(payload, lane, **kw):
        return 0

    monkeypatch.setattr(clc, "_gh_issue_comments", faux_gh)
    monkeypatch.setattr(clc, "_run_check", faux_run_check)
    resultat = clc.check_issues_batch(["9"], "ma:lane")
    assert appels == ["9"]
    assert resultat["results"]["9"]["code"] == "FREE"


def test_index_des_prs_equivaut_au_predicat_legacy(monkeypatch):
    """#22983 -- l'index des numeros cites doit rendre EXACTEMENT les memes
    PRs que le balayage predicat par candidat qu'il remplace."""
    clc = pig._claim_reader_module()

    prs = [
        {"number": 1, "body": "Closes #42"},
        {"number": 2, "body": "une reference nue #42 dans le texte"},
        {"number": 3, "body": "See #4242"},
        {"number": 4, "body": "rien ici"},
        {"number": 5, "body": "Part of #42 et #7"},
    ]

    index = clc._open_prs_by_referenced_issue(prs)
    for pr in prs:
        for numero in (42, 4242, 7, 99):
            legacy = clc._pr_body_references_issue(pr.get("body") or "", numero)
            assert (pr in index.get(numero, [])) is legacy, (
                f"divergence sur la PR #{pr['number']} / #{numero}")

    assert sorted(p["number"] for p in index.get(42, [])) == [1, 2, 5]
    assert sorted(p["number"] for p in index.get(7, [])) == [5]
    assert index.get(4242) == [prs[2]]


def test_index_ne_se_melange_pas_entre_deux_listes(monkeypatch):
    """La memo de l'index est keyed par l'IDENTITE de la liste : deux
    listes successives ne doivent pas se partager un index perime."""
    clc = pig._claim_reader_module()
    a = [{"number": 1, "body": "#11"}]
    b = [{"number": 2, "body": "#22"}]
    assert clc._open_prs_by_referenced_issue(a).get(22) is None
    assert clc._open_prs_by_referenced_issue(b).get(11) is None
