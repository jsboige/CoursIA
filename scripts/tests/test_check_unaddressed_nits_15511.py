"""#15511 (P1) : le gate B.0 detecte la boucle de diagnostic sans action.

Motif fondateur : PR #14821 -- 31 commentaires / 68 101 caracteres
d'infra-diagnostic sur 5 jours, pour un livrable qui n'avait pas bouge
depuis le commit du premier jour (~90 % des commentaires sans action
attachee).

Remede P1 de l'issue : taxonomie d'emission en premiere ligne non vide
(`[ACTION]` / `[DIAG]` / `[ASK]`), et `check_unaddressed_nits.py` bloque
la PR a plus de 3 `[DIAG]` consecutifs sans `[ACTION]` intercale.

Le contrat est cote EMISSION (lecon #14682) : un commentaire non tague
est INVISIBLE pour ce detecteur. Les tests verifient les deux bordures
de ce contrat -- transparence du non-tague et de `[ASK]`, neutralite des
bots et du post-cutoff, seuil strictement superieur a 3.

Aucun reseau : `analyse` est pure, les donnees sont synthetiques.
"""
import importlib.util
import sys
from datetime import datetime, timezone
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_unaddressed_nits.py"
spec = importlib.util.spec_from_file_location("check_unaddressed_nits_15511", SCRIPT)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

CUTOFF = datetime(2026, 10, 1, 20, 0, tzinfo=timezone.utc)


def _c(login, minutes, body):
    at = datetime(2026, 10, 1, 10, minutes, tzinfo=timezone.utc).isoformat()
    return {"author": {"login": login}, "createdAt": at, "body": body}


def _pr(comments):
    return {"number": 1, "title": "t", "author": {"login": "jsboige"},
            "comments": comments, "reviews": [], "commits": []}


def _analyse(comments):
    return mod.analyse(_pr(comments), [], CUTOFF)


def test_quatre_diag_consecutifs_bloquent():
    res = _analyse([
        _c("jsboige", 0, "[DIAG] etat du pool : rien de neuf"),
        _c("jsboige", 5, "[DIAG] le check rouge date d'avant le garde"),
        _c("jsboige", 10, "[DIAG] re-mesure : toujours rouge"),
        _c("jsboige", 15, "[DIAG] troisieme passe : le rouge tient"),
    ])
    assert res["diag_loop"]["max_run"] == 4
    assert res["blocked"] is True
    entry = next(b for b in res["blocking"] if b["kind"] == "DIAG-LOOP")
    assert entry["src"] == "comment"
    assert entry["excerpt"]


def test_action_intercale_rompt_la_serie():
    res = _analyse([
        _c("jsboige", 0, "[DIAG] etat du pool"),
        _c("jsboige", 5, "[DIAG] toujours rien"),
        _c("jsboige", 10, "[ACTION] rerun du job rouge 41223549682, commit 093d935e09"),
        _c("jsboige", 15, "[DIAG] re-mesure apres rerun"),
        _c("jsboige", 20, "[DIAG] suite de la mesure"),
    ])
    assert res["diag_loop"]["max_run"] == 2
    assert res["diag_loop"]["action_count"] == 1
    assert res["blocked"] is False


def test_non_tague_et_ask_sont_transparents():
    # Seul [ACTION] interrompt (issue P1 : « sans [ACTION] intercale ») ;
    # un commentaire non tague, ni [ASK] ni [ASK USER], ne coupe rien.
    res = _analyse([
        _c("jsboige", 0, "[DIAG] premiere mesure"),
        _c("jsboige", 5, "commentaire de protocole ordinaire, non tague"),
        _c("jsboige", 10, "[ASK] decision tierce attendue sur le schema"),
        _c("jsboige", 15, "[ASK USER] arbitrage demande"),
        _c("jsboige", 20, "[DIAG] deuxieme mesure"),
        _c("jsboige", 25, "[DIAG] troisieme mesure"),
        _c("jsboige", 30, "[DIAG] quatrieme mesure"),
    ])
    assert res["diag_loop"]["max_run"] == 4
    assert res["blocked"] is True


def test_trois_diag_sont_un_signal_sans_blocage():
    res = _analyse([
        _c("jsboige", 0, "[DIAG] un"),
        _c("jsboige", 5, "[DIAG] deux"),
        _c("jsboige", 10, "[DIAG] trois"),
    ])
    assert res["diag_loop"]["max_run"] == 3
    assert res["blocked"] is False


def test_bots_et_post_cutoff_exclus():
    res = _analyse([
        _c("jsboige", 0, "[DIAG] un"),
        _c("jsboige", 5, "[DIAG] deux"),
        _c("jsboige", 10, "[DIAG] trois"),
        _c("github-actions", 15, "[DIAG] bot : compte pour rien"),
        {"author": {"login": "jsboige"},
         "createdAt": "2026-10-02T10:00:00+00:00",  # posterieur au cutoff
         "body": "[DIAG] quatre"},
    ])
    assert res["diag_loop"]["max_run"] == 3
    assert res["blocked"] is False


def test_tag_lu_sur_la_premiere_ligne_non_vide():
    # ligne vide d'ouverture : le tag reste lu ; un titre markdown "## [DIAG]"
    # n'est PAS un tag (ancre de debut de ligne).
    res = _analyse([
        _c("jsboige", 0, "\n[DIAG] apres une ligne vide"),
        _c("jsboige", 5, "## [DIAG] titre de section"),
        _c("jsboige", 10, "[DIAG] deux"),
    ])
    assert res["diag_loop"]["max_run"] == 2
    assert res["blocked"] is False


def test_pr_sans_taxonomie_inchangee():
    # Contrat d'emission : sans aucun tag, le detecteur rend max_run=0 et
    # le verdict de l'organe ne change pas d'un iota.
    res = _analyse([
        _c("jsboige", 0, "reponse ecrite qui adresse la remarque"),
        _c("clusterManager-Myia", 5, "[Hermes] verdict de review"),
    ])
    assert res["diag_loop"]["max_run"] == 0
    assert res["diag_loop"]["diag_count"] == 0
    assert res["diag_loop"]["action_count"] == 0
    assert res["blocked"] is False
