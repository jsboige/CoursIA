from __future__ import annotations

import json
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import ci_overflow_controller as ctl  # noqa: E402

NOW = datetime(2026, 10, 27, 12, 0, tzinfo=timezone.utc)
# Derniere ecriture de la variable, hors fenetre de dwell : le controleur
# n'est pas bloque par son propre dwell dans ces tests de CLI.
OLD = NOW - timedelta(hours=2)


def hosted(queued: int = 0, old: int = 0, oldest: float = 0.0,
           complete: bool = True, truncated: bool = False, reason: str = "",
           in_progress: int = 0, in_progress_unread: int = 0) -> ctl.HostedSample:
    return ctl.HostedSample(queued=queued, old=old, oldest_age_min=oldest,
                             complete=complete, truncated=truncated, reason=reason,
                             in_progress=in_progress,
                             in_progress_unread=in_progress_unread)


def local(free: int = 0, online: int = 0, starved: int = 0,
          busy: int = 0, unknown: int = 0,
          complete: bool = True, truncated: bool = False, reason: str = "") -> ctl.LocalSample:
    return ctl.LocalSample(online=online, free=free, starved=starved, busy=busy,
                            unknown=unknown, complete=complete, truncated=truncated,
                            reason=reason)


def cohort(queued: int = 0, in_progress: int = 0, complete: bool = True,
           truncated: bool = False, in_progress_unread: int = 0,
           reason: str = "") -> ctl.CohortSample:
    """Charge rendue de la cohorte, mesuree sur le parc local."""
    return ctl.CohortSample(queued=queued, in_progress=in_progress,
                            complete=complete, truncated=truncated,
                            in_progress_unread=in_progress_unread,
                            reason=reason)


# --- Regle de decision (fonction pure) -------------------------------------

def test_offre_saturee_et_parc_local_libre_bascule_vers_true():
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0), local(free=7, online=14),
                     current="false", now=NOW)
    assert d.action == "SWITCH_TRUE" and d.target == "true"


def test_file_hebergee_videe_bascule_vers_false():
    # La liberation exige une charge rendue de cohorte dans la marge
    # hebergee ET sa confirmation : la cohorte ne rend rien sur les DEUX
    # lectures.
    d = ctl.evaluate(hosted(queued=0, old=0, oldest=0.0), local(free=7, online=14),
                     current="true", cohort=cohort(), cohort_confirm=cohort(),
                     now=NOW)
    assert d.action == "SWITCH_FALSE" and d.target == "false"


def test_etat_deja_au_bout_ne_bascule_pas():
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0), local(free=7, online=14),
                     current="true", now=NOW)
    assert d.action == "HOLD" and d.target == "true"


def test_parc_local_affame_ne_bascule_pas_vers_true():
    # Garde de securite : on n'envoie pas de debordement vers un parc qui
    # n'absorbe rien, meme si l'offre hebergee est saturee.
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0),
                     local(free=2, online=14, starved=4), current="true", now=NOW)
    assert d.action == "SWITCH_FALSE" and d.target == "false"


def test_parc_local_affame_deja_en_false_ne_bascule_pas():
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0),
                     local(free=2, online=14, starved=4), current="false", now=NOW)
    assert d.action == "HOLD"


def test_parc_local_sature_n_accepte_pas_le_debordement():
    # Le parc local n'a plus de slot libre -> on n'active pas la jambe locale.
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0),
                     local(free=0, online=14), current="false", now=NOW)
    assert d.action == "HOLD"


def test_jeux_de_jobs_en_file_sous_le_seuil_ne_declenchent_pas():
    d = ctl.evaluate(hosted(queued=2, old=1, oldest=20.0), local(free=7, online=14),
                     current="false", now=NOW)
    assert d.action == "HOLD"


def test_mesure_illisible_ne_bascule_jamais():
    d = ctl.evaluate(hosted(complete=False, reason="listing en echec"),
                     local(free=7, online=14), current="false", now=NOW)
    assert d.action == "UNREADABLE"


def test_mesure_locale_illisible_ne_bascule_jamais():
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0),
                     local(complete=False, reason="droit admin absent"),
                     current="false", now=NOW)
    assert d.action == "UNREADABLE"


def test_dwell_differe_la_bascule():
    # Backlog SOFT (le plus ancien attend 20 min, sous le seuil de panique
    # de 30 min) : le dwell oppose la re-absorption.
    recent = NOW - timedelta(minutes=5)
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=20.0), local(free=7, online=14),
                     current="false", dwell_minutes=30, last_change_at=recent, now=NOW)
    assert d.action == "HOLD" and "dwell" in d.reason


def test_dwell_derape_une_bascule_ancienne():
    old = NOW - timedelta(minutes=120)
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0), local(free=7, online=14),
                     current="false", dwell_minutes=30, last_change_at=old, now=NOW)
    assert d.action == "SWITCH_TRUE"


# --- CLI --------------------------------------------------------------------

def _env(monkeypatch, token: str | None = "t", write_token: str | None = None):
    for name in ("GH_TOKEN", "GITHUB_TOKEN", "ACTIONS_VARIABLES_PAT"):
        monkeypatch.delenv(name, raising=False)
    if token is not None:
        monkeypatch.setenv("GH_TOKEN", token)
    if write_token is not None:
        monkeypatch.setenv("ACTIONS_VARIABLES_PAT", write_token)


def test_cli_sans_jeton_refuse_sans_ecrire(monkeypatch, capsys):
    _env(monkeypatch, None)
    monkeypatch.setattr(ctl, "write_variable", lambda *a, **k: (_ for _ in ()).throw(
        AssertionError("aucune ecriture sans jeton")))
    rc = ctl.main(["--repo", "jsboige/CoursIA", "--apply"])
    assert rc == ctl.EXIT_REFUSED
    assert "variables: write" in capsys.readouterr().err


def test_cli_dry_run_ne_bascule_pas(monkeypatch, capsys):
    _env(monkeypatch)
    monkeypatch.setattr(ctl, "read_variable", lambda *a, **k: ("false", OLD, ""))
    monkeypatch.setattr(ctl, "collect_hosted",
                        lambda *a, **k: hosted(queued=9, old=6, oldest=41.0))
    monkeypatch.setattr(ctl, "collect_local",
                        lambda *a, **k: local(free=7, online=14))
    written = []
    monkeypatch.setattr(ctl, "write_variable",
                        lambda *a, **k: (written.append(a), (True, "ok"))[1])
    rc = ctl.main(["--repo", "jsboige/CoursIA", "--json"])
    assert rc == ctl.EXIT_OK
    assert written == []
    report = json.loads(capsys.readouterr().out)
    assert report["verdict"] == "SWITCH_TRUE"
    assert report["written"] is False and report["mode"] == "dry-run"


def test_cli_apply_bascule_et_ecrit(monkeypatch, capsys):
    _env(monkeypatch, write_token="pat-variables")
    monkeypatch.setattr(ctl, "read_variable", lambda *a, **k: ("false", OLD, ""))
    monkeypatch.setattr(ctl, "collect_hosted",
                        lambda *a, **k: hosted(queued=9, old=6, oldest=41.0))
    monkeypatch.setattr(ctl, "collect_local",
                        lambda *a, **k: local(free=7, online=14))
    seen = {}

    def fake_write(repo, name, value, token):
        seen["value"] = value
        seen["token"] = token
        return True, "variable mise a jour"

    monkeypatch.setattr(ctl, "write_variable", fake_write)
    rc = ctl.main(["--repo", "jsboige/CoursIA", "--apply", "--json"])
    assert rc == ctl.EXIT_OK
    assert seen["value"] == "true"
    # L'ecriture passe par le jeton DEDIE, pas par le jeton de mesure.
    assert seen["token"] == "pat-variables"
    report = json.loads(capsys.readouterr().out)
    assert report["written"] is True and report["verdict"] == "SWITCH_TRUE"
    assert report["write_token_present"] is True
    assert report["write_blocked"] == ""


def test_cli_ecriture_refusee_rend_refused(monkeypatch, capsys):
    _env(monkeypatch, write_token="pat-variables")
    monkeypatch.setattr(ctl, "read_variable", lambda *a, **k: ("false", OLD, ""))
    monkeypatch.setattr(ctl, "collect_hosted",
                        lambda *a, **k: hosted(queued=9, old=6, oldest=41.0))
    monkeypatch.setattr(ctl, "collect_local",
                        lambda *a, **k: local(free=7, online=14))
    monkeypatch.setattr(ctl, "write_variable",
                        lambda *a, **k: (False, "HTTP 403: Resource not accessible"))
    rc = ctl.main(["--repo", "jsboige/CoursIA", "--apply", "--json"])
    assert rc == ctl.EXIT_REFUSED
    report = json.loads(capsys.readouterr().out)
    assert report["verdict"] == "REFUSED"


def test_cli_lecture_impossible_rend_le_verdict_sans_ecrire(monkeypatch, capsys):
    # L'etat de la variable illisible n'empeêche plus le VERDICT : il
    # empeche l'ECRITURE (ni l'etat courant ni le dwell ne sont
    # verifiables). C'est ce que demande l'arbitrage user (a) du 27/10 pour
    # le mode degrade : le verdict est rendu et la cause est nommee.
    _env(monkeypatch)
    monkeypatch.setattr(ctl, "read_variable",
                        lambda *a, **k: (None, None, "HTTP 403: Resource not accessible"))
    monkeypatch.setattr(ctl, "collect_hosted",
                        lambda *a, **k: hosted(queued=9, old=6, oldest=41.0))
    monkeypatch.setattr(ctl, "collect_local",
                        lambda *a, **k: local(free=7, online=14))
    monkeypatch.setattr(ctl, "write_variable", lambda *a, **k: (_ for _ in ()).throw(
        AssertionError("aucune ecriture si l'etat de la variable est inconnu")))
    rc = ctl.main(["--repo", "jsboige/CoursIA", "--apply", "--json"])
    report = json.loads(capsys.readouterr().out)
    assert report["verdict"] == "SWITCH_TRUE"
    assert report["written"] is False
    assert report["state_known"] is False
    assert "variables: read" in report["state_reason"]
    # Cause principale nommee : le jeton d'ecriture absent. L'etat
    # illisible est rapporte a part (c'est sa consequence, pas la cause).
    assert "ACTIONS_VARIABLES_PAT" in report["write_blocked"]
    assert rc == ctl.EXIT_UNREADABLE


def test_etat_inconnu_bloque_l_ecriture_meme_avec_le_secret_present(monkeypatch, capsys):
    # Secret present MAIS etat de la variable illisible : l'ecriture est
    # refusee (le dwell et l'etat courant seraient invérifiables).
    _env(monkeypatch, write_token="pat-variables")
    monkeypatch.setattr(ctl, "read_variable",
                        lambda *a, **k: (None, None, "HTTP 403: Resource not accessible"))
    monkeypatch.setattr(ctl, "collect_hosted",
                        lambda *a, **k: hosted(queued=9, old=6, oldest=41.0))
    monkeypatch.setattr(ctl, "collect_local",
                        lambda *a, **k: local(free=7, online=14))
    monkeypatch.setattr(ctl, "write_variable", lambda *a, **k: (_ for _ in ()).throw(
        AssertionError("aucune ecriture si l'etat de la variable est inconnu")))
    rc = ctl.main(["--repo", "jsboige/CoursIA", "--apply", "--json"])
    report = json.loads(capsys.readouterr().out)
    assert report["verdict"] == "SWITCH_TRUE"
    assert report["written"] is False
    assert report["write_token_present"] is True
    assert "etat de la variable" in report["write_blocked"]
    assert "variables: read" in report["state_reason"]
    assert rc == ctl.EXIT_UNREADABLE


def test_cli_mesure_illisible_sort_en_1(monkeypatch, capsys):
    _env(monkeypatch)
    monkeypatch.setattr(ctl, "read_variable", lambda *a, **k: ("false", OLD, ""))
    monkeypatch.setattr(ctl, "collect_hosted",
                        lambda *a, **k: hosted(complete=False, reason="listing en echec"))
    monkeypatch.setattr(ctl, "collect_local",
                        lambda *a, **k: local(free=7, online=14))
    rc = ctl.main(["--repo", "jsboige/CoursIA", "--json"])
    assert rc == ctl.EXIT_UNREADABLE
    assert json.loads(capsys.readouterr().out)["verdict"] == "UNREADABLE"


# --- Jeton d'inventaire des runners (point ai-01 du 2026-10-27, 14:27Z) -----
#
# `github.token` ne porte pas le droit de lire `/actions/runners` : sans le
# secret read-only `RUNNERS_READ_PAT` que six workflows freres exposent deja,
# chaque passage du workflow planifie rendait UNREADABLE. Ces tests fixent les
# trois comportements : jeton dedie utilise, repli sur le jeton courant en
# local, et cause NOMMEE quand aucun ne donne le droit.

def _inventory_unavailable(reason: str = "HTTP 403: Resource not accessible"):
    return ctl.crs.InventoryUnavailable(reason=reason)


def test_collect_local_lit_l_inventaire_avec_le_jeton_dedie(monkeypatch):
    seen = {}

    def fake_inventory(repo, label, token):
        seen["token"] = token
        return ctl.crs.RunnerInventory(online=["slot-1"], idle=["slot-1"])

    monkeypatch.setattr(ctl.crs, "fetch_inventory", fake_inventory)
    sample = ctl.collect_local(
        "jsboige/CoursIA", 15.0, 40, NOW, "ghs_workflow",
        measure_starvation=False, runners_token="pat-runners",
    )
    assert seen["token"] == "pat-runners"
    assert sample.complete is True and sample.free == 1


def test_collect_local_sans_jeton_dedie_retombe_sur_le_jeton_courant(monkeypatch):
    # L'operateur en local presente un jeton qui a le droit : ne pas exiger le
    # secret du depot dans ce cas (aucune regression de la commande locale).
    seen = {}

    def fake_inventory(repo, label, token):
        seen["token"] = token
        return ctl.crs.RunnerInventory(online=["slot-1"], idle=["slot-1"])

    monkeypatch.setattr(ctl.crs, "fetch_inventory", fake_inventory)
    sample = ctl.collect_local(
        "jsboige/CoursIA", 15.0, 40, NOW, "jsboige-token",
        measure_starvation=False,
    )
    assert seen["token"] == "jsboige-token"
    assert sample.complete is True


def test_collect_local_sans_jeton_dedie_nomme_la_cause(monkeypatch):
    monkeypatch.setattr(
        ctl.crs, "fetch_inventory",
        lambda repo, label, token: _inventory_unavailable(),
    )
    sample = ctl.collect_local(
        "jsboige/CoursIA", 15.0, 40, NOW, "ghs_workflow",
        measure_starvation=False,
    )
    assert sample.complete is False
    assert "RUNNERS_READ_PAT" in sample.reason
    assert "jeton d'inventaire des runners absent" in sample.reason


def test_cli_sans_jeton_d_inventaire_sort_unreadable_nomme(monkeypatch, capsys):
    # Le point du coordinateur : jamais un OK par defaut quand l'inventaire du
    # parc est illisible faute de jeton.
    _env(monkeypatch)
    monkeypatch.delenv("RUNNERS_READ_PAT", raising=False)
    monkeypatch.setattr(ctl, "read_variable", lambda *a, **k: ("false", OLD, ""))
    monkeypatch.setattr(ctl, "collect_hosted",
                        lambda *a, **k: hosted(queued=9, old=6, oldest=41.0))
    monkeypatch.setattr(
        ctl.crs, "fetch_inventory",
        lambda repo, label, token: _inventory_unavailable(),
    )
    rc = ctl.main(["--repo", "jsboige/CoursIA", "--json"])
    assert rc == ctl.EXIT_UNREADABLE
    report = json.loads(capsys.readouterr().out)
    assert report["verdict"] == "UNREADABLE"
    assert "RUNNERS_READ_PAT" in report["reason"]
    assert report["written"] is False


# --- Canal d'ecriture dedie (arbitrage user (a), 27/10) ------------------
#
# Le jeton qui ecrit la variable est un canal DEDIE (`ACTIONS_VARIABLES_PAT`),
# distinct du jeton de mesure. Aucun repli : sans lui, le VERDICT est rendu,
# rien n'est ecrit, et la cause est nommee.

def test_secret_present_ecrit_avec_le_jeton_dedie(monkeypatch, capsys):
    _env(monkeypatch, write_token="pat-variables")
    monkeypatch.setattr(ctl, "read_variable", lambda *a, **k: ("false", OLD, ""))
    monkeypatch.setattr(ctl, "collect_hosted",
                        lambda *a, **k: hosted(queued=9, old=6, oldest=41.0))
    monkeypatch.setattr(ctl, "collect_local",
                        lambda *a, **k: local(free=7, online=14))
    seen = {}

    def fake_write(repo, name, value, token):
        seen["token"] = token
        seen["value"] = value
        return True, "variable mise a jour"

    monkeypatch.setattr(ctl, "write_variable", fake_write)
    rc = ctl.main(["--repo", "jsboige/CoursIA", "--apply", "--json"])
    assert rc == ctl.EXIT_OK
    assert seen["value"] == "true"
    assert seen["token"] == "pat-variables"
    report = json.loads(capsys.readouterr().out)
    assert report["written"] is True
    assert report["write_token_present"] is True
    assert report["write_blocked"] == ""


def test_secret_absent_verdict_seul_et_aucune_ecriture(monkeypatch, capsys):
    _env(monkeypatch)
    monkeypatch.setattr(ctl, "read_variable", lambda *a, **k: ("false", OLD, ""))
    monkeypatch.setattr(ctl, "collect_hosted",
                        lambda *a, **k: hosted(queued=9, old=6, oldest=41.0))
    monkeypatch.setattr(ctl, "collect_local",
                        lambda *a, **k: local(free=7, online=14))
    monkeypatch.setattr(ctl, "write_variable", lambda *a, **k: (_ for _ in ()).throw(
        AssertionError("aucune ecriture sans jeton d'ecriture")))
    rc = ctl.main(["--repo", "jsboige/CoursIA", "--apply", "--json"])
    assert rc == ctl.EXIT_OK
    report = json.loads(capsys.readouterr().out)
    # Le VERDICT est rendu...
    assert report["verdict"] == "SWITCH_TRUE" and report["target"] == "true"
    # ... mais rien n'est ecrit, et la cause est nommee.
    assert report["written"] is False
    assert report["write_token_present"] is False
    assert "ACTIONS_VARIABLES_PAT" in report["write_blocked"]
    assert "Aucun repli" in report["write_blocked"]


def test_secret_absent_et_vide_est_traite_comme_absent(monkeypatch, capsys):
    # Un secret pose mais VIDE est un secret absent : meme traitement, meme
    # cause nommee.
    _env(monkeypatch)
    monkeypatch.setenv("ACTIONS_VARIABLES_PAT", "   ")
    monkeypatch.setattr(ctl, "read_variable", lambda *a, **k: ("false", OLD, ""))
    monkeypatch.setattr(ctl, "collect_hosted",
                        lambda *a, **k: hosted(queued=9, old=6, oldest=41.0))
    monkeypatch.setattr(ctl, "collect_local",
                        lambda *a, **k: local(free=7, online=14))
    monkeypatch.setattr(ctl, "write_variable", lambda *a, **k: (_ for _ in ()).throw(
        AssertionError("aucune ecriture avec un secret vide")))
    ctl.main(["--repo", "jsboige/CoursIA", "--apply", "--json"])
    report = json.loads(capsys.readouterr().out)
    assert report["written"] is False
    assert report["write_token_present"] is False
    assert "ACTIONS_VARIABLES_PAT" in report["write_blocked"]


def test_resume_du_job_nomme_la_cause_du_mode_degrade(monkeypatch, tmp_path):
    _env(monkeypatch)
    monkeypatch.setattr(ctl, "read_variable", lambda *a, **k: ("false", OLD, ""))
    monkeypatch.setattr(ctl, "collect_hosted",
                        lambda *a, **k: hosted(queued=9, old=6, oldest=41.0))
    monkeypatch.setattr(ctl, "collect_local",
                        lambda *a, **k: local(free=7, online=14))
    out = tmp_path / "summary.md"
    ctl.main(["--repo", "jsboige/CoursIA", "--apply", "--json",
              "--summary-out", str(out)])
    text = out.read_text(encoding="utf-8")
    assert "SWITCH_TRUE" in text
    assert "DEGRADE" in text
    assert "ACTIONS_VARIABLES_PAT" in text
    assert "NON ECRIT" in text


def test_resume_du_job_sans_degrade_quand_tout_est_nominal(monkeypatch, tmp_path):
    _env(monkeypatch, write_token="pat-variables")
    monkeypatch.setattr(ctl, "read_variable", lambda *a, **k: ("false", OLD, ""))
    monkeypatch.setattr(ctl, "collect_hosted",
                        lambda *a, **k: hosted(queued=9, old=6, oldest=41.0))
    monkeypatch.setattr(ctl, "collect_local",
                        lambda *a, **k: local(free=7, online=14))
    monkeypatch.setattr(ctl, "write_variable",
                        lambda *a, **k: (True, "variable mise a jour"))
    out = tmp_path / "summary.md"
    ctl.main(["--repo", "jsboige/CoursIA", "--apply", "--json",
              "--summary-out", str(out)])
    text = out.read_text(encoding="utf-8")
    assert "DEGRADE" not in text
    assert "ECRIT" in text


# --- Lecture tronquee (point Hermes du 27/10, 12:53Z) --------------------
#
# Un budget de lecture atteint rend les comptes de file une BORNE
# INFERIEURE. Une borne inferieure etablit une affirmation POSITIVE (« au
# moins N jobs ages ») mais n'etablit AUCUNE affirmation NEGATIVE (« aucun
# job en file », « le parc local n'est pas affame »). La regle est donc
# directionnelle, et non « toute troncature interdit d'ecrire ».

def test_troncature_hebergee_bloque_la_bascule_vers_false():
    # « la file hebergee est videe » est NEGATIVE : sous troncature, le
    # compte lu est une borne inferieure, la file peut contenir des jobs
    # non lus -> on ne rend pas la main a l'offre hebergee.
    d = ctl.evaluate(hosted(queued=0, old=0, oldest=0.0, truncated=True,
                             reason="3 run(s) non lu(s)"),
                     local(free=7, online=14), current="true", now=NOW)
    assert d.action == "HOLD"
    assert "TRONQUEE" in d.reason


def test_troncature_locale_bloque_la_bascule_vers_true():
    # « le parc local n'est pas affame » est NEGATIVE : sous troncature
    # locale elle n'est pas etablie -> pas de debordement vers le local.
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0),
                     local(free=7, online=14, truncated=True,
                           reason="15 run(s) non lu(s)"),
                     current="false", now=NOW)
    assert d.action == "HOLD"
    assert "TRONQUEE" in d.reason


def test_troncature_hebergee_ne_bloque_pas_la_saturation():
    # « l'offre hebergee est saturee » est POSITIVE : la troncature ne fait
    # que sous-compter, elle n'annule pas la saturation etablie par les jobs
    # effectivement lus.
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0, truncated=True,
                             reason="3 run(s) non lu(s)"),
                     local(free=7, online=14), current="false", now=NOW)
    assert d.action == "SWITCH_TRUE" and d.target == "true"


def test_troncature_locale_ne_bloque_pas_la_constatation_d_affamescence():
    # « le parc local est affame » est POSITIVE : elle est confirmee par la
    # lecture partielle, donc on rend la main a l'offre hebergee.
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0),
                     local(free=2, online=14, starved=4, truncated=True,
                           reason="15 run(s) non lu(s)"),
                     current="true", now=NOW)
    assert d.action == "SWITCH_FALSE" and d.target == "false"


# --- #22937 vague 2 : la premise de liberation est l'AGE, pas le VIDE ------

def test_offre_hebergee_suit_bascule_vers_false_malgre_une_file_non_vide():
    """Une file hebergee NON VIDE dont rien n'attend au-dela du seuil de
    saturation, et une cohorte qui ne rend rien : la cohorte rend la main.

    La mesure du 27/10 (`hosted.queued = 74`, `old = 0`) ne suffit plus a
    elle seule : 74 jobs heberges depassent le plafond de l'offre
    (`HOSTED_CONCURRENCY_CAP`), la marge est negative, il n'y a donc pas de
    place ou rendre la cohorte. Le cas garde son interet sous le plafond :
    « aucun job n'attend » n'exige pas « aucune file ».

    La liberation exige DEUX lectures de la charge rendue qui tiennent dans
    la marge : sans la seconde, elle n'est pas confirmee et le controleur
    attend.
    """
    d = ctl.evaluate(hosted(queued=5, old=0, oldest=15.0),
                     local(free=29, online=32), current="true",
                     cohort=cohort(), cohort_confirm=cohort(), now=NOW)
    assert d.action == "SWITCH_FALSE" and d.target == "false"
    assert "charge rendue" in d.reason


def test_offre_hebergee_en_retard_de_1_a_2_jobs_ne_bascule_pas():
    """Bande morte entre les deux premises : 1 ou 2 jobs ages ne declenchent
    ni la liberation (l'offre suit -> aucun job de plus de 15 min) ni le
    debordement (seuil de saturation = 3). Le controleur attend."""
    d = ctl.evaluate(hosted(queued=9, old=2, oldest=20.0),
                     local(free=7, online=14), current="false", now=NOW)
    assert d.action == "HOLD"


def test_offre_hebergee_suit_mais_troncuree_ne_bascule_pas():
    """« l'offre hebergee n'attend pas » est une premise NEGATIVE : sous
    troncature, un job age peut etre dans la part non lue -> on ne rend pas
    la main."""
    d = ctl.evaluate(hosted(queued=5, old=0, oldest=15.0, truncated=True,
                             reason="3 run(s) non lu(s)"),
                     local(free=29, online=32), current="true",
                     cohort=cohort(), cohort_confirm=cohort(), now=NOW)
    assert d.action == "HOLD"
    assert "TRONQUEE" in d.reason


def test_l_offre_hebergee_suit_prime_sur_la_saturation():
    """Les deux premises ne peuvent pas etre vraies en meme temps : un job
    age de plus de 15 min est par definition un job en file. Ce test
    verifie l'ordre des regles quand la lecture est incoherente (old > 0 et
    oldest < seuil) : la saturation -- premise POSITIVE -- l'emporte, elle
    est confirmee par les jobs effectivement lus."""
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0),
                     local(free=7, online=14), current="false", now=NOW)
    assert d.action == "SWITCH_TRUE" and d.target == "true"


# --- #22937 vague 3 : la liberation mesure la COHORTE dans la MARGE ---------
#
# La regle `hosted.old == 0` seule est un ARTEFACT : pendant que la cohorte
# tourne en local, l'offre hebergee ne porte que les jobs hors debordement,
# elle parait donc allegee meme quand la charge de la cohorte est enorme.
# Liberer sur cette seule lecture rend la cohorte entiere a une offre qui
# s'etouffe derriere, et le dwell de 90 min interdit ensuite de revenir a
# `true` : on rejoue la nuit du 27/10 (reserve du coordinateur, 28/10).
#
# La vague 2 corrigeait ce defaut en mesurant l'occupation du PARC ENTIER
# contre un seuil absolu (2) -- et remplacait le pendule par un verrou : le
# parc porte en permanence des jobs STATIQUES qui ne reviendront jamais sur
# l'heberge, donc `charge > 2` des trois jobs statiques et la liberation
# n'avait plus jamais lieu (review du coordinateur, 28/10).
#
# La vague 3 mesure la charge rendue de la COHORTE (les workflows qui lisent
# `vars.CI_OVERFLOW_LOCAL`), et la compare a la MARGE hebergee (plafond moins
# les jobs heberges en file et en cours), sur deux lectures.


def test_liberation_exige_une_charge_rendue_dans_la_marge():
    """La cohorte rend 5 jobs, la marge hebergee n'en vaut que 2 : on ne rend
    pas la main. L'occupation du parc (busy/unknown) n'entre plus dans le
    calcul -- ici elle vaut 5 aussi, mais c'est la cohorte qui decide."""
    d = ctl.evaluate(hosted(queued=17, old=0, oldest=15.0, in_progress=1),
                     local(free=29, online=32, busy=5), current="true",
                     cohort=cohort(queued=5), cohort_confirm=cohort(queued=5),
                     now=NOW)
    assert d.action == "HOLD"
    assert "charge rendue" in d.reason
    assert "marge hebergee" in d.reason


def test_liberation_exige_la_confirmation_de_la_lecture():
    """Sans seconde lecture de la charge rendue, elle n'est pas confirmee."""
    d = ctl.evaluate(hosted(queued=5, old=0, oldest=15.0),
                     local(free=29, online=32), current="true",
                     cohort=cohort(), now=NOW)
    assert d.action == "HOLD"
    assert "confirmation" in d.reason


def test_liberation_refusee_par_une_confirmation_qui_contredit():
    """La premiere lecture tient dans la marge, la seconde la depasse :
    la charge rendue n'est pas confirmee, on attend."""
    d = ctl.evaluate(hosted(queued=17, old=0, oldest=15.0, in_progress=1),
                     local(free=29, online=32), current="true",
                     cohort=cohort(), cohort_confirm=cohort(queued=3), now=NOW)
    assert d.action == "HOLD"
    assert "confirmation" in d.reason


def test_marge_hebergee_nulle_ou_negative_ne_libere_pas():
    """L'offre hebergee est au-dela de son plafond : il n'y a pas de place ou
    rendre la cohorte, meme si la cohorte ne rend rien."""
    d = ctl.evaluate(hosted(queued=18, old=0, oldest=15.0, in_progress=2),
                     local(free=29, online=32), current="true",
                     cohort=cohort(), cohort_confirm=cohort(), now=NOW)
    assert d.action == "HOLD"
    assert "marge hebergee" in d.reason


def test_charge_rendue_tronquee_ne_libere_pas():
    """Une lecture tronquee fait de la charge rendue une borne INFERIEURE :
    « la charge tient dans la marge » est une affirmation NEGATIVE, elle
    n'est pas etablie."""
    d = ctl.evaluate(hosted(queued=5, old=0, oldest=15.0),
                     local(free=29, online=32), current="true",
                     cohort=cohort(truncated=True, reason="2 run(s) non lu(s)"),
                     cohort_confirm=cohort(), now=NOW)
    assert d.action == "HOLD"
    assert "TRONQUEE" in d.reason


def test_runs_locaux_en_cours_non_lus_ne_liberent_pas():
    """Des runs locaux en cours non lus rendent la charge de cohorte une
    borne INFERIEURE : on ne libere pas sur une borne inferieure."""
    d = ctl.evaluate(hosted(queued=5, old=0, oldest=15.0),
                     local(free=29, online=32), current="true",
                     cohort=cohort(in_progress_unread=4),
                     cohort_confirm=cohort(), now=NOW)
    assert d.action == "HOLD"
    assert "borne INFERIEURE" in d.reason


def test_occupation_hebergee_non_lue_rend_la_marge_non_etablie():
    """Des runs heberges en cours non lus rendent la marge une borne
    SUPERIEURE : on ne libere pas dessus."""
    d = ctl.evaluate(hosted(queued=2, old=0, oldest=15.0, in_progress_unread=6),
                     local(free=29, online=32), current="true",
                     cohort=cohort(), cohort_confirm=cohort(), now=NOW)
    assert d.action == "HOLD"
    assert "borne SUPERIEURE" in d.reason


def test_deux_lectures_dans_la_marge_liberent():
    """Les DEUX lectures tiennent dans la marge : la liberation a lieu."""
    d = ctl.evaluate(hosted(queued=5, old=0, oldest=15.0),
                     local(free=29, online=32), current="true",
                     cohort=cohort(queued=2, in_progress=1),
                     cohort_confirm=cohort(queued=1), now=NOW)
    assert d.action == "SWITCH_FALSE" and d.target == "false"


def test_le_dwell_ne_derange_jamais_la_liberation():
    """Le dwell oppose la LIBERATION comme il oppose la re-absorption : c'est
    elle qui fait revenir la cohorte, donc c'est elle qui reste freinee."""
    recent = NOW - timedelta(minutes=5)
    d = ctl.evaluate(hosted(queued=5, old=0, oldest=15.0),
                     local(free=29, online=32), current="true",
                     cohort=cohort(), cohort_confirm=cohort(), dwell_minutes=90,
                     last_change_at=recent, now=NOW)
    assert d.action == "HOLD" and "dwell" in d.reason


def test_le_dwell_derape_la_reabsorption_quand_le_backlog_est_dur():
    """Backlog DUR (le plus ancien attend 41 min > 30) : la re-absorption
    n'est plus differee par le dwell. C'est la starvation qu'on a vecue le
    27/10 : attendre 90 min la prolonge.

    L'echappement ne peut pas creer d'oscillation : il exige un backlog dur
    (le plus ancien job attend), ce qui est incompatible avec la premise de
    liberation (« l'offre hebergee n'attend pas »).
    """
    recent = NOW - timedelta(minutes=5)
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0),
                     local(free=7, online=14), current="false",
                     dwell_minutes=90, last_change_at=recent, now=NOW)
    assert d.action == "SWITCH_TRUE" and d.target == "true"
    assert "backlog dur" in d.reason


# --- La COHORTE : derivee du depot, jamais recopiee ------------------------
#
# La charge rendue n'est pas celle du parc : c'est celle des jobs dont le
# workflow lit `vars.CI_OVERFLOW_LOCAL`. La liste se derive du checkout a
# chaque passage (un workflow qui rejoint la forme hybride entre dans le
# calcul sans qu'on touche a l'organe), et une liste VIDE est un echec de
# derivation, jamais une cohorte qui ne rend rien.

def _workflow(root: Path, name: str, body: str) -> None:
    directory = root / ".github" / "workflows"
    directory.mkdir(parents=True, exist_ok=True)
    (directory / name).write_text(body, encoding="utf-8")


def test_derive_cohort_workflows_lit_les_fichiers_qui_chargent_la_variable(tmp_path):
    _workflow(tmp_path, "cohorte.yml",
              "runs-on: ${{ vars.CI_OVERFLOW_LOCAL == 'true' && 'x' || 'y' }}\n")
    _workflow(tmp_path, "cohorte-b.yaml",
              "env:\n  DEBORDEMENT: ${{ vars.CI_OVERFLOW_LOCAL }}\n")
    _workflow(tmp_path, "statique.yml",
              "runs-on: [self-hosted, coursia-ephemeral, coursia-linux]\n")
    # Le nom de la variable en COMMENTAIRE ne fait pas un workflow de
    # cohorte : c'est un job STATIQUE du parc, qui ne revient jamais sur
    # l'heberge. Le controleur lui-meme est dans ce cas, et son en-tete cite
    # la forme exacte -- en commentaire.
    _workflow(tmp_path, "commentaire.yml",
              "# pilote vars.CI_OVERFLOW_LOCAL, sans jamais le lire\n"
              "runs-on: [self-hosted, coursia-ephemeral, coursia-linux]\n")
    paths, reason = ctl.derive_cohort_workflows(tmp_path)
    assert reason == ""
    assert paths == {
        ".github/workflows/cohorte.yml",
        ".github/workflows/cohorte-b.yaml",
    }


def test_derive_cohort_workflows_repertoire_absent(tmp_path):
    paths, reason = ctl.derive_cohort_workflows(tmp_path)
    assert paths == set()
    assert "absent" in reason


def test_derive_cohort_workflows_liste_vide_rend_un_motif(tmp_path):
    _workflow(tmp_path, "statique.yml", "runs-on: ubuntu-latest\n")
    paths, reason = ctl.derive_cohort_workflows(tmp_path)
    assert paths == set()
    assert reason != ""


def _job(path: str, *, status: str = "queued", age: float = 3.0,
         run_id: int = 11) -> ctl.crs.JobRow:
    return ctl.crs.JobRow(workflow="W", run_number=1, run_id=run_id,
                          job_name="j", status=status, age_min=age,
                          run_path=path)


def test_collect_cohort_charge_ignore_les_jobs_statiques(monkeypatch):
    """Le parc porte deux jobs de cohorte et deux jobs qui n'en sont pas (un
    workflow statique, un run sans chemin) : la charge rendue vaut 2."""
    starv = ctl.crs.Starvation(
        starved=[
            _job(".github/workflows/cohorte.yml"),
            _job(".github/workflows/statique.yml", run_id=12),
            _job("", run_id=13),
        ],
        in_progress=[
            _job(".github/workflows/cohorte.yml", status="in_progress", run_id=14)
        ],
    )
    monkeypatch.setattr(ctl.crs, "fetch_starvation", lambda *a, **k: starv)
    sample = ctl.collect_cohort_charge(
        "jsboige/CoursIA", {".github/workflows/cohorte.yml"}, 120, NOW, "t")
    assert sample.complete is True and sample.truncated is False
    assert sample.queued == 1 and sample.in_progress == 1 and sample.charge == 2


def test_collect_cohort_charge_sans_liste_ne_mesure_rien(monkeypatch):
    monkeypatch.setattr(ctl.crs, "fetch_starvation",
                        lambda *a, **k: (_ for _ in ()).throw(
                            AssertionError("aucune lecture sans liste de cohorte")))
    sample = ctl.collect_cohort_charge("jsboige/CoursIA", set(), 120, NOW, "t")
    assert sample.complete is False
    assert "cohorte vide" in sample.reason


def test_collect_cohort_charge_tronquee_est_une_borne_inferieure(monkeypatch):
    starv = ctl.crs.Starvation(
        starved=[_job(".github/workflows/cohorte.yml")],
        budget_unread=[("W", 1, 20.0)],
    )
    monkeypatch.setattr(ctl.crs, "fetch_starvation", lambda *a, **k: starv)
    sample = ctl.collect_cohort_charge(
        "jsboige/CoursIA", {".github/workflows/cohorte.yml"}, 120, NOW, "t")
    assert sample.truncated is True
    assert "borne INFERIEURE" in sample.reason


# --- Les trois cas de la review du coordinateur (28/10) --------------------

def test_parc_charge_de_jobs_statiques_cohorte_vide_libere():
    """LE cas que la version precedente VERROUILLAIT : le parc local porte
    11 jobs statiques (le regime normal d'une journee de PRs), la cohorte ne
    rend rien et l'heberge est sous son plafond.

    L'ancienne condition (`local.charge <= 2`) rendait un HOLD : 11 > 2, pour
    toujours, et la variable restait a `true` a perpetuite. La charge qui
    revient est celle de la COHORTE, pas celle du parc : la liberation a
    lieu.
    """
    d = ctl.evaluate(
        hosted(queued=5, old=0, oldest=15.0, in_progress=2),
        local(free=21, online=32, busy=11, unknown=2),
        current="true",
        cohort=cohort(),
        cohort_confirm=cohort(),
        now=NOW,
    )
    assert d.action == "SWITCH_FALSE" and d.target == "false"
    assert "marge" in d.reason


def test_charge_rendue_superieure_a_la_marge_hebergee_tient():
    """La cohorte rend 3 jobs, la marge hebergee vaut 1 : on tient."""
    d = ctl.evaluate(
        hosted(queued=16, old=0, oldest=15.0, in_progress=3),
        local(free=21, online=32, busy=3),
        current="true",
        cohort=cohort(queued=3),
        cohort_confirm=cohort(queued=3),
        now=NOW,
    )
    assert d.action == "HOLD"
    assert "marge hebergee (1" in d.reason


def test_liste_de_cohorte_vide_ou_illisible_rend_unreadable():
    """Une cohorte non etablie n'est pas « une cohorte qui ne rend rien » :
    c'est une mesure ILLISIBLE, et elle ne libere jamais."""
    d = ctl.evaluate(
        hosted(queued=5, old=0, oldest=15.0),
        local(free=21, online=32),
        current="true",
        cohort=ctl.CohortSample(
            complete=False,
            reason="liste de la cohorte vide ou illisible, derivee du depot",
        ),
        now=NOW,
    )
    assert d.action == "UNREADABLE"
    assert d.target is None
    assert "cohorte" in d.reason


def test_cli_liberation_mesure_la_cohorte_deux_fois(monkeypatch, capsys, tmp_path):
    """Le chemin de bout en bout de la liberation : la charge rendue de la
    cohorte est mesuree, puis CONFIRMEE par une seconde lecture espacee de
    `--confirm-seconds`, et le rapport porte la marge hebergee."""
    _env(monkeypatch, write_token="pat-variables")
    monkeypatch.setattr(ctl, "read_variable", lambda *a, **k: ("true", OLD, ""))
    monkeypatch.setattr(ctl, "collect_hosted",
                        lambda *a, **k: hosted(queued=5, old=0, oldest=15.0))
    monkeypatch.setattr(ctl, "collect_local",
                        lambda *a, **k: local(free=21, online=32, busy=11))
    monkeypatch.setattr(ctl, "derive_cohort_workflows",
                        lambda root: ({".github/workflows/cohorte.yml"}, ""))
    calls = []

    def fake_charge(repo, paths, budget, now, token, delay_seconds=0.0):
        calls.append(delay_seconds)
        return cohort(queued=0)

    monkeypatch.setattr(ctl, "collect_cohort_charge", fake_charge)
    seen = {}

    def fake_write(repo, name, value, token):
        seen["value"] = value
        return True, "variable mise a jour"

    monkeypatch.setattr(ctl, "write_variable", fake_write)
    out = tmp_path / "summary.md"
    rc = ctl.main(["--repo", "jsboige/CoursIA", "--apply", "--json",
                   "--summary-out", str(out), "--confirm-seconds", "7"])
    assert rc == ctl.EXIT_OK
    assert seen["value"] == "false"
    # Une mesure, puis une confirmation espacee de --confirm-seconds.
    assert calls == [0.0, 7.0]
    report = json.loads(capsys.readouterr().out)
    assert report["verdict"] == "SWITCH_FALSE"
    assert report["cohort"]["workflows"] == 1
    assert report["cohort"]["measured"] is True
    assert report["cohort_confirm"]["measured"] is True
    assert report["hosted_margin"] == 15
    text = out.read_text(encoding="utf-8")
    assert "cohorte" in text
    assert "confirmation" in text
    assert "marge 15" in text


def test_cli_liste_de_cohorte_illisible_rend_unreadable(monkeypatch, capsys):
    """Sans liste de cohorte derivee, la liberation est impossible : le
    verdict est UNREADABLE, et rien n'est ecrit."""
    _env(monkeypatch, write_token="pat-variables")
    monkeypatch.setattr(ctl, "read_variable", lambda *a, **k: ("true", OLD, ""))
    monkeypatch.setattr(ctl, "collect_hosted",
                        lambda *a, **k: hosted(queued=5, old=0, oldest=15.0))
    monkeypatch.setattr(ctl, "collect_local",
                        lambda *a, **k: local(free=21, online=32))
    monkeypatch.setattr(ctl, "derive_cohort_workflows",
                        lambda root: (set(), "repertoire des workflows absent"))
    monkeypatch.setattr(ctl, "write_variable", lambda *a, **k: (_ for _ in ()).throw(
        AssertionError("aucune ecriture sur une cohorte non etablie")))
    rc = ctl.main(["--repo", "jsboige/CoursIA", "--apply", "--json"])
    assert rc == ctl.EXIT_UNREADABLE
    report = json.loads(capsys.readouterr().out)
    assert report["verdict"] == "UNREADABLE"
    assert report["written"] is False
    assert "cohorte" in report["reason"]
