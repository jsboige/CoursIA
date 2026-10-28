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
           complete: bool = True, truncated: bool = False, reason: str = "") -> ctl.HostedSample:
    return ctl.HostedSample(queued=queued, old=old, oldest_age_min=oldest,
                             complete=complete, truncated=truncated, reason=reason)


def local(free: int = 0, online: int = 0, starved: int = 0,
          busy: int = 0, unknown: int = 0,
          complete: bool = True, truncated: bool = False, reason: str = "") -> ctl.LocalSample:
    return ctl.LocalSample(online=online, free=free, starved=starved, busy=busy,
                            unknown=unknown, complete=complete, truncated=truncated,
                            reason=reason)


def confirm(busy: int = 0, unknown: int = 0, complete: bool = True,
            reason: str = "") -> ctl.LoadConfirm:
    """Seconde lecture de l'inventaire local (confirmation d'inaction)."""
    return ctl.LoadConfirm(busy=busy, unknown=unknown, complete=complete, reason=reason)


# --- Regle de decision (fonction pure) -------------------------------------

def test_offre_saturee_et_parc_local_libre_bascule_vers_true():
    d = ctl.evaluate(hosted(queued=9, old=6, oldest=41.0), local(free=7, online=14),
                     current="false", now=NOW)
    assert d.action == "SWITCH_TRUE" and d.target == "true"


def test_file_hebergee_videe_bascule_vers_false():
    # La liberation exige une charge rendue bornee ET sa confirmation : le
    # parc local ne porte rien sur les DEUX lectures.
    d = ctl.evaluate(hosted(queued=0, old=0, oldest=0.0), local(free=7, online=14),
                     current="true", local_confirm=confirm(), now=NOW)
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
    """Le cas MESURE du 27/10 : la file hebergee est pleine mais RIEN n'y
    attend au-dela du seuil de saturation, et le parc local ne porte rien.

    Mesure de 22h50Z sur ce siege : variable a `true` depuis 11:04Z,
    `hosted.queued = 74`, `hosted.old = 0` (le plus ancien attend 15,0 min),
    29 slots locaux LIBRES. L'offre hebergee n'attend pas et le parc ne
    porte rien : la charge rendue est predite (elle est nulle) -> la
    cohorte rend la main.

    La liberation exige DEUX lectures inactives : sans la confirmation,
    l'inaction du parc n'est pas etablie et le controleur attend.
    """
    d = ctl.evaluate(hosted(queued=74, old=0, oldest=15.0),
                     local(free=29, online=32), current="true",
                     local_confirm=confirm(), now=NOW)
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
    d = ctl.evaluate(hosted(queued=74, old=0, oldest=15.0, truncated=True,
                             reason="3 run(s) non lu(s)"),
                     local(free=29, online=32), current="true",
                     local_confirm=confirm(), now=NOW)
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


# --- #22937 vague 2 (bis) : la liberation PREDIT la charge rendue ---------
#
# La regle `hosted.old == 0` seule est un ARTEFACT : pendant que la cohorte
# tourne en local, l'offre hebergee ne porte que les jobs hors debordement,
# elle parait donc allegee meme quand la charge de la cohorte est enorme.
# Liberer sur cette seule lecture rend la cohorte entiere a une offre qui
# s'etouffe derriere, et le dwell de 90 min interdit ensuite de revenir a
# `true` : on rejoue la nuit du 27/10 (reserve du coordinateur, 28/10).
#
# La liberation exige donc que la charge RENDUE soit predite et bornee :
# le parc local ne porte presque rien, confirme sur deux lectures.


def test_liberation_exige_une_charge_rendue_bornee():
    """Le parc local porte 5 jobs : la charge rendue depasse le seuil
    (2), on ne rend pas la main."""
    d = ctl.evaluate(hosted(queued=74, old=0, oldest=15.0),
                     local(free=29, online=32, busy=5), current="true",
                     local_confirm=confirm(busy=5), now=NOW)
    assert d.action == "HOLD"
    assert "charge rendue" in d.reason


def test_liberation_exige_la_confirmation_de_la_lecture():
    """Sans seconde lecture, l'inaction du parc n'est pas etablie."""
    d = ctl.evaluate(hosted(queued=74, old=0, oldest=15.0),
                     local(free=29, online=32), current="true", now=NOW)
    assert d.action == "HOLD"
    assert "confirmation" in d.reason


def test_liberation_refusee_par_une_confirmation_qui_contredit():
    """La premiere lecture dit le parc inactif, la seconde dit le contraire :
    l'inaction n'est pas confirmee, on attend."""
    d = ctl.evaluate(hosted(queued=74, old=0, oldest=15.0),
                     local(free=29, online=32), current="true",
                     local_confirm=confirm(busy=4), now=NOW)
    assert d.action == "HOLD"
    assert "confirmation" in d.reason


def test_occupation_inconnue_compte_comme_occupee():
    """Un runner dont l'occupation est illisible n'est PAS comptabilise comme
    libre (fail-CLOSED) : il compte dans la charge."""
    d = ctl.evaluate(hosted(queued=74, old=0, oldest=15.0),
                     local(free=29, online=32, unknown=3), current="true",
                     local_confirm=confirm(unknown=3), now=NOW)
    assert d.action == "HOLD"


def test_deux_lectures_inactives_liberent():
    """Les DEUX lectures sont inactives : la charge rendue est predite
    (nulle) et la liberation a lieu."""
    d = ctl.evaluate(hosted(queued=74, old=0, oldest=15.0),
                     local(free=29, online=32), current="true",
                     local_confirm=confirm(), now=NOW)
    assert d.action == "SWITCH_FALSE" and d.target == "false"


def test_le_dwell_ne_derange_jamais_la_liberation():
    """Le dwell oppose la LIBERATION comme il oppose la re-absorption : c'est
    elle qui fait revenir la cohorte, donc c'est elle qui reste freinee."""
    recent = NOW - timedelta(minutes=5)
    d = ctl.evaluate(hosted(queued=74, old=0, oldest=15.0),
                     local(free=29, online=32), current="true",
                     local_confirm=confirm(), dwell_minutes=90,
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
