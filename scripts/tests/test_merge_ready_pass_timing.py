"""Tests hermetiques de l'organe de duree des passages de merge_ready (#26799).

Aucun reseau, aucun journal reel : chaque test ecrit son propre JSONL dans
``tmp_path``. Le module sous test est importable a nu (``scripts/coordination``
est sur le ``sys.path`` par le conftest des tests de scripts).

Ce que ces tests verrouillent, et pourquoi :
- l'attribution du cout a la ligne dont l'evaluation **s'acheve** a cet
  horodatage (le journal est ecrit apres ``evaluate_pr``) -- l'inverser
  attribuerait les 120 s d'attente de mergeabilite a la PR precedente ;
- le decoupage des passages, qui n'a aucun identifiant dans le journal et
  repose donc sur deux signaux objectifs (PR repetee, ecart trop grand) ;
- l'honnetete de la mesure : la premiere ligne n'a pas de cout attribuable, et
  un horodatage qui recule ne fabrique jamais une duree negative.
"""

import importlib.util
import json
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
COORD = HERE.parent / "coordination"
TIMING_PATH = COORD / "merge_ready_pass_timing.py"

_spec = importlib.util.spec_from_file_location("merge_ready_pass_timing_under_test", TIMING_PATH)
timing = importlib.util.module_from_spec(_spec)
sys.modules["merge_ready_pass_timing_under_test"] = timing
_spec.loader.exec_module(timing)

T0 = datetime(2026, 11, 15, 21, 30, 0, tzinfo=timezone.utc)


def write_journal(path: Path, rows) -> Path:
    """Ecrit un journal synthetique : (offset_s, pr, verdict, reason)."""
    lines = []
    for offset, pr, verdict, reason in rows:
        stamp = T0 + timedelta(seconds=offset)
        lines.append(
            json.dumps(
                {
                    "ts": stamp.strftime("%Y-%m-%dT%H:%M:%SZ"),
                    "pr": pr,
                    "head": None,
                    "verdict": verdict,
                    "reason": reason,
                    "merged": verdict == "merged",
                    "review": "not-evaluated",
                    "stack": None,
                },
                ensure_ascii=False,
            )
        )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return path


# --- chemin par defaut ----------------------------------------------------------


def test_default_journal_path_matches_merge_ready():
    """La copie du chemin ne doit pas deriver de l'organe d'origine."""
    spec = importlib.util.spec_from_file_location(
        "merge_ready_for_path_check", COORD / "merge_ready.py"
    )
    merge_ready = importlib.util.module_from_spec(spec)
    sys.modules["merge_ready_for_path_check"] = merge_ready
    spec.loader.exec_module(merge_ready)
    assert timing.default_journal_path() == merge_ready.default_journal_path()


def test_not_evaluated_verdict_matches_merge_ready():
    """La copie du verdict des PRs non evaluees ne doit pas deriver."""
    spec = importlib.util.spec_from_file_location(
        "merge_ready_for_verdict_check", COORD / "merge_ready.py"
    )
    merge_ready = importlib.util.module_from_spec(spec)
    sys.modules["merge_ready_for_verdict_check"] = merge_ready
    spec.loader.exec_module(merge_ready)
    assert timing.NOT_EVALUATED_VERDICT == merge_ready.VERDICT_NOT_EVALUATED


# --- PRs non evaluees (#28009) ----------------------------------------------------


def test_les_lignes_non_evaluees_ne_portent_aucun_cout(tmp_path):
    """Une PR non evaluee ne porte ni cout, ni compte de PRs.

    Comptees comme des PRs evaluees, elles gonfleraient le compte du passage
    de centaines de lignes sans evaluation : la projection ``span * (132 /
    count)`` -- une regle de trois sur le compte de PRs -- annoncerait alors
    un passage lent comme un passage rapide.
    """
    journal = write_journal(
        tmp_path / "journal.jsonl",
        [
            (0, 101, "skipped", "no-approval"),
            (10, 102, "merged", None),
            (20, 103, "unevaluated", "pass-budget-exceeded"),
            (20, 104, "unevaluated", "pass-budget-exceeded"),
        ],
    )
    rows, unreadable = timing.read_journal(journal)
    assert unreadable == 0
    passes = timing.split_passes(rows, timing.DEFAULT_MAX_GAP_S)
    assert len(passes) == 1
    p = passes[0]
    assert p.count == 2  # seules les PRs EVALUEES comptent
    assert p.not_evaluated == 2
    # L'etendue et le cout ne bougent pas : les lignes non evaluees ne
    # delimitaient aucune evaluation.
    assert p.span_s == pytest.approx(10.0)
    assert p.measured_s == pytest.approx(p.span_s)
    assert "pass-budget-exceeded" not in p.by_class
    assert "pass-budget-exceeded" not in p.by_class_count


def test_une_pr_non_evaluee_ouvre_un_passage_au_tour_suivant(tmp_path):
    """La PR non evaluee par la passe 1, evaluee par la passe 2, ouvre un
    NOUVEAU passage -- sans quoi la mesure de la passe 2 serait absorbee
    par la passe 1.

    L'ecart temporel est ici de 40 s : la separation ne peut pas venir de
    lui, elle vient de la PR repetee.
    """
    journal = write_journal(
        tmp_path / "journal.jsonl",
        [
            (0, 101, "skipped", "no-approval"),
            (10, 102, "merged", None),
            (20, 103, "unevaluated", "pass-budget-exceeded"),
            (60, 103, "merged", None),
        ],
    )
    rows, _ = timing.read_journal(journal)
    passes = timing.split_passes(rows, timing.DEFAULT_MAX_GAP_S)
    assert len(passes) == 2
    assert passes[0].count == 2 and passes[0].not_evaluated == 1
    assert passes[1].count == 1 and passes[1].not_evaluated == 0


def test_le_json_nome_les_prs_non_evaluees(tmp_path, capsys):
    journal = write_journal(
        tmp_path / "journal.jsonl",
        [
            (0, 101, "skipped", "no-approval"),
            (10, 102, "unevaluated", "pass-budget-exceeded"),
        ],
    )
    rc = timing.main(["--journal", str(journal), "--json"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["not_evaluated"] == 1
    assert payload["selected"][0]["not_evaluated"] == 1
    assert payload["selected"][0]["prs"] == 1


# --- attribution du cout --------------------------------------------------------


def test_cost_is_attributed_to_the_line_that_ends_it(tmp_path):
    # 4 PRs : 10 s, puis 120 s (l'attente de mergeabilite de #103), puis 5 s.
    journal = write_journal(
        tmp_path / "journal.jsonl",
        [
            (0, 101, "skipped", "no-approval"),
            (10, 102, "merged", None),
            (130, 103, "skipped", "mergeable-state:unknown"),
            (135, 104, "skipped", "no-approval"),
        ],
    )
    rows, unreadable = timing.read_journal(journal)
    assert unreadable == 0
    passes = timing.split_passes(rows, timing.DEFAULT_MAX_GAP_S)
    assert len(passes) == 1
    p = passes[0]
    # Les 120 s se sont ecoulees AVANT la ligne 102 : c'est l'evaluation de
    # 102 qui les a payees, pas celle de 101.
    assert p.by_class["mergeable-state:unknown"] == pytest.approx(120.0)
    assert p.by_class["merged"] == pytest.approx(10.0)
    assert p.by_class["no-approval"] == pytest.approx(5.0)
    assert p.span_s == pytest.approx(135.0)
    assert p.measured_s == pytest.approx(p.span_s)


def test_first_line_has_no_attributable_cost(tmp_path):
    journal = write_journal(
        tmp_path / "journal.jsonl",
        [
            (0, 101, "skipped", "no-approval"),
            (7, 102, "merged", None),
        ],
    )
    rows, _ = timing.read_journal(journal)
    p = timing.split_passes(rows, timing.DEFAULT_MAX_GAP_S)[0]
    # `no-approval` est vue une fois mais ne porte aucun cout : la premiere
    # ligne d'un passage inclut un demarrage non mesure, on n'invente rien.
    assert p.by_class_count["no-approval"] == 1
    assert "no-approval" not in p.by_class
    assert p.by_class["merged"] == pytest.approx(7.0)


# --- decoupage des passages -----------------------------------------------------


def test_pr_repeat_opens_a_new_pass(tmp_path):
    # Une PR revue = un second passage : la boucle ne l'evalue qu'une fois.
    journal = write_journal(
        tmp_path / "journal.jsonl",
        [
            (0, 101, "skipped", "no-approval"),
            (5, 102, "merged", None),
            (30, 101, "skipped", "no-approval"),
            (35, 102, "merged", None),
        ],
    )
    rows, _ = timing.read_journal(journal)
    passes = timing.split_passes(rows, timing.DEFAULT_MAX_GAP_S)
    assert len(passes) == 2
    assert [p.count for p in passes] == [2, 2]


def test_gap_opens_a_new_pass(tmp_path):
    # 2 min d'ecart : meme passage. 40 min : passage suivant.
    journal = write_journal(
        tmp_path / "journal.jsonl",
        [
            (0, 101, "skipped", "no-approval"),
            (120, 102, "merged", None),
            (120 + 2400, 103, "skipped", "no-approval"),
            (120 + 2405, 104, "merged", None),
        ],
    )
    rows, _ = timing.read_journal(journal)
    passes = timing.split_passes(rows, timing.DEFAULT_MAX_GAP_S)
    assert len(passes) == 2
    assert passes[0].count == 2
    assert passes[1].count == 2


def test_time_travel_never_creates_a_negative_duration(tmp_path):
    journal = write_journal(
        tmp_path / "journal.jsonl",
        [
            (0, 101, "skipped", "no-approval"),
            (100, 102, "merged", None),
            (50, 103, "merged", None),  # horodatage recule
        ],
    )
    rows, _ = timing.read_journal(journal)
    passes = timing.split_passes(rows, timing.DEFAULT_MAX_GAP_S)
    # Le recul ouvre un passage : il ne peut pas appartenir a la meme mesure.
    assert len(passes) == 2
    assert all(p.span_s >= 0 for p in passes)
    assert passes[1].count == 1
    assert passes[1].span_s == 0.0
    # L'anomalie est comptee sur le passage qu'elle ouvre, pas avalee.
    assert passes[1].time_travel == 1


# --- classes --------------------------------------------------------------------


@pytest.mark.parametrize(
    "verdict,reason,expected",
    [
        ("skipped", "mergeable-state:unknown", "mergeable-state:unknown"),
        ("skipped", "mergeable-state:unstable:Check:FAILURE", "mergeable-state:unstable"),
        ("skipped", "hold:collision", "hold"),
        ("skipped", "stacked-on-main:17:MERGED", "stacked-on-main"),
        ("skipped", "no-approval", "no-approval"),
        ("merged", None, "merged"),
        ("run-error", "gh api rc=1", "gh api rc=1"),
        ("skipped", None, "skipped"),
    ],
)
def test_reason_class(verdict, reason, expected):
    assert timing.reason_class(verdict, reason) == expected


# --- robustesse de la lecture ---------------------------------------------------


def test_unreadable_lines_are_counted_not_fatal(tmp_path):
    journal = tmp_path / "journal.jsonl"
    good = json.dumps(
        {"ts": "2026-11-15T21:30:00Z", "pr": 1, "verdict": "merged", "reason": None}
    ) + "\n"
    journal.write_text(
        good
        + "{ pas du json\n"
        + json.dumps({"pr": 2, "verdict": "merged"}) + "\n"  # pas de ts
        + json.dumps({"ts": "2026-11-15T21:30:10", "pr": 3}) + "\n",  # sans fuseau
        encoding="utf-8",
    )
    rows, unreadable = timing.read_journal(journal)
    assert len(rows) == 1
    assert unreadable == 3


def test_missing_journal_exits_2(tmp_path, capsys):
    rc = timing.main(["--journal", str(tmp_path / "absent.jsonl")])
    assert rc == 2
    assert "introuvable" in capsys.readouterr().err


def test_empty_journal_exits_2(tmp_path, capsys):
    path = tmp_path / "journal.jsonl"
    path.write_text("\n", encoding="utf-8")
    rc = timing.main(["--journal", str(path)])
    assert rc == 2
    assert "aucune ligne exploitable" in capsys.readouterr().err


def test_rejects_bad_last(tmp_path, capsys):
    journal = write_journal(tmp_path / "journal.jsonl", [(0, 1, "merged", None)])
    rc = timing.main(["--journal", str(journal), "--last", "0"])
    assert rc == 2
    assert "--last" in capsys.readouterr().err


# --- sortie ---------------------------------------------------------------------


def test_json_shape_and_last_selection(tmp_path, capsys):
    journal = write_journal(
        tmp_path / "journal.jsonl",
        [
            (0, 101, "skipped", "no-approval"),
            (10, 102, "skipped", "mergeable-state:unknown"),
            (130, 103, "merged", None),
            # second passage
            (2000, 101, "merged", None),
            (2005, 102, "merged", None),
        ],
    )
    rc = timing.main(["--journal", str(journal), "--last", "1", "--json"])
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["passes_total"] == 2
    assert payload["unreadable"] == 0
    assert len(payload["selected"]) == 1
    passage = payload["selected"][0]
    assert passage["pass"] == 2
    assert passage["prs"] == 2
    assert passage["startup_unmeasured_prs"] == 1
    assert [c["class"] for c in passage["classes"]] == ["merged"]


def test_human_report_names_the_expensive_evaluations(tmp_path, capsys):
    journal = write_journal(
        tmp_path / "journal.jsonl",
        [
            (0, 101, "skipped", "no-approval"),
            (120, 102, "skipped", "mergeable-state:unknown"),
            (130, 103, "merged", None),
        ],
    )
    rc = timing.main(["--journal", str(journal), "--top", "2"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "mergeable-state:unknown" in out
    assert "PR #102" in out
    assert "acceptance #26799" in out


def test_control_reproduces_the_issue_measurement(tmp_path):
    """Controle : le journal synthetise a la mesure publiee de #26799.

    L'issue mesure le passage du 2026-11-15 -- 132 PRs, 11 merges = 3 040 s
    (50 %), 17 sauts ``mergeable-state:*`` = 2 426 s (40 %), 103 autres sauts
    = 437 s (7 %). Les trois postes somment 5 903 s quand le passage dure
    1 h 41 (6 060 s) : l'ecart est le demarrage du passage, que cet organe ne
    mesure pas. Le compte des PRs porte la meme trace -- 11 + 17 + 103 = 131
    pour 132 PRs evaluees -- parce que la premiere ligne d'un passage n'a pas
    de cout attribuable. Si l'organe reproduit ces trois postes au second pres,
    il lit le meme journal que l'issue ; s'il ne les reproduit pas, c'est lui
    qui est faux.
    """
    spans = []
    for total, count in ((3040, 11), (2426, 17), (437, 103)):
        base, extra = divmod(total, count)
        spans.extend([base + (1 if i < extra else 0) for i in range(count)])

    rows = [(0, 900000, "skipped", "no-approval")]  # premiere ligne, non mesuree
    offset = 0
    plan = (
        [("merged", None)] * 11
        + [("skipped", "mergeable-state:unknown")] * 17
        + [("skipped", "no-approval")] * 103
    )
    for delta, (verdict, reason) in zip(spans, plan):
        offset += delta
        rows.append((offset, 900000 + len(rows), verdict, reason))

    journal = write_journal(tmp_path / "journal.jsonl", rows)
    rows_read, unreadable = timing.read_journal(journal)
    assert unreadable == 0
    passes = timing.split_passes(rows_read, timing.DEFAULT_MAX_GAP_S)
    assert len(passes) == 1
    p = passes[0]

    assert p.count == 132
    assert p.span_s == pytest.approx(5903.0)
    assert p.by_class["merged"] == pytest.approx(3040.0)
    assert p.by_class["mergeable-state:unknown"] == pytest.approx(2426.0)
    assert p.by_class["no-approval"] == pytest.approx(437.0)
    assert p.by_class_count["merged"] == 11
    assert p.by_class_count["mergeable-state:unknown"] == 17
    # 104 lignes portent la classe, 103 en portent le cout : la premiere du
    # passage est celle dont le cout appartient au demarrage.
    assert p.by_class_count["no-approval"] == 104
    assert p.measured_s == pytest.approx(p.span_s)


def test_fail_over_target_is_opt_in(tmp_path):
    # 3 PRs sur 2 min : projete a 132 PRs, tres au-dessus de 30 min.
    journal = write_journal(
        tmp_path / "journal.jsonl",
        [
            (0, 101, "merged", None),
            (60, 102, "merged", None),
            (120, 103, "merged", None),
        ],
    )
    assert timing.main(["--journal", str(journal)]) == 0
    assert timing.main(["--journal", str(journal), "--fail-over-target"]) == 1
    # Un seuil genereux rend le meme passage acceptable.
    assert timing.main(
        ["--journal", str(journal), "--fail-over-target", "--target-minutes", "120"]
    ) == 0