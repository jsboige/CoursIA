#!/usr/bin/env python3
"""Tests pour build_editorial_review_dossier.py -- couche INSTRUMENTS du dossier
de revue editoriale (acceptance 2 de #11259).

Aucun organe reel n'est invoque : le runner est injecte. Ce qui est teste ici est
le CONTRAT du dossier -- les 7 axes nommes par l'acceptance, la lecture des
charges utiles, et surtout la regle qui fait sa valeur : **un organe illisible
sort en ERROR, jamais en PASS**.
"""

import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
AUDIT_DIR = HERE.parent
sys.path.insert(0, str(AUDIT_DIR))

import build_editorial_review_dossier as dos  # noqa: E402

NOTEBOOK = "MyIA.AI.Notebooks/Sudoku/Sudoku-01-Backtracking-Python.ipynb"


# ---------------------------------------------------------------------------
# Registre -- les 7 axes nommes par l'acceptance 2
# ---------------------------------------------------------------------------

def test_registry_covers_exactly_the_seven_named_axes():
    assert dos.AXES == ("execution", "outputs", "density", "cell_order",
                        "citations", "twin_parity", "i18n")


def test_registry_axes_are_unique():
    assert len(set(dos.AXES)) == len(dos.AXES)


def test_every_instrument_has_a_note_justifying_its_verdict():
    for instrument in dos.INSTRUMENTS:
        assert instrument.note, f"{instrument.axis} sans note"


def test_three_questions_and_only_three():
    assert len(dos.QUESTIONS) == 3
    texts = [q for q, _ in dos.QUESTIONS]
    assert texts == ["Est-ce que ca s'enseigne bien ?",
                     "Est-ce que l'exemple porte ?",
                     "Est-ce que je signe ?"]


def test_questions_reference_known_axes():
    for _, axes in dos.QUESTIONS:
        for axis in axes:
            assert axis in dos.AXES, f"question reliee a un axe inconnu : {axis}"


# ---------------------------------------------------------------------------
# Localisation
# ---------------------------------------------------------------------------

def test_family_of_first_component():
    assert dos.family_of(NOTEBOOK) == "Sudoku"


def test_family_of_nested_family_takes_top_level():
    assert dos.family_of("MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-Python-01.ipynb") == "SymbolicAI"


def test_family_of_outside_root_is_none():
    assert dos.family_of("scripts/audit/foo.ipynb") is None


def test_normalize_notebook_leaves_relative_posix_untouched():
    assert dos.normalize_notebook(NOTEBOOK, Path("/repo")) == NOTEBOOK


def test_normalize_notebook_converts_absolute(tmp_path):
    nb = tmp_path / "MyIA.AI.Notebooks" / "Sudoku" / "x.ipynb"
    nb.parent.mkdir(parents=True)
    nb.write_text("{}", encoding="utf-8")
    assert dos.normalize_notebook(str(nb), tmp_path) == \
        "MyIA.AI.Notebooks/Sudoku/x.ipynb"


# ---------------------------------------------------------------------------
# Lecture de charge utile
# ---------------------------------------------------------------------------

def test_parse_json_skips_preamble():
    assert dos.parse_json('log line\n{"a": 1}\ntrailer') == {"a": 1}


def test_parse_json_empty_is_none():
    assert dos.parse_json("") is None


def test_parse_json_garbage_is_none():
    assert dos.parse_json("pas de json ici") is None


def test_count_at_reads_int_and_list():
    assert dos.count_at({"summary": {"n": 3}}, ("summary", "n")) == 3
    assert dos.count_at({"reports": [1, 2]}, ("reports",)) == 2


def test_count_at_missing_is_zero():
    assert dos.count_at({}, ("summary", "n")) == 0


def test_count_at_bool_is_zero():
    # True est un int en Python : un drapeau ne doit pas se lire comme un compte.
    assert dos.count_at({"ok": True}, ("ok",)) == 0


# ---------------------------------------------------------------------------
# Juges
# ---------------------------------------------------------------------------

def test_judge_rc_pass_warn_error():
    assert dos.judge_rc(None, 0, NOTEBOOK)[0] == dos.PASS
    assert dos.judge_rc(None, 1, NOTEBOOK)[0] == dos.WARN
    assert dos.judge_rc(None, 2, NOTEBOOK)[0] == dos.ERROR


def test_judge_counts_passes_only_when_every_counter_is_zero():
    judge = dos.judge_counts(("summary", "below_threshold"), ("summary", "unmeasured"))
    payload = {"summary": {"below_threshold": 0, "unmeasured": 0}}
    assert judge(payload, 0, NOTEBOOK)[0] == dos.PASS

    payload["summary"]["below_threshold"] = 2
    verdict, detail = judge(payload, 0, NOTEBOOK)
    assert verdict == dos.WARN
    assert "below_threshold=2" in detail


def test_judge_counts_unreadable_payload_is_error_not_pass():
    judge = dos.judge_counts(("reports",))
    assert judge(None, 0, NOTEBOOK)[0] == dos.ERROR


def test_judge_counts_rc_two_is_error():
    judge = dos.judge_counts(("reports",))
    assert judge({"reports": []}, 2, NOTEBOOK)[0] == dos.ERROR


# --- citations -------------------------------------------------------------

def _citations(mine=True, covered=True):
    return {
        "occurrences": {"cs/0011047": [
            {"notebook": "Sudoku-01-Backtracking-Python.ipynb", "cell_idx": 0},
            {"notebook": "Sudoku-02-DancingLinks-CSharp.ipynb", "cell_idx": 3},
        ]} if mine else {"cs/0011047": [
            {"notebook": "Sudoku-02-DancingLinks-CSharp.ipynb", "cell_idx": 3}]},
        "delta_not_covered": [] if covered else ["cs/0011047"],
    }


def test_citations_pass_when_notebook_cites_nothing():
    verdict, detail = dos.judge_citations({"occurrences": {}, "delta_not_covered": []},
                                          0, NOTEBOOK)
    assert verdict == dos.PASS
    assert "0 citation" in detail


def test_citations_pass_when_all_covered():
    assert dos.judge_citations(_citations(covered=True), 0, NOTEBOOK)[0] == dos.PASS


def test_citations_warn_when_uncovered():
    verdict, detail = dos.judge_citations(_citations(covered=False), 0, NOTEBOOK)
    assert verdict == dos.WARN
    assert "cs/0011047" in detail


def test_citations_ignore_a_neighbour_notebook():
    # Le notebook voisin cite, pas le notre : le verdict ne doit pas deborder.
    verdict, _ = dos.judge_citations(_citations(mine=False, covered=False), 0, NOTEBOOK)
    assert verdict == dos.PASS


def test_citations_unreadable_payload_is_error():
    assert dos.judge_citations(None, 0, NOTEBOOK)[0] == dos.ERROR


def test_judge_na_declares_its_reason():
    verdict, detail = dos.judge_na("sans objet, motif")(None, 0, NOTEBOOK)
    assert verdict == dos.NA
    assert detail == "sans objet, motif"


# ---------------------------------------------------------------------------
# build_dossier -- runner injecte
# ---------------------------------------------------------------------------

def _runner_from(table, record=None):
    """Rend un runner qui repond selon le nom d'organe present dans argv.

    L'organe de citations ne rend pas sa charge utile sur stdout mais dans le
    fichier nomme par `--out` : un runner qui ne l'ecrit pas est un organe muet,
    et le generateur le classe ERROR -- c'est le contrat, on l'ecrit donc ici.
    """
    def _run(argv, cwd=None):
        if record is not None:
            record.append(argv)
        joined = " ".join(argv)
        for key, (rc, out) in table.items():
            if key in joined:
                if "--out" in argv:
                    idx = argv.index("--out")
                    Path(argv[idx + 1]).write_text(
                        out or json.dumps({"occurrences": {}, "delta_not_covered": []}),
                        encoding="utf-8")
                return dos.RunResult(rc, out)
        return dos.RunResult(0, "")
    return _run


HEALTHY = {
    "check_null_exec": (0, "H.3 pre-commit: 1 notebook(s) OK"),
    "check_notebook_outputs_required": (0, "=== 0 defective code-cell(s)"),
    "pedagogy_density": (0, json.dumps({"summary": {"below_threshold": 0,
                                                    "unmeasured": 0}})),
    "scan_cell_ordering": (0, json.dumps({"reports": []})),
    "check_twin_parity": (0, json.dumps({"drift": 0, "missing": 0,
                                         "numbering_drift": 0})),
    "scan_arxiv_citations": (0, ""),  # la charge utile part dans --out (cf _runner_from)
}


def test_dossier_has_one_row_per_axis():
    dossier = dos.build_dossier(NOTEBOOK, repo_root=Path("/repo"),
                                runner=_runner_from(HEALTHY))
    assert [r.axis for r in dossier.rows] == list(dos.AXES)


def test_i18n_axis_is_na_with_its_reason():
    dossier = dos.build_dossier(NOTEBOOK, repo_root=Path("/repo"),
                                runner=_runner_from(HEALTHY))
    row = next(r for r in dossier.rows if r.axis == "i18n")
    assert row.verdict == dos.NA
    assert ".lean" in row.detail


def test_healthy_notebook_has_no_error():
    dossier = dos.build_dossier(NOTEBOOK, repo_root=Path("/repo"),
                                runner=_runner_from(HEALTHY))
    assert dossier.errors == []


def test_family_axes_are_na_outside_the_notebook_root():
    dossier = dos.build_dossier("scripts/audit/foo.ipynb", repo_root=Path("/repo"),
                                runner=_runner_from(HEALTHY))
    for axis in ("citations", "twin_parity"):
        row = next(r for r in dossier.rows if r.axis == axis)
        assert row.verdict == dos.NA


def test_uninvocable_organ_is_error_not_pass():
    def boom(argv, cwd=None):
        raise FileNotFoundError("organe absent")

    dossier = dos.build_dossier(NOTEBOOK, repo_root=Path("/repo"), runner=boom)
    assert dossier.rows  # le dossier existe malgre la panne
    assert all(r.verdict == dos.ERROR for r in dossier.rows if r.axis != "i18n")


def test_organ_that_writes_no_outfile_is_error():
    """Le contrat du dossier : un organe muet n'est jamais un organe vert.

    L'organe de citations rend 0 et rien d'autre -- pas de fichier. Le declarer
    PASS serait affirmer « citations verifiees » sur la foi d'un silence.
    """
    def _run(argv, cwd=None):
        joined = " ".join(argv)
        for key, (rc, out) in HEALTHY.items():
            if key in joined and "--out" not in argv:
                return dos.RunResult(rc, out)
        return dos.RunResult(0, "")

    dossier = dos.build_dossier(NOTEBOOK, repo_root=Path("/repo"), runner=_run)
    row = next(r for r in dossier.rows if r.axis == "citations")
    assert row.verdict == dos.ERROR
    assert "illisible" in row.detail


def test_provenance_carries_organ_and_return_code():
    dossier = dos.build_dossier(NOTEBOOK, repo_root=Path("/repo"),
                                runner=_runner_from(HEALTHY))
    row = next(r for r in dossier.rows if r.axis == "execution")
    assert "check_null_exec.py" in row.provenance
    assert "rc=0" in row.provenance


def test_portable_command_reduces_interpreter_to_its_basename():
    assert dos.portable_command([r"C:\Python313\python.exe", "x.py"]) == "python.exe x.py"


def test_portable_command_masks_the_temporary_payload_file():
    cmd = dos.portable_command(["python", "org.py", "--out", "/tmp/a/citations.json"],
                               outfile="/tmp/a/citations.json")
    assert "/tmp/a" not in cmd
    assert "<tmp>" in cmd


def test_provenance_carries_no_machine_path():
    """Le dossier est lu sur une autre machine que celle qui l'a produit : le
    basename de l'interpreteur suffit, son chemin absolu n'y a rien a faire."""
    dossier = dos.build_dossier(NOTEBOOK, repo_root=Path("/repo"),
                                runner=_runner_from(HEALTHY))
    for row in dossier.rows:
        assert str(sys.executable) not in row.provenance
        assert "C:\\" not in row.provenance


def test_json_organs_show_no_useless_excerpt():
    dossier = dos.build_dossier(NOTEBOOK, repo_root=Path("/repo"),
                                runner=_runner_from(HEALTHY))
    row = next(r for r in dossier.rows if r.axis == "density")
    # L'extrait d'un organe JSON serait l'accolade ouvrante : on ne le montre pas.
    assert row.provenance.endswith("rc=0")


def test_family_instrument_is_invoked_with_its_family():
    seen = []
    dos.build_dossier(NOTEBOOK, repo_root=Path("/repo"),
                      runner=_runner_from(HEALTHY, record=seen))
    twin = [a for a in seen if any("check_twin_parity" in x for x in a)]
    assert twin, "l'organe de parite jumeau n'a pas ete invoque"
    assert "Sudoku" in twin[0]


# ---------------------------------------------------------------------------
# Rendu
# ---------------------------------------------------------------------------

def test_render_has_a_row_per_axis_and_the_three_questions():
    dossier = dos.build_dossier(NOTEBOOK, repo_root=Path("/repo"),
                                runner=_runner_from(HEALTHY))
    text = dos.render_dossier(dossier)
    for axis in dos.AXES:
        assert f"`{axis}`" in text
    for question, _ in dos.QUESTIONS:
        assert question in text


def test_render_questions_annotates_the_axes_they_depend_on():
    dossier = dos.build_dossier(NOTEBOOK, repo_root=Path("/repo"),
                                runner=_runner_from(HEALTHY))
    text = dos.render_questions(dossier)
    assert "`execution` = **PASS**" in text


def test_json_render_is_loadable_and_lists_axes():
    dossier = dos.build_dossier(NOTEBOOK, repo_root=Path("/repo"),
                                runner=_runner_from(HEALTHY))
    payload = json.loads(dos.dossier_to_json(dossier))
    assert [a["axis"] for a in payload["axes"]] == list(dos.AXES)
    assert len(payload["questions"]) == 3


# ---------------------------------------------------------------------------
# main -- de bout en bout, sans organe reel
# ---------------------------------------------------------------------------

def test_main_returns_zero_on_healthy_dossier(monkeypatch, capsys):
    monkeypatch.setattr(dos, "build_dossier",
                        lambda nb, repo_root=None: dos.Dossier(notebook=nb, family="Sudoku",
                                                               rows=[dos.Row(
                                                                   "execution", "Execution",
                                                                   dos.PASS, "ok", "organe")]))
    rc = dos.main(["--notebook", NOTEBOOK])
    assert rc == 0
    assert "Dossier de revue editoriale" in capsys.readouterr().out


def test_main_returns_one_when_an_axis_errors(monkeypatch, capsys):
    monkeypatch.setattr(dos, "build_dossier",
                        lambda nb, repo_root=None: dos.Dossier(notebook=nb, family=None,
                                                               rows=[dos.Row(
                                                                   "execution", "Execution",
                                                                   dos.ERROR, "muet", "organe")]))
    rc = dos.main(["--notebook", NOTEBOOK])
    assert rc == 1
    assert "ERROR execution" in capsys.readouterr().err


def test_main_writes_the_file_it_is_asked_for(monkeypatch, tmp_path):
    monkeypatch.setattr(dos, "build_dossier",
                        lambda nb, repo_root=None: dos.Dossier(notebook=nb, family=None,
                                                               rows=[]))
    out = tmp_path / "dossier.md"
    rc = dos.main(["--notebook", NOTEBOOK, "--out", str(out)])
    assert rc == 0
    assert "Dossier de revue editoriale" in out.read_text(encoding="utf-8")
