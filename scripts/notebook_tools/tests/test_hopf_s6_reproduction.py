"""Tests du lanceur natif de reproduction Hopf S6 (#21442).

Le protocole complet (WSL, builds Lean Challenge/Solution, comparator) n'est
jamais execute ici : ``subprocess.run`` est mocke, et la reproduction reelle au
pin reste couverte par les artefacts du checkout (build.log, comparator.log),
pas par ces tests.
"""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from hopf_s6_reproduction import (  # noqa: E402
    BUILD_LOG,
    COMPARATOR_LOG,
    FULL_PROTOCOL,
    HOPF_DIR,
    HOPF_URL,
    LANDRUN_BIN,
    LANDRUN_PROBE,
    PINNED_SHA,
    TOOLCHAIN,
    _landrun_probe_sh,
    captured_step,
    cmd_check,
    cmd_full,
    landrun_probe,
    prepare_checkout_step,
    rotate_if_present,
    toolchain_step,
)

EXPORTER_PATH = (
    f"{HOPF_DIR}/.lake/packages/lean4export/.lake/build/bin/lean4export"
)


def _completed(cmd, returncode):
    return subprocess.CompletedProcess(cmd, returncode)


def _fake_run(calls, fail_at=None, fail_rc=7):
    """subprocess.run mocke : rc=0 partout sauf a l'index fail_at."""
    def fake_run(cmd, *args, **kwargs):
        calls.append((tuple(cmd), kwargs))
        index = len(calls) - 1
        return _completed(cmd, fail_rc if index == fail_at else 0)
    return fake_run


class TestFullProtocolSteps:
    def test_comparator_step_uses_absolute_exporter_path(self):
        step = FULL_PROTOCOL[-1]
        assert f"COMPARATOR_LEAN4EXPORT={EXPORTER_PATH}" in step
        assert f"cd {HOPF_DIR} &&" in step
        assert "lake exe comparator comparator/config.json" in step

    def test_no_step_keeps_undefined_shell_variable_or_placeholder(self):
        for step in FULL_PROTOCOL:
            # $d n'est jamais defini cote shell : il rendait le chemin racine.
            assert "$d" not in step
            # aucun placeholder .format() non resolu ne doit atteindre le shell
            # (``{ident}`` ; le groupe bash ``{ time ... ; }`` -- espace apres
            # l'accolade ouvrante -- n'est pas un placeholder).
            assert not re.search(r"\{\w+\}", step)

    def test_intentional_shell_variables_are_preserved(self):
        # Le fix ne touche que $d : les variables WSL legitimes restent.
        step = FULL_PROTOCOL[-1]
        assert "COMPARATOR_LANDRUN=$HOME/bin/landrun" in step
        assert (
            "COMPARATOR_NANODA=$HOME/nanoda_lib/target/release/nanoda_bin"
            in step
        )


class TestCmdFullDryRun:
    def test_dry_run_prints_protocol_without_any_execution(self, capsys):
        with patch("hopf_s6_reproduction.subprocess.run") as run:
            rc = cmd_full(dry_run=True)
        run.assert_not_called()
        assert rc == 0
        out = capsys.readouterr().out
        assert "(dry-run: nothing executed)" in out
        for step in FULL_PROTOCOL:
            assert step in out


class TestCmdFullExecution:
    def test_success_runs_every_step_in_order_and_returns_zero(self):
        calls = []
        with patch(
            "hopf_s6_reproduction.subprocess.run",
            side_effect=_fake_run(calls),
        ):
            rc = cmd_full(dry_run=False)
        assert rc == 0
        assert [cmd for cmd, _ in calls] == [
            ("wsl", "-e", "bash", "-lc", step) for step in FULL_PROTOCOL
        ]
        # Execution adaptee aux builds longs : jamais le timeout borne de wsl().
        for _, kwargs in calls:
            assert kwargs.get("timeout") is None

    @pytest.mark.parametrize("fail_at", [0, 3, len(FULL_PROTOCOL) - 1])
    def test_first_failure_stops_protocol_and_propagates_rc(
        self, fail_at, capsys
    ):
        calls = []
        with patch(
            "hopf_s6_reproduction.subprocess.run",
            side_effect=_fake_run(calls, fail_at=fail_at, fail_rc=7),
        ):
            rc = cmd_full(dry_run=False)
        assert rc == 7
        assert len(calls) == fail_at + 1
        assert [cmd for cmd, _ in calls] == [
            ("wsl", "-e", "bash", "-lc", step)
            for step in FULL_PROTOCOL[: fail_at + 1]
        ]
        err = capsys.readouterr().err
        assert "Step failed" in err
        assert FULL_PROTOCOL[fail_at] in err


class TestRotationClause:
    def test_rotation_is_guarded_and_utc_stamped(self):
        clause = rotate_if_present(BUILD_LOG)
        # garde [ -f ] : un log absent n'echoue pas l'etape (rc 0)
        assert clause.startswith(f"if [ -f {BUILD_LOG} ]; then mv ")
        # mv --backup=numbered : deux rotations dans la meme seconde ne se
        # remplacent pas (numerotation GNU), jamais de sauvegarde ecrasee
        assert "mv --backup=numbered " in clause
        # suffixe date UTC : conservation identifiable
        assert "$(date -u +%Y%m%dT%H%M%SZ).bak" in clause
        assert clause.endswith(".bak; fi")


class TestCapturedStep:
    def test_first_write_rotates_then_truncating_tee(self):
        step = captured_step("lake build Challenge", BUILD_LOG)
        assert step == (
            f"cd {HOPF_DIR} && {rotate_if_present(BUILD_LOG)} "
            f"&& set -o pipefail && lake build Challenge 2>&1 "
            f"| tee {BUILD_LOG}"
        )

    def test_append_skips_rotation_and_appends(self):
        step = captured_step("lake build Solution", BUILD_LOG, append=True)
        assert "mv" not in step  # pas de rotation du build.log fraichement ouvert
        assert step == (
            f"cd {HOPF_DIR} && set -o pipefail && lake build Solution 2>&1 "
            f"| tee -a {BUILD_LOG}"
        )

    def test_timed_step_wraps_producer_and_keeps_pipefail(self):
        step = captured_step("lake exe comparator c.json", COMPARATOR_LOG,
                             timed=True)
        # groupe { time ... ; } : le timing (stderr du groupe) suit le 2>&1
        # vers tee -> la ligne ``real XmY.Ys`` atterrit dans le log
        assert step == (
            f"cd {HOPF_DIR} && {rotate_if_present(COMPARATOR_LOG)} "
            f"&& set -o pipefail && {{ time lake exe comparator c.json ; }} 2>&1 "
            f"| tee {COMPARATOR_LOG}"
        )
        assert step.index("set -o pipefail") < step.index("| tee")


class TestFullProtocolLogCapture:
    def test_challenge_step_preserves_previous_build_log(self):
        step = FULL_PROTOCOL[-3]
        assert rotate_if_present(BUILD_LOG) in step
        assert "lake build Challenge 2>&1 | tee /home/jesse/HopfProblem/build.log" in step
        assert "tee -a" not in step

    def test_solution_step_appends_to_same_build_log_without_rotation(self):
        step = FULL_PROTOCOL[-2]
        assert rotate_if_present(BUILD_LOG) not in step
        assert "lake build Solution 2>&1 | tee -a /home/jesse/HopfProblem/build.log" in step

    def test_comparator_step_rotates_own_log_then_tees(self):
        step = FULL_PROTOCOL[-1]
        assert rotate_if_present(COMPARATOR_LOG) in step
        assert "tee -a" not in step
        assert f"| tee {COMPARATOR_LOG}" in step

    def test_comparator_step_is_timed(self):
        # sans enveloppe time, comparator.log ne contient aucune ligne
        # ``real`` et check_ok rend real_seconds None (defaut mesure 2026-10-19)
        step = FULL_PROTOCOL[-1]
        assert "{ time " in step and " ; } 2>&1 | tee" in step

    def test_pipefail_precedes_every_captured_pipeline(self):
        # tee ne masque jamais le rc du producteur : pipefail avant le pipeline.
        for step in FULL_PROTOCOL[-3:]:
            assert step.index("set -o pipefail") < step.index("| tee")

    def test_both_builds_target_the_same_build_log(self):
        assert BUILD_LOG in FULL_PROTOCOL[-3]
        assert BUILD_LOG in FULL_PROTOCOL[-2]
        assert COMPARATOR_LOG not in FULL_PROTOCOL[-3]
        assert COMPARATOR_LOG not in FULL_PROTOCOL[-2]


class TestPreparationSteps:
    def test_toolchain_step_installs_only_if_exact_name_missing(self):
        step = toolchain_step()
        assert step == (
            "if ! installed=$(elan toolchain list); then "
            'echo "refus: elan toolchain list a echoue" >&2; exit 1; fi; '
            "echo \"$installed\" | cut -d' ' -f1 "
            f"| grep -qxF '{TOOLCHAIN}' || elan toolchain install {TOOLCHAIN}"
        )
        # pas de masquage general : un echec reel d'install echoue l'etape
        assert "|| true" not in step
        # match EXACT : v4.33.0 ne doit pas matcher v4.33.0-rc1
        assert "-qxF" in step

    def test_prepare_step_clones_or_refuses_explicitly(self):
        step = prepare_checkout_step()
        assert f"git clone {HOPF_URL} {HOPF_DIR}" in step
        assert "refus: /home/jesse/HopfProblem existe sans etre un depot git" in step
        assert "refus: pas de remote origin" in step
        assert "refus: origin inattendu: $origin" in step
        assert "refus: lecture de l'etat du depot impossible" in step
        assert "refus: arbre de travail sale" in step
        assert f"git -C {HOPF_DIR} checkout -q {PINNED_SHA}" in step
        # jamais de suppression de la cible, quel que soit son etat
        assert "rm " not in step

    def test_prepare_step_has_no_untested_substitution(self):
        # une substitution $( ) placee DIRECTEMENT dans un test [ -n ... ]
        # rendrait une chaine vide en cas de panne, lue a tort comme 'propre'
        step = prepare_checkout_step()
        assert '[ -n "$(' not in step
        assert '[ -z "$(' not in step

    def test_protocol_starts_with_idempotent_preparation(self):
        assert FULL_PROTOCOL[0] == prepare_checkout_step()
        assert FULL_PROTOCOL[1] == toolchain_step()


# --- Contrat cmd_check : fail-closed, absence != compte nul -----------------

BUILD_LOG_TEXT = (
    "info: decision procedure elaborated\n"
    "Build completed successfully (8707 jobs)\n"
    "Built Solution (1154s)\n"
    "info: Solution.lean:1:0: 'Solution.solution' depends on axioms: "
    "[propext, Classical.choice, Quot.sound]\n"
)
COMPARATOR_LOG_TEXT = (
    "real 11m2.3s\n"
    "Nanoda kernel accepts the solution\n"
    "Lean default kernel accepts the solution\n"
    "Your solution is okay!\n"
)


def fake_sh_for(values):
    def fake_sh(cmd, default=""):
        for needle, value in values.items():
            if needle in cmd:
                return value
        return default
    return fake_sh


def positive_mapping():
    return {
        "rev-parse HEAD": PINNED_SHA,
        "lean-toolchain": "leanprover/lean4:v4.33.0",
        f"test -f {HOPF_DIR}/Solution.lean": "yes",
        "wc -l": "248818",
        "stat -c %s": "197642508",
        r"grep -cE '^\s*sorry\s*$'": "0",
        "grep -cw sorry": "0",
        r"grep -cE '^\s*axiom\s'": "0",
        "grep -cw native_decide": "0",
        "head -1": "MIT License",
        "od -An -tx1": "elf64-x86-64",
        f"cat {BUILD_LOG}": BUILD_LOG_TEXT,
        f"cat {COMPARATOR_LOG}": COMPARATOR_LOG_TEXT,
        f"date -u -r {BUILD_LOG}": "2026-10-19T10:00:00Z",
        f"date -u -r {COMPARATOR_LOG}": "2026-10-19T10:20:00Z",
    }


def run_check(values, capsys):
    with patch("hopf_s6_reproduction.sh", side_effect=fake_sh_for(values)):
        rc = cmd_check()
    return rc, json.loads(capsys.readouterr().out)


class TestCmdCheckVerdict:
    def test_complete_realistic_evidence_passes(self, capsys):
        rc, out = run_check(positive_mapping(), capsys)
        assert rc == 0
        assert out["check_ok"] is True
        assert out["pinned_sha"] == PINNED_SHA
        assert out["sha_matches_pin"] is True
        assert out["solution_lines"] == 248818
        assert out["solution_olean_bytes"] == 197642508
        # comptes nuls LUS (grep || true), jamais des defauts
        assert out["sorry_proof_count"] == 0
        assert out["axiom_decl_count"] == 0
        assert out["native_decide_count"] == 0
        assert out["build"]["jobs_counts"] == [8707]
        assert out["build"]["solution_seconds"] == 1154
        assert out["axioms_within_permitted"] is True
        assert out["comparator"]["verdict"] == "Your solution is okay!"
        assert out["comparator"]["real_seconds"] == 662.3
        assert out["comparator"]["nanoda"] == "accepts"
        assert out["build_log_mtime_utc"] == "2026-10-19T10:00:00Z"
        assert out["comparator_log_mtime_utc"] == "2026-10-19T10:20:00Z"

    def test_wrong_pin_fails_closed(self, capsys):
        values = positive_mapping()
        values["rev-parse HEAD"] = "deadbeef" * 5
        rc, out = run_check(values, capsys)
        assert rc == 1
        assert out["pinned_sha"] == "deadbeef" * 5
        assert out["sha_matches_pin"] is False
        assert out["check_ok"] is False

    def test_absent_checkout_reports_none_not_zero_and_fails(self, capsys):
        rc, out = run_check({}, capsys)  # tout defaut : aucun artefact
        assert rc == 1
        assert out["check_ok"] is False
        assert out["pinned_sha"] is None
        # absence != preuve nulle : jamais 0 par defaut (#21442 acceptance)
        assert out["solution_present"] is False
        assert out["solution_lines"] is None
        assert out["solution_olean_bytes"] is None
        assert out["sorry_proof_count"] is None
        assert out["native_decide_count"] is None
        assert out["build"] is None and out["build_log_present"] is False
        assert out["comparator"] is None
        assert out["comparator_log_present"] is False
        assert out["build_log_mtime_utc"] is None
        assert out["comparator_log_mtime_utc"] is None

    def test_comparator_rejected_fails_closed(self, capsys):
        values = positive_mapping()
        values[f"cat {COMPARATOR_LOG}"] = (
            "Nanoda kernel REJECTED the solution\n"
            "Lean default kernel accepts the solution\n"
        )
        rc, out = run_check(values, capsys)
        assert rc == 1
        assert out["comparator_log_present"] is True
        assert out["comparator"]["verdict"] is None
        assert out["comparator"]["nanoda"] is None
        assert out["check_ok"] is False

    def test_missing_comparator_timing_fails_closed(self, capsys):
        # les trois verdicts d'acceptation SANS ligne ``real`` : le run reel du
        # 2026-10-19 a produit exactement ce log (comparator execute sans
        # enveloppe time) -- check doit le refuser, real_seconds etant consomme
        # par le notebook (division par 60 dans la cellule verdict)
        values = positive_mapping()
        values[f"cat {COMPARATOR_LOG}"] = (
            "Running nanoda kernel on solution\n"
            "Nanoda kernel accepts the solution\n"
            "Running Lean default kernel on solution.\n"
            "Lean default kernel accepts the solution\n"
            "Your solution is okay!\n"
        )
        rc, out = run_check(values, capsys)
        assert rc == 1
        assert out["comparator_log_present"] is True
        assert out["comparator"]["verdict"] == "Your solution is okay!"
        assert out["comparator"]["real_seconds"] is None
        assert out["check_ok"] is False

    def test_missing_olean_fails_closed(self, capsys):
        values = positive_mapping()
        del values["stat -c %s"]
        rc, out = run_check(values, capsys)
        assert rc == 1
        assert out["solution_olean_bytes"] is None
        assert out["check_ok"] is False

    def test_read_sorry_count_fails_closed(self, capsys):
        values = positive_mapping()
        values[r"grep -cE '^\s*sorry\s*$'"] = "3"
        rc, out = run_check(values, capsys)
        assert rc == 1
        assert out["sorry_proof_count"] == 3  # compte LU, pas une absence
        assert out["check_ok"] is False

    def test_failed_build_log_fails_closed(self, capsys):
        values = positive_mapping()
        values[f"cat {BUILD_LOG}"] = "error: build failed\n"
        rc, out = run_check(values, capsys)
        assert rc == 1
        assert out["build"]["jobs_counts"] == []
        assert out["check_ok"] is False

    def test_missing_axiom_evidence_fails_closed(self, capsys):
        values = positive_mapping()
        values[f"cat {BUILD_LOG}"] = (
            "Build completed successfully (8707 jobs)\n"
            "Built Solution (1154s)\n"
        )
        rc, out = run_check(values, capsys)
        assert rc == 1
        assert out["axioms_within_permitted"] is False
        assert out["check_ok"] is False


class TestLandrunBinaryVerified:
    """Critere 2 de #21442 : le binaire Landrun se verifie, il ne se nomme pas."""

    def test_probe_reads_the_elf_header_not_the_file_name(self):
        assert "od -An -tx1 -N20" in LANDRUN_PROBE
        assert 'cut -c1-8' in LANDRUN_PROBE and "7f454c46" in LANDRUN_PROBE
        assert 'cut -c9-10' in LANDRUN_PROBE                  # classe 64 bits
        assert 'cut -c37-40' in LANDRUN_PROBE                 # e_machine x86-64
        assert "3e00" in LANDRUN_PROBE
        # `-lt 40` : un fichier trop court est un etat distinct, pas un refus
        # generique (regression mesuree : parametres positionnels $19 = ${1}9)
        assert '-lt 40' in LANDRUN_PROBE
        assert "$19" not in LANDRUN_PROBE

    def test_probe_is_parameterised_so_it_can_be_measured(self):
        # la sonde prend un chemin : elle est testable sur des fichiers reels
        assert "/tmp/quelque-chose" in _landrun_probe_sh("/tmp/quelque-chose")
        assert LANDRUN_BIN in _landrun_probe_sh()

    def test_gate_runs_before_the_comparator_invocation(self):
        step = FULL_PROTOCOL[-1]
        assert step.index("landrun_type") < step.index("lake exe comparator")
        # refus explicite sur stderr (donc dans comparator.log), rc non nul
        assert ">&2" in step
        assert "exit 1" in step
        assert LANDRUN_BIN in step

    @pytest.mark.parametrize(
        "landrun_type",
        [
            "missing",
            "not-a-file",
            "not-executable",
            "not-elf",
            "elf-not-64bit",
            "elf64-not-x86-64",
            "too-short",
        ],
    )
    def test_check_fails_closed_on_every_other_type(self, landrun_type, capsys):
        values = positive_mapping()
        values["od -An -tx1"] = landrun_type
        rc, out = run_check(values, capsys)
        assert rc == 1
        assert out["landrun_type"] == landrun_type  # type LU, pas un booleen
        assert out["check_ok"] is False

    def test_check_reports_none_when_probe_is_silent(self, capsys):
        values = positive_mapping()
        values["od -An -tx1"] = ""
        rc, out = run_check(values, capsys)
        assert rc == 1
        # absence de lecture != type hors norme : deux etats distincts
        assert out["landrun_type"] is None
        assert out["check_ok"] is False

    def test_check_names_the_binary_path_in_its_output(self, capsys):
        rc, out = run_check(positive_mapping(), capsys)
        assert rc == 0
        assert out["landrun_path"] == LANDRUN_BIN
        assert out["landrun_type"] == "elf64-x86-64"


# --- Tests bash REELS (WSL) -------------------------------------------------
# Repertoire jetable sous /tmp du WSL (jamais le checkout Hopf), producteurs
# echo/bash uniquement : aucun build, aucun clone, aucun reseau.

WSL_AVAILABLE = shutil.which("wsl") is not None


def wsl_bash(cmd: str, timeout: int = 60) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["wsl", "-e", "bash", "-lc", cmd],
        capture_output=True, text=True, timeout=timeout, encoding="utf-8",
        errors="replace",
    )


@pytest.mark.skipif(not WSL_AVAILABLE, reason="WSL requis : tests bash reels")
class TestRealBashCapture:
    @pytest.fixture()
    def wsl_tmp(self):
        # Scratch EXT4 du WSL, pas drvfs : les tests de permissions (chmod 555)
        # et la semantique mv/tee exigent un filesystem Linux natif ; /tmp du
        # WSL est aussi le substrat des runs reels (lake stall sur /mnt drvfs,
        # cf. docstring du module). Le scratchpad de session est un chemin
        # Windows (= /mnt drvfs vu du WSL) : inutilisable pour ces tests.
        proc = wsl_bash("mktemp -d /tmp/hopf_s6_test.XXXXXX")
        assert proc.returncode == 0, proc.stderr
        directory = proc.stdout.strip()
        assert directory.startswith("/tmp/hopf_s6_test."), directory
        yield directory
        # Discipline : suppression NOMMEE des artefacts crees (bornes au
        # prefix build.log), puis rmdir du repertoire devenu vide -- jamais
        # de rm -rf.
        files = wsl_bash(f"ls -A {directory}").stdout.split()
        for name in files:
            assert name.startswith("build.log"), (directory, name, files)
            assert wsl_bash(f"rm -f {directory}/{name}").returncode == 0
        assert wsl_bash(f"rmdir {directory}").returncode == 0

    def test_bash_n_accepts_every_full_protocol_step(self):
        for step in FULL_PROTOCOL:
            proc = subprocess.run(
                ["wsl", "-e", "bash", "-n", "-c", step],
                capture_output=True, text=True, timeout=60,
                encoding="utf-8", errors="replace",
            )
            assert proc.returncode == 0, (step, proc.stderr)

    def test_old_log_preserved_then_captured(self, wsl_tmp):
        log = f"{wsl_tmp}/build.log"
        assert wsl_bash(f"echo OLD_EVIDENCE > {log}").returncode == 0
        proc = wsl_bash(captured_step("echo CHALLENGE_LINE", log, cwd=wsl_tmp))
        assert proc.returncode == 0, proc.stderr
        baks = [f for f in wsl_bash(f"ls {wsl_tmp}").stdout.split()
                if ".bak" in f]
        assert len(baks) == 1, baks
        assert "OLD_EVIDENCE" in wsl_bash(f"cat {wsl_tmp}/{baks[0]}").stdout
        assert "CHALLENGE_LINE" in wsl_bash(f"cat {log}").stdout

    def test_two_rotations_same_second_keep_both_backups(self, wsl_tmp):
        log = f"{wsl_tmp}/build.log"
        step = captured_step("echo RUN_OUTPUT", log, cwd=wsl_tmp)
        # date FIGEE par fonction shell : les deux rotations utilisent le meme
        # stamp, deterministe (frontiere de seconde ne peut plus fausser le
        # test). Le gel ne vit que dans CE shell de test, la production est
        # intacte.
        combined = (
            "date() { echo 20000101T000000Z; }; "
            f"echo V1 > {log}; {step}; echo V2 > {log}; {step}"
        )
        proc = wsl_bash(combined)
        assert proc.returncode == 0, proc.stderr
        baks = [f for f in wsl_bash(f"ls {wsl_tmp}").stdout.split()
                if ".bak" in f]
        assert len(baks) == 2, baks  # aucune sauvegarde remplacee
        # preuve que la collision meme-stamp a bien ete exercee
        stamps = {f.split(".")[2] for f in baks}
        assert stamps == {"20000101T000000Z"}, baks
        archived = wsl_bash(f"cat {wsl_tmp}/*.bak*").stdout
        assert "V1" in archived and "V2" in archived
        assert "RUN_OUTPUT" in wsl_bash(f"cat {log}").stdout

    def test_producer_rc_propagates_through_tee(self, wsl_tmp):
        log = f"{wsl_tmp}/build.log"
        step = captured_step("bash -c 'echo boom; exit 7'", log, cwd=wsl_tmp)
        proc = wsl_bash(step)
        assert proc.returncode == 7, (proc.returncode, proc.stdout, proc.stderr)
        # le log capture quand meme la sortie du producteur
        assert "boom" in wsl_bash(f"cat {log}").stdout

    def test_timed_producer_rc_and_timing_line_both_land_in_log(self, wsl_tmp):
        log = f"{wsl_tmp}/build.log"
        step = captured_step("bash -c 'echo verdict; exit 0'", log,
                             cwd=wsl_tmp, timed=True)
        proc = wsl_bash(step)
        assert proc.returncode == 0, (proc.returncode, proc.stdout, proc.stderr)
        captured = wsl_bash(f"cat {log}").stdout
        assert "verdict" in captured
        # la ligne ``real XmY.Ys`` (stderr du groupe time) est bien dans le log
        assert "real" in captured and re.search(r"real\s+\d+m[\d.]+s", captured)

    def test_timed_producer_failure_keeps_producer_rc(self, wsl_tmp):
        log = f"{wsl_tmp}/build.log"
        step = captured_step("bash -c 'echo boom; exit 7'", log,
                             cwd=wsl_tmp, timed=True)
        proc = wsl_bash(step)
        # time retourne le rc de la commande enveloppee : pipefail le garde
        assert proc.returncode == 7, (proc.returncode, proc.stdout, proc.stderr)
        assert "boom" in wsl_bash(f"cat {log}").stdout

    def test_failed_rotation_never_truncates_existing_log(self, wsl_tmp):
        log = f"{wsl_tmp}/build.log"
        assert wsl_bash(f"echo PRECIOUS > {log}").returncode == 0
        assert wsl_bash(f"chmod 555 {wsl_tmp}").returncode == 0  # mv impossible
        try:
            step = captured_step("echo SHOULD_NOT_RUN", log, cwd=wsl_tmp)
            proc = wsl_bash(step)
            assert proc.returncode != 0  # court-circuit du && : etape echouee
            # tee ne s'est PAS execute : la preuve existante est intacte
            assert wsl_bash(f"cat {log}").stdout.strip() == "PRECIOUS"
        finally:
            wsl_bash(f"chmod 755 {wsl_tmp}")
            assert "SHOULD_NOT_RUN" not in wsl_bash(f"cat {log}").stdout

    def test_failed_cd_aborts_without_creating_log(self, wsl_tmp):
        gone = f"{wsl_tmp}/does_not_exist"
        log = f"{gone}/build.log"
        proc = wsl_bash(captured_step("echo NOPE", log, cwd=gone))
        assert proc.returncode != 0
        # tee n'a pas ouvert le log : le repertoire n'existe meme pas
        assert not wsl_bash(f"test -e {gone} && echo EXISTS").stdout.strip()

    def test_append_chains_challenge_then_solution(self, wsl_tmp):
        log = f"{wsl_tmp}/build.log"
        challenge = captured_step("echo CHALLENGE_OUT", log, cwd=wsl_tmp)
        solution = captured_step(
            "echo SOLUTION_OUT", log, cwd=wsl_tmp, append=True)
        assert wsl_bash(challenge).returncode == 0
        assert wsl_bash(solution).returncode == 0
        content = wsl_bash(f"cat {log}").stdout
        assert "CHALLENGE_OUT" in content and "SOLUTION_OUT" in content
        assert content.index("CHALLENGE_OUT") < content.index("SOLUTION_OUT")
        # l'append ne rotationne pas : un seul fichier de log, zero .bak
        files = wsl_bash(f"ls {wsl_tmp}").stdout.split()
        assert files == ["build.log"], files


# --- Tests bash REELS de la preparation idempotente --------------------------
# elan stubbe par fonction shell ; depots git LOCAUX (git init/clone locaux,
# hors ligne). Aucun build, aucun reseau, aucune source upstream touchee.

ELAN_LIST_OK_INSTALLED = (
    "elan() { if [ \"$1\" = toolchain ] && [ \"$2\" = list ]; then "
    "printf 'leanprover/lean4:v4.33.0\\nleanprover/lean4:v4.33.1\\n'; "
    "else echo 'INSTALL_APPELE_A_TORT' >&2; exit 1; fi; }; "
)
ELAN_LIST_ONLY_RC = (
    "elan() { if [ \"$1\" = toolchain ] && [ \"$2\" = list ]; then "
    "printf 'leanprover/lean4:v4.33.0-rc1 (default)\\n'; "
    "else echo 'INSTALL_APPELE_A_TORT' >&2; exit 1; fi; }; "
)
ELAN_LIST_FAILS = (
    "elan() { if [ \"$1\" = toolchain ] && [ \"$2\" = list ]; then "
    "echo 'elan casse' >&2; exit 5; "
    "else echo 'INSTALL_APPELE_A_TORT' >&2; exit 1; fi; }; "
)


@pytest.mark.skipif(not WSL_AVAILABLE, reason="WSL requis : tests bash reels")
class TestRealBashPreparation:
    @pytest.fixture()
    def wsl_repo_tmp(self):
        proc = wsl_bash("mktemp -d /tmp/hopf_s6_test.XXXXXX")
        assert proc.returncode == 0, proc.stderr
        directory = proc.stdout.strip()
        assert directory.startswith("/tmp/hopf_s6_test."), directory
        yield directory
        # Nettoyage borne sous le chemin mktemp exact : fichiers ENUMERES par
        # find (compte sane), supprimes un a un, puis repertoires vides
        # supprimes de bas en haut -- jamais de rm -rf.
        listed = wsl_bash(f"find {directory} -type f").stdout.split()
        assert len(listed) < 200, listed
        assert wsl_bash(
            f"find {directory} -type f -exec rm -f {{}} +").returncode == 0
        assert wsl_bash(
            f"find {directory} -depth -type d -delete").returncode == 0
        residue = wsl_bash(f"test -e {directory} && echo STILL_THERE")
        assert residue.stdout.strip() == ""

    @staticmethod
    def _make_repo(base: str, url: str, name: str = "repo"):
        repo = f"{base}/{name}"
        proc = wsl_bash(
            f"git init -q {repo} && "
            f"git -C {repo} remote add origin {url} && "
            f"echo sol > {repo}/Solution.lean && "
            f"git -C {repo} add Solution.lean && "
            f"git -C {repo} -c user.email=hopf@test -c user.name=hopf "
            f"commit -q -m init && git -C {repo} rev-parse HEAD"
        )
        assert proc.returncode == 0, proc.stderr
        return repo, proc.stdout.strip()

    # --- toolchain ---

    def test_toolchain_already_installed_skips_install(self):
        proc = wsl_bash(ELAN_LIST_OK_INSTALLED + toolchain_step())
        assert proc.returncode == 0, proc.stderr
        assert "INSTALL_APPELE_A_TORT" not in proc.stderr

    def test_toolchain_missing_runs_install(self):
        # liste ne contenant QUE v4.33.0-rc1 : le match exact ne doit pas le
        # confondre avec v4.33.0 -- l'installation doit etre tentee
        stub = ELAN_LIST_ONLY_RC.replace(
            "echo 'INSTALL_APPELE_A_TORT' >&2; exit 1", "echo INSTALL_OK")
        proc = wsl_bash(stub + toolchain_step())
        assert proc.returncode == 0, proc.stderr
        assert "INSTALL_OK" in proc.stdout

    def test_toolchain_install_failure_propagates(self):
        stub = ELAN_LIST_ONLY_RC.replace(
            "echo 'INSTALL_APPELE_A_TORT' >&2; exit 1", "exit 3")
        proc = wsl_bash(stub + toolchain_step())
        assert proc.returncode == 3

    def test_toolchain_listing_failure_refuses_instead_of_installing(self):
        # echec de LISTING != absence : refus explicite, installation jamais
        # tentee (le stub d'install echoue bruyamment s'il est appele)
        proc = wsl_bash(ELAN_LIST_FAILS + toolchain_step())
        assert proc.returncode == 1
        assert "refus: elan toolchain list a echoue" in proc.stderr
        assert "INSTALL_APPELE_A_TORT" not in proc.stderr

    # --- checkout ---

    def test_foreign_origin_refused(self, wsl_repo_tmp):
        repo, sha = self._make_repo(wsl_repo_tmp, "https://example.com/other.git")
        proc = wsl_bash(
            prepare_checkout_step(directory=repo,
                                  url="https://example.com/expected.git",
                                  pin=sha))
        assert proc.returncode == 1
        assert "refus: origin inattendu" in proc.stderr

    def test_not_a_git_directory_refused(self, wsl_repo_tmp):
        plain = f"{wsl_repo_tmp}/plain"
        assert wsl_bash(f"mkdir {plain}").returncode == 0
        proc = wsl_bash(
            prepare_checkout_step(directory=plain,
                                  url="https://example.com/expected.git",
                                  pin=PINNED_SHA))
        assert proc.returncode == 1
        assert "sans etre un depot git" in proc.stderr

    def test_dirty_tree_refused(self, wsl_repo_tmp):
        repo, sha = self._make_repo(wsl_repo_tmp, "https://example.com/expected.git")
        assert wsl_bash(f"echo drift >> {repo}/Solution.lean").returncode == 0
        proc = wsl_bash(
            prepare_checkout_step(directory=repo,
                                  url="https://example.com/expected.git",
                                  pin=sha))
        assert proc.returncode == 1
        assert "refus: arbre de travail sale" in proc.stderr

    def test_status_read_failure_refused_not_treated_as_clean(self, wsl_repo_tmp):
        # git status qui ECHOUE dans une substitution non testee rendrait une
        # chaine vide, lue a tort comme 'propre' : le refus doit etre explicite
        repo, sha = self._make_repo(wsl_repo_tmp, "https://example.com/expected.git")
        stub = (
            "git() { if [ \"$1\" = -C ] && [ \"$3\" = status ]; then exit 5; fi; "
            "command git \"$@\"; }; "
        )
        proc = wsl_bash(stub + prepare_checkout_step(
            directory=repo, url="https://example.com/expected.git", pin=sha))
        assert proc.returncode == 1
        assert "refus: lecture de l'etat du depot impossible" in proc.stderr

    def test_clean_repo_at_pin_reused_as_noop(self, wsl_repo_tmp):
        repo, sha = self._make_repo(wsl_repo_tmp, "https://example.com/expected.git")
        step = prepare_checkout_step(
            directory=repo, url="https://example.com/expected.git", pin=sha)
        assert wsl_bash(step).returncode == 0
        assert wsl_bash(f"git -C {repo} rev-parse HEAD").stdout.strip() == sha

    def test_clone_then_reuse_is_relaunchable(self, wsl_repo_tmp):
        # origine LOCALE hors ligne : le chemin clone est reellement exerce
        repo, sha = self._make_repo(wsl_repo_tmp, "x", name="src")
        assert wsl_bash(f"git clone -q --bare {repo} {wsl_repo_tmp}/origin.git"
                        ).returncode == 0
        work = f"{wsl_repo_tmp}/work"
        step = prepare_checkout_step(
            directory=work, url=f"{wsl_repo_tmp}/origin.git", pin=sha)
        first = wsl_bash(step)
        assert first.returncode == 0, first.stderr
        assert wsl_bash(f"git -C {work} rev-parse HEAD").stdout.strip() == sha
        # relance : la cible existe -> chemin reutilisation, toujours rc 0
        second = wsl_bash(step)
        assert second.returncode == 0, second.stderr
        assert wsl_bash(f"git -C {work} rev-parse HEAD").stdout.strip() == sha

    def test_pin_absent_from_repo_fails(self, wsl_repo_tmp):
        repo, _sha = self._make_repo(wsl_repo_tmp, "https://example.com/expected.git")
        bogus = "a" * 40
        proc = wsl_bash(
            prepare_checkout_step(directory=repo,
                                  url="https://example.com/expected.git",
                                  pin=bogus))
        assert proc.returncode != 0

@pytest.mark.skipif(not WSL_AVAILABLE, reason="WSL requis : tests bash reels")
class TestRealBashLandrunProbe:
    """La sonde exercee sur de VRAIS fichiers, pas sur un mock de `sh`."""

    @pytest.fixture
    def probe_dir(self):
        proc = wsl_bash("mktemp -d /tmp/hopf_landrun.XXXXXX")
        assert proc.returncode == 0, proc.stderr
        directory = proc.stdout.strip()
        assert directory.startswith("/tmp/hopf_landrun."), directory
        yield directory
        # suppression NOMMEE (un sous-repertoire eventuel par rmdir), puis
        # rmdir du repertoire devenu vide : jamais de rm -rf
        for name in wsl_bash(f"ls -A {directory}").stdout.split():
            target = f"{directory}/{name}"
            if wsl_bash(f"test -d {target}").returncode == 0:
                assert wsl_bash(f"rmdir {target}").returncode == 0
            else:
                assert wsl_bash(f"rm -f {target}").returncode == 0
        assert wsl_bash(f"rmdir {directory}").returncode == 0

    def test_absent_path_is_missing(self, probe_dir):
        assert landrun_probe(f"{probe_dir}/absent") == "missing"

    def test_directory_is_not_a_file(self, probe_dir):
        assert wsl_bash(f"mkdir {probe_dir}/rep").returncode == 0
        assert landrun_probe(f"{probe_dir}/rep") == "not-a-file"

    def test_non_executable_file_is_refused(self, probe_dir):
        # /bin/true est un ELF64 x86-64 : seule l'executabilite manque
        assert wsl_bash(f"cp /bin/true {probe_dir}/noexec").returncode == 0
        assert wsl_bash(f"chmod -x {probe_dir}/noexec").returncode == 0
        assert landrun_probe(f"{probe_dir}/noexec") == "not-executable"

    def test_executable_text_file_is_not_elf(self, probe_dir):
        # plus de vingt octets : le seuil de longueur est franchi, donc le
        # refus observe est bien celui de la magie ELF et non `too-short`
        assert wsl_bash(
            f"printf '#!/bin/sh\\nexit 0\\n# quelques octets de plus\\n' "
            f"> {probe_dir}/script"
        ).returncode == 0
        assert wsl_bash(f"chmod +x {probe_dir}/script").returncode == 0
        assert landrun_probe(f"{probe_dir}/script") == "not-elf"

    def test_truncated_elf_is_too_short(self, probe_dir):
        assert wsl_bash(f"head -c 3 /bin/true > {probe_dir}/short").returncode == 0
        assert wsl_bash(f"chmod +x {probe_dir}/short").returncode == 0
        assert landrun_probe(f"{probe_dir}/short") == "too-short"

    def test_real_elf64_x86_64_binary_is_accepted(self, probe_dir):
        assert wsl_bash(f"cp /bin/true {probe_dir}/good").returncode == 0
        assert wsl_bash(f"chmod +x {probe_dir}/good").returncode == 0
        assert landrun_probe(f"{probe_dir}/good") == "elf64-x86-64"

    def test_the_machine_landrun_binary_is_a_real_elf64_x86_64(self):
        # mesure de la machine courante : si elle est absente, le test le DIT
        # (un `missing` n'est jamais acquitte comme un succes).
        observed = landrun_probe()
        assert observed in ("elf64-x86-64", "missing"), observed
        if observed == "missing":
            pytest.skip(f"binaire absent sur cette machine : {LANDRUN_BIN}")
