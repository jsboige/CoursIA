# -*- coding: utf-8 -*-
"""Tests unitaires pour le verrou de clocks GPU (commands/gpu.py).

La suite est hermetique : nvidia-smi n'est jamais execute (mock de _run_cmd),
le journal est ecrit dans un dossier temporaire. Verifiables sur n'importe quel
runner (pas de GPU requis).

Voir : docs/genai/genai-services.md (verrou clocks GPU / undervolt lock).
"""

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

# Sortie reelle capturee sur la machine (nvidia-smi -q -d CLOCK). Le parseur doit
# extraire Graphics courant=1230 sous "Clocks" et Graphics max=2100 sous "Max Clocks",
# tout en ignorant les valeurs "deprecated" / N/A / "Not Found" des autres sections.
CLOCK_OUTPUT = """==============NVSMI LOG==============

Timestamp                                 : Sun Sep  6 23:35:19 2026
Driver Version                            : 616.56
CUDA Version                              : 13.4

Attached GPUs                             : 1
GPU 00000000:01:00.0
    Clocks
        Graphics                          : 1230 MHz
        SM                                : 1230 MHz
        Memory                            : 6001 MHz
        Video                             : 1080 MHz
    Applications Clocks
        Graphics                          : Requested functionality has been deprecated
        Memory                            : Requested functionality has been deprecated
    Default Applications Clocks
        Graphics                          : Requested functionality has been deprecated
        Memory                            : Requested functionality has been deprecated
    Deferred Clocks
        Memory                            : N/A
    Max Clocks
        Graphics                          : 2100 MHz
        SM                                : 2100 MHz
        Memory                            : 8001 MHz
        Video                             : 1950 MHz
    Max Customer Boost Clocks
        Graphics                          : N/A
    SM Clock Samples
        Duration                          : Not Found
        Number of Samples                 : Not Found
        Max                               : Not Found
        Min                               : Not Found
        Avg                               : Not Found
    Clock Policy
        Auto Boost                        : N/A
        Auto Boost Default                : N/A
"""


class TestGpuLockParse(unittest.TestCase):
    """Parseur des valeurs de clocks."""

    def test_parse_mhz_values(self):
        from commands.gpu import _parse_mhz
        self.assertEqual(_parse_mhz("1230 MHz"), 1230)
        self.assertEqual(_parse_mhz(" 1800 MHz"), 1800)
        self.assertIsNone(_parse_mhz("N/A"))
        self.assertIsNone(_parse_mhz("Requested functionality has been deprecated"))
        self.assertIsNone(_parse_mhz("Not Found"))
        self.assertIsNone(_parse_mhz(""))

    def test_parse_clocks_stdout_real_format(self):
        from commands.gpu import _parse_clocks_stdout
        current, max_clock = _parse_clocks_stdout(CLOCK_OUTPUT)
        self.assertEqual(current, 1230)
        self.assertEqual(max_clock, 2100)

    def test_parse_clocks_stdout_ignores_other_sections(self):
        # Une valeur Graphics sous une section non ciblee ne doit pas ecraser.
        from commands.gpu import _parse_clocks_stdout
        out = ("    Clocks\n        Graphics : 1230 MHz\n"
               "    Max Clocks\n        Graphics : 2100 MHz\n"
               "    Max Customer Boost Clocks\n        Graphics : N/A\n")
        current, max_clock = _parse_clocks_stdout(out)
        self.assertEqual(current, 1230)
        self.assertEqual(max_clock, 2100)

    def test_parse_clocks_stdout_no_graphics(self):
        from commands.gpu import _parse_clocks_stdout
        current, max_clock = _parse_clocks_stdout("    Clocks\n        SM : 1230 MHz\n")
        self.assertIsNone(current)
        self.assertIsNone(max_clock)


class TestGpuLockStatus(unittest.TestCase):
    """gpu_lock_status (lecture seule, mock de _run_cmd)."""

    @patch("commands.gpu._run_cmd")
    def test_status_reads_clocks(self, mock_run):
        from commands.gpu import gpu_lock_status
        mock_run.return_value = (True, CLOCK_OUTPUT, "")
        st = gpu_lock_status()
        self.assertEqual(st, {"current_mhz": 1230, "max_mhz": 2100})

    @patch("commands.gpu._run_cmd")
    def test_status_nvidia_fail_returns_none(self, mock_run):
        from commands.gpu import gpu_lock_status
        mock_run.return_value = (False, "", "driver error")
        self.assertIsNone(gpu_lock_status())


class TestGpuLockVerify(unittest.TestCase):
    """Verdict du verrou selon les clocks observees."""

    def test_verify_lock_on(self):
        from commands.gpu import _verify_lock
        self.assertEqual(_verify_lock(True, 1380, 1800), "OK")
        self.assertEqual(_verify_lock(True, 1380, 2100), "ECHEC")
        self.assertEqual(_verify_lock(True, 1380, None), "INDETERMINE")

    def test_verify_lock_off(self):
        from commands.gpu import _verify_lock
        self.assertEqual(_verify_lock(False, 1380, 2100), "OK")
        self.assertEqual(_verify_lock(False, 1380, 1800), "ECHEC")
        self.assertEqual(_verify_lock(False, 1380, None), "INDETERMINE")


class TestGpuLockApply(unittest.TestCase):
    """gpu_lock_apply (nvidia-smi -lgc / -rgc, mocke)."""

    @patch("commands.gpu._gpu_lock_journal")
    @patch("commands.gpu.gpu_lock_status")
    @patch("commands.gpu._run_cmd")
    def test_apply_on_verified_capped(self, mock_run, mock_status, mock_journal):
        from commands.gpu import gpu_lock_apply
        mock_run.return_value = (True, "", "")
        mock_status.return_value = {"current_mhz": 1800, "max_mhz": 1800}
        self.assertTrue(gpu_lock_apply(True))
        self.assertIn("-lgc 210,1800", mock_run.call_args_list[0][0][0])
        # journalise le verdict OK
        self.assertEqual(mock_journal.call_args[0][1], "OK")

    @patch("commands.gpu._gpu_lock_journal")
    @patch("commands.gpu.gpu_lock_status")
    @patch("commands.gpu._run_cmd")
    def test_apply_on_not_capped_journalized_echac(self, mock_run, mock_status, mock_journal):
        from commands.gpu import gpu_lock_apply
        mock_run.return_value = (True, "", "")
        mock_status.return_value = {"current_mhz": 1380, "max_mhz": 2100}
        self.assertTrue(gpu_lock_apply(True))
        self.assertEqual(mock_journal.call_args[0][1], "ECHEC")

    @patch("commands.gpu.gpu_lock_status")
    @patch("commands.gpu._run_cmd")
    def test_apply_on_cmd_fail_returns_false(self, mock_run, mock_status):
        from commands.gpu import gpu_lock_apply
        mock_run.return_value = (False, "", "rc!=0")
        mock_status.return_value = {"current_mhz": 1380, "max_mhz": 2100}
        self.assertFalse(gpu_lock_apply(True))
        # si la commande echoue, on ne relit pas l'etat
        self.assertEqual(mock_status.call_count, 0)

    @patch("commands.gpu._gpu_lock_journal")
    @patch("commands.gpu.gpu_lock_status")
    @patch("commands.gpu._run_cmd")
    def test_apply_off_uncapped(self, mock_run, mock_status, mock_journal):
        from commands.gpu import gpu_lock_apply
        mock_run.return_value = (True, "", "")
        mock_status.return_value = {"current_mhz": 1380, "max_mhz": 2100}
        self.assertTrue(gpu_lock_apply(False))
        self.assertIn("-rgc", mock_run.call_args_list[0][0][0])
        self.assertEqual(mock_journal.call_args[0][1], "OK")


class TestGpuLockJournal(unittest.TestCase):
    """Journal hermetique (ecrit dans un dossier temporaire)."""

    def test_journal_writes_line(self):
        from commands.gpu import _gpu_lock_journal
        with tempfile.TemporaryDirectory() as td:
            log = Path(td) / "gpu_lock.log"
            with patch("commands.gpu._gpu_lock_log_path", return_value=log):
                line = _gpu_lock_journal("lock-on 210,1800", "OK", "courant=1800MHz max=1800MHz")
            self.assertIn("lock-on 210,1800 -> OK", line)
            content = log.read_text(encoding="utf-8")
            self.assertIn("lock-on 210,1800 -> OK", content)


class TestGpuLockRegister(unittest.TestCase):
    """register : dry-run, aucune execution."""

    def test_register_is_dry_run(self):
        from commands.gpu import gpu_lock_register
        with patch("commands.gpu._gpu_lock_log_path", return_value=Path("gpu_lock.log")):
            with patch("builtins.print") as mock_print:
                gpu_lock_register()
                out = "\n".join(str(c[0]) for c in mock_print.call_args_list)
        self.assertIn("schtasks /create", out)
        self.assertIn("onstart", out)
        self.assertIn("INTERACTIVE-ONLY", out)
        self.assertIn("/delete", out)


if __name__ == "__main__":
    unittest.main()
