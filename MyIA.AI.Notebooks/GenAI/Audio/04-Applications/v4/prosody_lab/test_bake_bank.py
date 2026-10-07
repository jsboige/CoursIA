"""test_bake_bank.py — tests unitaires du schéma v1 et des outils associés.

Couvre :
- T1 : record minimal valide (tous les champs requis)
- T2 : record avec tous les champs (gate pré-UAT fidelity)
- T3 : record sans champ requis → rejeté
- T4 : champ enum hors liste → rejeté
- T5 : champ hash hors pattern → rejeté
- T6 : idempotence : deux appends mêmes clé → 1 OK + 1 SKIP-DUP
- T7 : bake_report : tri par extract+WER+motor
- T8 : bake_report : rapport vide → header seul

Ce test ne dépend PAS d'un workflow CI dédié (décision ai-01 sur #19695,
2026-10-07). Il est invocable localement :
    python -m pytest prosody_lab/test_bake_bank.py -v
ou :
    python -m unittest prosody_lab/test_bake_bank.py -v
"""
from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

PROSODY_LAB_ROOT = Path(__file__).resolve().parent
SCHEMA_PATH = PROSODY_LAB_ROOT / "bank_schema_v1.json"

# Encodage pour les sous-processus Windows (cp1252 → décodage laxiste)
SUBPROC_KW = dict(capture_output=True, text=True, encoding="utf-8", errors="replace")


def _minimal_record() -> dict:
    return {
        "schema_version": "v1",
        "ts": "2026-10-07T13:25:33Z",
        "machine": "myia-po-2023",
        "motor": "cosyvoice3",
        "extract": "A",
    }


def _full_record() -> dict:
    return {
        "schema_version": "v1",
        "ts": "2026-10-07T13:25:33Z",
        "machine": "myia-po-2023",
        "motor": "qwen3_tts_1_7b_customvoice",
        "motor_size_b": 1.7,
        "motor_license": "Apache-2.0",
        "extract": "A",
        "extract_text_sha256_prefix": "a2cab722b97d2378",
        "extract_text_chars": 1649,
        "seed": None,
        "speaker": "serena",
        "instruct": "voix posée, débit lent, ton narratif",
        "language": "fr",
        "wer": 0.3294,
        "wer_model": "openai/whisper-large-v3",
        "rtf": 5.524,
        "vram_mb": 4432.0,
        "duration_s": 132.88,
        "load_s": 2893.8,
        "wallclock_total_s": 734.0,
        "prosody_st_range": None,
        "prosody_cv": None,
        "prosody_velocity": None,
        "prosody_verdict": None,
        "fidelity_added_words": 0,
        "fidelity_omitted_segments_3plus": 0,
        "voice_consistent": True,
        "hallu_per_100_syl": None,
        "notes": "Test fixture.",
    }


def _validate(record: dict, schema: dict) -> tuple[bool, list[str]]:
    """Valide via bake_append.py import direct du validateur."""
    sys.path.insert(0, str(PROSODY_LAB_ROOT))
    import bake_append  # noqa: E402
    errs = bake_append._validate_jsonschema(record, schema)
    if not errs:
        errs = bake_append._validate_locally(record, schema)
    return (len(errs) == 0, errs)


class TestSchema(unittest.TestCase):
    def setUp(self):
        with open(SCHEMA_PATH, encoding="utf-8") as f:
            self.schema = json.load(f)

    def test_T1_minimal_record_ok(self):
        ok, errs = _validate(_minimal_record(), self.schema)
        self.assertTrue(ok, f"Devrait être valide, erreurs : {errs}")

    def test_T2_full_record_ok(self):
        ok, errs = _validate(_full_record(), self.schema)
        self.assertTrue(ok, f"Devrait être valide, erreurs : {errs}")

    def test_T3_missing_required(self):
        rec = _minimal_record()
        del rec["motor"]
        ok, errs = _validate(rec, self.schema)
        self.assertFalse(ok)
        self.assertTrue(any("motor" in e for e in errs))

    def test_T4_enum_extract_invalid(self):
        rec = _minimal_record()
        rec["extract"] = "Z"
        ok, errs = _validate(rec, self.schema)
        self.assertFalse(ok)
        self.assertTrue(any("extract" in e for e in errs))

    def test_T5_sha256_prefix_wrong_length(self):
        rec = _full_record()
        rec["extract_text_sha256_prefix"] = "tooshort"  # 8 chars, pas 16
        ok, errs = _validate(rec, self.schema)
        self.assertFalse(ok)

    def test_T5b_unknown_field_rejected(self):
        rec = _minimal_record()
        rec["champ_qui_n_existe_pas"] = "x"
        ok, errs = _validate(rec, self.schema)
        self.assertFalse(ok)
        # jsonschema écrit "Additional properties are not allowed" ;
        # le validateur interne (filet) écrit "champ non autorisé par le schéma".
        self.assertTrue(any(
            "non autoris" in e.lower() or "additional properties" in e.lower()
            for e in errs
        ), f"Erreur attendue 'non autorisé' introuvable dans : {errs}")

    def test_T6_schema_version_const(self):
        rec = _minimal_record()
        rec["schema_version"] = "v2"  # pas v1
        ok, errs = _validate(rec, self.schema)
        self.assertFalse(ok)


class TestIdempotence(unittest.TestCase):
    """T6 (idempotence) : deux appends mêmes clé → 1 OK + 1 rc=4."""

    def test_T6_idempotent_append(self):
        with tempfile.TemporaryDirectory() as tmp:
            bank = Path(tmp) / "bank.jsonl"
            # Construire un metrics.json minimal valide (avec text pour sha256)
            mjson = Path(tmp) / "metrics.json"
            mjson.write_text(json.dumps({
                "model": "test_motor",
                "wer": 0.42,
                "rtf": 1.5,
                "vram_peak_gb": 4.0,
                "duration_s": 30.0,
                "text": "référence A",
                "seed": 0,
            }), encoding="utf-8")
            base = [sys.executable, str(PROSODY_LAB_ROOT / "bake_append.py"),
                    "--bank", str(bank), "--metrics", str(mjson),
                    "--motor", "test_motor", "--extract", "A",
                    "--machine", "myia-po-2023", "--seed", "0",
                    "--motor-license", "Apache-2.0"]
            r1 = subprocess.run(base, **SUBPROC_KW)
            self.assertEqual(r1.returncode, 0,
                             f"premier append a échoué : {r1.stderr}")
            r2 = subprocess.run(base, **SUBPROC_KW)
            self.assertEqual(r2.returncode, 4,
                             f"deuxième append aurait dû échouer (rc=4) ; "
                             f"rc={r2.returncode}, stderr={r2.stderr}")
            # Le banc contient 1 ligne
            with open(bank, encoding="utf-8") as f:
                self.assertEqual(len(f.readlines()), 1)


class TestReport(unittest.TestCase):
    """T7/T8 : bake_report génère un tableau trié par extract+WER+motor."""

    def test_T7_sort_order(self):
        with tempfile.TemporaryDirectory() as tmp:
            bank = Path(tmp) / "bank.jsonl"
            records = [
                {"schema_version": "v1", "ts": "t1", "machine": "m", "motor": "z",
                 "extract": "B", "wer": 0.5, "rtf": 1.0},
                {"schema_version": "v1", "ts": "t2", "machine": "m", "motor": "a",
                 "extract": "A", "wer": 0.3, "rtf": 1.0},
                {"schema_version": "v1", "ts": "t3", "machine": "m", "motor": "m",
                 "extract": "A", "wer": 0.1, "rtf": 1.0},
            ]
            with open(bank, "w", encoding="utf-8") as f:
                for r in records:
                    f.write(json.dumps(r) + "\n")
            out = subprocess.run(
                [sys.executable, str(PROSODY_LAB_ROOT / "bake_report.py"),
                 "--bank", str(bank)],
                **SUBPROC_KW,
            )
            self.assertEqual(out.returncode, 0)
            md = out.stdout or ""
            # Vérifier l'ordre attendu : A/0.1 (m), A/0.3 (a), B/0.5 (z)
            m_idx = md.index("m |")
            a_idx = md.index("| a ")
            z_idx = md.index("z |")
            self.assertLess(m_idx, a_idx)
            self.assertLess(a_idx, z_idx)

    def test_T8_empty_bank(self):
        with tempfile.TemporaryDirectory() as tmp:
            bank = Path(tmp) / "bank.jsonl"  # n'existe pas
            out = subprocess.run(
                [sys.executable, str(PROSODY_LAB_ROOT / "bake_report.py"),
                 "--bank", str(bank)],
                **SUBPROC_KW,
            )
            self.assertEqual(out.returncode, 0)
            self.assertIn("Lignes : 0", (out.stdout or ""))


if __name__ == "__main__":
    unittest.main(verbosity=2)