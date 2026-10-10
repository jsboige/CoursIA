"""test_bake_bank.py -- tests unitaires pour bake_append + bake_report.

Cible : schema v1, unicite (motor, extract, seed), idempotence, rapport markdown.
Sortie : exit 0 si tous les tests passent, exit 1 sinon.

Usage (depuis la racine du worktree) :
    python MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/test_bake_bank.py

Cablage CI : suite existante, pas de nouveau workflow bloqueur (cadrage
coordinateur #19695 point 4 : "le controle de schema et d'unicite est un test
unitaire dans la suite existante, pas un nouveau workflow CI bloquant"). Ce
fichier est collecte par la jambe `Scripts Tests (CPU)` de
`.github/workflows/scripts-tests.yml` -- cite nommement dans sa liste de cibles
pytest, et ses trois fichiers-sujets (bake_append.py, bake_report.py,
bank_schema_v1.json) figurent dans ses declencheurs `paths:`.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

THIS_DIR = Path(__file__).resolve().parent
BAKE_APPEND = THIS_DIR / "bake_append.py"
BAKE_REPORT = THIS_DIR / "bake_report.py"
SCHEMA = THIS_DIR / "bank_schema_v1.json"


def fail(msg: str) -> None:
    print(f"FAIL: {msg}", file=sys.stderr)
    sys.exit(1)


def assert_eq(label: str, got, expected) -> None:
    if got != expected:
        fail(f"{label}: got {got!r}, expected {expected!r}")


def assert_true(label: str, got: bool) -> None:
    if not got:
        fail(f"{label}: expected True, got False")


def assert_contains(label: str, haystack: str, needle: str) -> None:
    if needle not in haystack:
        fail(f"{label}: {needle!r} not in output (preview: {haystack[:200]!r})")


def run(cmd: list[str]) -> tuple[int, str, str]:
    # PYTHONIOENCODING force l'enfant en UTF-8 quel que soit l'OS. Sans lui, un
    # stdout PIPE prend l'encodage de la locale (cp1252 sous Windows) et le
    # decodage UTF-8 ci-dessous echoue sur le premier accent du rapport
    # (#19820 : le rapport porte "référence"/"Durée", mesure sur myia-po-2027).
    env = {**os.environ, "PYTHONIOENCODING": "utf-8"}
    proc = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", env=env)
    return proc.returncode, proc.stdout, proc.stderr


# Tests ---------------------------------------------------------------------

def test_schema_valid() -> None:
    """Le schéma v1 doit être un JSON-Schema valide (syntaxe)."""
    data = json.loads(SCHEMA.read_text(encoding="utf-8"))
    assert_true("schema est un objet JSON", isinstance(data, dict))
    assert_true("schema.type == array", data.get("type") == "array")
    assert_true("schema a items.required", "required" in data.get("items", {}))
    assert_true("schema a uniqueness.key", data.get("uniqueness", {}).get("key") == ["motor", "extract", "seed"])
    print("[OK] test_schema_valid")


def test_append_dry_run_valid() -> None:
    """Append d'un run complet doit passer en dry-run."""
    rc, _, _ = run([
        sys.executable, str(BAKE_APPEND), "--bank", str(THIS_DIR / "_test_bank.json"),
        "--dry-run",
        "--run", json.dumps({
            "ts": "2026-10-08T01:00:00Z",
            "machine": "myia-po-2027",
            "motor": "test_motor",
            "extract": "A",
            "seed": 1,
            "wer": 0.5,
            "duration_s": 12.3,
        }),
    ])
    assert_eq("dry-run valid rc", rc, 0)
    # Le fichier ne doit pas avoir été créé
    if (THIS_DIR / "_test_bank.json").exists():
        fail("dry-run a écrit alors qu'il ne devrait pas")
    print("[OK] test_append_dry_run_valid")


def test_append_validation_failure() -> None:
    """Append d'un run avec champs obligatoires manquants doit échouer (rc=1)."""
    rc, _, stderr = run([
        sys.executable, str(BAKE_APPEND), "--bank", str(THIS_DIR / "_test_bank.json"),
        "--run", json.dumps({"motor": "x", "extract": "A", "seed": 1}),  # manque machine, ts, duration_s
    ])
    assert_eq("validation failure rc", rc, 1)
    assert_contains("validation failure message", stderr, "VALIDATION FAILED")
    print("[OK] test_append_validation_failure")


def test_append_validation_type_error() -> None:
    """Type incorrect (string au lieu de number) doit échouer."""
    rc, _, stderr = run([
        sys.executable, str(BAKE_APPEND), "--bank", str(THIS_DIR / "_test_bank.json"),
        "--run", json.dumps({
            "ts": "2026-10-08T01:00:00Z", "machine": "myia-po-2027",
            "motor": "x", "extract": "A", "seed": 1, "duration_s": "twelve",  # type incorrect
        }),
    ])
    assert_eq("type error rc", rc, 1)
    assert_contains("type error message", stderr, "duration_s")
    print("[OK] test_append_validation_type_error")


def test_append_idempotence() -> None:
    """Deux appends successifs avec la même clé (motor, extract, seed) = 1 ligne."""
    with tempfile.TemporaryDirectory() as tmp:
        bank = Path(tmp) / "bank.json"
        for _ in range(2):
            rc, _, _ = run([
                sys.executable, str(BAKE_APPEND), "--bank", str(bank),
                "--run", json.dumps({
                    "ts": "2026-10-08T01:00:00Z", "machine": "myia-po-2027",
                    "motor": "idem", "extract": "A", "seed": 1,
                    "wer": 0.5, "duration_s": 10.0,
                }),
            ])
            assert_eq("idempotence append rc", rc, 0)
        rows = json.loads(bank.read_text(encoding="utf-8"))
        assert_eq("idempotence row count", len(rows), 1)
    print("[OK] test_append_idempotence")


def test_append_upsert_updates_field() -> None:
    """Un upsert doit mettre à jour le champ modifié sans dupliquer."""
    with tempfile.TemporaryDirectory() as tmp:
        bank = Path(tmp) / "bank.json"
        # Premier append
        run([
            sys.executable, str(BAKE_APPEND), "--bank", str(bank),
            "--run", json.dumps({
                "ts": "2026-10-08T01:00:00Z", "machine": "myia-po-2027",
                "motor": "upd", "extract": "B", "seed": 7,
                "wer": 0.9, "duration_s": 5.0,
            }),
        ])
        # Deuxième append avec un WER corrigé
        rc, _, _ = run([
            sys.executable, str(BAKE_APPEND), "--bank", str(bank),
            "--run", json.dumps({
                "ts": "2026-10-08T02:00:00Z", "machine": "myia-po-2027",
                "motor": "upd", "extract": "B", "seed": 7,
                "wer": 0.3, "duration_s": 5.0,
                "notes": "corrigé",
            }),
        ])
        assert_eq("upsert rc", rc, 0)
        rows = json.loads(bank.read_text(encoding="utf-8"))
        assert_eq("upsert row count", len(rows), 1)
        assert_eq("upsert wer updated", rows[0].get("wer"), 0.3)
        assert_eq("upsert notes added", rows[0].get("notes"), "corrigé")
        assert_eq("upsert ts updated", rows[0].get("ts"), "2026-10-08T02:00:00Z")
    print("[OK] test_append_upsert_updates_field")


def test_report_format() -> None:
    """Le rapport doit trier par WER croissant et lister tous les runs."""
    with tempfile.TemporaryDirectory() as tmp:
        bank = Path(tmp) / "bank.json"
        bank.write_text(json.dumps([
            {"ts": "2026-10-08T01:00:00Z", "machine": "myia-po-2027",
             "motor": "good", "extract": "A", "seed": 1, "wer": 0.1, "duration_s": 10.0},
            {"ts": "2026-10-08T01:00:00Z", "machine": "myia-po-2027",
             "motor": "bad", "extract": "A", "seed": 1, "wer": 0.9, "duration_s": 8.0},
            {"ts": "2026-10-08T01:00:00Z", "machine": "myia-po-2027",
             "motor": "null_wer", "extract": "A", "seed": 1, "wer": None, "duration_s": 12.0},
        ]), encoding="utf-8")
        rc, stdout, _ = run([
            sys.executable, str(BAKE_REPORT), "--bank", str(bank), "--sort", "wer",
        ])
        assert_eq("report rc", rc, 0)
        # WER croissant : good (0.1) doit apparaitre avant bad (0.9)
        i_good = stdout.find("good")
        i_bad = stdout.find("bad")
        i_null = stdout.find("null_wer")
        assert_true("good before bad", i_good < i_bad)
        assert_true("bad before null", i_bad < i_null)
        assert_contains("report has WER column", stdout, "WER")
        assert_contains("report has counts", stdout, "run(s)")
    print("[OK] test_report_format")


def test_report_sort_chronological() -> None:
    """`--sort ts` doit trier chronologiquement sans lever (temoin #19820).

    `ts` est une chaine ISO-8601, pas un nombre : un tri qui applique `float()`
    a toutes les cles levait `ValueError` des la premiere date. Les trois dates
    sont volontairement desordonnees, et la troisieme est `None` pour verifier
    que les nulles restent en fin de tableau.
    """
    with tempfile.TemporaryDirectory() as tmp:
        bank = Path(tmp) / "bank.json"
        bank.write_text(json.dumps([
            {"ts": "2026-10-08T01:00:00Z", "machine": "myia-po-2027",
             "motor": "recent", "extract": "A", "seed": 1, "duration_s": 10.0},
            {"ts": "2026-10-06T01:00:00Z", "machine": "myia-po-2027",
             "motor": "ancien", "extract": "A", "seed": 1, "duration_s": 10.0},
            {"ts": None, "machine": "myia-po-2027",
             "motor": "sans_ts", "extract": "A", "seed": 1, "duration_s": 10.0},
            {"ts": "2026-10-07T01:00:00Z", "machine": "myia-po-2027",
             "motor": "median", "extract": "A", "seed": 1, "duration_s": 10.0},
        ]), encoding="utf-8")
        rc, stdout, stderr = run([
            sys.executable, str(BAKE_REPORT), "--bank", str(bank), "--sort", "ts",
        ])
        # Vue du bug : `render(..., sort_key='ts')` rendait rc=1 avec
        # `ValueError: could not convert string to float` dans stderr.
        assert_eq(f"report --sort ts rc (stderr: {stderr[:200]!r})", rc, 0)
        i_ancien = stdout.find("ancien")
        i_median = stdout.find("median")
        i_recent = stdout.find("recent")
        i_none = stdout.find("sans_ts")
        assert_true("les trois moteurs dates sont presents",
                    min(i_ancien, i_median, i_recent, i_none) >= 0)
        assert_true("ancien avant median", i_ancien < i_median)
        assert_true("median avant recent", i_median < i_recent)
        assert_true("dates avant la nulle", i_recent < i_none)
    print("[OK] test_report_sort_chronological")


def test_append_validation_union_enum() -> None:
    """Un `asr_models` interdit doit etre refuse (temoin #19820).

    `asr_models` est declare en union JSON-Schema `["array", "null"]` : un test
    d'items ecrit `ftype == "array"` est faux sur ce champ, et les elements
    n'etaient jamais verifies. `validate_run` rendait `[]` pour
    `[123, "invalid-model"]`.
    """
    with tempfile.TemporaryDirectory() as tmp:
        bank = Path(tmp) / "bank.json"
        rc, _, stderr = run([
            sys.executable, str(BAKE_APPEND), "--bank", str(bank),
            "--run", json.dumps({
                "ts": "2026-10-08T01:00:00Z", "machine": "myia-po-2027",
                "motor": "union", "extract": "A", "seed": 1, "duration_s": 10.0,
                "asr_models": [123, "invalid-model"],
            }),
        ])
        assert_eq(f"union enum rc (stderr: {stderr[:200]!r})", rc, 1)
        assert_contains("union enum message", stderr, "asr_models")
        assert_contains("union enum cite le 1er element", stderr, "invalid-model")
        if bank.exists():
            fail("un run invalide a ete ecrit dans le banc")
        # Controle positif : les valeurs de l'enum restent acceptees.
        rc_ok, _, stderr_ok = run([
            sys.executable, str(BAKE_APPEND), "--bank", str(bank), "--dry-run",
            "--run", json.dumps({
                "ts": "2026-10-08T01:00:00Z", "machine": "myia-po-2027",
                "motor": "union", "extract": "A", "seed": 1, "duration_s": 10.0,
                "asr_models": ["tiny", "large-v3"],
            }),
        ])
        assert_eq(f"enum valide rc (stderr: {stderr_ok[:200]!r})", rc_ok, 0)
    print("[OK] test_append_validation_union_enum")


def test_ingest_bakeoff_small() -> None:
    """Ingestion depuis bakeoff_small/results doit produire au moins les 4 runs (Chatterbox A/B + pocket_tts A/B)."""
    rc, stdout, _ = run([
        sys.executable, str(BAKE_APPEND),
        "--bank", str(THIS_DIR / "_test_bank_ingest.json"),
        "--ingest-root", str(THIS_DIR / "bakeoff_small" / "results"),
        "--dry-run",
    ])
    assert_eq("ingest dry-run rc", rc, 0)
    # Le dry-run affiche la liste des runs
    n_runs = stdout.count("duration=")
    assert_true(f"ingest a produit >=4 runs (got {n_runs})", n_runs >= 4)
    # Vérifie la presence de chatterbox_mtl_v3 et pocket_tts
    assert_contains("ingest contient chatterbox", stdout, "chatterbox_mtl_v3")
    assert_contains("ingest contient pocket_tts", stdout, "pocket_tts")
    print(f"[OK] test_ingest_bakeoff_small ({n_runs} runs)")


def test_extended_schema_fields() -> None:
    """Couche #19722 : un run portant les champs étendus (fidelité, prosodie,
    traçabilité moteur) doit valider ; les champs restent OPTIONNELS (le run
    socle-seul de test_append_dry_run_valid le prouve déjà)."""
    schema = json.loads(SCHEMA.read_text(encoding="utf-8"))
    props = schema["items"]["properties"]
    for field in ["fidelity_added_words", "fidelity_omitted_segments_3plus",
                  "voice_consistent", "prosody_verdict", "motor_license",
                  "motor_size_b", "wer_model", "source_path", "schema_version"]:
        assert_true(f"schéma déclare {field}", field in props)
    assert_true("required ignore les champs étendus",
                "fidelity_added_words" not in schema["items"]["required"])
    rc, _, stderr = run([
        sys.executable, str(BAKE_APPEND), "--bank", str(THIS_DIR / "_test_bank.json"),
        "--dry-run",
        "--run", json.dumps({
            "schema_version": "v1",
            "ts": "2026-10-08T02:00:00Z",
            "machine": "myia-po-2027",
            "motor": "test_motor_ext",
            "extract": "A",
            "seed": 7,
            "duration_s": 9.5,
            "fidelity_added_words": 0,
            "fidelity_omitted_segments_3plus": 1,
            "voice_consistent": True,
            "prosody_st_range": 41.2,
            "prosody_cv": 0.18,
            "prosody_velocity": 3.4,
            "prosody_verdict": "EXPRESSIVE",
            "motor_license": "apache-2.0",
            "motor_size_b": 0.5,
            "wer_model": "large-v3",
            "load_s": 11.2,
            "wallclock_total_s": 30.1,
            "extract_text_sha256_prefix": "deadbeefdeadbeef",
            "source_path": "bakeoff_small/results/test/A__test.json",
        }),
    ])
    assert_eq("extended dry-run rc", rc, 0)
    if rc != 0:
        print(stderr[:400], file=sys.stderr)
    print("[OK] test_extended_schema_fields")


def test_bootstrap_metrics_to_run() -> None:
    """bootstrap_bank._metrics_to_run : aplatie metrics.*, porte license/size
    du conteneur bake_results, et fournit duration_s=0.0+note si absent."""
    sys.path.insert(0, str(THIS_DIR))
    import bootstrap_bank  # noqa: E402
    path = THIS_DIR / "bakeoff_small" / "results" / "demo_m" / "A__demo.json"
    run1 = bootstrap_bank._metrics_to_run(
        path,
        {"cell": "demo_m", "motor_license": "mit", "motor_size_b": 2.0,
         "metrics": {"duration_s": 8.4, "wer": 0.12}, "seed": 3},
        "demo_m", "A")
    assert_eq("mapping duration_s (aplati)", run1["duration_s"], 8.4)
    assert_eq("mapping wer (aplati)", run1["wer"], 0.12)
    assert_eq("mapping seed", run1["seed"], 3)
    assert_eq("mapping motor_license", run1["motor_license"], "mit")
    assert_eq("mapping motor_size_b", run1["motor_size_b"], 2.0)
    assert_eq("mapping schema_version", run1.get("schema_version"), "v1")
    assert_true("mapping source_path relatif", not run1["source_path"].startswith((":\\", "/")))
    run2 = bootstrap_bank._metrics_to_run(path, {"wer": 0.4}, "demo_m", "A")
    assert_eq("duration_s manquant -> 0.0", run2["duration_s"], 0.0)
    assert_contains("note duration inconnue", run2["notes"], "duration_s inconnue")
    # Label humain "0.5B" -> nombre ; seed null -> 42 ; g_* -> prosody_*
    run3 = bootstrap_bank._metrics_to_run(
        path, {"motor_size_b": "0.5B", "seed": None,
               "g_st_range": 18.85, "g_cv": 0.21}, "demo_m", "A")
    assert_eq("size '0.5B' -> 0.5", run3["motor_size_b"], 0.5)
    assert_eq("seed None -> 42", run3["seed"], 42)
    assert_eq("g_st_range -> prosody_st_range", run3["prosody_st_range"], 18.85)
    assert_eq("g_cv -> prosody_cv", run3["prosody_cv"], 0.21)
    # Graphie moteur uniformisée : stem GDrive `chatterbox-mtl-v3` == bakeoff
    # `chatterbox_mtl_v3`, sinon l'upsert laisse deux lignes pour un moteur.
    run4 = bootstrap_bank._metrics_to_run(path, {"wer": 0.4},
                                          "chatterbox-mtl-v3", "A")
    assert_eq("motor snake_case", run4["motor"], "chatterbox_mtl_v3")
    print("[OK] test_bootstrap_metrics_to_run")


def test_bootstrap_gdrive_decoders() -> None:
    """bootstrap_bank : décodage extract/motor des stems A0-review.

    Terrain (2026-10-10) : tous les stems A0C-* de A0-review portent le texte
    de l'extrait A (ouverture Boule de Suif) — le « C » de « A0C » appartient
    au nom de campagne. L'ancien regex `^A0([A-E])` décodait « C » à tort.
    """
    sys.path.insert(0, str(THIS_DIR))
    import bootstrap_bank  # noqa: E402
    assert_eq("A0C-cosyvoice3-metrics -> extract A",
              bootstrap_bank._gdrive_extract_from_stem("A0C-cosyvoice3-metrics"), "A")
    assert_eq("A0C-cosyvoice3-metrics -> motor",
              bootstrap_bank._gdrive_motor_from_stem("A0C-cosyvoice3-metrics"),
              "cosyvoice3")
    assert_eq("A0C-zonos-chunked-metrics -> motor",
              bootstrap_bank._gdrive_motor_from_stem("A0C-zonos-chunked-metrics"),
              "zonos")
    assert_eq("stem hors pattern -> None",
              bootstrap_bank._gdrive_extract_from_stem("metrics"), None)
    print("[OK] test_bootstrap_gdrive_decoders")


def test_bootstrap_gdrive_flatten() -> None:
    """_flatten_gdrive : wer.wer, seed.base, prosody/synth imbriqués -> à plat."""
    sys.path.insert(0, str(THIS_DIR))
    import bootstrap_bank  # noqa: E402
    flat = bootstrap_bank._flatten_gdrive({
        "client": "cosyvoice3",
        "text": "Pendant plusieurs jours...",
        "wer": {"wer": 0.518, "model": "faster-whisper-tiny"},
        "seed": {"base": 42, "per_chunk": "torch.manual_seed(42 + i)"},
        "prosody": {"duration_s": 89.52, "melodic_span_p5p95_st": 13.27,
                    "melody_verdict": "EXPRESSIVE", "voice_verdict": "CONSISTENT"},
        "synth": {"model": "FunAudioLLM/Fun-CosyVoice3-0.5B-2512",
                  "language": "French", "rtf": 1.13, "vram_peak_gb": 2.5,
                  "speaker": None, "instruct": None},
        "wallclock_total_s": 101.1,
    })
    assert_eq("wer.wer aplati", flat["wer"], 0.518)
    assert_eq("wer_model", flat["wer_model"], "faster-whisper-tiny")
    assert_eq("asr_models court", flat["asr_models"], ["tiny"])
    assert_eq("seed.base", flat["seed"], 42)
    assert_eq("duration_s (prosody)", flat["duration_s"], 89.52)
    assert_eq("prosody_st_range", flat["prosody_st_range"], 13.27)
    assert_eq("prosody_verdict", flat["prosody_verdict"], "EXPRESSIVE")
    assert_true("voice_consistent", flat["voice_consistent"] is True)
    assert_eq("rtf", flat["rtf"], 1.13)
    assert_eq("vram_mb", flat["vram_mb"], 2560)
    assert_eq("language BCP-47", flat["language"], "fr")
    assert_eq("synth_model traçabilité", flat["synth_model"],
              "FunAudioLLM/Fun-CosyVoice3-0.5B-2512")
    assert_true("speaker None non posé", "speaker" not in flat)
    print("[OK] test_bootstrap_gdrive_flatten")


def main() -> int:
    tests = [
        test_schema_valid,
        test_append_dry_run_valid,
        test_append_validation_failure,
        test_append_validation_type_error,
        test_append_idempotence,
        test_append_upsert_updates_field,
        test_report_format,
        test_report_sort_chronological,
        test_append_validation_union_enum,
        test_ingest_bakeoff_small,
        test_extended_schema_fields,
        test_bootstrap_metrics_to_run,
        test_bootstrap_gdrive_decoders,
        test_bootstrap_gdrive_flatten,
    ]
    print(f"Running {len(tests)} tests...\n")
    failed = 0
    for t in tests:
        try:
            t()
        except SystemExit:
            failed += 1
        except Exception as e:
            print(f"FAIL: {t.__name__}: {type(e).__name__}: {e}", file=sys.stderr)
            failed += 1
    print(f"\n{len(tests) - failed}/{len(tests)} passed")
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())