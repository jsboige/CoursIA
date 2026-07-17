"""Tests for scripts/translation/translate_csv.py (T3 fork Argumentum, #6949 PR #2).

The T3 engine forks Argumentum ``tools/dnn_i18n/translate_game_rules.py`` (gpt-5.5,
193 LOC) into the CoursIA 7-lang CSV schema. These tests lock the safety gates and
the hash contract WITHOUT calling any live API (``call_chat`` is mocked):

1. **Hash contract** -- ``normalize`` / ``cell_hash`` are byte-identical to T1
   (extract_cells_to_csv.py) and T2 (check_translation_sync.py). T3 must write
   ``hash_<lang> = cell_hash(text_<lang>)`` or T2 drift detection breaks.
2. **Safety gates** -- ``ENABLED=False`` + ``--apply`` is a no-op (no API, no
   mutation); default mode is dry-run (no mutation); missing env keys raise
   ``ValueError`` (never a literal fallback -- secrets-hygiene.md).
3. **Plan semantics** -- markdown cells with empty ``text_<lang>`` are queued;
   code cells skipped by default (``--include-code`` opts in); pre-filled
   ``text_<lang>`` are skipped (resume cache).
4. **CSV coherence** -- write/load round-trip preserves column order + LF endings.
"""

import csv
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "translation"))

import translate_csv as tc  # noqa: E402


# ---------------------------------------------------------------------------
# Fixtures helpers.
# ---------------------------------------------------------------------------
COLUMNS = tc.CSV_COLUMNS


def _write_csv(path, rows):
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        w = csv.DictWriter(f, fieldnames=COLUMNS, lineterminator="\n")
        w.writeheader()
        for r in rows:
            w.writerow({c: r.get(c, "") for c in COLUMNS})


def _row(cell_id, cell_type, text_fr, **filled):
    r = {c: "" for c in COLUMNS}
    r["notebook"] = f"nb/{cell_id}.ipynb"
    r["cell_id"] = cell_id
    r["cell_type"] = cell_type
    r["src_lang"] = "fr"
    r["text_fr"] = text_fr
    r["src_hash"] = tc.cell_hash(text_fr)
    r["hash_fr"] = r["src_hash"]
    r.update(filled)
    return r


# ---------------------------------------------------------------------------
# 1. Hash contract (byte-identical to T1/T2).
# ---------------------------------------------------------------------------
def test_normalize_rstrips_lines_and_trailing_newline():
    # Trailing whitespace + final newline must NOT create faux drift.
    assert tc.normalize("line   \nsecond\t\n") == "line\nsecond"
    assert tc.normalize("single") == "single"
    assert tc.normalize("") == ""


def test_cell_hash_is_sha256_16_of_normalized():
    # Pinned vector: sha256("Bonjour")[:16]. Computed once, locks the contract.
    import hashlib
    expected = hashlib.sha256("Bonjour".encode("utf-8")).hexdigest()[:16]
    assert tc.cell_hash("Bonjour") == expected
    assert len(tc.cell_hash("x")) == 16


def test_cell_hash_trailing_whitespace_stable():
    # Drift-detection invariant: cosmetic whitespace must not change the hash.
    assert tc.cell_hash("text\n") == tc.cell_hash("text")
    assert tc.cell_hash("a \n b") == tc.cell_hash("a\n b")


# ---------------------------------------------------------------------------
# 2. Plan semantics.
# ---------------------------------------------------------------------------
def test_plan_markdown_only_skips_code_by_default():
    rows = [
        _row("c1", "markdown", "Bonjour le monde"),
        _row("c2", "code", "print('hi')"),
        _row("c3", "markdown", "Autre prose"),
    ]
    plan = list(tc.translation_plan(rows, ["en", "es"]))
    # c1 -> en, c1 -> es, c3 -> en, c3 -> es. Code c2 excluded.
    idxs = sorted({i for i, _ in plan})
    assert idxs == [0, 2]
    assert (0, "en") in plan and (0, "es") in plan
    assert (1, "en") not in plan  # code skipped


def test_plan_include_code_opts_in():
    rows = [_row("c1", "code", "x = 1  # comment")]
    assert list(tc.translation_plan(rows, ["en"])) == []
    assert list(tc.translation_plan(rows, ["en"], include_code=True)) == [(0, "en")]


def test_plan_skips_prefilled_target_resume_cache():
    rows = [_row("c1", "markdown", "Bonjour", text_en="Hello world")]
    plan = list(tc.translation_plan(rows, ["en", "es"]))
    # en already filled -> only es queued (resume cache semantics).
    assert (0, "en") not in plan
    assert (0, "es") in plan


def test_plan_skips_empty_fr():
    rows = [_row("c1", "markdown", "   ")]
    assert list(tc.translation_plan(rows, ["en"])) == []


# ---------------------------------------------------------------------------
# 3. CSV round-trip coherence.
# ---------------------------------------------------------------------------
def test_write_load_roundtrip_preserves_columns_and_lf(tmp_path):
    p = tmp_path / "x.csv"
    rows = [_row("c1", "markdown", "Bonjour", text_en="Hello")]
    tc.write_csv(str(p), rows)
    raw = p.read_bytes()
    assert b"\r\n" not in raw  # LF endings, not CRLF
    loaded = tc.load_csv(str(p))
    assert len(loaded) == 1
    assert loaded[0]["cell_id"] == "c1"
    assert loaded[0]["text_en"] == "Hello"
    # All canonical columns present.
    assert set(loaded[0].keys()) >= set(COLUMNS)


def test_load_csv_tolerates_utf8_bom(tmp_path):
    p = tmp_path / "bom.csv"
    rows = [_row("c1", "markdown", "Été café")]
    _write_csv(str(p), rows)
    # Inject a BOM.
    p.write_bytes(b"\xef\xbb\xbf" + p.read_bytes())
    loaded = tc.load_csv(str(p))
    assert loaded[0]["text_fr"] == "Été café"
    assert loaded[0]["cell_id"] == "c1"  # header not polluted by BOM


# ---------------------------------------------------------------------------
# 4. run_translations with mocked call_chat -- writes text_<lang> + hash_<lang>.
# ---------------------------------------------------------------------------
def test_run_translations_writes_text_and_hash(monkeypatch, tmp_path):
    calls = []

    def fake_call(messages, model, key, base_url, max_tokens, reasoning_effort="low", timeout=240):
        calls.append((model, base_url))
        # Deterministic translation derived from the target lang (parsed from the
        # user message "Translate ... into {LangName}.") -- no real LLM call.
        um = next(m["content"] for m in messages if m["role"] == "user")
        lang_name = um.split("into ")[1].split(".")[0]
        return f"[{lang_name}] translated", 0.1, 5

    monkeypatch.setattr(tc, "call_chat", fake_call)
    monkeypatch.setenv("OPENAI_API_KEY", "fake-key-for-testing")

    p = tmp_path / "x.csv"
    rows = [_row("c1", "markdown", "Bonjour le monde")]
    _write_csv(str(p), rows)

    loaded = tc.load_csv(str(p))
    done, fails = tc.run_translations(loaded, ["en"], include_code=False,
                                      out_path=str(p), smoke=False)
    assert done == 1 and fails == 0
    result = tc.load_csv(str(p))
    assert result[0]["text_en"] == "[English] translated"
    # hash_en MUST equal cell_hash of the written text (T2 coherence).
    assert result[0]["hash_en"] == tc.cell_hash("[English] translated")
    assert calls  # provider actually invoked


def test_run_translations_no_env_keys_raises(monkeypatch, tmp_path):
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)
    p = tmp_path / "x.csv"
    _write_csv(str(p), [_row("c1", "markdown", "Bonjour")])
    rows = tc.load_csv(str(p))
    try:
        tc.run_translations(rows, ["en"], False, str(p), False)
    except ValueError as e:
        assert "OPENAI_API_KEY" in str(e)
    else:
        raise AssertionError("ValueError attendue sans clé env (secrets-hygiene)")


# ---------------------------------------------------------------------------
# 5. Safety gates via main() CLI.
# ---------------------------------------------------------------------------
def test_main_apply_gated_when_disabled(monkeypatch, tmp_path, capsys):
    # ENABLED=False (module default). --apply must be a no-op.
    monkeypatch.setattr(tc, "ENABLED", False)
    monkeypatch.setenv("OPENAI_API_KEY", "fake-key-for-testing")
    p = tmp_path / "x.csv"
    original = [_row("c1", "markdown", "Bonjour")]
    _write_csv(str(p), original)
    monkeypatch.setattr(sys, "argv", ["translate_csv.py", "--csv", str(p), "--apply"])
    rc = tc.main()
    assert rc == 0
    # No mutation, no API: text_en still empty.
    assert tc.load_csv(str(p))[0]["text_en"] == ""
    err = capsys.readouterr().err
    assert "GATED" in err and "ENABLED=False" in err


def test_main_dry_run_default_no_mutation(monkeypatch, tmp_path, capsys):
    p = tmp_path / "x.csv"
    _write_csv(str(p), [_row("c1", "markdown", "Bonjour le monde")])
    monkeypatch.setattr(sys, "argv", ["translate_csv.py", "--csv", str(p)])
    rc = tc.main()
    assert rc == 0
    assert tc.load_csv(str(p))[0]["text_en"] == ""  # untouched
    err = capsys.readouterr().err
    assert "dry-run" in err or "dry_run" in err
    assert "traductions nécessaires" in err  # plan reported


def test_main_smoke_limits_to_one_cell(monkeypatch, tmp_path, capsys):
    p = tmp_path / "x.csv"
    _write_csv(str(p), [
        _row("c1", "markdown", "Premier"),
        _row("c2", "markdown", "Deuxième"),
    ])
    monkeypatch.setattr(sys, "argv", ["translate_csv.py", "--csv", str(p), "--smoke"])
    tc.main()
    # Smoke plan = 1 cell x 7 langs = 7 (not 14).
    err = capsys.readouterr().err
    # The plan line reports the count after smoke reduction.
    assert "7 traductions nécessaires" in err or " 7 " in err


# ---------------------------------------------------------------------------
# 5. Extra contract coverage (ported from a short-lived duplicate test file
#    that consolidated here: CRLF/LF hash stability, anchored regression value,
#    ENABLED-default via module reload, schema alignment, env-only provider
#    keys, and plan exclusion of already-translated langs).
# ---------------------------------------------------------------------------
def test_cell_hash_ignores_crlf_vs_lf():
    # CRLF vs LF must NOT create faux drift across Windows/POSIX checkouts.
    assert tc.cell_hash("ligne un\r\nligne deux") == tc.cell_hash("ligne un\nligne deux")


def test_cell_hash_anchored_value():
    # Anchored regression value : locks the hash algorithm itself (16 hex sha256
    # of the normalized text). Changing normalize/cell_hash breaks drift-detection
    # parity with T1/T2, so this must stay stable.
    assert tc.cell_hash("## Introduction au machine learning") == "ec9615f904e04755"


def test_enabled_is_false_by_default_on_fresh_module_load():
    # Reload the module to read its pristine default (a prior test may have
    # monkeypatched tc.ENABLED). The gate must ship disabled.
    import importlib
    fresh = importlib.reload(tc)
    assert fresh.ENABLED is False


def test_targets_are_the_seven_canonical_languages():
    # T1/T2/T3 must agree on the 7 target languages (order matters for CSV cols).
    assert tc.TARGETS == ["en", "ru", "pt", "es", "ar", "fa", "zh"]


def test_every_target_has_text_and_hash_column():
    for lang in tc.TARGETS:
        assert f"text_{lang}" in tc.CSV_COLUMNS, f"missing text_{lang}"
        assert f"hash_{lang}" in tc.CSV_COLUMNS, f"missing hash_{lang}"


def test_provider_keys_empty_without_env(monkeypatch):
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)
    assert tc._provider_keys() == []


def test_provider_keys_read_openai_env(monkeypatch):
    monkeypatch.setenv("OPENAI_API_KEY", "sk-test-only-in-env")
    monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)
    provs = tc._provider_keys()
    assert len(provs) == 1
    _model, key, base = provs[0]
    assert key == "sk-test-only-in-env"
    assert base == "https://api.openai.com/v1"


def test_provider_keys_have_no_literal_default_in_source():
    # secrets-hygiene rule 1-3 : never os.getenv("KEY", "<literal>"). The key
    # must come from env only (no inline fallback that could leak a real secret).
    src = Path(tc.__file__).read_text(encoding="utf-8")
    assert 'getenv("OPENAI_API_KEY"' in src
    assert 'getenv("OPENAI_API_KEY", "' not in src  # no literal default


def test_plan_excludes_already_translated_language():
    # A cell with text_en filled must NOT be re-queued for 'en' (resume cache),
    # but an untranslated cell in the same CSV is still queued.
    rows = [
        _row("c1", "markdown", "Bonjour", text_en="Hello", hash_en=tc.cell_hash("Hello")),
        _row("c2", "markdown", "Salut"),
    ]
    plan = list(tc.translation_plan(rows, ["en"]))
    idxs = {i for i, _ in plan}
    assert 0 not in idxs  # c1 already translated to en
    assert 1 in idxs      # c2 still needs en
