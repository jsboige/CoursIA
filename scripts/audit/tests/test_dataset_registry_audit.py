"""Tests for scripts/audit/check_dataset_registry.py.

Covers the importable pure helpers that implement the registry-coherence audit
(Issue #8055 tranche 2), plus check_entry (via tmp_path synthetic repos) and
main (via monkeypatch on sys.argv).

Scope: the four module-level helpers each carry real branching logic worth pinning:
  - SHA256_RE / is_sha256_complete : hex-format recognition (truncated ellipsis
    vs full 64-char, case sensitivity, length boundaries 14/15/64)
  - sha256_file                   : chunked file hashing (known content, empty)
  - parse_registry                : markdown-table split-by-`|` parsing
    (backtick strip, empty-col filtering, taille int with space/NBSP thousands
    separator, regex filter on sha column, skip <5 cols / non-int taille /
    non-`|` lines / missing file)
  - check_entry                   : the six verdicts (MISSING / OK /
    OK_TRUNCATED / DRIFT-truncated / DRIFT-complete / UNKNOWN) plus the
    `**sensible**` CARD_REQUIRED override (card-absent CRITICAL vs
    card-present-but-path-undocumented MAJOR vs documented no-override)

main() exercises: missing-registry exit 1, empty-parse exit 1, global_status
precedence ladder (CARD_REQUIRED > MISSING > DRIFT > UNKNOWN > OK), all-OK exit 0,
and `--out` file write.

All tests hermetic: synthetic DATASET_REGISTRY.md rows + tmp files, no network,
no subprocess, no real-repo dependency. The registry format used in fixtures
matches the real DATASET_REGISTRY.md (bare int taille with space thousands
separator, truncated sha256 + ellipsis, enum categorie) -- NOT the inaccurate
"<taille> B" in the source docstring.
"""
import hashlib
import importlib.util
import sys
from pathlib import Path

# Module lives in scripts/audit/ (flat, not a package) -> spec_from_file_location.
_MOD_PATH = Path(__file__).resolve().parent.parent / "check_dataset_registry.py"
_spec = importlib.util.spec_from_file_location("check_dataset_registry", _MOD_PATH)
cdr = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cdr)


# ---------------------------------------------------------------------------
# helpers to build synthetic registries + repos
# ---------------------------------------------------------------------------

def _write_registry(path: Path, rows: list[str]) -> Path:
    """Write a registry file whose body is the given table rows (one `| ... |` str each)."""
    path.write_text("\n".join(rows) + "\n", encoding="utf-8")
    return path


def _entry(chemin: str, taille: int, sha: str, licence="MIT",
           categorie="pedagogique-synthetique") -> str:
    """One registry table row in the real on-disk format (backticked path/sha, bare int taille)."""
    return f"| `{chemin}` | {taille} | `{sha}` | {licence} | {categorie} | usage | card |"


# A real 64-char lowercase hex sha256 (of b"hello").
SHA_HELLO = hashlib.sha256(b"hello").hexdigest()  # 64 chars
PREFIX_HELLO = SHA_HELLO[:16]  # truncated form used in the registry


# ---------------------------------------------------------------------------
# SHA256_RE
# ---------------------------------------------------------------------------

def test_regex_matches_full_64_char_hex():
    assert cdr.SHA256_RE.match(SHA_HELLO) is not None


def test_regex_matches_truncated_hex_with_ellipsis():
    assert cdr.SHA256_RE.match(PREFIX_HELLO + "…") is not None


def test_regex_matches_truncated_hex_with_three_dots():
    # `...` (ASCII) is also accepted by the trailing […\.]* class.
    assert cdr.SHA256_RE.match(PREFIX_HELLO + "...") is not None


def test_regex_min_boundary_15_chars_accepted():
    assert cdr.SHA256_RE.match("a" * 15) is not None


def test_regex_below_min_14_chars_rejected():
    assert cdr.SHA256_RE.match("a" * 14) is None


def test_regex_rejects_uppercase_hex():
    # The class is [0-9a-f] -- lowercase only. Uppercase is rejected.
    assert cdr.SHA256_RE.match("A" * 16) is None


def test_regex_rejects_non_hex():
    assert cdr.SHA256_RE.match("xyz" * 6) is None


# ---------------------------------------------------------------------------
# is_sha256_complete
# ---------------------------------------------------------------------------

def test_is_complete_true_for_64_lowercase_hex():
    assert cdr.is_sha256_complete(SHA_HELLO) is True


def test_is_complete_false_for_truncated():
    assert cdr.is_sha256_complete(PREFIX_HELLO) is False


def test_is_complete_false_for_64_chars_with_uppercase():
    assert cdr.is_sha256_complete("A" * 64) is False


def test_is_complete_false_for_non_hex_64_chars():
    assert cdr.is_sha256_complete("z" * 64) is False


# ---------------------------------------------------------------------------
# sha256_file
# ---------------------------------------------------------------------------

def test_sha256_file_known_content(tmp_path):
    f = tmp_path / "blob.bin"
    f.write_bytes(b"hello")
    assert cdr.sha256_file(f) == SHA_HELLO


def test_sha256_file_empty(tmp_path):
    f = tmp_path / "empty.bin"
    f.write_bytes(b"")
    assert cdr.sha256_file(f) == hashlib.sha256(b"").hexdigest()


# ---------------------------------------------------------------------------
# parse_registry
# ---------------------------------------------------------------------------

def test_parse_missing_file_returns_empty():
    assert cdr.parse_registry(tmp_path_missing := Path("/no/such/registry.md")) == []


def test_parse_well_formed_row(tmp_path):
    reg = _write_registry(tmp_path / "reg.md", [_entry("data/x.csv", 19662, PREFIX_HELLO + "…")])
    entries = cdr.parse_registry(reg)
    assert len(entries) == 1
    e = entries[0]
    assert e["chemin"] == "data/x.csv"
    assert e["taille"] == 19662
    assert e["sha256_short"] == PREFIX_HELLO + "…"
    assert e["licence"] == "MIT"
    assert e["categorie"] == "pedagogique-synthetique"


def test_parse_taille_space_thousands_separator(tmp_path):
    # Real registry uses a space as thousands separator: `19 662` -> 19662.
    row = "| `data/x.csv` | 19 662 | `" + PREFIX_HELLO + "…` | MIT | pedagogique-synthetique | u | c |"
    reg = _write_registry(tmp_path / "reg.md", [row])
    assert cdr.parse_registry(reg)[0]["taille"] == 19662


def test_parse_taille_nbsp_separator(tmp_path):
    # Non-breaking space U+00A0 as thousands separator is also normalized away.
    nbsp = " "
    row = f"| `data/x.csv` | 19{nbsp}662 | `{PREFIX_HELLO}…` | MIT | cat | u | c |"
    reg = _write_registry(tmp_path / "reg.md", [row])
    assert cdr.parse_registry(reg)[0]["taille"] == 19662


def test_parse_skips_non_pipe_lines(tmp_path):
    reg = _write_registry(tmp_path / "reg.md", [
        "# Title prose line",
        "Some narrative without pipes.",
        _entry("data/x.csv", 100, PREFIX_HELLO + "…"),
    ])
    assert len(cdr.parse_registry(reg)) == 1


def test_parse_skips_short_rows_below_five_cols(tmp_path):
    # A separator row `|---|---|` has no valid sha and <5 meaningful cols.
    reg = _write_registry(tmp_path / "reg.md", [
        "| col1 | col2 |",
        "|---|---|",
        _entry("data/x.csv", 100, PREFIX_HELLO + "…"),
    ])
    assert len(cdr.parse_registry(reg)) == 1


def test_parse_skips_non_integer_taille(tmp_path):
    row = "| `data/x.csv` | notanint | `" + PREFIX_HELLO + "…` | MIT | cat | u | c |"
    reg = _write_registry(tmp_path / "reg.md", [row])
    assert cdr.parse_registry(reg) == []


def test_parse_skips_sha_not_matching_regex(tmp_path):
    # 8-char hex is below the 15-char minimum -> filtered out.
    row = "| `data/x.csv` | 100 | `abcd1234` | MIT | cat | u | c |"
    reg = _write_registry(tmp_path / "reg.md", [row])
    assert cdr.parse_registry(reg) == []


def test_parse_strips_backticks(tmp_path):
    row = "| `data/x.csv` | 100 | `" + PREFIX_HELLO + "…` | `MIT` | cat | u | c |"
    reg = _write_registry(tmp_path / "reg.md", [row])
    e = cdr.parse_registry(reg)[0]
    assert e["chemin"] == "data/x.csv"      # no backticks
    assert e["licence"] == "MIT"             # backticks stripped here too


# ---------------------------------------------------------------------------
# check_entry
# ---------------------------------------------------------------------------

def test_check_entry_missing_path_is_critical(tmp_path):
    e = {"chemin": "nope/missing.csv", "taille": 100,
         "sha256_short": PREFIX_HELLO + "…", "licence": "MIT",
         "categorie": "pedagogique-synthetique"}
    f = cdr.check_entry(e, tmp_path)
    assert f["status"] == "MISSING"
    assert f["severity"] == "CRITICAL"
    assert "actual_sha256" not in f  # file never hashed


def test_check_entry_ok_complete_sha_match(tmp_path):
    blob = tmp_path / "x.csv"
    blob.write_bytes(b"hello")
    e = {"chemin": "x.csv", "taille": 5, "sha256_short": SHA_HELLO,
         "licence": "MIT", "categorie": "pedagogique-synthetique"}
    f = cdr.check_entry(e, tmp_path)
    assert f["status"] == "OK"
    assert f["severity"] is None


def test_check_entry_ok_truncated_prefix_match(tmp_path):
    blob = tmp_path / "x.csv"
    blob.write_bytes(b"hello")
    e = {"chemin": "x.csv", "taille": 5, "sha256_short": PREFIX_HELLO + "…",
         "licence": "MIT", "categorie": "pedagogique-synthetique"}
    f = cdr.check_entry(e, tmp_path)
    assert f["status"] == "OK_TRUNCATED"


def test_check_entry_drift_truncated_prefix_mismatch(tmp_path):
    blob = tmp_path / "x.csv"
    blob.write_bytes(b"hello")
    e = {"chemin": "x.csv", "taille": 5, "sha256_short": "deadbeefdeadbeef" + "…",
         "licence": "MIT", "categorie": "pedagogique-synthetique"}
    f = cdr.check_entry(e, tmp_path)
    assert f["status"] == "DRIFT"
    assert f["severity"] == "MAJOR"


def test_check_entry_drift_complete_mismatch(tmp_path):
    blob = tmp_path / "x.csv"
    blob.write_bytes(b"hello")
    e = {"chemin": "x.csv", "taille": 5, "sha256_short": "0" * 64,
         "licence": "MIT", "categorie": "pedagogique-synthetique"}
    f = cdr.check_entry(e, tmp_path)
    assert f["status"] == "DRIFT"
    assert f["severity"] == "MAJOR"


def test_check_entry_unknown_unrecognized_sha_format(tmp_path):
    # 20 hex chars (passes the 15-64 regex) but neither truncated nor 64-complete.
    blob = tmp_path / "x.csv"
    blob.write_bytes(b"hello")
    e = {"chemin": "x.csv", "taille": 5, "sha256_short": "a" * 20,
         "licence": "MIT", "categorie": "pedagogique-synthetique"}
    f = cdr.check_entry(e, tmp_path)
    assert f["status"] == "UNKNOWN"
    assert f["severity"] == "MINOR"


def test_check_entry_size_mismatch_sets_warning_but_keeps_ok(tmp_path):
    blob = tmp_path / "x.csv"
    blob.write_bytes(b"hello")  # actual size 5
    e = {"chemin": "x.csv", "taille": 999, "sha256_short": SHA_HELLO,
         "licence": "MIT", "categorie": "pedagogique-synthetique"}
    f = cdr.check_entry(e, tmp_path)
    assert f["status"] == "OK"           # sha still matches
    assert "size_warning" in f
    assert "999" in f["size_warning"]


def test_check_entry_sensible_card_absent_is_critical(tmp_path):
    blob = tmp_path / "x.csv"
    blob.write_bytes(b"hello")
    e = {"chemin": "x.csv", "taille": 5, "sha256_short": SHA_HELLO,
         "licence": "MIT", "categorie": "**sensible**"}
    # No docs/notebook-metadata/DATASET_CARD.md under tmp_path.
    f = cdr.check_entry(e, tmp_path)
    assert f["status"] == "CARD_REQUIRED"
    assert f["severity"] == "CRITICAL"


def test_check_entry_sensible_card_present_path_undocumented_is_major(tmp_path):
    blob = tmp_path / "x.csv"
    blob.write_bytes(b"hello")
    card_dir = tmp_path / "docs" / "notebook-metadata"
    card_dir.mkdir(parents=True)
    (card_dir / "DATASET_CARD.md").write_text("# Card\nNothing relevant here.\n",
                                              encoding="utf-8")
    e = {"chemin": "x.csv", "taille": 5, "sha256_short": SHA_HELLO,
         "licence": "MIT", "categorie": "**sensible**"}
    f = cdr.check_entry(e, tmp_path)
    assert f["status"] == "CARD_REQUIRED"
    assert f["severity"] == "MAJOR"


def test_check_entry_sensible_card_documents_path_no_override(tmp_path):
    # When the card mentions the relative path, the sensible check does NOT
    # override the OK from the matching sha.
    blob = tmp_path / "sensitive.csv"
    blob.write_bytes(b"hello")
    card_dir = tmp_path / "docs" / "notebook-metadata"
    card_dir.mkdir(parents=True)
    (card_dir / "DATASET_CARD.md").write_text(
        "### sensitive.csv\nDocumented dataset.\n", encoding="utf-8")
    e = {"chemin": "sensitive.csv", "taille": 5, "sha256_short": SHA_HELLO,
         "licence": "MIT", "categorie": "**sensible**"}
    f = cdr.check_entry(e, tmp_path)
    assert f["status"] == "OK"


def test_check_entry_sensible_card_matches_relative_after_notebooks_prefix(tmp_path):
    # The card uses the shortened path (after MyIA.AI.Notebooks/); the matcher
    # must find it via the relative-portion fallback.
    nb_root = tmp_path / "MyIA.AI.Notebooks" / "Data"
    nb_root.mkdir(parents=True)
    (nb_root / "secret.csv").write_bytes(b"hello")
    card_dir = tmp_path / "docs" / "notebook-metadata"
    card_dir.mkdir(parents=True)
    (card_dir / "DATASET_CARD.md").write_text(
        "### Data/secret.csv\nDocumented.\n", encoding="utf-8")
    e = {"chemin": "MyIA.AI.Notebooks/Data/secret.csv", "taille": 5,
         "sha256_short": SHA_HELLO, "licence": "MIT", "categorie": "**sensible**"}
    f = cdr.check_entry(e, tmp_path)
    assert f["status"] == "OK"


# ---------------------------------------------------------------------------
# main (via monkeypatch on sys.argv + tmp_path repo)
# ---------------------------------------------------------------------------

def _make_repo(tmp_path, rows, files: dict | None = None):
    """Build a synthetic repo: registry under docs/notebook-metadata/ + named data files."""
    nbmeta = tmp_path / "docs" / "notebook-metadata"
    nbmeta.mkdir(parents=True)
    reg = nbmeta / "DATASET_REGISTRY.md"
    reg.write_text("\n".join(rows) + "\n", encoding="utf-8")
    for relpath, content in (files or {}).items():
        p = tmp_path / relpath
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(content if isinstance(content, bytes) else content.encode())
    return reg


def test_main_missing_registry_returns_1(tmp_path, monkeypatch, capsys):
    monkeypatch.setattr(sys, "argv", [
        "check_dataset_registry.py",
        "--repo-root", str(tmp_path),
        "--registry", "does/not/exist.md",
    ])
    rc = cdr.main()
    assert rc == 1
    err = capsys.readouterr().err
    assert "introuvable" in err


def test_main_empty_parse_returns_1(tmp_path, monkeypatch, capsys):
    _make_repo(tmp_path, ["# only prose, no table rows"])
    monkeypatch.setattr(sys, "argv", [
        "check_dataset_registry.py",
        "--repo-root", str(tmp_path),
    ])
    rc = cdr.main()
    assert rc == 1
    assert "aucune entr" in capsys.readouterr().err


def test_main_all_ok_returns_0(tmp_path, monkeypatch, capsys):
    _make_repo(
        tmp_path,
        [_entry("d/a.csv", 5, SHA_HELLO), _entry("d/b.csv", 5, SHA_HELLO)],
        files={"d/a.csv": b"hello", "d/b.csv": b"hello"},
    )
    monkeypatch.setattr(sys, "argv", [
        "check_dataset_registry.py", "--repo-root", str(tmp_path)])
    rc = cdr.main()
    out = capsys.readouterr().out
    assert rc == 0
    assert "global_status: OK" in out
    assert "ok_count: 2" in out


def test_main_precedence_card_required_beats_missing_and_drift(tmp_path, monkeypatch, capsys):
    # One CARD_REQUIRED, one MISSING, one DRIFT -> global must be CARD_REQUIRED.
    _make_repo(
        tmp_path,
        [
            _entry("d/missing.csv", 5, SHA_HELLO, categorie="pedagogique-synthetique"),
            _entry("d/sensible.csv", 5, SHA_HELLO, categorie="**sensible**"),
            _entry("d/drift.csv", 5, "0" * 64, categorie="pedagogique-synthetique"),
        ],
        # missing.csv intentionally NOT created; drift.csv content mismatches the all-zero sha.
        files={"d/sensible.csv": b"hello", "d/drift.csv": b"hello"},
    )
    monkeypatch.setattr(sys, "argv", [
        "check_dataset_registry.py", "--repo-root", str(tmp_path)])
    rc = cdr.main()
    out = capsys.readouterr().out
    assert rc == 1
    assert "global_status: CARD_REQUIRED" in out


def test_main_missing_beats_drift_when_no_card(tmp_path, monkeypatch, capsys):
    _make_repo(
        tmp_path,
        [
            _entry("d/missing.csv", 5, SHA_HELLO),
            _entry("d/drift.csv", 5, "0" * 64),
        ],
        files={"d/drift.csv": b"hello"},
    )
    monkeypatch.setattr(sys, "argv", [
        "check_dataset_registry.py", "--repo-root", str(tmp_path)])
    rc = cdr.main()
    out = capsys.readouterr().out
    assert rc == 1
    assert "global_status: MISSING" in out


def test_main_out_writes_file(tmp_path, monkeypatch):
    _make_repo(
        tmp_path,
        [_entry("d/a.csv", 5, SHA_HELLO)],
        files={"d/a.csv": b"hello"},
    )
    out_file = tmp_path / "audit.yml"
    monkeypatch.setattr(sys, "argv", [
        "check_dataset_registry.py",
        "--repo-root", str(tmp_path),
        "--out", str(out_file),
    ])
    rc = cdr.main()
    assert rc == 0
    text = out_file.read_text(encoding="utf-8")
    assert "global_status: OK" in text
    assert "ok_count: 1" in text
