"""Tests for scripts/audit/check_dataset_registry.py (#8055 tranche 2).

Covers the dataset-registry coherence checker: pure helpers (sha256_file,
is_sha256_complete, parse_registry) and every status branch of check_entry
(OK / OK_TRUNCATED / DRIFT / MISSING / UNKNOWN / CARD_REQUIRED), including the
sensible-category override and the non-status-changing size_warning.

Uses a synthetic mini-tree under tmp_path so the tests do not depend on the
live repo state. No network (unlike check_editorial_review, this validator has
no gh_pr_state call).
"""
import hashlib
import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_dataset_registry.py"


def _load_check():
    spec = importlib.util.spec_from_file_location("check_dataset_registry", CHECK_PATH)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _write_file(path: Path, content: bytes) -> str:
    """Create a file under tmp_path, return its full sha256 hex."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(content)
    return hashlib.sha256(content).hexdigest()


def _entry(chemin, sha256_short, taille, categorie="public"):
    return {
        "chemin": chemin,
        "taille": taille,
        "sha256_short": sha256_short,
        "licence": "MIT",
        "categorie": categorie,
    }


# --- Pure helpers ---------------------------------------------------------


def test_is_sha256_complete():
    chk = _load_check()
    full = "a" * 64
    assert chk.is_sha256_complete(full) is True
    # too short
    assert chk.is_sha256_complete("a" * 63) is False
    # non-hex char
    assert chk.is_sha256_complete("g" * 64) is False
    # truncated marker is not complete
    assert chk.is_sha256_complete("a" * 16 + "…") is False
    # empty
    assert chk.is_sha256_complete("") is False


def test_sha256_file_matches_hashlib(tmp_path):
    chk = _load_check()
    content = b"dataset fixture content\n"
    p = tmp_path / "blob.bin"
    sha = _write_file(p, content)
    assert chk.sha256_file(p) == sha
    assert chk.sha256_file(p) == hashlib.sha256(content).hexdigest()


# --- parse_registry -------------------------------------------------------


def test_parse_registry_nonexistent_returns_empty(tmp_path):
    chk = _load_check()
    assert chk.parse_registry(tmp_path / "absent.md") == []


def test_parse_registry_parses_table_rows(tmp_path):
    """Real registry format: bare-integer taille (e.g. `19 662`), the space is a
    thousands separator that the parser strips. A trailing unit like `100 B`
    would NOT parse (int() fails on `100B`) -- the parser expects an integer."""
    chk = _load_check()
    reg = tmp_path / "DATASET_REGISTRY.md"
    sha16 = "abcdef0123456789"
    reg.write_text(
        "# Registre\n\n"
        "| chemin | taille | sha256 | licence | categorie |\n"
        "|--------|--------|--------|---------|-----------|\n"
        f"| `data/a.csv` | 100 | `{sha16}…` | MIT | public |\n"
        f"| `data/b.csv` | 200 | `{sha16}` | MIT | **sensible** |\n"
        # non-table line (ignored)
        "Some prose line without pipes.\n"
        # row with < 5 cols (ignored)
        "| `short` | 10 |\n"
        # row with non-integer taille (ignored)
        f"| `data/c.csv` | NA | `{sha16}` | MIT | public |\n"
        # row with too-short sha (ignored: needs >=15 hex)
        f"| `data/d.csv` | 10 | `abc` | MIT | public |\n",
        encoding="utf-8",
    )
    entries = chk.parse_registry(reg)
    paths = [e["chemin"] for e in entries]
    assert paths == ["data/a.csv", "data/b.csv"]
    assert entries[0]["sha256_short"] == sha16 + "…"
    assert entries[0]["taille"] == 100
    assert entries[1]["categorie"] == "**sensible**"


def test_parse_registry_strips_thousands_separator(tmp_path):
    """Real-world registry rows use a thousands separator in the taille column
    (e.g. `19 662`). The parser strips both a regular space and a non-breaking
    space (U+00A0) before int() -- pin this non-obvious behaviour."""
    chk = _load_check()
    reg = tmp_path / "DATASET_REGISTRY.md"
    sha16 = "abcdef0123456789"
    reg.write_text(
        f"| `data/big.csv` | 19 662 | `{sha16}…` | MIT | public |\n"
        f"| `data/nbsp.csv` | 1 296 | `{sha16}…` | MIT | public |\n",
        encoding="utf-8",
    )
    entries = chk.parse_registry(reg)
    assert [e["taille"] for e in entries] == [19662, 1296]


# --- check_entry: status branches ----------------------------------------


def test_check_entry_missing(tmp_path):
    chk = _load_check()
    e = _entry("data/ghost.csv", "a" * 64, 100)
    f = chk.check_entry(e, tmp_path)
    assert f["status"] == "MISSING"
    assert f["severity"] == "CRITICAL"
    assert "absent" in f["detail"]
    # no actual_sha for a missing file
    assert "actual_sha256" not in f


def test_check_entry_ok_full_sha(tmp_path):
    chk = _load_check()
    content = b"hello dataset\n"
    rel = "data/ok.csv"
    sha = _write_file(tmp_path / rel, content)
    e = _entry(rel, sha, len(content))
    f = chk.check_entry(e, tmp_path)
    assert f["status"] == "OK"
    assert f["severity"] is None


def test_check_entry_drift_full_sha(tmp_path):
    chk = _load_check()
    content = b"hello dataset\n"
    rel = "data/drift.csv"
    _write_file(tmp_path / rel, content)
    # a different-but-valid 64-hex sha
    e = _entry(rel, "0" * 64, len(content))
    f = chk.check_entry(e, tmp_path)
    assert f["status"] == "DRIFT"
    assert f["severity"] == "MAJOR"
    assert "SHA256" in f["detail"]


def test_check_entry_ok_truncated_prefix(tmp_path):
    chk = _load_check()
    content = b"truncated match\n"
    rel = "data/trunc.csv"
    sha = _write_file(tmp_path / rel, content)
    e = _entry(rel, sha[:16] + "…", len(content))
    f = chk.check_entry(e, tmp_path)
    assert f["status"] == "OK_TRUNCATED"
    assert f["severity"] is None


def test_check_entry_drift_truncated_prefix(tmp_path):
    chk = _load_check()
    content = b"truncated mismatch\n"
    rel = "data/trunc_drift.csv"
    _write_file(tmp_path / rel, content)
    # a prefix that does NOT match (starts with 0, real starts otherwise)
    e = _entry(rel, "0000000000000000" + "…", len(content))
    f = chk.check_entry(e, tmp_path)
    assert f["status"] == "DRIFT"
    assert f["severity"] == "MAJOR"


def test_check_entry_unknown_sha_format(tmp_path):
    chk = _load_check()
    content = b"weird\n"
    rel = "data/unknown.csv"
    _write_file(tmp_path / rel, content)
    # 10 hex chars: too short to be truncated-valid (regex needs >=15) but not
    # complete (needs 64). Format unrecognized.
    e = _entry(rel, "abc123def0", len(content))
    f = chk.check_entry(e, tmp_path)
    assert f["status"] == "UNKNOWN"
    assert f["severity"] == "MINOR"


def test_check_entry_size_warning_does_not_change_status(tmp_path):
    chk = _load_check()
    content = b"x" * 50
    rel = "data/size_mismatch.csv"
    sha = _write_file(tmp_path / rel, content)
    # sha matches (OK) but declared size is wrong
    e = _entry(rel, sha, 999)
    f = chk.check_entry(e, tmp_path)
    assert f["status"] == "OK"
    assert "size_warning" in f
    assert "999" in f["size_warning"]


# --- check_entry: sensible-category CARD_REQUIRED override ----------------


def test_check_entry_card_required_no_card_file(tmp_path):
    """Sensible category + no DATASET_CARD.md -> CARD_REQUIRED CRITICAL,
    overriding an otherwise-OK sha."""
    chk = _load_check()
    content = b"sensible data\n"
    rel = "data/secret.csv"
    sha = _write_file(tmp_path / rel, content)
    e = _entry(rel, sha, len(content), categorie="**sensible**")
    f = chk.check_entry(e, tmp_path)
    assert f["status"] == "CARD_REQUIRED"
    assert f["severity"] == "CRITICAL"


def test_check_entry_card_required_path_not_in_card(tmp_path):
    """Sensible category + card exists but path absent from it -> CARD_REQUIRED
    MAJOR."""
    chk = _load_check()
    content = b"sensible data\n"
    rel = "data/undocumented.csv"
    sha = _write_file(tmp_path / rel, content)
    # card exists but does NOT mention this path
    card = tmp_path / "docs" / "notebook-metadata" / "DATASET_CARD.md"
    card.parent.mkdir(parents=True)
    card.write_text("# Card\ndocuments some OTHER dataset\n", encoding="utf-8")
    e = _entry(rel, sha, len(content), categorie="**sensible**")
    f = chk.check_entry(e, tmp_path)
    assert f["status"] == "CARD_REQUIRED"
    assert f["severity"] == "MAJOR"


def test_check_entry_sensible_with_documented_card_is_ok(tmp_path):
    """Sensible category + card exists and documents the path -> status stays
    OK (sha valid)."""
    chk = _load_check()
    content = b"sensible data\n"
    rel = "MyIA.AI.Notebooks/data/documented.csv"
    sha = _write_file(tmp_path / rel, content)
    card = tmp_path / "docs" / "notebook-metadata" / "DATASET_CARD.md"
    card.parent.mkdir(parents=True)
    # card mentions the relative portion after MyIA.AI.Notebooks/
    card.write_text(f"# Card\ndocuments data/documented.csv\n", encoding="utf-8")
    e = _entry(rel, sha, len(content), categorie="**sensible**")
    f = chk.check_entry(e, tmp_path)
    assert f["status"] == "OK"
    assert f["severity"] is None


def test_check_entry_sensible_override_takes_precedence_over_drift(tmp_path):
    """A sensible-category entry whose sha DRIFTS but whose card is missing
    reports CARD_REQUIRED CRITICAL (the not-exists branch), not DRIFT MAJOR."""
    chk = _load_check()
    content = b"sensible\n"
    rel = "data/both.csv"
    _write_file(tmp_path / rel, content)
    e = _entry(rel, "0" * 64, len(content), categorie="**sensible**")
    f = chk.check_entry(e, tmp_path)
    assert f["status"] == "CARD_REQUIRED"
    assert f["severity"] == "CRITICAL"
