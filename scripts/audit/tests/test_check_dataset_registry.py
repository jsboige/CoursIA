#!/usr/bin/env python3
"""Tests pour scripts/audit/check_dataset_registry.py — vérificateur de cohérence
du registre des datasets.

Issue #8055 tranche 2 — DATASET_REGISTRY.md + check_dataset_registry.py.

Couvre les 4 fonctions pures hermétiques (sha256_file, parse_registry,
is_sha256_complete, check_entry) + main() (exit codes + sortie YAML manuelle).
Aucun réseau, aucun subprocess : stdlib uniquement (argparse/hashlib/re/sys/
pathlib). Fixtures synthétiques sous tmp_path (registre markdown + fichiers de
données) — les tests ne dépendent pas de l'état du repo live.

Logique métier testée dans check_entry (le cœur de l'audit) :
  - MISSING      : chemin absent du repo (CRITICAL)
  - OK           : SHA256 complet correspond (taille OK)
  - DRIFT        : SHA256 complet diffère (MAJOR)
  - OK_TRUNCATED : préfixe SHA256 tronqué (`…`) correspond
  - UNKNOWN      : format SHA256 non reconnu (MINOR)
  - CARD_REQUIRED: catégorie **sensible** sans DATASET_CARD (CRITICAL/MAJOR)
  - size_warning : taille mismatch (SHA OK mais taille déclarée fausse)
"""

import importlib.util
import hashlib
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_dataset_registry.py"


def _load_mod():
    """Charge check_dataset_registry.py par chemin (pas de sys.path pollution)."""
    spec = importlib.util.spec_from_file_location("check_dataset_registry", CHECK_PATH)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# --------------------------------------------------------------------------
# Helpers — fixtures synthétiques (registre markdown + fichiers de données)
# --------------------------------------------------------------------------

def _make_registry_line(chemin, taille, sha, licence="MIT", categorie="public",
                        usage="", card=""):
    """Génère une ligne de table markdown conforme au format réel du registre.

    Format réel (DATASET_REGISTRY.md) : 7 colonnes séparées par des pipes —
    chemin backtick-quoté, taille en octets (int, séparateur milliers = espace),
    sha256 backtick-quoté (tronqué `…` ou complet 64 hex), licence, catégorie,
    usage_principal, dataset_card.
    """
    cols = [f"`{chemin}`", str(taille), f"`{sha}`", licence, categorie, usage, card]
    return "| " + " | ".join(cols) + " |"


def _write_registry(path: Path, body_lines: list[str]) -> Path:
    """Écrit un registre markdown minimal (header + separator + body lines)."""
    path.parent.mkdir(parents=True, exist_ok=True)
    header = [
        "# DATASET_REGISTRY",
        "",
        "| Chemin | Taille | SHA256 | Licence | Catégorie | Usage | Card |",
        "|--------|--------|--------|---------|-----------|-------|------|",
    ]
    path.write_text("\n".join(header + body_lines) + "\n", encoding="utf-8")
    return path


def _write_data(path: Path, content: bytes) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(content)
    return path


# --------------------------------------------------------------------------
# sha256_file — hash déterministe par chunks (mémoire constante)
# --------------------------------------------------------------------------

def test_sha256_file_deterministic(tmp_path):
    mod = _load_mod()
    f = _write_data(tmp_path / "a.bin", b"hello world")
    assert mod.sha256_file(f) == mod.sha256_file(f)


def test_sha256_file_matches_hashlib(tmp_path):
    mod = _load_mod()
    content = b"\x00\x01\x02\x03 binary data \xff\xfe"
    f = _write_data(tmp_path / "a.bin", content)
    assert mod.sha256_file(f) == hashlib.sha256(content).hexdigest()


def test_sha256_file_chunked_large_file(tmp_path):
    """Le hash est lu par chunks de 65536 ; un fichier > 1 chunk doit rester correct."""
    mod = _load_mod()
    content = b"abcdefgh" * 20000  # 160 000 octets > 65 536
    f = _write_data(tmp_path / "big.bin", content)
    assert mod.sha256_file(f) == hashlib.sha256(content).hexdigest()


def test_sha256_file_empty_file_known_hash(tmp_path):
    mod = _load_mod()
    f = _write_data(tmp_path / "empty.bin", b"")
    # SHA256 du contenu vide — valeur canonique bien connue.
    assert mod.sha256_file(f) == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"


# --------------------------------------------------------------------------
# parse_registry — parsing de la table markdown en entrées structurées
# --------------------------------------------------------------------------

def test_parse_registry_valid_line(tmp_path):
    mod = _load_mod()
    reg = _write_registry(tmp_path / "REG.md", [
        _make_registry_line("data/a.csv", 100, "abcdef0123456789", "MIT", "public"),
    ])
    entries = mod.parse_registry(reg)
    assert len(entries) == 1
    e = entries[0]
    assert e["chemin"] == "data/a.csv"
    assert e["taille"] == 100
    assert e["sha256_short"] == "abcdef0123456789"
    assert e["licence"] == "MIT"
    assert e["categorie"] == "public"


def test_parse_registry_strips_backticks(tmp_path):
    """Les colonnes chemin et sha256 sont backtick-quotées dans le markdown."""
    mod = _load_mod()
    reg = _write_registry(tmp_path / "REG.md", [
        _make_registry_line("path/x.csv", 50, "0123456789abcdef"),
    ])
    e = mod.parse_registry(reg)[0]
    assert "`" not in e["chemin"]
    assert "`" not in e["sha256_short"]


def test_parse_registry_ignores_non_table_lines(tmp_path):
    mod = _load_mod()
    path = tmp_path / "REG.md"
    path.write_text(
        "# Titre\n"
        "Un paragraphe de prose sans pipe.\n"
        "Encore du texte.\n",
        encoding="utf-8",
    )
    assert mod.parse_registry(path) == []


def test_parse_registry_ignores_short_rows(tmp_path):
    """Les lignes < 5 colonnes (ex separator `|---|---|`, prose) sont ignorées,
    seules les lignes >= 5 colonnes valides sont retenues."""
    mod = _load_mod()
    path = tmp_path / "REG.md"
    path.write_text(
        "| Chemin | Taille | SHA256 | Licence | Catégorie |\n"
        "|--------|--------|--------|---------|-----------|\n"
        "| `data/ok.csv` | 10 | `abcdef0123456789` | MIT | public | usage | card |\n"
        "| a | b | c | d |  # 4 cols < 5 -> ignore\n",
        encoding="utf-8",
    )
    entries = mod.parse_registry(path)
    assert len(entries) == 1
    assert entries[0]["chemin"] == "data/ok.csv"


def test_parse_registry_ignores_non_integer_size(tmp_path):
    mod = _load_mod()
    reg = _write_registry(tmp_path / "REG.md", [
        _make_registry_line("data/a.csv", "NAN", "abcdef0123456789"),
    ])
    # taille non-entière -> ValueError -> ligne ignorée
    assert mod.parse_registry(reg) == []


def test_parse_registry_ignores_invalid_sha256(tmp_path):
    """SHA256 trop court (< 15 hex) ou non-hex ne matche pas SHA256_RE -> ignoré."""
    mod = _load_mod()
    reg = _write_registry(tmp_path / "REG.md", [
        _make_registry_line("data/short.csv", 10, "abc"),          # trop court
        _make_registry_line("data/nonhex.csv", 10, "xyzxyzxyzxyzxyz"),  # non-hex
        _make_registry_line("data/ok.csv", 10, "abcdef0123456789"),     # valide
    ])
    entries = mod.parse_registry(reg)
    assert len(entries) == 1
    assert entries[0]["chemin"] == "data/ok.csv"


def test_parse_registry_returns_empty_when_file_missing(tmp_path):
    mod = _load_mod()
    assert mod.parse_registry(tmp_path / "absent.md") == []


def test_parse_registry_multiple_entries_ordered(tmp_path):
    mod = _load_mod()
    reg = _write_registry(tmp_path / "REG.md", [
        _make_registry_line("data/a.csv", 10, "aaaaaaaaaaaaaaaa"),
        _make_registry_line("data/b.csv", 20, "bbbbbbbbbbbbbbbb"),
        _make_registry_line("data/c.csv", 30, "cccccccccccccccc"),
    ])
    entries = mod.parse_registry(reg)
    assert [e["chemin"] for e in entries] == ["data/a.csv", "data/b.csv", "data/c.csv"]
    assert [e["taille"] for e in entries] == [10, 20, 30]


def test_parse_registry_preserves_sensitive_category(tmp_path):
    """La catégorie `**sensible**` (PII) doit être préservée intacte."""
    mod = _load_mod()
    reg = _write_registry(tmp_path / "REG.md", [
        _make_registry_line("data/secret.csv", 10, "abcdef0123456789",
                            categorie="**sensible**"),
    ])
    e = mod.parse_registry(reg)[0]
    assert e["categorie"] == "**sensible**"


def test_parse_registry_accepts_truncated_sha_with_ellipsis(tmp_path):
    """SHA tronqué avec `…` est valide pour le parsing (15-64 hex + `…`)."""
    mod = _load_mod()
    reg = _write_registry(tmp_path / "REG.md", [
        _make_registry_line("data/a.csv", 10, "abcdef0123456789…"),
    ])
    entries = mod.parse_registry(reg)
    assert len(entries) == 1
    assert entries[0]["sha256_short"] == "abcdef0123456789…"


def test_parse_registry_handles_thousands_separator_space(tmp_path):
    """Le vrai registre utilise un espace comme séparateur de milliers
    (`19 662`). Le module fait replace(' ', '') -> int correct."""
    mod = _load_mod()
    path = tmp_path / "REG.md"
    # ligne à la main avec séparateur de milliers (pas via le helper qui str()ifie)
    path.write_text(
        "| `data/big.csv` | 19 662 | `abcdef0123456789…` | MIT | public | u | — |\n",
        encoding="utf-8",
    )
    e = mod.parse_registry(path)[0]
    assert e["taille"] == 19662


# --------------------------------------------------------------------------
# is_sha256_complete — validation format SHA256 complet (64 hex)
# --------------------------------------------------------------------------

def test_is_sha256_complete_true_for_64_hex():
    mod = _load_mod()
    assert mod.is_sha256_complete("a" * 64) is True
    assert mod.is_sha256_complete("0123456789abcdef" * 4) is True


def test_is_sha256_complete_false_for_short():
    mod = _load_mod()
    assert mod.is_sha256_complete("a" * 16) is False
    assert mod.is_sha256_complete("a" * 63) is False


def test_is_sha256_complete_false_for_non_hex():
    mod = _load_mod()
    assert mod.is_sha256_complete("g" * 64) is False  # g non-hex
    assert mod.is_sha256_complete("A" * 64) is False  # majuscules rejetées


def test_is_sha256_complete_false_for_truncated():
    mod = _load_mod()
    assert mod.is_sha256_complete("abcdef0123456789…") is False


# --------------------------------------------------------------------------
# check_entry — cœur métier (MISSING / OK / DRIFT / OK_TRUNCATED / UNKNOWN /
# CARD_REQUIRED / size_warning)
# --------------------------------------------------------------------------

def _entry(chemin, sha, taille, categorie="public"):
    return {"chemin": chemin, "taille": taille, "sha256_short": sha,
            "licence": "MIT", "categorie": categorie}


def test_check_entry_missing_path_critical(tmp_path):
    mod = _load_mod()
    e = _entry("data/absent.csv", "a" * 64, 100)
    f = mod.check_entry(e, tmp_path)
    assert f["status"] == "MISSING"
    assert f["severity"] == "CRITICAL"
    assert "absent" in f["detail"].lower()
    assert "actual_sha256" not in f  # pas de hash calculé (fichier absent)


def test_check_entry_ok_full_sha_match(tmp_path):
    mod = _load_mod()
    content = b"donnees du dataset"
    _write_data(tmp_path / "data" / "ok.csv", content)
    sha = hashlib.sha256(content).hexdigest()
    e = _entry("data/ok.csv", sha, len(content))
    f = mod.check_entry(e, tmp_path)
    assert f["status"] == "OK"
    assert f["severity"] is None
    assert f["actual_sha256"] == sha
    assert f["size_bytes_actual"] == len(content)


def test_check_entry_drift_full_sha_mismatch(tmp_path):
    mod = _load_mod()
    content = b"donnees modifiees"
    _write_data(tmp_path / "data" / "x.csv", content)
    # sha déclaré délibérément faux (différent du contenu réel)
    e = _entry("data/x.csv", "b" * 64, len(content))
    f = mod.check_entry(e, tmp_path)
    assert f["status"] == "DRIFT"
    assert f["severity"] == "MAJOR"
    assert "DRIFT" not in f.get("detail", "") or "SHA256" in f["detail"]


def test_check_entry_ok_truncated_prefix_match(tmp_path):
    mod = _load_mod()
    content = b"dataset tronque sha"
    _write_data(tmp_path / "data" / "t.csv", content)
    full = hashlib.sha256(content).hexdigest()
    e = _entry("data/t.csv", full[:16] + "…", len(content))
    f = mod.check_entry(e, tmp_path)
    assert f["status"] == "OK_TRUNCATED"


def test_check_entry_drift_truncated_prefix_mismatch(tmp_path):
    mod = _load_mod()
    content = b"contenu reel"
    _write_data(tmp_path / "data" / "t2.csv", content)
    # préfixe tronqué qui ne matche pas le contenu réel
    e = _entry("data/t2.csv", "ffffffffffffffff" + "…", len(content))
    f = mod.check_entry(e, tmp_path)
    assert f["status"] == "DRIFT"
    assert f["severity"] == "MAJOR"


def test_check_entry_unknown_sha_format_minor(tmp_path):
    """Un sha de longueur intermédiaire (40 hex, valide pour parse mais ni
    tronqué ni complet) -> UNKNOWN/MINOR dans check_entry."""
    mod = _load_mod()
    content = b"x"
    _write_data(tmp_path / "data" / "u.csv", content)
    e = _entry("data/u.csv", "a" * 40, len(content))  # 40 hex, pas de `…`, pas 64
    f = mod.check_entry(e, tmp_path)
    assert f["status"] == "UNKNOWN"
    assert f["severity"] == "MINOR"


def test_check_entry_size_warning_when_size_mismatch_but_sha_ok(tmp_path):
    """SHA OK mais taille déclarée fausse -> size_warning présent, status reste OK."""
    mod = _load_mod()
    content = b"donnees"
    _write_data(tmp_path / "data" / "sz.csv", content)
    sha = hashlib.sha256(content).hexdigest()
    e = _entry("data/sz.csv", sha, 9999)  # taille déclarée volontairement fausse
    f = mod.check_entry(e, tmp_path)
    assert f["status"] == "OK"
    assert "size_warning" in f
    assert "9999" in f["size_warning"]
    assert str(len(content)) in f["size_warning"]


def test_check_entry_card_required_when_sensitive_and_no_card(tmp_path):
    """Catégorie **sensible** + DATASET_CARD.md absent -> CARD_REQUIRED/CRITICAL."""
    mod = _load_mod()
    content = b"donnees sensibles (PII)"
    _write_data(tmp_path / "data" / "secret.csv", content)
    sha = hashlib.sha256(content).hexdigest()
    e = _entry("data/secret.csv", sha, len(content), categorie="**sensible**")
    # PAS de DATASET_CARD.md créé sous tmp_path/docs/notebook-metadata/
    f = mod.check_entry(e, tmp_path)
    assert f["status"] == "CARD_REQUIRED"
    assert f["severity"] == "CRITICAL"


def test_check_entry_card_required_when_sensitive_card_present_but_path_undocumented(tmp_path):
    """Catégorie sensible + card présent MAIS chemin non documenté -> CARD_REQUIRED/MAJOR."""
    mod = _load_mod()
    content = b"pii non documente"
    chemin = "MyIA.AI.Notebooks/data/undoc.csv"
    _write_data(tmp_path / chemin, content)
    sha = hashlib.sha256(content).hexdigest()
    # DATASET_CARD.md présent mais ne mentionne pas le chemin
    card = tmp_path / "docs" / "notebook-metadata" / "DATASET_CARD.md"
    card.parent.mkdir(parents=True, exist_ok=True)
    card.write_text("# DATASET_CARD\n\nDocumentation d'autres datasets seulement.\n",
                    encoding="utf-8")
    e = _entry(chemin, sha, len(content), categorie="**sensible**")
    f = mod.check_entry(e, tmp_path)
    assert f["status"] == "CARD_REQUIRED"
    assert f["severity"] == "MAJOR"
    assert "DATASET_CARD" in f["detail"]


def test_check_entry_card_ok_when_sensitive_and_documented_full_path(tmp_path):
    """Catégorie sensible + card documente le chemin complet -> pas CARD_REQUIRED."""
    mod = _load_mod()
    content = b"pii bien documente"
    chemin = "data/documented.csv"
    _write_data(tmp_path / chemin, content)
    sha = hashlib.sha256(content).hexdigest()
    card = tmp_path / "docs" / "notebook-metadata" / "DATASET_CARD.md"
    card.parent.mkdir(parents=True, exist_ok=True)
    # le card mentionne le chemin complet
    card.write_text(f"# DATASET_CARD\n\n### {chemin}\nDataset sensible documenté.\n",
                    encoding="utf-8")
    e = _entry(chemin, sha, len(content), categorie="**sensible**")
    f = mod.check_entry(e, tmp_path)
    assert f["status"] == "OK"  # sha OK + card documente -> OK, pas CARD_REQUIRED


def test_check_entry_card_ok_when_sensitive_documented_by_relative_path(tmp_path):
    """Le card utilise souvent le chemin raccourci (après MyIA.AI.Notebooks/)."""
    mod = _load_mod()
    content = b"pii relatif"
    chemin_complet = "MyIA.AI.Notebooks/Probas/data/rel.csv"
    _write_data(tmp_path / chemin_complet, content)
    sha = hashlib.sha256(content).hexdigest()
    card = tmp_path / "docs" / "notebook-metadata" / "DATASET_CARD.md"
    card.parent.mkdir(parents=True, exist_ok=True)
    rel = "Probas/data/rel.csv"
    card.write_text(f"# DATASET_CARD\n\n### {rel}\nDocumenté par chemin relatif.\n",
                    encoding="utf-8")
    e = _entry(chemin_complet, sha, len(content), categorie="**sensible**")
    f = mod.check_entry(e, tmp_path)
    assert f["status"] == "OK"


def test_check_entry_card_required_overrides_ok_status(tmp_path):
    """Si une entrée sensible a un sha OK mais pas de card, CARD_REQUIRED gagne."""
    mod = _load_mod()
    content = b"secret sans card"
    _write_data(tmp_path / "data" / "s2.csv", content)
    sha = hashlib.sha256(content).hexdigest()
    e = _entry("data/s2.csv", sha, len(content), categorie="**sensible**")
    f = mod.check_entry(e, tmp_path)
    # sha OK aurait donné OK, mais CARD_REQUIRED override (priorité sécurité)
    assert f["status"] == "CARD_REQUIRED"


# --------------------------------------------------------------------------
# main() — exit codes + sortie YAML manuelle
# --------------------------------------------------------------------------

def test_main_returns_1_when_registry_missing(tmp_path, capsys, monkeypatch):
    mod = _load_mod()
    monkeypatch.setattr(sys, "argv", [
        "check_dataset_registry.py",
        "--repo-root", str(tmp_path),
        "--registry", "absent.md",
    ])
    rc = mod.main()
    assert rc == 1
    err = capsys.readouterr().err
    assert "introuvable" in err.lower() or "absent" in err.lower()


def test_main_returns_1_when_registry_empty(tmp_path, capsys, monkeypatch):
    """Registre lisible mais 0 entrées parsées -> exit 1."""
    mod = _load_mod()
    reg = tmp_path / "REG.md"
    reg.write_text("# Registre vide\n\nAucune table ici.\n", encoding="utf-8")
    monkeypatch.setattr(sys, "argv", [
        "check_dataset_registry.py",
        "--repo-root", str(tmp_path),
        "--registry", "REG.md",
    ])
    rc = mod.main()
    assert rc == 1
    err = capsys.readouterr().err
    assert "aucune entrée" in err.lower()


def test_main_returns_0_when_all_ok(tmp_path, monkeypatch):
    mod = _load_mod()
    content = b"dataset conforme"
    _write_data(tmp_path / "data" / "ok.csv", content)
    sha = hashlib.sha256(content).hexdigest()
    _write_registry(tmp_path / "REG.md", [
        _make_registry_line("data/ok.csv", len(content), sha),
    ])
    monkeypatch.setattr(sys, "argv", [
        "check_dataset_registry.py",
        "--repo-root", str(tmp_path),
        "--registry", "REG.md",
    ])
    rc = mod.main()
    assert rc == 0


def test_main_returns_1_on_drift(tmp_path, monkeypatch):
    mod = _load_mod()
    content = b"contenu reel modifie"
    _write_data(tmp_path / "data" / "d.csv", content)
    # sha déclaré faux
    _write_registry(tmp_path / "REG.md", [
        _make_registry_line("data/d.csv", len(content), "b" * 64),
    ])
    monkeypatch.setattr(sys, "argv", [
        "check_dataset_registry.py",
        "--repo-root", str(tmp_path),
        "--registry", "REG.md",
    ])
    rc = mod.main()
    assert rc == 1


def test_main_yaml_output_contains_counts(tmp_path, capsys, monkeypatch):
    mod = _load_mod()
    content1 = b"aaa"
    content2 = b"bbb"
    _write_data(tmp_path / "data" / "ok1.csv", content1)
    _write_data(tmp_path / "data" / "ok2.csv", content2)
    _write_data(tmp_path / "data" / "miss.csv", b"will be deleted")
    sha1 = hashlib.sha256(content1).hexdigest()
    sha2 = hashlib.sha256(content2).hexdigest()
    _write_registry(tmp_path / "REG.md", [
        _make_registry_line("data/ok1.csv", len(content1), sha1),
        _make_registry_line("data/ok2.csv", len(content2), sha2),
        _make_registry_line("data/miss.csv", 5, "c" * 64),  # MISSING
    ])
    (tmp_path / "data" / "miss.csv").unlink()  # supprime -> MISSING
    monkeypatch.setattr(sys, "argv", [
        "check_dataset_registry.py",
        "--repo-root", str(tmp_path),
        "--registry", "REG.md",
    ])
    rc = mod.main()
    out = capsys.readouterr().out
    assert rc == 1  # MISSING -> global != OK
    assert "global_status: MISSING" in out
    assert "total_entries: 3" in out
    assert "ok_count: 2" in out
    assert "missing_count: 1" in out
    assert "drift_count: 0" in out


def test_main_writes_to_out_file(tmp_path, monkeypatch):
    mod = _load_mod()
    content = b"x"
    _write_data(tmp_path / "data" / "ok.csv", content)
    sha = hashlib.sha256(content).hexdigest()
    _write_registry(tmp_path / "REG.md", [
        _make_registry_line("data/ok.csv", len(content), sha),
    ])
    out_file = tmp_path / "audit.yml"
    monkeypatch.setattr(sys, "argv", [
        "check_dataset_registry.py",
        "--repo-root", str(tmp_path),
        "--registry", "REG.md",
        "--out", str(out_file),
    ])
    rc = mod.main()
    assert rc == 0
    assert out_file.exists()
    txt = out_file.read_text(encoding="utf-8")
    assert "global_status: OK" in txt
    assert "ok_count: 1" in txt
