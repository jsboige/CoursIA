#!/usr/bin/env python3
"""Unit tests for the pure helpers of `scripts/audit/check_dataset_registry.py`.

Covers the network-free logic so the validator used by the cycle-75 fix
(PR #13999, DATASET_REGISTRY drift) can be evolved safely:

  - `sha256_file` : SHA256 hex, lecture par chunks (mémoire constante).
  - `parse_registry` : parse les lignes du tableau markdown, ignore les
    lignes non-tableau, gere les espaces typographiques francais.
  - `is_sha256_complete` : 64 chars hex, pas de troncature.
  - `check_entry` : audit une entree (chemin/taille/SHA/categorie).
    Couvre DRIFT, MISSING, OK_TRUNCATED, OK, UNKNOWN, CARD_REQUIRED.

The end-to-end `main()` is exercised by the harness (`python scripts/audit/
check_dataset_registry.py` on a real repo) — pas en pytest (besoin du repo
complet). Ces tests sont **unitaires** : ils utilisent un repertoire tmp
isolé pour les chemins.

Contexte : cycle 75 (PR #13999) a fixe un drift DATASET_REGISTRY sur 2 CSV
Argument_Analysis. Le validateur a fait son travail, mais n'avait aucun
test pytest ; un patch ulterieur (refactor parse_registry, ajustement
categorie sensible, etc.) pourrait casser silencieusement. Ce fichier
ferme ce trou.
"""
from __future__ import annotations

import sys
import textwrap
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "audit"))

import check_dataset_registry as cdr  # noqa: E402


# --- sha256_file ---------------------------------------------------------


def test_sha256_file_known_content(tmp_path):
    """SHA256 d'un fichier avec contenu connu doit etre déterministe."""
    f = tmp_path / "blob.csv"
    f.write_bytes(b"hello world")
    # SHA256("hello world") = 0xb94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9
    assert cdr.sha256_file(f) == "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9"


def test_sha256_file_empty(tmp_path):
    """SHA256 d'un fichier vide = SHA256 de la chaine vide."""
    f = tmp_path / "empty"
    f.write_bytes(b"")
    assert cdr.sha256_file(f) == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"


def test_sha256_file_large_uses_chunks(tmp_path):
    """SHA256 sur 200 Ko (plus que le chunk de 64 Ko) : resultat stable."""
    f = tmp_path / "large.bin"
    f.write_bytes(b"x" * (200 * 1024))
    sha = cdr.sha256_file(f)
    assert len(sha) == 64
    # Deterministe : 2 appels consecutifs = meme SHA
    assert sha == cdr.sha256_file(f)


# --- is_sha256_complete --------------------------------------------------


def test_is_sha256_complete_valid():
    assert cdr.is_sha256_complete("a" * 64) is True
    assert cdr.is_sha256_complete("0123456789abcdef" * 4) is True


def test_is_sha256_complete_truncated():
    """Un SHA tronqué (16 hex + ...) ne passe pas."""
    assert cdr.is_sha256_complete("a" * 16 + "...") is False
    assert cdr.is_sha256_complete("a" * 16 + "…") is False


def test_is_sha256_complete_wrong_chars():
    """Caracteres non-hex rejetés même si 64 chars."""
    assert cdr.is_sha256_complete("z" * 64) is False
    assert cdr.is_sha256_complete("0" * 63 + " ") is False


# --- parse_registry ------------------------------------------------------


REGISTRY_MINIMAL = textwrap.dedent("""\
    # Header markdown

    Une phrase descriptive sans tableau.

    | Chemin | Taille (B) | SHA256 (16 hex) | Licence | Catégorie | Usage | Card |
    |--------|----------:|-----------------|---------|-----------|-------|------|
    | `data/foo.csv` | 1234 | `3ff86bb20f78bf8…` | CC-BY-4.0 | marche-public | usage foo | — |
    | `data/bar.csv` | 5 678 | `fdba6a1630a1564…` | ODbL-1.0 | vocabulaire-ontologie | taxonomie | — |
    | `data/baz.csv` | 9012 | `3ff86bb20f78bf8…` | ODbL-1.0 | **sensible** | cas foo | DATASET_CARD.md |

    Trailing paragraph.
""")


def test_parse_registry_returns_3_entries(tmp_path):
    """3 lignes du tableau = 3 entrées ; header et paragraphe ignores."""
    reg = tmp_path / "REGISTRY.md"
    reg.write_text(REGISTRY_MINIMAL, encoding="utf-8")
    entries = cdr.parse_registry(reg)
    assert len(entries) == 3
    assert entries[0]["chemin"] == "data/foo.csv"
    assert entries[0]["taille"] == 1234
    assert entries[0]["sha256_short"] == "3ff86bb20f78bf8…"
    assert entries[0]["licence"] == "CC-BY-4.0"
    assert entries[1]["taille"] == 5678  # espaces typographiques OK
    assert entries[2]["categorie"] == "**sensible**"


def test_parse_registry_missing_file(tmp_path):
    """parse_registry d'un fichier inexistant = [] (pas de raise).)."""
    assert cdr.parse_registry(tmp_path / "nope.md") == []


def test_parse_registry_skips_malformed_rows(tmp_path):
    """Lignes sans 5 colonnes ou taille non-int sont ignorées."""
    reg = tmp_path / "REGISTRY.md"
    reg.write_text(
        "| `data/x.csv` | 100 | `3ff86bb20f78bf8…` | CC-BY-4.0 | marche-public |\n"
        "| `data/y.csv` | not-a-number | `3ff86bb20f78bf8…` | CC-BY-4.0 | marche-public |\n"
        "| `data/z.csv` | 200 | not-a-sha | CC-BY-4.0 | marche-public |\n",
        encoding="utf-8",
    )
    entries = cdr.parse_registry(reg)
    assert len(entries) == 1
    assert entries[0]["chemin"] == "data/x.csv"


# --- check_entry ---------------------------------------------------------


def test_check_entry_ok_truncated(tmp_path):
    """SHA tronqué qui matche le prefixe = OK_TRUNCATED (pas DRIFT)."""
    csv = tmp_path / "foo.csv"
    csv.write_bytes(b"x" * 100)
    full_sha = cdr.sha256_file(csv)
    entry = {
        "chemin": "foo.csv",
        "taille": 100,
        "sha256_short": full_sha[:16] + "…",
        "licence": "CC-BY-4.0",
        "categorie": "marche-public",
    }
    finding = cdr.check_entry(entry, tmp_path)
    assert finding["status"] == "OK_TRUNCATED"
    assert finding["actual_sha256"] == full_sha
    assert finding["size_bytes_actual"] == 100


def test_check_entry_drift_size_and_sha(tmp_path):
    """Taille et SHA tous deux drift = DRIFT (severity MAJOR)."""
    csv = tmp_path / "foo.csv"
    csv.write_bytes(b"x" * 200)  # taille reelle 200, declaree 100
    entry = {
        "chemin": "foo.csv",
        "taille": 100,
        "sha256_short": "0000000000000000…",  # SHA fixe != reel
        "licence": "CC-BY-4.0",
        "categorie": "marche-public",
    }
    finding = cdr.check_entry(entry, tmp_path)
    assert finding["status"] == "DRIFT"
    assert finding["severity"] == "MAJOR"
    assert finding["size_warning"]  # taille mismatch warné
    assert finding["size_bytes_actual"] == 200


def test_check_entry_missing(tmp_path):
    """Chemin absent du repo = MISSING (severity CRITICAL)."""
    entry = {
        "chemin": "does/not/exist.csv",
        "taille": 0,
        "sha256_short": "0000000000000000…",
        "licence": "CC-BY-4.0",
        "categorie": "marche-public",
    }
    finding = cdr.check_entry(entry, tmp_path)
    assert finding["status"] == "MISSING"
    assert finding["severity"] == "CRITICAL"


def test_check_entry_ok_full_sha(tmp_path):
    """SHA complet (64 chars) qui matche = OK (statut distinct de OK_TRUNCATED)."""
    csv = tmp_path / "foo.csv"
    csv.write_bytes(b"y" * 50)
    full_sha = cdr.sha256_file(csv)
    entry = {
        "chemin": "foo.csv",
        "taille": 50,
        "sha256_short": full_sha,  # 64 chars complets
        "licence": "CC-BY-4.0",
        "categorie": "marche-public",
    }
    finding = cdr.check_entry(entry, tmp_path)
    assert finding["status"] == "OK"
    assert finding["actual_sha256"] == full_sha


def test_check_entry_unknown_sha_format(tmp_path):
    """SHA qui n'est ni tronqué ni complet = UNKNOWN (severity MINOR)."""
    csv = tmp_path / "foo.csv"
    csv.write_bytes(b"z" * 10)
    entry = {
        "chemin": "foo.csv",
        "taille": 10,
        "sha256_short": "format-bizarre-mais-15-chars",  # 15 chars, pas 16 ni 64
        "licence": "CC-BY-4.0",
        "categorie": "marche-public",
    }
    finding = cdr.check_entry(entry, tmp_path)
    assert finding["status"] == "UNKNOWN"
    assert finding["severity"] == "MINOR"


def test_check_entry_sensible_categorie_requires_card(tmp_path):
    """Categorie '**sensible**' + DATASET_CARD.md absent = CARD_REQUIRED CRITICAL."""
    csv = tmp_path / "patients.csv"
    csv.write_text("name,age\nAlice,42\n")
    entry = {
        "chemin": "patients.csv",
        "taille": csv.stat().st_size,
        "sha256_short": cdr.sha256_file(csv)[:16] + "…",
        "licence": "SYNTHETIQUE-COURS",
        "categorie": "**sensible**",
    }
    # Pas de DATASET_CARD.md dans tmp_path
    finding = cdr.check_entry(entry, tmp_path)
    assert finding["status"] == "CARD_REQUIRED"
    assert finding["severity"] == "CRITICAL"


# --- integration : parse + check_entry -----------------------------------


def test_integration_drift_detection(tmp_path):
    """Registre avec 1 entree dont la taille est driftée -> check_entry la marque."""
    csv = tmp_path / "data.csv"
    csv.write_bytes(b"hello" * 100)  # taille reelle 500
    full_sha = cdr.sha256_file(csv)
    reg = tmp_path / "REG.md"
    reg.write_text(
        f"| Chemin | Taille (B) | SHA256 (16 hex) | Licence | Catégorie |\n"
        f"|--------|----------:|-----------------|---------|-----------|\n"
        f"| `data.csv` | 999 | `{full_sha[:16]}…` | CC-BY-4.0 | marche-public |\n",
        encoding="utf-8",
    )
    entries = cdr.parse_registry(reg)
    assert len(entries) == 1
    finding = cdr.check_entry(entries[0], tmp_path)
    assert finding["status"] == "OK_TRUNCATED"  # SHA OK
    assert finding["size_warning"]  # taille drift warnée