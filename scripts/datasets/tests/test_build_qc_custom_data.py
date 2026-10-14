#!/usr/bin/env python3
"""Tests pour build_qc_custom_data.py — convertisseur tabulaire -> module QC.

Couvre le convertisseur generalise qui remplace, pour les formats nouveaux, le
convertisseur lie a EDGAR (`edgar_signal.write_cloud_module`). Le point de
livraison est le **format JSONL**, qu'aucun script de `scripts/datasets/` ne
lisait avant ce fichier.

Scope (hermetique, 0 reseau) :
  - detect_format : deduction par suffixe, alias .ndjson, suffixe inconnu -> erreur
  - read_source : jsonl (format nouveau), json (liste d'objets), csv `;`, tsv tabulation
  - read_source : lignes vides/commentaires ignores, JSON invalide -> erreur situee,
    source vide -> erreur, json non-liste -> erreur
  - render_module : determinisme (deux rendus byte-identiques), fail-closed quand
    --class-name est demande sans colonnes date/valeur
  - module emis : `ast.parse` OK (c'est du `.py` valide, ce que QC exige) et
    **execution reelle de la classe PythonData** contre un faux `AlgorithmImports`
    (GetSource + Reader rendent un objet typé) — c'est la preuve que l'artefact
    est consommable, pas seulement ecrit
  - main() : aller-retour CLI complet + code de sortie 1 sur erreur de format

Run: ``python -m pytest scripts/datasets/tests/test_build_qc_custom_data.py -q``
"""
import ast
import importlib.util
import json
import sys
import types
from datetime import datetime
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
DATASETS_DIR = HERE.parent  # scripts/datasets/ (ou vit build_qc_custom_data.py)
sys.path.insert(0, str(DATASETS_DIR))

import build_qc_custom_data as bq  # noqa: E402

JSONL_ROWS = [
    {"accepted_at": "2022-01-03T14:30:00", "ticker": "AAPL", "similarity": 0.812},
    {"accepted_at": "2022-04-01T20:05:00", "ticker": "MSFT", "similarity": -0.244},
]


def _write(tmp_path: Path, name: str, text: str) -> Path:
    path = tmp_path / name
    path.write_text(text, encoding="utf-8")
    return path


def _fake_algorithm_imports() -> types.ModuleType:
    """Faux `AlgorithmImports` LEAN : juste ce que la classe emise consomme."""

    class PythonData:
        pass

    class _Medium:
        LocalFile = "LocalFile"
        RemoteFile = "RemoteFile"

    class SubscriptionDataSource:
        def __init__(self, source, transport):
            self.source = source
            self.transport = transport

    class Symbol:
        def __init__(self, value):
            self.Value = value

        @staticmethod
        def Create(ticker, security_type, market):
            return Symbol(f"{ticker}:{security_type}:{market}")

    class _SecurityType:
        Base = "Base"

    class _Market:
        USA = "USA"

    module = types.ModuleType("AlgorithmImports")
    module.PythonData = PythonData
    module.SubscriptionDataSource = SubscriptionDataSource
    module.SubscriptionTransportMedium = _Medium
    module.Symbol = Symbol
    module.SecurityType = _SecurityType
    module.Market = _Market
    module.datetime = datetime
    return module


def _load_emitted_module(path: Path):
    """Importe le module emis, en injectant le faux `AlgorithmImports`."""
    fake = _fake_algorithm_imports()
    previous = sys.modules.get("AlgorithmImports")
    sys.modules["AlgorithmImports"] = fake
    try:
        spec = importlib.util.spec_from_file_location(f"emitted_{path.stem}", path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
    finally:
        if previous is None:
            sys.modules.pop("AlgorithmImports", None)
        else:
            sys.modules["AlgorithmImports"] = previous
    return module


# ---------------------------------------------------------------------------
# detect_format
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "name,expected",
    [
        ("a.csv", "csv"),
        ("a.tsv", "tsv"),
        ("a.json", "json"),
        ("a.jsonl", "jsonl"),
        ("a.ndjson", "jsonl"),
        ("A.JSONL", "jsonl"),
    ],
)
def test_detect_format_by_suffix(name, expected):
    assert bq.detect_format(name) == expected


def test_detect_format_unknown_suffix_raises():
    with pytest.raises(bq.SourceFormatError) as exc:
        bq.detect_format("data.parquet")
    assert "non reconnu" in str(exc.value)


# ---------------------------------------------------------------------------
# read_source — JSONL est le format nouveau
# ---------------------------------------------------------------------------


def test_read_source_jsonl_new_format(tmp_path):
    path = _write(
        tmp_path,
        "signals.jsonl",
        "\n".join(json.dumps(row) for row in JSONL_ROWS) + "\n",
    )
    rows, columns = bq.read_source(path)
    assert columns == ["accepted_at", "ticker", "similarity"]
    assert len(rows) == 2
    assert rows[0]["ticker"] == "AAPL"
    assert rows[1]["similarity"] == -0.244


def test_read_source_jsonl_ignores_blank_and_comment_lines(tmp_path):
    text = (
        "# export du 2026-10-07\n"
        "\n"
        + json.dumps(JSONL_ROWS[0])
        + "\n   \n"
        + json.dumps(JSONL_ROWS[1])
        + "\n"
    )
    path = _write(tmp_path, "signals.jsonl", text)
    rows, _ = bq.read_source(path)
    assert len(rows) == 2


def test_read_source_jsonl_invalid_line_reports_lineno(tmp_path):
    text = json.dumps(JSONL_ROWS[0]) + "\n{ pas du json }\n"
    path = _write(tmp_path, "broken.jsonl", text)
    with pytest.raises(bq.SourceFormatError) as exc:
        bq.read_source(path)
    assert "ligne 2" in str(exc.value)


def test_read_source_ndjson_alias_is_jsonl(tmp_path):
    path = _write(tmp_path, "signals.ndjson", json.dumps(JSONL_ROWS[0]) + "\n")
    rows, _ = bq.read_source(path)
    assert rows == [JSONL_ROWS[0]]


def test_read_source_json_list_of_objects(tmp_path):
    path = _write(tmp_path, "signals.json", json.dumps(JSONL_ROWS))
    rows, columns = bq.read_source(path)
    assert rows == JSONL_ROWS
    assert columns == ["accepted_at", "ticker", "similarity"]


def test_read_source_json_non_list_raises(tmp_path):
    path = _write(tmp_path, "obj.json", json.dumps({"a": 1}))
    with pytest.raises(bq.SourceFormatError) as exc:
        bq.read_source(path)
    assert "tableau JSON" in str(exc.value)


def test_read_source_csv_semicolon_delimiter(tmp_path):
    path = _write(tmp_path, "a.csv", "ticker;similarity\nAAPL;0.8\n")
    rows, columns = bq.read_source(path, delimiter=";")
    assert columns == ["ticker", "similarity"]
    assert rows[0]["similarity"] == "0.8"


def test_read_source_tsv_default_tabulation(tmp_path):
    path = _write(tmp_path, "a.tsv", "ticker\tsimilarity\nAAPL\t0.8\n")
    rows, columns = bq.read_source(path)
    assert columns == ["ticker", "similarity"]
    assert rows[0]["ticker"] == "AAPL"


def test_read_source_empty_jsonl_raises(tmp_path):
    path = _write(tmp_path, "empty.jsonl", "\n# rien\n")
    with pytest.raises(bq.SourceFormatError) as exc:
        bq.read_source(path)
    assert "vide" in str(exc.value)


def test_read_source_unknown_format_name_raises(tmp_path):
    path = _write(tmp_path, "a.csv", "a\n1\n")
    with pytest.raises(bq.SourceFormatError):
        bq.read_source(path, fmt="parquet")


# ---------------------------------------------------------------------------
# render_module / emit_module
# ---------------------------------------------------------------------------


def test_render_module_is_deterministic():
    first = bq.render_module(JSONL_ROWS, "SIGNALS")
    second = bq.render_module(JSONL_ROWS, "SIGNALS")
    assert first == second
    assert "SIGNALS = [" in first


def test_render_module_data_only_has_no_lean_imports():
    text = bq.render_module(JSONL_ROWS, "SIGNALS")
    assert "AlgorithmImports" not in text
    assert ast.parse(text)  # .py valide


def test_render_module_class_requires_date_and_value_columns():
    with pytest.raises(bq.SourceFormatError) as exc:
        bq.render_module(JSONL_ROWS, "SIGNALS", class_name="Signals")
    assert "date-column" in str(exc.value)


def test_emit_module_roundtrip_importable(tmp_path):
    out = tmp_path / "out" / "signals_data.py"
    written = bq.emit_module(JSONL_ROWS, out, "SIGNALS")
    assert written == 2
    module = _load_emitted_module(out)
    assert module.SIGNALS == JSONL_ROWS


def test_emitted_custom_data_class_executes(tmp_path):
    """Le module emis porte un `PythonData` qui tourne (preuve de consommation)."""
    out = tmp_path / "signals_data.py"
    bq.emit_module(
        JSONL_ROWS,
        out,
        "SIGNALS",
        class_name="FilingSignal",
        date_column="accepted_at",
        value_column="similarity",
        ticker_column="ticker",
    )
    module = _load_emitted_module(out)
    instance = module.FilingSignal()

    source = instance.GetSource(config=types.SimpleNamespace(Symbol=module.Symbol("spy")),
                                date=None, isLiveMode=False)
    assert source.transport == "LocalFile"

    config = types.SimpleNamespace(Symbol=module.Symbol("spy"))
    obj = instance.Reader(config=config, line=json.dumps(JSONL_ROWS[0]), date=None, isLiveMode=False)
    assert obj.Time == datetime.fromisoformat("2022-01-03T14:30:00")
    assert obj.Value == pytest.approx(0.812)
    assert obj.Symbol.Value == "AAPL:Base:USA"

    # Ligne sans les colonnes requises : ignoree, le moteur ne tombe pas.
    assert instance.Reader(config=config, line=json.dumps({"ticker": "AAPL"}), date=None,
                           isLiveMode=False) is None
    assert instance.Reader(config=config, line="", date=None, isLiveMode=False) is None


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def test_main_jsonl_end_to_end(tmp_path):
    src = _write(tmp_path, "in.jsonl", json.dumps(JSONL_ROWS[0]) + "\n")
    out = tmp_path / "nested" / "mod.py"
    rc = bq.main(["--input", str(src), "--output", str(out), "--variable", "KAGGLE_SIGNALS"])
    assert rc == 0
    assert out.exists()
    assert _load_emitted_module(out).KAGGLE_SIGNALS == [JSONL_ROWS[0]]


def test_main_returns_1_on_unknown_format(tmp_path, capsys):
    src = _write(tmp_path, "data.parquet", "x")
    rc = bq.main(["--input", str(src), "--output", str(tmp_path / "m.py"), "--variable", "V"])
    assert rc == 1
    assert "ERROR" in capsys.readouterr().err


def test_main_returns_1_when_class_requested_without_columns(tmp_path, capsys):
    src = _write(tmp_path, "in.jsonl", json.dumps(JSONL_ROWS[0]) + "\n")
    rc = bq.main([
        "--input", str(src), "--output", str(tmp_path / "m.py"),
        "--variable", "V", "--class-name", "X",
    ])
    assert rc == 1
    assert "date-column" in capsys.readouterr().err
