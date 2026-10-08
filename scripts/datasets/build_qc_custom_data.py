#!/usr/bin/env python3
"""Convertit un fichier tabulaire quelconque en module Python consommable par QuantConnect.

Pourquoi ce script existe
-------------------------
Un projet QuantConnect Cloud refuse les fichiers ``.csv`` : seul du ``.py`` est
accepte. Le convertisseur historique de ce depot est ``write_cloud_module``
(``MyIA.AI.Notebooks/QuantConnect/projects/Filing-Language-Stability/edgar_signal.py``,
ligne 642) : il emet deja le bon *type* d'artefact, mais il est lie a une source
unique (SEC EDGAR) et a un schema unique (paires 10-K adjacentes).

Ce fichier generalise le meme geste sans le remplacer : le convertisseur EDGAR
reste en place et inchange pour son usage ; celui-ci sait lire **n'importe quel**
format tabulaire et emettre le module correspondant, ce qui permet de brancher
une source ouverte nouvelle (Kaggle, EDGAR full-text, export maison) sans
reecrire un convertisseur a chaque fois.

Formats d'entree
----------------
``csv`` · ``tsv`` · ``json`` (liste d'objets) · ``jsonl`` (un objet JSON par ligne)

Le format ``jsonl`` (alias ``ndjson``) n'etait lu par **aucun** script de
``scripts/datasets/`` avant ce fichier — c'est le format nouveau que la
generalisation rend consommable.

Sortie
------
Un module ``.py`` portant :

1. la constante de donnees ``<VARIABLE> = [ {...}, {...} ]`` ;
2. si ``--class-name`` est fourni, une classe ``PythonData`` derivee qui relit
   ces lignes en transport ``LocalFile`` (patron du depot, cf
   ``partner-course-quant-trading/examples/Sector-Momentum/FredRate.py``).

Les valeurs sont conservees **en chaines de caracteres** (meme choix que le
convertisseur EDGAR) : un consommateur typant ses colonnes lui-meme ne subit
aucune perte de precision au transport, et ``None`` reste distinct de la chaine
``"None"``.

Determinisme
------------
L'ordre des lignes suit l'ordre d'entree ; l'ordre des colonnes suit la premiere
ligne du fichier source. Deux conversions du meme fichier sont byte-identiques.

Usage
-----
    python scripts/datasets/build_qc_custom_data.py \\
        --input signals.jsonl --variable KAGGLE_SIGNALS --output signals.py

    python scripts/datasets/build_qc_custom_data.py \\
        --input filings.csv --delimiter ';' --variable FILINGS \\
        --class-name FilingSignal --date-column accepted_at \\
        --ticker-column ticker --value-column similarity --output filing_data.py

Tests : ``python -m pytest scripts/datasets/tests/test_build_qc_custom_data.py -q``
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from pathlib import Path

#: Formats d'entree reconnus par :func:`read_source`.
SUPPORTED_FORMATS = ("csv", "tsv", "json", "jsonl")

#: Alias de suffixe -> format canonique (``.ndjson`` est un synonyme de ``.jsonl``).
_SUFFIX_TO_FORMAT = {
    ".csv": "csv",
    ".tsv": "tsv",
    ".json": "json",
    ".jsonl": "jsonl",
    ".ndjson": "jsonl",
}


class SourceFormatError(ValueError):
    """Le fichier source est illisible, vide, ou ne respecte pas son format annonce."""


def detect_format(path: Path | str) -> str:
    """Deduit le format depuis le suffixe du fichier.

    Leve :class:`SourceFormatError` si le suffixe n'est pas reconnu — on ne
    devine jamais, un suffixe inconnu est une erreur d'appel, pas un cas a
    traiter silencieusement.
    """
    suffix = Path(path).suffix.lower()
    try:
        return _SUFFIX_TO_FORMAT[suffix]
    except KeyError:
        raise SourceFormatError(
            f"suffixe {suffix!r} non reconnu ; formats acceptes : "
            f"{', '.join(sorted(_SUFFIX_TO_FORMAT))}"
        ) from None


def _rows_from_delimited(path: Path, delimiter: str) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8-sig", newline="") as fh:
        reader = csv.DictReader(fh, delimiter=delimiter)
        if reader.fieldnames is None:
            raise SourceFormatError(f"{path} : aucune ligne d'en-tete")
        return [dict(row) for row in reader]


def _check_rows(rows: list[dict], path: Path) -> list[dict[str, str]]:
    """Valide la forme commune : liste non vide de dictionnaires plats."""
    if not rows:
        raise SourceFormatError(f"{path} : source vide (aucune ligne de donnees)")
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            raise SourceFormatError(
                f"{path} : ligne {index} est un {type(row).__name__}, un objet attendu"
            )
    return rows


def _rows_from_json(path: Path) -> list[dict[str, str]]:
    payload = json.loads(path.read_text(encoding="utf-8-sig"))
    if not isinstance(payload, list):
        raise SourceFormatError(
            f"{path} : un tableau JSON d'objets est attendu, "
            f"{type(payload).__name__} recu"
        )
    return _check_rows(payload, path)


def _rows_from_jsonl(path: Path) -> list[dict[str, str]]:
    """Un objet JSON par ligne ; les lignes vides et commentaires ``#`` sont ignores."""
    rows = []
    with path.open("r", encoding="utf-8-sig") as fh:
        for lineno, line in enumerate(fh, start=1):
            stripped = line.strip()
            if not stripped or stripped.startswith("#"):
                continue
            try:
                rows.append(json.loads(stripped))
            except json.JSONDecodeError as exc:
                raise SourceFormatError(f"{path} ligne {lineno} : JSON invalide ({exc.msg})") from exc
    return _check_rows(rows, path)


def read_source(
    path: Path | str,
    fmt: str | None = None,
    delimiter: str | None = None,
) -> tuple[list[dict[str, str]], list[str]]:
    """Lit ``path`` et rend ``(lignes, colonnes)``.

    ``fmt`` vaut ``None`` pour deduire le format du suffixe. ``delimiter``
    n'a de sens que pour ``csv``/``tsv`` (defaut ``","`` et ``"\\t"``).
    """
    path = Path(path)
    resolved = fmt or detect_format(path)
    if resolved in ("csv", "tsv"):
        if delimiter is None:
            delimiter = "\t" if resolved == "tsv" else ","
        rows = _rows_from_delimited(path, delimiter)
    elif resolved == "json":
        rows = _rows_from_json(path)
    elif resolved == "jsonl":
        rows = _rows_from_jsonl(path)
    else:
        raise SourceFormatError(
            f"format {resolved!r} inconnu ; attendu : {', '.join(SUPPORTED_FORMATS)}"
        )
    columns = list(rows[0].keys())
    return rows, columns


def _render_data_class(
    class_name: str,
    variable_name: str,
    date_column: str,
    value_column: str,
    ticker_column: str | None,
) -> str:
    """Rend une classe ``PythonData`` derivee lisant ``variable_name``.

    Le ``Reader`` est volontairement permissif sur le typage (``Value`` en
    ``float``, horodatage ISO-8601) et strict sur la forme : une ligne trop
    courte est ignoree plutot que de faire tomber le moteur.
    """
    ticker_line = (
        f"        obj.Symbol = Symbol.Create(row[{ticker_column!r}], SecurityType.Base, Market.USA)\n"
        if ticker_column
        else "        obj.Symbol = config.Symbol\n"
    )
    return (
        f"class {class_name}(PythonData):\n"
        f'    """Custom data relisant ``{variable_name}`` (transport LocalFile).\n'
        f"\n"
        f"    Colonnes requises : {date_column!r} (ISO-8601), {value_column!r} (float)"
        + (f", {ticker_column!r} (ticker)" if ticker_column else "")
        + ".\n"
        f'    """\n'
        f"\n"
        f"    def GetSource(self, config, date, isLiveMode):\n"
        f"        return SubscriptionDataSource(\n"
        f"            config.Symbol.Value, SubscriptionTransportMedium.LocalFile\n"
        f"        )\n"
        f"\n"
        f"    def Reader(self, config, line, date, isLiveMode):\n"
        f"        line = line.strip()\n"
        f"        if not line:\n"
        f"            return None\n"
        f"        row = json.loads(line)\n"
        f"        if {date_column!r} not in row or {value_column!r} not in row:\n"
        f"            return None\n"
        f"        obj = {class_name}()\n"
        f"{ticker_line}"
        f"        obj.Time = datetime.fromisoformat(str(row[{date_column!r}]))\n"
        f"        obj.Value = float(row[{value_column!r}])\n"
        f"        obj.EndTime = obj.Time\n"
        f"        return obj\n"
    )


def render_module(
    rows: list[dict[str, str]],
    variable_name: str,
    *,
    class_name: str | None = None,
    date_column: str | None = None,
    value_column: str | None = None,
    ticker_column: str | None = None,
) -> str:
    """Rend le texte du module Python QC-compatible (sans ecrire sur disque).

    Un module de donnees seul est rendu si ``class_name`` est ``None``. Sinon,
    la classe est ajoutee et le module importe ``json``/``AlgorithmImports``
    pour la faire tourner dans LEAN. Les trois colonnes nommees sont alors
    **obligatoires** dans les donnees : leur absence est une erreur d'appel,
    jamais un module a moitie fonctionnel.
    """
    if not rows:
        raise SourceFormatError("source vide : aucun module a rendre")
    if class_name is not None:
        missing = [c for c in (date_column, value_column) if not c]
        if missing:
            raise SourceFormatError(
                "--class-name exige --date-column et --value-column "
                "(aucun defaut devine depuis la source)"
            )
        header = (
            "# region imports\n"
            "from AlgorithmImports import *\n"
            "\n"
            "import json\n"
            "# endregion\n"
            "\n"
        )
        body = _render_data_class(
            class_name, variable_name, date_column, value_column, ticker_column
        )
        return (
            f"{header}"
            f"# Genere par scripts/datasets/build_qc_custom_data.py — ne pas editer.\n"
            f"{body}\n\n"
            f"{variable_name} = {rows!r}\n"
        )
    return (
        "# Genere par scripts/datasets/build_qc_custom_data.py — ne pas editer.\n"
        f"{variable_name} = {rows!r}\n"
    )


def emit_module(
    rows: list[dict[str, str]],
    path: Path | str,
    variable_name: str,
    **kwargs,
) -> int:
    """Ecrit le module dans ``path`` et rend le nombre de lignes ecrites."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    text = render_module(rows, variable_name, **kwargs)
    path.write_text(text, encoding="utf-8")
    return len(rows)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Convertit un fichier tabulaire (csv/tsv/json/jsonl) en module Python "
            "consommable par un projet QuantConnect Cloud."
        )
    )
    parser.add_argument("--input", required=True, help="fichier source")
    parser.add_argument("--output", required=True, help="module .py a ecrire")
    parser.add_argument(
        "--variable", required=True, help="nom de la constante de donnees (ex. KAGGLE_SIGNALS)"
    )
    parser.add_argument(
        "--format",
        dest="fmt",
        choices=SUPPORTED_FORMATS,
        default=None,
        help="format source (defaut : deduit du suffixe)",
    )
    parser.add_argument("--delimiter", default=None, help="separateur csv/tsv (defaut : , ou tabulation)")
    parser.add_argument(
        "--class-name",
        default=None,
        help="emet aussi une classe PythonData derivee portant ce nom",
    )
    parser.add_argument("--date-column", default=None, help="colonne d'horodatage ISO-8601 (avec --class-name)")
    parser.add_argument("--value-column", default=None, help="colonne de valeur numerique (avec --class-name)")
    parser.add_argument("--ticker-column", default=None, help="colonne de ticker (optionnelle)")
    args = parser.parse_args(argv)

    try:
        rows, columns = read_source(args.input, fmt=args.fmt, delimiter=args.delimiter)
        written = emit_module(
            rows,
            args.output,
            args.variable,
            class_name=args.class_name,
            date_column=args.date_column,
            value_column=args.value_column,
            ticker_column=args.ticker_column,
        )
    except SourceFormatError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    extra = f" + classe {args.class_name}" if args.class_name else ""
    print(
        f"{written} lignes ({len(columns)} colonnes: {', '.join(columns)}){extra} "
        f"-> {args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
