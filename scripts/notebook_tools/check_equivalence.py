"""check_equivalence.py -- verifie l'equivalence entre un carnet execute et sa page publiee.

Issue #19301, decision du mainteneur 2026-10-05 :
- Pour une cible X.ipynb, l'organe verifie que la page publiee X.html
  repond 200, ET que chaque ligne de sortie propre au carnet
  (stream et text/plain, hors lignes deja presentes dans les sources)
  se retrouve dans le texte de la page.
- Normaliser les prefixes d'affichage Lean et les espaces.
- Verdicts : EQUIVALENT / MISSING_PAGE / LOST_OUTPUTS / UNKNOWN (reseau : jamais un rouge).

Usage :
    python scripts/notebook_tools/check_equivalence.py --notebook MyIA.AI.Notebooks/.../foo.ipynb
    python scripts/notebook_tools/check_equivalence.py --notebook ... --base-url https://jsboige.github.io/CoursIA
    python scripts/notebook_tools/check_equivalence.py --notebook ... --json

Codes de sortie :
    0 : EQUIVALENT
    1 : LOST_OUTPUTS (sortie manquante dans la page)
    2 : MISSING_PAGE (page 404 ou inaccessible)
    3 : UNKNOWN (erreur reseau, retry possible)
    4 : NOTEBOOK_ERROR (carnet invalide)
"""
import argparse
import json
import re
import sys
import urllib.error
import urllib.request
from pathlib import Path
from typing import Iterable

DEFAULT_BASE_URL = "https://jsboige.github.io/CoursIA"
HTTP_TIMEOUT_S = 10

# Prefixes d'affichage a normaliser (leon: ──────▶ etc.)
LEAN_PREFIX_PATTERN = re.compile(r"^[─━\-=]{2,}\s*[▶>»]+\s*", re.MULTILINE)
WHITESPACE_PATTERN = re.compile(r"\s+")


def _normalize_line(line: str) -> str:
    """Normalise une ligne pour la comparaison : prefixes Lean, espaces."""
    line = LEAN_PREFIX_PATTERN.sub("", line)
    line = WHITESPACE_PATTERN.sub(" ", line).strip()
    return line


def extract_outputs(notebook_path: str) -> list[str]:
    """Extrait les lignes de sortie text/plain et stream d'un carnet.

    Renvoie la liste des lignes normalisees, en excluant les lignes qui
    sont deja presentes dans les sources de cellules (reprises de code).
    """
    try:
        with open(notebook_path, encoding="utf-8") as fh:
            nb = json.load(fh)
    except Exception:
        return []
    sources_text: set[str] = set()
    for cell in nb.get("cells", []):
        src = "".join(cell.get("source", []))
        for line in src.splitlines():
            norm = _normalize_line(line)
            if norm:
                sources_text.add(norm)
    output_lines: list[str] = []
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        for out in cell.get("outputs", []):
            otype = out.get("output_type", "")
            text = None
            if otype == "stream":
                # Stream: text is a string under 'out['text']'
                raw = out.get("text")
                if isinstance(raw, str):
                    text = raw
                elif isinstance(raw, list):
                    text = "".join(raw)
            elif otype in ("execute_result", "display_data"):
                # execute_result / display_data: text/plain is under data['text/plain']
                data = out.get("data", {})
                if isinstance(data, dict):
                    raw = data.get("text/plain")
                    if isinstance(raw, str):
                        text = raw
                    elif isinstance(raw, list):
                        text = "".join(raw)
            if text is None:
                continue
            for line in text.splitlines():
                norm = _normalize_line(line)
                if norm and norm not in sources_text:
                    output_lines.append(norm)
    return output_lines


def fetch_page(page_url: str) -> tuple[int, str | None, str | None]:
    """Recupere une page web. Renvoie (status_code, html_text, error_message).

    Erreur reseau : status_code=0, html=None, error_message=...
    Erreur HTTP : status_code=int, html=None, error_message=...
    """
    try:
        req = urllib.request.Request(page_url, headers={"User-Agent": "CoursIA-check_equivalence/1.0"})
        with urllib.request.urlopen(req, timeout=HTTP_TIMEOUT_S) as resp:
            return resp.status, resp.read().decode("utf-8", errors="replace"), None
    except urllib.error.HTTPError as e:
        return e.code, None, f"http_error: {e.code} {e.reason}"
    except urllib.error.URLError as e:
        return 0, None, f"url_error: {e.reason}"
    except Exception as e:
        return 0, None, f"unexpected: {type(e).__name__}: {e}"


def notebook_to_page_url(notebook_path: str, base_url: str) -> str:
    """Convertit un chemin de carnet en URL de page publiee.

    MyIA.AI.Notebooks/Series/file.ipynb -> <base>/Series/file.html
    """
    p = Path(notebook_path)
    parts = list(p.parts)
    if "MyIA.AI.Notebooks" in parts:
        idx = parts.index("MyIA.AI.Notebooks")
        rel = "/".join(parts[idx + 1 :])
    else:
        rel = str(p).replace("\\", "/")
    rel = rel[:-len(".ipynb")] + ".html"
    return f"{base_url.rstrip('/')}/{rel}"


def check_equivalence(notebook_path: str, base_url: str = DEFAULT_BASE_URL) -> dict:
    """Verifie l'equivalence entre un carnet et sa page publiee.

    Renvoie un dict avec : notebook, page_url, status, verdict, missing_lines, error.
    """
    verdict: dict = {
        "notebook": notebook_path,
        "page_url": "",
        "status": None,
        "verdict": "UNKNOWN",
        "missing_lines": [],
        "found_lines": 0,
        "total_lines": 0,
        "error": None,
    }
    if not Path(notebook_path).is_file():
        verdict["verdict"] = "NOTEBOOK_ERROR"
        verdict["error"] = f"notebook not found: {notebook_path}"
        return verdict
    page_url = notebook_to_page_url(notebook_path, base_url)
    verdict["page_url"] = page_url
    status, html, err = fetch_page(page_url)
    verdict["status"] = status
    if status == 0:
        verdict["verdict"] = "UNKNOWN"
        verdict["error"] = err
        return verdict
    if status != 200:
        verdict["verdict"] = "MISSING_PAGE"
        verdict["error"] = err or f"http status {status}"
        return verdict
    if html is None:
        verdict["verdict"] = "UNKNOWN"
        verdict["error"] = "no html body"
        return verdict
    outputs = extract_outputs(notebook_path)
    verdict["total_lines"] = len(outputs)
    html_norm = WHITESPACE_PATTERN.sub(" ", html)
    missing: list[str] = []
    found = 0
    for line in outputs:
        line_norm = _normalize_line(line)
        if not line_norm:
            continue
        if line_norm in html_norm:
            found += 1
        else:
            missing.append(line)
    verdict["found_lines"] = found
    verdict["missing_lines"] = missing
    if missing:
        verdict["verdict"] = "LOST_OUTPUTS"
    else:
        verdict["verdict"] = "EQUIVALENT"
    return verdict


def render_text(verdict: dict) -> str:
    """Rendu texte pour le mode --report."""
    out = []
    out.append(f"Notebook : {verdict['notebook']}")
    out.append(f"Page URL : {verdict['page_url']}")
    out.append(f"HTTP status : {verdict['status']}")
    out.append(f"Verdict : {verdict['verdict']}")
    out.append(f"Lignes : {verdict['found_lines']}/{verdict['total_lines']} trouvees dans la page")
    if verdict.get("error"):
        out.append(f"Erreur : {verdict['error']}")
    if verdict.get("missing_lines"):
        out.append(f"Lignes manquantes ({len(verdict['missing_lines'])}):")
        for line in verdict["missing_lines"][:20]:
            out.append(f"  - {line[:120]}")
        if len(verdict["missing_lines"]) > 20:
            out.append(f"  ... et {len(verdict['missing_lines']) - 20} autres")
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--notebook", required=True, help="Chemin du .ipynb (relatif ou absolu)")
    p.add_argument("--base-url", default=DEFAULT_BASE_URL, help="Base URL des pages publiees")
    p.add_argument("--json", action="store_true", help="Sortie JSON")
    p.add_argument("--report", action="store_true", help="Sortie rapport texte")
    args = p.parse_args(argv)

    verdict = check_equivalence(args.notebook, args.base_url)
    if args.json and not args.report:
        print(json.dumps(verdict, ensure_ascii=False, indent=2))
    else:
        print(render_text(verdict))
    rc_map = {
        "EQUIVALENT": 0,
        "LOST_OUTPUTS": 1,
        "MISSING_PAGE": 2,
        "UNKNOWN": 3,
        "NOTEBOOK_ERROR": 4,
    }
    return rc_map.get(verdict["verdict"], 3)


if __name__ == "__main__":
    sys.exit(main())
