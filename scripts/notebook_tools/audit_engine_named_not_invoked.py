#!/usr/bin/env python3
"""Audit notebooks that name an engine/LLM without invoking it.

Standing-ASK class (SOTA #3801, regle H) -- un notebook qui claim un
moteur (Google ADK, OpenAI, BigQuery, etc.) sans importer/invoquer le SDK
officiel ET sans outputs reels est un **claim creux** : le rendu passe la
barre C.2 (outputs/exec) mais le moteur annonce n'est pas celui qui
s'execute. Defaut firsthand documente dans #13927 :

* ``Track2-GoogleADK`` : titres/objectifs parlent de Google ADK, mais 10
  labs sur 10 ont zero import/appel ``google.adk``.
* ``SW-12-Python-GraphRAG.ipynb`` : objectifs "Extraction reelle avec
  GPT/Claude" mais outputs "Reponse simulee".

Ce scanner croise **trois surfaces** par notebook :

* **claim** : prose (markdown), titre, objectifs -- emploie un moteur avec
  un verbe d'execution/integration ;
* **wiring** : code source -- import et appel de l'API officielle ou du
  client reel ;
* **proof** : outputs executes -- real output compatible avec l'appel
  reel, sans marqueur de simulation/fallback.

Un notebook sans wiring local peut etre admissible uniquement si :

1. il se declare explicitement deterministe/sans LLM ;
2. la meme sequence (dossier-serie) reference un notebook successeur ;
3. ce successeur apporte wiring **et outputs reels**.

## Verdicts (5)

| Verdict | Sens |
|---|---|
| ``ENGINE_EXEC_PROVED`` | claim + wiring + outputs reels |
| ``DISCLOSED_SEQUENCE_PROVED`` | notebook deterministe declare + successeur avec wiring+proof dans la meme serie |
| ``WIRING_ONLY`` | import present mais aucun output reel (cle absente, exec gate par env, etc.) |
| ``SIMULATED_TERMINAL`` | outputs = simulation/fallback, pas de successeur avec wiring |
| ``NAMED_NOT_INVOKED`` | claim present mais zero import/wiring |

## Registre moteur (extensible)

Chaque entree porte : ``imports`` (regex sur code source), ``claims`` (regex
sur prose markdown), ``simulation_markers`` (regex sur outputs), et un
verdict par defaut si rien ne matche. Le registre est explicite -- aucune
heuristique opaque.

Usage::

    python audit_engine_named_not_invoked.py --scan <notebook.ipynb>
    python audit_engine_named_not_invoked.py --scan-all
    python audit_engine_named_not_invoked.py --scan-all --check   # exit 1 si NAMED_NOT_INVOKED/SIMULATED_TERMINAL
    python audit_engine_named_not_invoked.py --scan-all --json
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Tuple


# --- Registre moteur -------------------------------------------------------

@dataclass(frozen=True)
class EngineSpec:
    """Specification d'un moteur dans le registre."""

    key: str
    label: str
    imports: Tuple[str, ...]
    claims: Tuple[str, ...]
    simulation_markers: Tuple[str, ...]
    notes: str = ""


ENGINE_REGISTRY: Dict[str, EngineSpec] = {
    "google_adk": EngineSpec(
        key="google_adk",
        label="Google ADK",
        imports=(r"\bgoogle\.adk\b", r"\bfrom\s+google\s+import\s+adk\b"),
        claims=(
            r"\bgoogle\s+adk\b",
            r"\badk\s+agent\b",
            r"\badk\s+runtime\b",
            r"\badk\s+reel\b",
        ),
        simulation_markers=(
            r"class\s+MockAgent",
            r"class\s+FakeAgent",
            r"#\s*simulated\s+adk",
            r"\bsdk\s+fictif\b",
        ),
        notes="Track2-GoogleADK : 10 labs sans import `google.adk` detecte en 2026-09.",
    ),
    "openai_llm": EngineSpec(
        key="openai_llm",
        label="OpenAI/Anthropic/LiteLLM (LLM reel)",
        imports=(
            r"\bopenai\b",
            r"\banthropic\b",
            r"\blitellm\b",
            r"\bfrom\s+openai\s+import\b",
            r"\bfrom\s+anthropic\s+import\b",
        ),
        claims=(
            r"\bgpt-[34]\b",
            r"\bclaude-(?:opus|sonnet|haiku)\b",
            r"\bGPT\s*/\s*Claude\b",
            r"\bappel\s+(?:a|au)\s+(?:gpt|claude|llm)\b",
            r"\b(?:avec|via)\s+(?:gpt|claude|llm)\b",
            r"\blLM\s+reel\b",
        ),
        simulation_markers=(
            r"Reponse simulee",
            r"simulated\s+response",
            r"class\s+MockLLM",
            r"#\s*TODO.*api\s+key",
        ),
        notes="SW-12 GraphRAG : claim 'GPT/Claude' avec outputs 'Reponse simulee'.",
    ),
    "bigquery": EngineSpec(
        key="bigquery",
        label="Google BigQuery / BQML",
        imports=(
            r"\bgoogle\.cloud\.bigquery\b",
            r"\bfrom\s+google\.cloud\s+import\s+bigquery\b",
        ),
        claims=(
            r"\bbigquery\b",
            r"\bBQML\b",
            r"\bML\.PREDICT\b",
        ),
        simulation_markers=(
            r"schema\s+simul",
            r"donnees\s+simulees",
            r"bigquery\s+simul",
        ),
        notes="Lab16 DataScienceWithAgents : claim BQML avec schema simule -- corrige via #14040 (RECOVERABLE-USER-HAND).",
    ),
}


# --- Lecture notebook ------------------------------------------------------

def _read_notebook(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _cell_source(cell: dict) -> str:
    src = cell.get("source", [])
    if isinstance(src, list):
        return "".join(src)
    return src or ""


def _cell_output_text(cell: dict) -> str:
    """Concatene tous les outputs d'une cellule en texte."""
    parts: List[str] = []
    for out in cell.get("outputs", []) or []:
        otype = out.get("output_type", "")
        if otype == "stream":
            text = out.get("text", "")
            if isinstance(text, list):
                text = "".join(text)
            parts.append(text or "")
        elif otype in ("execute_result", "display_data"):
            data = out.get("data", {})
            for k in ("text/plain", "text/html"):
                v = data.get(k)
                if isinstance(v, list):
                    parts.append("".join(str(x) for x in v))
                elif isinstance(v, str):
                    parts.append(v)
        elif otype == "error":
            tb = out.get("traceback", [])
            if isinstance(tb, list):
                parts.append("\n".join(str(x) for x in tb))
            else:
                parts.append(str(tb))
    return "\n".join(str(p) for p in parts)


# --- Detection -------------------------------------------------------------

@dataclass
class SurfaceHits:
    """Resultat du croisement des 3 surfaces pour un moteur."""
    claim_hits: List[Tuple[int, str]] = field(default_factory=list)   # (cell_idx, snippet)
    wiring_hits: List[Tuple[int, str]] = field(default_factory=list)
    proof_hits: List[Tuple[int, str]] = field(default_factory=list)
    simulation_hits: List[Tuple[int, str]] = field(default_factory=list)


def _strip_comments(src: str) -> str:
    """Retire les commentaires `#` et les docstrings pour le scan wiring/proof.

    Un match dans un commentaire n'est pas une preuve d'invocation -- c'est
    juste une mention discursive. On garde les chaines de caracteres
    (print("openai...")) parce qu'elles peuvent etre des appels caches,
    mais on retire les commentaires Python purs.
    """
    lines = src.split("\n")
    out = []
    for line in lines:
        stripped = line.lstrip()
        if stripped.startswith("#"):
            continue
        # Retrait d'un commentaire en milieu de ligne (apres du code)
        # Heuristique : `#` non precede d'un caractere alphanumerique (donc pas dans une string)
        # Simplification : on retire tout apres le premier `#` qui n'est pas dans une string.
        # Les strings simples avec `#` (`"#hashtag"`) ne sont pas affectees par notre regex wiring
        # (qui cherche `google.adk` etc.), donc cette approximation suffit.
        in_str = False
        for i, c in enumerate(line):
            if c == '"' or c == "'":
                in_str = not in_str
            elif c == "#" and not in_str:
                line = line[:i]
                break
        out.append(line)
    return "\n".join(out)


def _scan_engine(notebook: dict, spec: EngineSpec) -> SurfaceHits:
    hits = SurfaceHits()
    cells = notebook.get("cells", [])
    for idx, cell in enumerate(cells):
        ctype = cell.get("cell_type", "")
        src = _cell_source(cell)
        out_text = _cell_output_text(cell) if ctype == "code" else ""
        # Code sans commentaires : utilise pour wiring (un import dans un
        # commentaire n'est pas un import reel).
        code_clean = _strip_comments(src) if ctype == "code" else ""

        # --- claim : markdown prose ---
        if ctype == "markdown":
            for pat in spec.claims:
                m = re.search(pat, src, re.IGNORECASE)
                if m:
                    snippet = m.group(0)
                    hits.claim_hits.append((idx, snippet[:80]))
                    break

        if ctype != "code":
            continue

        # --- simulation markers : scan sur source ET outputs ---
        # Le marker de simulation peut etre dans le code (class Mock...)
        # OU dans l'output (print("Reponse simulee")).
        cell_is_simulation = False
        for pat in spec.simulation_markers:
            m_src = re.search(pat, src, re.IGNORECASE)
            m_out = re.search(pat, out_text, re.IGNORECASE)
            if m_src or m_out:
                marker = (m_src or m_out).group(0)
                hits.simulation_hits.append((idx, marker[:80]))
                cell_is_simulation = True
                break

        # --- wiring : import ou appel SDK dans la source (commentaires retires) ---
        for pat in spec.imports:
            m = re.search(pat, code_clean)
            if m:
                hits.wiring_hits.append((idx, m.group(0)[:80]))
                break

        # --- proof : output reel d'execution, non vide, sans marker simulation ---
        # Si la cellule EST simulation, son output ne compte pas comme proof.
        if not cell_is_simulation and out_text.strip():
            hits.proof_hits.append((idx, out_text[:80].replace("\n", " ")))

    return hits


# --- Verdict ---------------------------------------------------------------

def _is_disclosed_deterministic(notebook: dict) -> bool:
    """Verifie si le notebook se declare deterministe/sans LLM."""
    markers = (
        r"deterministe",
        r"sans\s+llm",
        r"no\s+llm",
        r"n['’]appelle\s+pas\s+de\s+llm",
        r"ne\s+consomme\s+pas\s+de\s+llm",
    )
    cells = notebook.get("cells", [])
    md_text = "\n".join(_cell_source(c) for c in cells if c.get("cell_type") == "markdown")
    return any(re.search(m, md_text, re.IGNORECASE) for m in markers)


def _detect_disclosed_sequence(
    notebook_path: Path, current_spec: EngineSpec, current_hits: SurfaceHits,
    sibling_notebooks: Optional[List[Path]] = None,
) -> Optional[bool]:
    """Verifie si un successeur dans la même série apporte wiring+proof.

    Convention de serie : meme dossier parent. Le successeur est le notebook
    suivant dans l'ordre lexicographique des fichiers .ipynb.
    """
    if sibling_notebooks is None:
        # Best-effort : lister les .ipynb du meme dossier
        try:
            siblings = sorted(
                p for p in notebook_path.parent.glob("*.ipynb")
                if not p.name.endswith(("_output.ipynb", "_executed.ipynb"))
            )
        except OSError:
            return None
    else:
        siblings = sibling_notebooks

    if notebook_path not in siblings:
        return None
    idx = siblings.index(notebook_path)
    successors = siblings[idx + 1:]
    for sib in successors:
        try:
            nb = _read_notebook(sib)
        except (OSError, json.JSONDecodeError):
            continue
        sib_hits = _scan_engine(nb, current_spec)
        if sib_hits.wiring_hits and sib_hits.proof_hits:
            return True
    return False


def classify_notebook(
    notebook_path: Path, notebook: dict,
    engine_keys: Optional[List[str]] = None,
    sibling_cache: Optional[Dict[Path, List[Path]]] = None,
) -> Dict[str, dict]:
    """Classifie un notebook par moteur, retourne un dict {engine_key: {verdict, evidence}}."""
    if engine_keys is None:
        engine_keys = list(ENGINE_REGISTRY.keys())

    siblings: Optional[List[Path]] = None
    if sibling_cache is not None:
        siblings = sibling_cache.get(notebook_path.parent.resolve())

    results: Dict[str, dict] = {}
    for key in engine_keys:
        spec = ENGINE_REGISTRY[key]
        hits = _scan_engine(notebook, spec)

        # Si aucun claim, on ne declenche rien (moteur non pertinent pour ce notebook)
        if not hits.claim_hits:
            continue

        # Croisement
        has_wiring = bool(hits.wiring_hits)
        has_proof = bool(hits.proof_hits)
        has_simulation = bool(hits.simulation_hits)
        disclosed = _is_disclosed_deterministic(notebook)

        # Verdict
        # Regle fondamentale : sans wiring (import SDK), un proof (output)
        # ne peut pas etre attribue au moteur claim. Un print(10) sans
        # import bigquery n'est pas une preuve d'execution BigQuery.
        if has_wiring and has_proof and not has_simulation:
            verdict = "ENGINE_EXEC_PROVED"
        elif disclosed and (siblings is None or _detect_disclosed_sequence(notebook_path, spec, hits, siblings) is True):
            verdict = "DISCLOSED_SEQUENCE_PROVED"
        elif has_wiring and not has_proof:
            verdict = "WIRING_ONLY"
        elif has_simulation:
            verdict = "SIMULATED_TERMINAL"
        elif not has_wiring:
            verdict = "NAMED_NOT_INVOKED"
        else:
            verdict = "UNMEASURED"

        results[key] = {
            "verdict": verdict,
            "claims": hits.claim_hits[:5],
            "wiring": hits.wiring_hits[:3],
            "proof": hits.proof_hits[:3],
            "simulation": hits.simulation_hits[:3],
            "disclosed_deterministic": disclosed,
        }

    return results


# --- Iteration repo --------------------------------------------------------

_EXCLUDED_SUFFIXES = ("_output.ipynb", "_executed.ipynb")


def _iter_notebooks(root: Path):
    """Yield notebooks .ipynb sous root, en excluant les artefacts d'execution."""
    for p in sorted(root.rglob("*.ipynb")):
        if p.name.endswith(_EXCLUDED_SUFFIXES):
            continue
        yield p


def _build_sibling_cache(notebooks: List[Path]) -> Dict[Path, List[Path]]:
    """Regroupe les notebooks par dossier parent pour la detection sequence-aware."""
    cache: Dict[Path, List[Path]] = {}
    for nb in notebooks:
        key = nb.parent.resolve()
        cache.setdefault(key, []).append(nb)
    for k in cache:
        cache[k] = sorted(cache[k])
    return cache


# --- Scan entry points -----------------------------------------------------

def scan_notebook(path: Path, engine_keys: Optional[List[str]] = None) -> Dict[str, dict]:
    """Scan un seul notebook."""
    nb = _read_notebook(path)
    siblings = sorted(
        p for p in path.parent.glob("*.ipynb")
        if not p.name.endswith(_EXCLUDED_SUFFIXES)
    )
    return classify_notebook(path, nb, engine_keys, {path.parent.resolve(): siblings})


def scan_repo(
    root: Path, engine_keys: Optional[List[str]] = None,
) -> Dict[str, Dict[str, dict]]:
    """Scan tous les notebooks d'un repo. Retourne {notebook_path: {engine: verdict}}."""
    notebooks = list(_iter_notebooks(root))
    cache = _build_sibling_cache(notebooks)
    out: Dict[str, Dict[str, dict]] = {}
    for nb in notebooks:
        try:
            data = _read_notebook(nb)
        except (OSError, json.JSONDecodeError) as e:
            out[str(nb)] = {"_error": str(e)}
            continue
        results = classify_notebook(nb, data, engine_keys, cache)
        if results:
            out[str(nb)] = results
    return out


# --- CLI -------------------------------------------------------------------

def _format_report(scan_results: Dict[str, Dict[str, dict]]) -> str:
    lines: List[str] = []
    total_by_verdict: Dict[str, int] = {}
    for nb_path, results in scan_results.items():
        if "_error" in results:
            lines.append(f"[ERROR] {nb_path}: {results['_error']}")
            continue
        for engine_key, info in results.items():
            v = info["verdict"]
            total_by_verdict[v] = total_by_verdict.get(v, 0) + 1
            lines.append(f"[{v:30s}] engine={engine_key:14s} {nb_path}")
    lines.append("")
    lines.append("=== Totaux par verdict ===")
    for v, count in sorted(total_by_verdict.items(), key=lambda x: -x[1]):
        lines.append(f"  {v}: {count}")
    return "\n".join(lines)


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Audit notebooks naming an engine/LLM without invoking it.",
    )
    parser.add_argument("--scan", type=Path, help="Scan a single notebook")
    parser.add_argument("--scan-all", type=Path, nargs="?", const=Path("."),
                        help="Scan all notebooks under PATH (default: cwd)")
    parser.add_argument("--engine", action="append", default=None,
                        help="Restrict to one or more engine keys (default: all)")
    parser.add_argument("--json", action="store_true", help="JSON output")
    parser.add_argument("--check", action="store_true",
                        help="Exit 1 if any NAMED_NOT_INVOKED or SIMULATED_TERMINAL found")
    args = parser.parse_args(argv)

    engine_keys = args.engine
    if args.scan:
        results = {str(args.scan): scan_notebook(args.scan, engine_keys)}
    elif args.scan_all is not None:
        results = scan_repo(args.scan_all, engine_keys)
    else:
        parser.error("Either --scan or --scan-all required")

    if args.json:
        print(json.dumps(results, indent=2, ensure_ascii=False))
    else:
        print(_format_report(results))

    if args.check:
        defects = 0
        for nb_results in results.values():
            for info in nb_results.values():
                if isinstance(info, dict) and info.get("verdict") in (
                    "NAMED_NOT_INVOKED", "SIMULATED_TERMINAL",
                ):
                    defects += 1
        return 1 if defects > 0 else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())