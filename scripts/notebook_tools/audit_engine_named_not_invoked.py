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

Ce scanner croise **quatre surfaces** par notebook :

* **claim** : prose (markdown), titre, objectifs -- emploie un moteur avec
  un verbe d'execution/integration ;
* **wiring** : code source -- import ou client officiel disponible ;
* **invocation** : appel top-level du SDK/binaire, direct ou via un helper
  notebook-wide effectivement appele ;
* **proof** : output attribuable a cette invocation, sans marqueur de
  simulation/fallback.

Un notebook sans wiring local peut etre admissible uniquement si :

1. il se declare explicitement deterministe/sans LLM ;
2. la meme sequence (dossier-serie) reference un notebook successeur ;
3. ce successeur apporte wiring **et outputs reels**.

## Verdicts (5)

| Verdict | Sens |
|---|---|
| ``ENGINE_EXEC_PROVED`` | claim + wiring + invocation + output attribuable |
| ``DISCLOSED_SEQUENCE_PROVED`` | notebook deterministe declare + successeur avec wiring/invocation/proof dans la meme serie |
| ``WIRING_ONLY`` | import present mais aucune invocation prouvee (cle absente, exec gate par env, etc.) |
| ``SIMULATED_TERMINAL`` | outputs = simulation/fallback, pas de successeur avec wiring |
| ``NAMED_NOT_INVOKED`` | claim present mais zero import/wiring |

## Registre moteur (extensible)

Chaque entree porte : ``imports`` (regex sur code source), ``claims`` (regex
sur prose markdown), ``invocations`` (regex sur code top-level),
``proof_markers`` et ``simulation_markers`` (regex sur outputs). Le registre
est explicite -- aucune heuristique opaque.

Usage::

    python audit_engine_named_not_invoked.py --scan <notebook.ipynb>
    python audit_engine_named_not_invoked.py --scan-all
    python audit_engine_named_not_invoked.py --scan-all --check   # exit 1 si NAMED_NOT_INVOKED/SIMULATED_TERMINAL
    python audit_engine_named_not_invoked.py --scan-all --json
"""
from __future__ import annotations

import argparse
import ast
import io
import json
import re
import sys
import tokenize
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Tuple


# --- Registre moteur -------------------------------------------------------

@dataclass(frozen=True)
class EngineSpec:
    """Specification explicite d'un moteur dans le registre."""

    key: str
    label: str
    imports: Tuple[str, ...]
    claims: Tuple[str, ...]
    invocations: Tuple[str, ...]
    proof_markers: Tuple[str, ...]
    simulation_markers: Tuple[str, ...]
    recoverability: str = "RECOVERABLE-LOCAL"
    notes: str = ""


ENGINE_REGISTRY: Dict[str, EngineSpec] = {
    "google_adk": EngineSpec(
        key="google_adk",
        label="Google ADK",
        imports=(r"\bgoogle\.adk\b", r"\bfrom\s+google\s+import\s+adk\b"),
        claims=(r"\bgoogle\s+adk\b", r"\badk\s+(?:agent|runtime|reel)\b"),
        invocations=(r"\b(?:Agent|Runner|InMemoryRunner)\s*\(", r"\brunner\.run"),
        proof_markers=(r"\bagent\b", r"\b(?:runner|session)\b"),
        simulation_markers=(r"class\s+(?:Mock|Fake)Agent", r"#\s*simulated\s+adk", r"\bsdk\s+fictif\b"),
        notes="Track2-GoogleADK : claims sans import `google.adk` detectes en 2026-09.",
    ),
    "openai_llm": EngineSpec(
        key="openai_llm",
        label="OpenAI/Anthropic/LiteLLM (LLM reel)",
        imports=(r"\bopenai\b", r"\banthropic\b", r"\blitellm\b"),
        claims=(
            r"\bgpt-(?:[345]|4o)\b", r"\bclaude-(?:opus|sonnet|haiku)\b",
            r"\bGPT\s*/\s*Claude\b", r"\bappel\s+(?:a|au)\s+(?:gpt|claude|llm)\b",
            r"\b(?:avec|via)\s+(?:gpt|claude|llm)\b", r"\bllm\s+reel\b",
        ),
        invocations=(
            r"\b(?:responses|completions|messages)\.create\s*\(",
            r"\b(?:completion|acompletion)\s*\(",
        ),
        proof_markers=(r".+",),
        simulation_markers=(
            r"reponse\s+simulee", r"simulated\s+response", r"mock\s+response",
            r"mode\s+mock", r"genere\s+par\s+llm\s*\(mock\)",
        ),
        recoverability="RECOVERABLE-USER-HAND",
        notes="Une cle absente ne justifie jamais un output mock presente comme resultat LLM.",
    ),
    "bigquery": EngineSpec(
        key="bigquery",
        label="Google BigQuery / BQML",
        imports=(r"\bgoogle\.cloud\.bigquery\b", r"\bfrom\s+google\.cloud\s+import\s+bigquery\b"),
        claims=(r"\bbigquery\b", r"\bBQML\b", r"\bML\.PREDICT\b"),
        invocations=(r"\b(?:client\.)?(?:query|create_dataset|get_table|insert_rows)\s*\(",),
        proof_markers=(r"\b(?:dataset|table|query|job)\b",),
        simulation_markers=(r"schema\s+simul", r"donnees\s+simulees", r"bigquery\s+simul"),
        recoverability="RECOVERABLE-USER-HAND",
    ),
    "foundry": EngineSpec(
        key="foundry",
        label="Foundry / Forge",
        imports=(r"\bforge_helper\b", r"\bsubprocess\b", r"\bshutil\.which\s*\(\s*['\"]forge['\"]"),
        claims=(r"\bfoundry\b", r"\bforge\s+(?:build|test|script)\b", r"\bfuzz(?:ing|\s+test)?\b"),
        invocations=(
            r"\bforge_(?:compile|compile_and_deploy)\s*\(",
            r"\bsubprocess\.(?:run|check_call|check_output|Popen)"
            r"\s*\([\s\S]{0,300}?\[\s*forge\b",
        ),
        proof_markers=(r"\b(?:compilation\s+reussie|compiler run|suite result|test result|tests? passed|bytecode)\b",),
        simulation_markers=(r"\bsortie\s+attendue\b", r"\bexpected\s+output\b", r"\bforge\s+non\s+installe\b"),
    ),
    "solc": EngineSpec(
        key="solc",
        label="Solidity compiler / SMTChecker",
        imports=(r"\bsolcx\b", r"\bsubprocess\b", r"\bshutil\.which\s*\(\s*['\"]solc['\"]"),
        claims=(r"\bsolc\b", r"\bSMTChecker\b", r"\bcompil(?:er|ation).*solidity\b"),
        invocations=(
            r"\bsolcx\.compile_(?:source|standard)\s*\(",
            r"\bsubprocess\.(?:run|check_output)\s*\([\s\S]{0,300}?\bsolc\b",
        ),
        proof_markers=(r"\b(?:compiled|compilation|bytecode|warning|error|smtchecker)\b",),
        simulation_markers=(r"\bsortie\s+attendue\b", r"\bsolc\s+non\s+(?:installe|disponible)\b"),
    ),
    "bitcoinlib": EngineSpec(
        key="bitcoinlib",
        label="python-bitcoinlib",
        imports=(r"\bbitcoin(?:\.core|\.wallet|\.signmessage)?\b", r"\bfrom\s+bitcoin\b"),
        claims=(r"\bpython-bitcoinlib\b", r"\bbitcoin\s+(?:script|signature|transaction)\b"),
        invocations=(r"\b(?:VerifyScript|SignatureHash|CBitcoinSecret|CMutableTransaction)\s*\(",),
        proof_markers=(r"\b(?:signature|script|transaction|txid|verification)\b",),
        simulation_markers=(r"\b(?:ficti(?:f|ve)|simul(?:e|ee)|toy)\b", r"python-bitcoinlib\s+non\s+installe"),
    ),
    "solders": EngineSpec(
        key="solders",
        label="Solana solders",
        imports=(r"\bsolders\b",),
        claims=(r"\bsolana\b", r"\bprogram\s+derived\s+address\b", r"\bPDA\b"),
        invocations=(r"\bPubkey\.(?:find_program_address|create_program_address)\s*\(",),
        proof_markers=(r"\b(?:pda|program\s+address|bump)\b",),
        simulation_markers=(r"\b(?:pda|solana).*simul", r"first\s+byte\s*<\s*128"),
    ),
    "sui_cli": EngineSpec(
        key="sui_cli",
        label="Sui CLI",
        imports=(r"\bsubprocess\b", r"\bshutil\.which\s*\(\s*['\"]sui['\"]"),
        claims=(r"\bsui\s+move\s+(?:build|test)\b", r"\bsui\s+cli\b"),
        invocations=(r"\bsubprocess\.(?:run|check_output)\s*\([^\n]*\bsui\b",),
        proof_markers=(r"\b(?:build|test result|tests? passed|move)\b",),
        simulation_markers=(r"\bsui\s+(?:non\s+installe|simul)", r"\bobjet.*dictionnaire\b"),
    ),
    "electionguard": EngineSpec(
        key="electionguard",
        label="Microsoft ElectionGuard",
        imports=(r"\belectionguard\b",),
        claims=(r"\belectionguard\b",),
        invocations=(r"\b(?:ElectionBuilder|encrypt_ballot|decrypt)\s*\(",),
        proof_markers=(r"\b(?:election|ballot|tally|ciphertext)\b",),
        simulation_markers=(r"electionguard\s+(?:non\s+installe|indisponible)", r"\brenvoi\s+documentaire\b"),
    ),
    "concrete": EngineSpec(
        key="concrete",
        label="Zama Concrete",
        imports=(r"\bconcrete(?:\.fhe)?\b",),
        claims=(r"\bconcrete(?:-python)?\b", r"\bzama\b"),
        invocations=(r"\bcompiler\.compile\s*\(", r"\bcircuit\.(?:encrypt_run_decrypt|keygen)\s*\(",),
        proof_markers=(r"\b(?:circuit|fhe|encrypted|decrypted)\b",),
        simulation_markers=(r"concrete.*(?:non\s+installe|indisponible|skip)",),
        recoverability="RECOVERABLE-MACHINE",
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
    """Resultat du croisement des surfaces pour un moteur."""

    claim_hits: List[Tuple[int, str]] = field(default_factory=list)
    wiring_hits: List[Tuple[int, str]] = field(default_factory=list)
    invocation_hits: List[Tuple[int, str]] = field(default_factory=list)
    proof_hits: List[Tuple[int, str]] = field(default_factory=list)
    simulation_hits: List[Tuple[int, str]] = field(default_factory=list)


def _strip_comments_and_strings(src: str) -> str:
    """Remove Python comments and strings while preserving token positions."""
    try:
        tokens = tokenize.generate_tokens(io.StringIO(src).readline)
        kept = [
            token._replace(string="")
            if token.type in (tokenize.COMMENT, tokenize.STRING)
            else token
            for token in tokens
        ]
        return tokenize.untokenize(kept)
    except (IndentationError, tokenize.TokenError):
        return ""



def _defined_helpers(src: str, spec: EngineSpec) -> set[str]:
    """Return helper functions whose body invokes the selected engine."""
    try:
        tree = ast.parse(src)
    except SyntaxError:
        return set()

    helpers: set[str] = set()
    for node in tree.body:
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        segment = ast.get_source_segment(src, node) or ""
        active = _strip_comments_and_strings(segment)
        if any(re.search(pattern, active, re.IGNORECASE) for pattern in spec.invocations):
            helpers.add(node.name)
    return helpers


def _top_level_active_code(src: str) -> str:
    """Remove function/class definitions while preserving top-level statements."""
    try:
        tree = ast.parse(src)
    except SyntaxError:
        return _strip_comments_and_strings(src)

    lines = src.splitlines(keepends=True)
    for node in tree.body:
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        start = max(node.lineno - 1, 0)
        end = node.end_lineno or node.lineno
        for index in range(start, min(end, len(lines))):
            lines[index] = "\n" if lines[index].endswith("\n") else ""
    return _strip_comments_and_strings("".join(lines))


def _top_level_helper_call(src: str, helper_names: set[str]) -> Optional[str]:
    """Return a top-level call to an engine helper, ignoring its definition."""
    if not helper_names:
        return None
    try:
        tree = ast.parse(src)
    except SyntaxError:
        return None

    for node in tree.body:
        for candidate in ast.walk(node):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                break
            if isinstance(candidate, ast.Call) and isinstance(candidate.func, ast.Name):
                if candidate.func.id in helper_names:
                    return candidate.func.id
    return None


def _scan_engine(notebook: dict, spec: EngineSpec) -> SurfaceHits:
    hits = SurfaceHits()
    cells = notebook.get("cells", [])
    helper_names: set[str] = set()
    for cell in cells:
        if cell.get("cell_type") == "code":
            helper_names.update(_defined_helpers(_cell_source(cell), spec))

    for idx, cell in enumerate(cells):
        ctype = cell.get("cell_type", "")
        src = _cell_source(cell)
        out_text = _cell_output_text(cell) if ctype == "code" else ""
        code_clean = _strip_comments_and_strings(src) if ctype == "code" else ""

        if ctype == "markdown":
            for pattern in spec.claims:
                match = re.search(pattern, src, re.IGNORECASE)
                if match:
                    hits.claim_hits.append((idx, match.group(0)[:80]))
                    break

        if ctype != "code":
            continue

        cell_is_simulation = False
        for pattern in spec.simulation_markers:
            source_match = re.search(pattern, src, re.IGNORECASE)
            output_match = re.search(pattern, out_text, re.IGNORECASE)
            if source_match or output_match:
                marker = (source_match or output_match).group(0)
                hits.simulation_hits.append((idx, marker[:80]))
                cell_is_simulation = True
                break

        for pattern in spec.imports:
            match = re.search(pattern, code_clean, re.IGNORECASE)
            if match:
                hits.wiring_hits.append((idx, match.group(0)[:80]))
                break

        invocation: Optional[str] = None
        top_level_code = _top_level_active_code(src)
        for pattern in spec.invocations:
            match = re.search(pattern, top_level_code, re.IGNORECASE)
            if match:
                invocation = match.group(0)
                break
        if invocation is None:
            invocation = _top_level_helper_call(src, helper_names)
        if invocation:
            hits.invocation_hits.append((idx, invocation[:80]))

        output_proves_engine = any(
            re.search(pattern, out_text, re.IGNORECASE | re.DOTALL)
            for pattern in spec.proof_markers
        )
        if invocation and output_proves_engine and not cell_is_simulation:
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
        has_invocation = bool(hits.invocation_hits)
        has_proof = bool(hits.proof_hits)
        has_simulation = bool(hits.simulation_hits)
        disclosed = _is_disclosed_deterministic(notebook)

        # Verdict
        # Regle fondamentale : sans wiring (import SDK), un proof (output)
        # ne peut pas etre attribue au moteur claim. Un print(10) sans
        # import bigquery n'est pas une preuve d'execution BigQuery.
        if has_wiring and has_invocation and has_proof and not has_simulation:
            verdict = "ENGINE_EXEC_PROVED"
        elif disclosed and (siblings is None or _detect_disclosed_sequence(notebook_path, spec, hits, siblings) is True):
            verdict = "DISCLOSED_SEQUENCE_PROVED"
        elif has_simulation:
            # Simulation detectee : un import SDK + un output simule = le wiring
            # est cosmétique, le moteur reel n'est pas invoqué. Prend precedence
            # sur WIRING_ONLY car le verdict `SIMULATED_TERMINAL` est plus
            # informatif pour le lecteur (cycle 93 feedback).
            verdict = "SIMULATED_TERMINAL"
        elif has_wiring and (not has_invocation or not has_proof):
            verdict = "WIRING_ONLY"
        elif not has_wiring:
            verdict = "NAMED_NOT_INVOKED"
        else:
            verdict = "UNMEASURED"

        results[key] = {
            "verdict": verdict,
            "claims": hits.claim_hits[:5],
            "wiring": hits.wiring_hits[:3],
            "invocation": hits.invocation_hits[:3],
            "proof": hits.proof_hits[:3],
            "simulation": hits.simulation_hits[:3],
            "recoverability": (
                "SOTA-OK"
                if verdict in ("ENGINE_EXEC_PROVED", "DISCLOSED_SEQUENCE_PROVED")
                else spec.recoverability
            ),
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

_VERDICT_SEVERITY = {
    "ENGINE_EXEC_PROVED": 0,
    "DISCLOSED_SEQUENCE_PROVED": 0,
    "WIRING_ONLY": 1,
    "NAMED_NOT_INVOKED": 2,
    "SIMULATED_TERMINAL": 3,
    "UNMEASURED": 3,
}


def compare_scan_results(
    base: Dict[str, Dict[str, dict]],
    head: Dict[str, Dict[str, dict]],
) -> List[dict]:
    """Return only newly introduced or worsened engine verdicts."""
    regressions: List[dict] = []
    for notebook_path, head_engines in head.items():
        if "_error" in head_engines:
            continue
        base_engines = base.get(notebook_path, {})
        for engine_key, head_info in head_engines.items():
            if not isinstance(head_info, dict) or "verdict" not in head_info:
                continue
            head_verdict = head_info["verdict"]
            head_severity = _VERDICT_SEVERITY.get(head_verdict, 3)
            base_info = base_engines.get(engine_key, {})
            base_verdict = base_info.get("verdict", "NOT_CLAIMED")
            base_severity = _VERDICT_SEVERITY.get(base_verdict, 0)
            if head_severity > base_severity:
                regressions.append({
                    "notebook": notebook_path,
                    "engine": engine_key,
                    "base_verdict": base_verdict,
                    "head_verdict": head_verdict,
                    "recoverability": head_info.get("recoverability"),
                    "evidence": {
                        "claim": head_info.get("claims", [])[:1],
                        "wiring": head_info.get("wiring", [])[:1],
                        "invocation": head_info.get("invocation", [])[:1],
                        "proof": head_info.get("proof", [])[:1],
                        "simulation": head_info.get("simulation", [])[:1],
                    },
                })
    return regressions


def _load_scan_snapshot(path: Path) -> Dict[str, Dict[str, dict]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError("scan snapshot must contain a JSON object")
    return data


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
                        help="Exit 1 if a deficient verdict is found")
    parser.add_argument("--compare-base", type=Path,
                        help="Compare two JSON scan snapshots")
    parser.add_argument("--compare-head", type=Path,
                        help="Head snapshot paired with --compare-base")
    args = parser.parse_args(argv)

    if bool(args.compare_base) != bool(args.compare_head):
        parser.error("--compare-base and --compare-head must be used together")

    if args.compare_base:
        if args.scan or args.scan_all is not None:
            parser.error("comparison mode cannot be combined with scan mode")
        try:
            base = _load_scan_snapshot(args.compare_base)
            head = _load_scan_snapshot(args.compare_head)
        except (OSError, json.JSONDecodeError, ValueError) as exc:
            print(f"[ERROR] unable to read scan snapshots: {exc}", file=sys.stderr)
            return 2
        snapshot_errors = [
            path for snapshot in (base, head)
            for path, engines in snapshot.items()
            if isinstance(engines, dict) and "_error" in engines
        ]
        if snapshot_errors:
            print(
                "[ERROR] unreadable notebooks in scan snapshots: "
                + ", ".join(snapshot_errors),
                file=sys.stderr,
            )
            return 2
        regressions = compare_scan_results(base, head)
        payload = {"regressions": regressions, "count": len(regressions)}
        if args.json:
            print(json.dumps(payload, indent=2, ensure_ascii=False))
        else:
            for item in regressions:
                print(
                    f"[REGRESSION] {item['notebook']} engine={item['engine']} "
                    f"{item['base_verdict']} -> {item['head_verdict']}"
                )
            print(f"Engine regressions: {len(regressions)}")
        return 1 if regressions else 0

    engine_keys = args.engine
    try:
        if args.scan:
            results = {str(args.scan): scan_notebook(args.scan, engine_keys)}
        elif args.scan_all is not None:
            results = scan_repo(args.scan_all, engine_keys)
        else:
            parser.error("Either --scan or --scan-all required")
    except (OSError, json.JSONDecodeError) as exc:
        print(f"[ERROR] unable to read notebook: {exc}", file=sys.stderr)
        return 2

    if args.json:
        print(json.dumps(results, indent=2, ensure_ascii=False))
    else:
        print(_format_report(results))

    if any("_error" in nb_results for nb_results in results.values()):
        return 2

    if args.check:
        defects = 0
        for nb_results in results.values():
            for info in nb_results.values():
                if isinstance(info, dict) and _VERDICT_SEVERITY.get(
                    info.get("verdict", "UNMEASURED"), 3
                ) > 0:
                    defects += 1
        return 1 if defects > 0 else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())