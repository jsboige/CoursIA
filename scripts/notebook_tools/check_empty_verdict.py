"""Detect a verdict asserted on an INVALID measurement in a committed output.

Issue #21750. Measured instance: ``MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb``
(cell 25, ``test_logit_bias_consistency``), at the head of PR #21162.

The cell measures one endpoint, then prints a conclusion:

    === Test logit_bias sur endpoint 'vllm-qwen3.6' ===
    Statut HTTP avec logit_bias: 200
    Réponse avec logit_bias:
    Statut HTTP sans logit_bias (1): 200
    Réponse sans logit_bias (1):
    ...
    => Cohérence vérifiée : les deux appels sans logit_bias avec la même seed renvoient la même réponse.
    => Aucune différence détectée. Le logit_bias n'a pas eu d'effet apparent.

The endpoint returned HTTP 200 with an EMPTY body on the three calls. Two empty
strings are trivially identical, so "cohérence vérifiée" measures nothing, and
"aucune différence détectée" is a conclusion drawn between nothing and nothing --
a reader takes it for an experimental result. The same class appears one block
above, on the OpenAI endpoint: the biased call answers HTTP 400 (empty body),
and the cell still concludes "Différence détectée entre AVEC et SANS logit_bias"
by comparing a failed call with a successful one.

This is the #18395 family ("degraded output validated anyway"), one level
further from the tool-failure banners: no tool is missing here, the tool
answered -- with nothing.

WHY AN ABSOLUTE DETECTOR, NOT A RATCHET
----------------------------------------
The sibling organs of this family (``check_output_failure_text.py``,
``check_output_collapse.py``) ratchet a count between the merge base and HEAD.
That shape cannot see this defect: the bad verdict is PRE-EXISTING (it is
already on ``main``), so its count never grows on a PR that merely re-executes
the notebook -- and the PR that FIXES it (the guard turns the verdict into an
explicit failure) also does not "grow" anything. So this organ reports the
ABSOLUTE state of the notebooks it is given: how many conclusions are asserted
on measurements that are empty or in error. ``--diff-base`` narrows the report
to the notebooks a PR touches, which is how a CI job should call it.

WHAT IS REPORTED
----------------
A finding is one BLOCK (a section of one cell's output, delimited by a
``=== ... ===`` header) that carries

  1. at least one CONCLUSION verdict -- a ``=>`` line asserting a measurement
     result (``Cohérence vérifiée``, ``Différence détectée``, ``Aucune
     différence détectée``, ...). Lines starting with ``=> ERREUR`` are NOT
     conclusions: they report a failure explicitly, which is the honest
     behaviour this organ asks for;
  2. and an INVALID measurement -- a response whose body is empty or only
     whitespace, or a non-2xx HTTP status.

The organ does not adjudicate WHICH verdict is wrong: it makes the
co-presence visible, and a human (or the notebook's own guard) decides.

Usage:
    python scripts/notebook_tools/check_empty_verdict.py <notebook|dir> ...
    python scripts/notebook_tools/check_empty_verdict.py --diff-base origin/main <repo>
    python scripts/notebook_tools/check_empty_verdict.py --self-test
    python scripts/notebook_tools/check_empty_verdict.py --json <repo>

Exit codes: 0 = no finding, 1 = finding(s), 2 = could not measure (fail-closed).
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

# Une conclusion : une ligne "=> " qui AFFIRME un resultat de mesure.
VERDICT_RE = re.compile(r"=>\s*(?P<text>.+)$")
CONCLUSION_RE = re.compile(
    r"(?i)\b(coh[ée]rence|coherence|diff[ée]rence|difference|identique|conforme)\b"
)
# Une ligne d'ERREUR explicite n'est pas une conclusion : elle signale l'echec.
ERROR_VERDICT_RE = re.compile(r"(?i)^=>\s*erreur\b")

# Une reponse : "Reponse ...: <corps>" (le corps peut etre vide).
RESPONSE_RE = re.compile(r"(?i)\br[ée]ponse\b[^:]*:\s?(?P<value>.*)$")
# Un statut HTTP : "Statut HTTP ...: 200"
STATUS_RE = re.compile(r"(?i)\bstatut http\b[^:]*:\s*(?P<code>\d{3})")

# Un bloc : un en-tete de section "=== ... ===" ouvre un bloc.
BLOCK_HEADER_RE = re.compile(r"===.*===")


def _strip_ansi(text: str) -> str:
    return re.sub(r"\x1b\[[0-9;]*m", "", text)


def cell_output_text(cell: dict) -> str:
    parts: list[str] = []
    for out in cell.get("outputs") or []:
        otype = out.get("output_type")
        if otype == "stream":
            parts.append("".join(out.get("text") or []))
        elif otype in ("execute_result", "display_data"):
            text = out.get("text")
            if isinstance(text, list):
                parts.append("".join(text))
            elif isinstance(text, str):
                parts.append(text)
            elif "data" in out:
                data = out.get("data") or {}
                plain = data.get("text/plain")
                if isinstance(plain, list):
                    parts.append("".join(plain))
                elif isinstance(plain, str):
                    parts.append(plain)
    return _strip_ansi("\n".join(parts))


def split_blocks(text: str) -> list[tuple[str, list[str]]]:
    """Decoupe la sortie en blocs, un par en-tete '=== ... ==='."""
    blocks: list[tuple[str, list[str]]] = []
    title = ""
    current: list[str] = []
    for line in text.splitlines():
        if BLOCK_HEADER_RE.search(line):
            if current:
                blocks.append((title, current))
            title = line.strip()
            current = []
        else:
            current.append(line)
    if current:
        blocks.append((title, current))
    return blocks


def analyse_block(title: str, lines: list[str]) -> dict | None:
    """Rend un finding si le bloc conclut sur une mesure invalide, sinon None."""
    verdicts: list[str] = []
    empty_answers: list[str] = []
    bad_statuses: list[str] = []

    for raw in lines:
        line = raw.rstrip()
        m = VERDICT_RE.search(line)
        if m:
            text = m.group("text").strip()
            if not ERROR_VERDICT_RE.match("=> " + text) and CONCLUSION_RE.search(text):
                verdicts.append(text)
            continue
        s = STATUS_RE.search(line)
        if s:
            code = s.group("code")
            if not code.startswith("2"):
                bad_statuses.append(code)
            continue
        r = RESPONSE_RE.search(line)
        if r:
            if not r.group("value").strip():
                label = line[r.start():].split(":", 1)[0].strip()
                empty_answers.append(label[-60:])

    if not verdicts:
        return None
    reasons: list[str] = []
    if empty_answers:
        reasons.append(
            f"{len(empty_answers)} reponse(s) vide(s) [{empty_answers[0]}]"
        )
    if bad_statuses:
        reasons.append(
            f"statut HTTP non-2xx [{', '.join(sorted(set(bad_statuses)))}]"
        )
    if not reasons:
        return None
    return {
        "block": title,
        "verdicts": verdicts,
        "reasons": reasons,
    }


def analyse_notebook(path: Path) -> list[dict]:
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:  # pragma: no cover - illisible = non mesurable
        raise ValueError(f"illisible: {exc}") from exc
    findings: list[dict] = []
    for idx, cell in enumerate(nb.get("cells") or []):
        if cell.get("cell_type") != "code":
            continue
        text = cell_output_text(cell)
        if not text.strip():
            continue
        for title, lines in split_blocks(text):
            hit = analyse_block(title, lines)
            if hit:
                hit["cell_index"] = idx
                hit["cell_id"] = cell.get("id") or ""
                findings.append(hit)
    return findings


def _changed_notebooks(base: str, root: Path) -> set[str]:
    try:
        out = subprocess.run(
            ["git", "-C", str(root), "diff", "--name-only", base, "--", "*.ipynb"],
            capture_output=True, text=True, encoding="utf-8", errors="replace", check=True,
        ).stdout
    except Exception:
        return set()
    return {line.strip().replace("\\", "/") for line in out.splitlines() if line.strip()}


def iter_notebooks(targets: list[str]) -> list[Path]:
    out: list[Path] = []
    for raw in targets:
        p = Path(raw)
        if p.is_dir():
            out.extend(sorted(p.rglob("*.ipynb")))
        elif p.suffix == ".ipynb":
            out.append(p)
    return out


SELFTEST_BLOCKS = {
    "empty": [
        "=== Test logit_bias sur endpoint 'vllm-qwen3.6' ===",
        "Statut HTTP avec logit_bias: 200",
        "Reponse avec logit_bias:",
        "Statut HTTP sans logit_bias (1): 200",
        "Reponse sans logit_bias (1):",
        "=> Coherence verifiee : les deux appels renvoient la meme reponse.",
        "=> Aucune difference detectee. Le logit_bias n'a pas eu d'effet apparent.",
    ],
    "http_error": [
        "=== Test logit_bias sur endpoint 'OpenAI' ===",
        "Statut HTTP avec logit_bias: 400",
        "Reponse avec logit_bias:",
        "Statut HTTP sans logit_bias (1): 200",
        "Reponse sans logit_bias (1): Je suis un assistant IA",
        "=> Coherence verifiee : les deux appels renvoient la meme reponse.",
        "=> Difference detectee entre AVEC et SANS logit_bias.",
    ],
    "clean": [
        "=== Test logit_bias sur endpoint 'local-mini-v2' ===",
        "Statut HTTP avec logit_bias: 200",
        "Reponse avec logit_bias: Salut! J'ai appele Qwen.",
        "Statut HTTP sans logit_bias (1): 200",
        "Reponse sans logit_bias (1): Bonjour! Je suis Qwen",
        "=> Coherence verifiee : les deux appels renvoient la meme reponse.",
        "=> Difference detectee entre AVEC et SANS logit_bias.",
    ],
    "explicit_error": [
        "=== Test seed sur endpoint 'x' ===",
        "Statut HTTP avec seed: 200",
        "Reponse avec seed:",
        "=> ERREUR : les deux appels renvoient des reponses differentes.",
    ],
    "no_verdict": [
        "=== Test temperature sur endpoint 'y' ===",
        "Statut HTTP: 200",
        "Reponse: ",
    ],
}


def self_test() -> int:
    """Rejoue des blocs synthetiques : la forme doit se valider par ses faux negatifs."""
    expectations = {
        "empty": True,        # reponse vide + verdict  -> finding
        "http_error": True,   # statut non-2xx + verdict -> finding
        "clean": False,       # tout valide            -> silence
        "explicit_error": False,  # un echec explicite n'est pas une conclusion
        "no_verdict": False,  # pas de verdict         -> silence
    }
    failures = []
    for name, expect_finding in expectations.items():
        hit = analyse_block("selftest", SELFTEST_BLOCKS[name])
        got = hit is not None
        if got != expect_finding:
            failures.append(f"{name}: attendu finding={expect_finding}, obtenu {got}")
    if failures:
        print("SELFTEST KO :")
        for f in failures:
            print(f"  - {f}")
        return 1
    print(f"SELFTEST OK ({len(expectations)} blocs synthetiques)")
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("targets", nargs="*", help="carnets ou repertoires")
    ap.add_argument("--diff-base", dest="diff_base", default=None,
                    help="ne rapporter que les carnets modifies par rapport a cette base")
    ap.add_argument("--json", action="store_true", dest="as_json")
    ap.add_argument("--self-test", action="store_true", dest="self_test")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()
    if not args.targets:
        ap.error("cible(s) requise(s), ou --self-test")

    notebooks = iter_notebooks(args.targets)
    if args.diff_base:
        changed = _changed_notebooks(args.diff_base, Path(args.targets[0]))
        kept = []
        for nb_path in notebooks:
            try:
                rel = nb_path.resolve().relative_to(Path(args.targets[0]).resolve())
            except ValueError:
                kept.append(nb_path)
                continue
            if rel.as_posix() in changed:
                kept.append(nb_path)
        notebooks = kept

    findings: list[dict] = []
    unreadable: list[str] = []
    for nb_path in notebooks:
        try:
            hits = analyse_notebook(nb_path)
        except ValueError as exc:
            unreadable.append(f"{nb_path}: {exc}")
            continue
        for hit in hits:
            findings.append({"notebook": str(nb_path), **hit})

    report = {
        "notebooks_scanned": len(notebooks),
        "findings": findings,
        "unreadable": unreadable,
    }
    if args.as_json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        print(f"carnets scannes : {report['notebooks_scanned']}")
        print(f"finding(s) : {len(findings)}")
        for f in findings:
            print(f"  - {f['notebook']} cellule {f['cell_index']} "
                  f"[{f['block'][:70]}]")
            for v in f["verdicts"]:
                print(f"      verdict : {v[:110]}")
            for r in f["reasons"]:
                print(f"      mesure invalide : {r}")
        for u in unreadable:
            print(f"  ! non mesurable : {u}")
    if unreadable:
        return 2
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
