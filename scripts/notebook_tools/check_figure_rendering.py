"""Figure-rendering detector: a notebook figure output that will NOT render
where the reader actually reads it -- the visual counterpart of the
``test -f`` trap named by the user on 2026-11-15 (#26690, demand 2).

Founding case, measured firsthand on PR #26613 (head ``0c3387edbb945f1aba3fb247592ad6c967b995b6``,
14/11). The user comment ``Concern: Le SVG n'est pas affiché`` was posted at
22:37:23Z -- AFTER the notebook's last commit (22:16:40Z), so it describes
the current head, not a fixed earlier state. The C# twin
``Z3-20-Machine-de-Goedel-CSharp.ipynb`` carries its four figures (cells 13,
20, 25, 28) as ``text/html`` outputs whose body is one well-formed inline
``<svg>`` element (2492, 5585, 1538 and 104520 chars; 19 to 1546 drawing
elements; every one closed). The SVGs are HEALTHY -- axes, polylines,
legends -- yet invisible on the GitHub notebook renderer, which sanitises
``text/html`` outputs and drops inline SVG, while local viewers (VS Code,
Jupyter) display them fine. A file-existence check passes; a source check
passes; the figure is still not displayed anywhere the reviewer reads.

The class is therefore NOT "broken SVG bytes" but "a figure the reader will
never see". Three findings, all mechanical (each one falsifiable by a
counter-example fixture in ``self_test``):

  SVG_IN_HTML  an output whose ``text/html`` body is DOMINATED by one or more
               well-formed ``<svg>`` elements (see ``DOMINANCE_FRACTION``).
               The figure renders locally but is sanitised away by the GitHub
               renderer -- the founding case. The fix is to emit the SVG as
               the ``image/svg+xml`` mime type (the .NET formatter registers
               ``"text/html"``; registering ``"image/svg+xml"`` displays
               everywhere). Deliberately narrow: a decorative icon inside a
               rich HTML table is NOT flagged, because hiding it does not
               hide a figure.
  BROKEN_SVG   an SVG (inline in ``text/html`` or as ``image/svg+xml``)
               that is truncated (no closing ``</svg>``) or has ZERO drawing
               elements (``path|rect|circle|ellipse|line|polyline|polygon|
               text|image|use``) -- bytes exist, the rendered page is blank.
               Covers the "SVG vide / placeholder" variant of the demand.
  TINY_PNG     an ``image/png`` payload that decodes to fewer than
               ``PNG_FLOOR`` bytes. A PNG with only IHDR+IEND weighs ~100
               bytes; no real figure does. Mechanical emptiness -- NOT a
               perceptual "is this image all white" test, which matplotlib
               can produce legitimately (empty axes) and which would be a
               false-positive factory.

Deliberately NOT implemented (documented so the next reader does not
re-litigate): perceptual blankness of substantial PNGs (legitimate empty
axes), HTML tables using SVG glyphs (not figures), and any judgment on
``application/vnd.*`` widget payloads.

Diff mode (--base <ref>): only cells ADDED, whose SOURCE changed, or whose
OUTPUTS changed since base are judged -- same bounding contract as
``check_source_collapse.py``, so wiring this as a PR ratchet later cannot
turn 950 legacy notebooks red on day one. Census mode (no --base): every
cell of every given notebook is judged; that is the corpus count for the PR
body (rule I of pr-review-discipline: an organ ships with its batch plan).

Exit codes: 0 = no finding (or only exempted), 1 = at least one finding,
2 = usage/IO error. ``--json`` prints one object per run; findings carry
``cell`` (index), ``kind`` and ``evidence`` (a short verbatim excerpt).
"""

from __future__ import annotations

import argparse
import base64
import json
import re
import sys
from pathlib import Path
from typing import Any

SVG_MIME = "image/svg+xml"
HTML_MIME = "text/html"
PNG_MIME = "image/png"

# An inline SVG counts as DOMINATING the HTML body when everything that is
# not an <svg>...</svg> block (and not whitespace) is under this fraction of
# the body. Founding case: the .NET formatter writes the bare SVG -- the
# non-SVG part is 0 %. A table with a small icon stays far above.
DOMINANCE_FRACTION = 0.1

# Under this many decoded bytes, a PNG cannot contain any pixel data.
PNG_FLOOR = 200

DRAW_ELEM_RE = re.compile(
    r"<(?:path|rect|circle|ellipse|line|polyline|polygon|text|image|use)\b",
    re.IGNORECASE,
)
SVG_BLOCK_RE = re.compile(r"<svg\b.*?</svg>", re.DOTALL | re.IGNORECASE)
SVG_OPEN_RE = re.compile(r"<svg\b", re.IGNORECASE)
SVG_CLOSE_RE = re.compile(r"</svg\s*>", re.IGNORECASE)

# Tags that wrap SVG without adding visible content of their own; ignored
# when measuring dominance (the .NET ``<div>`` scaffolding family).
NEUTRAL_TAG_RE = re.compile(r"</?(?:div|span|br|p)\b[^>]*>", re.IGNORECASE)


def _text_of(mime_payload: Any) -> str:
    """Join a Jupyter mime payload (str or list of str) into one string."""
    if isinstance(mime_payload, list):
        return "".join(mime_payload)
    return str(mime_payload)


def _svg_block_ok(block: str) -> bool:
    """True when an ``<svg>...</svg>`` block carries at least one drawing
    element -- i.e. rendering it draws something."""
    return bool(DRAW_ELEM_RE.search(block))


def _analyze_html(html: str) -> list[dict[str, str]]:
    """Findings for one ``text/html`` output payload."""
    blocks = SVG_BLOCK_RE.findall(html)
    if not blocks:
        # An unclosed <svg> with no closing tag is caught here: the block
        # regex needs the close, so look for a lone opener.
        if SVG_OPEN_RE.search(html) and not SVG_CLOSE_RE.search(html):
            return [{"kind": "BROKEN_SVG",
                     "evidence": "unclosed <svg> in text/html"}]
        return []
    residue = SVG_BLOCK_RE.sub("", html)
    residue = NEUTRAL_TAG_RE.sub("", residue)
    residue_non_ws = len("".join(residue.split()))
    total_non_ws = len("".join(html.split()))
    dominant = (
        total_non_ws == 0
        or residue_non_ws <= int(DOMINANCE_FRACTION * total_non_ws)
    )
    broken = [b for b in blocks if not _svg_block_ok(b)]
    if broken:
        return [{"kind": "BROKEN_SVG",
                 "evidence": f"{len(broken)}/{len(blocks)} svg block(s) "
                             f"without any drawing element"}]
    if dominant:
        return [{"kind": "SVG_IN_HTML",
                 "evidence": f"{len(blocks)} well-formed inline svg, "
                             f"mime text/html"}]
    return []


def _analyze_svg_mime(svg: str) -> list[dict[str, str]]:
    """Findings for one ``image/svg+xml`` output payload."""
    stripped = svg.strip()
    if not SVG_OPEN_RE.search(stripped):
        return []  # not an SVG body at all; nothing mechanical to say
    if not SVG_CLOSE_RE.search(stripped):
        return [{"kind": "BROKEN_SVG", "evidence": "unclosed svg payload"}]
    if not DRAW_ELEM_RE.search(stripped):
        return [{"kind": "BROKEN_SVG",
                 "evidence": "svg payload without any drawing element"}]
    return []  # healthy SVG served under its own mime: renders everywhere


def _analyze_png(b64: str) -> list[dict[str, str]]:
    """Findings for one ``image/png`` output payload."""
    try:
        raw = base64.b64decode(_text_of(b64), validate=False)
    except (ValueError, TypeError):
        return [{"kind": "BROKEN_PNG_BASE64",
                 "evidence": "base64 payload does not decode"}]
    if len(raw) < PNG_FLOOR:
        return [{"kind": "TINY_PNG",
                 "evidence": f"{len(raw)} decoded bytes < {PNG_FLOOR}"}]
    return []


def analyze(nb: dict[str, Any]) -> list[dict[str, Any]]:
    """Every figure-rendering finding of one notebook, in cell order.

    A finding is ``{"cell": <index>, "kind": <name>, "evidence": <str>}``.
    """
    findings: list[dict[str, Any]] = []
    for idx, cell in enumerate(nb.get("cells", [])):
        for out in cell.get("outputs", []):
            data = out.get("data", {})
            if not isinstance(data, dict):
                continue
            for mime, payload in data.items():
                if mime == HTML_MIME:
                    found = _analyze_html(_text_of(payload))
                elif mime == SVG_MIME:
                    found = _analyze_svg_mime(_text_of(payload))
                elif mime == PNG_MIME:
                    found = _analyze_png(payload)
                else:
                    continue
                for f in found:
                    findings.append({"cell": idx, **f})
    return findings


def _cell_signature(cell: dict[str, Any]) -> str:
    """Cheap content signature of a cell (source + outputs)."""
    return json.dumps(
        [cell.get("source"), cell.get("outputs")], sort_keys=True
    )


def analyze_diff(base_nb: dict[str, Any], head_nb: dict[str, Any]
                 ) -> list[dict[str, Any]]:
    """Findings restricted to cells added, source-changed or output-changed
    between base and head (ratchet bounding, cf check_source_collapse)."""
    base_cells = base_nb.get("cells", [])
    head_cells = head_nb.get("cells", [])
    if len(head_cells) > len(base_cells):
        new_cells = head_cells[len(base_cells):]
    else:
        new_cells = []
    new_sigs = {_cell_signature(c) for c in new_cells}
    changed_idx: set[int] = set(
        range(len(base_cells), len(head_cells)))
    base_sigs = [_cell_signature(c) for c in base_cells]
    for idx, cell in enumerate(head_cells[:len(base_cells)]):
        if _cell_signature(cell) != base_sigs[idx]:
            changed_idx.add(idx)
    # A cell whose signature matches a NEW cell (content moved) also counts.
    findings = []
    for idx, cell in enumerate(head_cells):
        sig = _cell_signature(cell)
        if idx in changed_idx or sig in new_sigs:
            sub = analyze({"cells": [cell]})
            for f in sub:
                findings.append({"cell": idx,
                                 "kind": f["kind"],
                                 "evidence": f["evidence"]})
    return findings


def run(paths: list[Path], base_ref: str | None = None,
        cwd: Path | None = None) -> dict[str, Any]:
    """Analyse notebooks (files or base/head pairs via git); report object."""
    import subprocess

    wd = cwd or Path.cwd()
    report: dict[str, Any] = {
        "base": base_ref, "notebooks": {}, "counts": {}, "total": 0,
    }
    kinds: dict[str, int] = {}
    for path in paths:
        rel = str(path)
        if base_ref is None:
            nb = json.loads(
                (wd / path).read_text(encoding="utf-8"))
            findings = analyze(nb)
        else:
            def _show(ref: str) -> str:
                return subprocess.run(
                    ["git", "show", f"{ref}:{rel}"], cwd=wd,
                    capture_output=True, text=True, check=True,
                    encoding="utf-8", errors="replace",
                ).stdout
            head_nb = json.loads((wd / path).read_text(encoding="utf-8"))
            try:
                base_nb = json.loads(_show(base_ref))
            except subprocess.CalledProcessError:
                base_nb = {"cells": []}  # notebook is new at head
            findings = analyze_diff(base_nb, head_nb)
        if findings:
            report["notebooks"][rel] = findings
            for f in findings:
                kinds[f["kind"]] = kinds.get(f["kind"], 0) + 1
    report["counts"] = dict(sorted(kinds.items()))
    report["total"] = sum(kinds.values())
    return report


def self_test() -> int:
    """Positive and negative controls, each named after its lesson."""
    def nb(cells: list[dict[str, Any]]) -> dict[str, Any]:
        return {"cells": cells}

    def code_cell(outputs: list[dict[str, Any]]) -> dict[str, Any]:
        return {"cell_type": "code", "source": ["x=1"], "outputs": outputs}

    def out(data: dict[str, Any]) -> dict[str, Any]:
        return {"output_type": "display_data", "data": data}

    healthy_svg = (
        "<svg xmlns='http://www.w3.org/2000/svg' width='10' height='10'>"
        "<rect width='10' height='10' fill='white'/>"
        "<path d='M 0 0 L 10 10' stroke='black'/></svg>"
    )
    empty_svg = (
        "<svg xmlns='http://www.w3.org/2000/svg' width='10' height='10'>"
        "</svg>"
    )
    tiny_png_b64 = base64.b64encode(b"\x89PNG\r\n\x1a\n" + b"x" * 40).decode()

    cases = [
        # name, notebook, expected kinds (sorted)
        ("founding: healthy svg inside text/html -> SVG_IN_HTML",
         nb([code_cell([out({HTML_MIME: [healthy_svg]})])]),
         ["SVG_IN_HTML"]),
        ("net formatter div wrapper still dominated",
         nb([code_cell([out({HTML_MIME: "<div>" + healthy_svg + "</div>"})])]),
         ["SVG_IN_HTML"]),
        ("svg under its own mime renders everywhere -> no finding",
         nb([code_cell([out({SVG_MIME: [healthy_svg]})])]), []),
        ("svg without any drawing element -> BROKEN_SVG",
         nb([code_cell([out({SVG_MIME: [empty_svg]})])]), ["BROKEN_SVG"]),
        ("unclosed svg in html -> BROKEN_SVG",
         nb([code_cell([out({HTML_MIME: healthy_svg[:30]})])]),
         ["BROKEN_SVG"]),
        ("rich html table with small svg icon -> no finding (not dominant)",
         nb([code_cell([out({HTML_MIME:
            "<table><tr><td>results</td></tr></table>" + healthy_svg})])]),
         []),
        ("substantial png -> no finding",
         nb([code_cell([out({PNG_MIME: base64.b64encode(b"x" * 5000).decode()})])]),
         []),
        ("decodes under the floor -> TINY_PNG",
         nb([code_cell([out({PNG_MIME: tiny_png_b64})])]), ["TINY_PNG"]),
        ("text-only output -> no finding",
         nb([code_cell([{"output_type": "stream", "name": "stdout",
                         "text": ["ok"] }])]), []),
    ]
    failures = 0
    for name, notebook, expected in cases:
        got = sorted(f["kind"] for f in analyze(notebook))
        want = sorted(expected)
        if got != want:
            failures += 1
            print(f"SELF-TEST FAIL: {name}: got {got}, want {want}")
        else:
            print(f"self-test ok: {name}")
    # diff bounding: identical cell signature is skipped, changed is judged
    base = nb([code_cell([out({HTML_MIME: [healthy_svg]})]),
               code_cell([out({PNG_MIME: base64.b64encode(b"y" * 5000).decode()})])])
    head_same = nb([code_cell([out({HTML_MIME: [healthy_svg]})]),
                    code_cell([out({PNG_MIME: base64.b64encode(b"y" * 5000).decode()})])])
    head_new = nb([code_cell([out({HTML_MIME: [healthy_svg]})]),
                   code_cell([out({HTML_MIME: [healthy_svg]})])])
    if analyze_diff(base, head_same):
        failures += 1
        print("SELF-TEST FAIL: unchanged notebook must yield no finding")
    else:
        print("self-test ok: diff bounding skips unchanged cells")
    if sorted(f["cell"] for f in analyze_diff(base, head_new)) != [1]:
        failures += 1
        print("SELF-TEST FAIL: added cell must be judged")
    else:
        print("self-test ok: added cell is judged")
    return 1 if failures else 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Detect notebook figure outputs that will not render "
                    "(SVG in text/html, broken SVG, tiny PNG).")
    ap.add_argument("paths", nargs="*",
                    help="notebook paths (census mode)")
    ap.add_argument("--base", metavar="REF", default=None,
                    help="git ref of the base; judge only cells added or "
                         "changed since REF (ratchet mode)")
    ap.add_argument("--self-test", action="store_true",
                    help="run the embedded positive/negative controls")
    ap.add_argument("--json", action="store_true", dest="as_json",
                    help="machine-readable report on stdout")
    args = ap.parse_args(argv)

    if args.self_test:
        sys.exit(self_test())

    if not args.paths:
        ap.error("provide notebook paths, or --self-test")

    report = run([Path(p) for p in args.paths], base_ref=args.base)
    if args.as_json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        for rel, findings in report["notebooks"].items():
            for f in findings:
                print(f"{rel} cell {f['cell']}: {f['kind']} -- {f['evidence']}")
        print(f"total: {report['total']} finding(s) "
              f"{report['counts'] or ''}")
    return 1 if report["total"] else 0


if __name__ == "__main__":
    sys.exit(main())
