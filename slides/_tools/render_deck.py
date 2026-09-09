#!/usr/bin/env python3
"""
render_deck.py — instrument de capture Playwright pour decks Slidev.

Navigation slide-par-slide, captures 1440x900 avec networkidle + 800ms
(compile Tailwind). Utilise pour verifier visuellement les PRs slides
(issue #13237 et suivantes).

Usage :
    # Terminal 1 : demarrer slidev sur le deck vise
    cd <worktree>
    npx slidev slides/S1-argumentation/slides.md --port 3031

    # Terminal 2 : lancer le rendu
    python slides/_tools/render_deck.py S1 --base http://localhost:3031
"""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

from playwright.sync_api import sync_playwright


def render(deck: str, base: str, outdir: Path, viewport=(1440, 900), cap: int = 60) -> int:
    outdir.mkdir(parents=True, exist_ok=True)
    rendered = 0
    with sync_playwright() as p:
        browser = p.chromium.launch()
        context = browser.new_context(viewport={"width": viewport[0], "height": viewport[1]})
        page = context.new_page()
        for n in range(1, cap + 1):
            url = f"{base.rstrip('/')}/{n}?clicks=99"
            try:
                page.goto(url, wait_until="networkidle", timeout=30000)
                page.wait_for_timeout(800)  # Tailwind compile
                h1 = page.locator("h1").first.text_content(timeout=2000) or ""
                fname = outdir / f"slide-{n:03d}.png"
                page.screenshot(path=str(fname), full_page=False)
                rendered += 1
                title_short = (h1[:50].strip() if h1 else "(no h1)")
                print(f"[{deck}] slide {n} : {title_short!r}")
            except Exception as e:
                print(f"[{deck}] slide {n} : ERROR {e}", file=sys.stderr)
                break
        browser.close()
    return rendered


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("deck", help="Identifiant deck (S1, S2, S3, ...)")
    parser.add_argument("--base", default="http://localhost:3031", help="URL Slidev")
    parser.add_argument(
        "--outdir",
        default=None,
        help="Dossier de sortie (defaut: a cote du script dans slide-renders/<deck>)",
    )
    parser.add_argument("--cap", type=int, default=60, help="Nombre max de slides a scanner")
    args = parser.parse_args()

    here = Path(__file__).resolve().parent
    outdir = Path(args.outdir) if args.outdir else here / "slide-renders" / args.deck
    t0 = time.time()
    n = render(args.deck, args.base, outdir, cap=args.cap)
    elapsed = time.time() - t0
    print(f"[{args.deck}] {n} slides rendues dans {outdir} en {elapsed:.1f}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
