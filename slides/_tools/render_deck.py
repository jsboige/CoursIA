#!/usr/bin/env python3
"""
render_deck.py — instrument de capture Playwright pour decks Slidev.

Navigation slide-par-slide, captures 1440x900 avec networkidle + 800ms
(compile Tailwind). Utilise pour verifier visuellement les PRs slides
(issue #13237 et suivantes).

Trois modes de ciblage :

  - plage     : diapositives 1..--cap (mode d'origine) ;
  - --slides  : indices explicites ("54,59,61") ;
  - --match   : un selecteur CSS — le deck est parcourt via
                `window.__slidev__.nav.go(i)` et seules les diapositives
                dont le DOM RENDU contient le selecteur sont capturees.
                C'est la seule liste qui fasse foi sur la classe au
                rendu : l'indexation du markdown decale (frontmatter par
                diapositive, fences), et la question "la classe est-elle
                morte au rendu ?" se pose sur le DOM, pas sur le source.

Usage :
    # Terminal 1 : demarrer slidev sur le deck vise
    cd <worktree>
    npx slidev slides/S1-argumentation/slides.md --port 3031

    # Terminal 2 : lancer le rendu
    python slides/_tools/render_deck.py S1 --base http://localhost:3031

    # Capture ciblee : quelques diapositives eparses d'un deck
    python slides/_tools/render_deck.py 02 --base http://localhost:3031 \
        --slides 54,59,61,67,68,69,71,84,88

    # Capture des diapositives qui portent la classe au rendu
    python slides/_tools/render_deck.py 02 --base http://localhost:3031 \
        --match ".dense-list"

    # ... avec un manifeste JSON (classes portees, style calcule, debordements)
    python slides/_tools/render_deck.py 02 --base http://localhost:3031 \
        --match ".dense-list" --manifest /tmp/02.json
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

from playwright.sync_api import sync_playwright


def _head(page) -> str:
    """Titre de la diapositive AFFICHEE.

    Le premier `h1` du document n'est pas le titre courant : le DOM Slidev
    porte aussi les pages voisines (et, en `clicks=99`, la page 1), si bien
    que `page.locator('h1').first` restitue souvent le titre d'une autre
    diapositive. On lit la page visible, designee par `data-slidev-no` et
    localisee au point central du viewport.
    """
    try:
        return page.evaluate(
            """() => {
              const el = document.elementFromPoint(window.innerWidth / 2, window.innerHeight / 2);
              let pg = el;
              while (pg && !pg.classList?.contains('slidev-page')) pg = pg.parentElement;
              if (!pg) {
                pg = Array.from(document.querySelectorAll('.slidev-page')).find(p => {
                  const r = p.getBoundingClientRect();
                  return r.width > 0 && r.height > 0;
                });
              }
              if (!pg) return '';
              const h = pg.querySelector('h1');
              return h ? (h.textContent || '').trim() : '';
            }"""
        )
    except Exception:
        return ""


def render(
    deck: str,
    base: str,
    outdir: Path,
    viewport=(1440, 900),
    cap: int = 60,
    slides: list[int] | None = None,
) -> int:
    outdir.mkdir(parents=True, exist_ok=True)
    rendered = 0
    targets = slides if slides else list(range(1, cap + 1))
    with sync_playwright() as p:
        browser = p.chromium.launch()
        context = browser.new_context(viewport={"width": viewport[0], "height": viewport[1]})
        page = context.new_page()
        for n in targets:
            url = f"{base.rstrip('/')}/{n}?clicks=99"
            try:
                page.goto(url, wait_until="networkidle", timeout=30000)
                page.wait_for_timeout(800)  # Tailwind compile
                h1 = _head(page)
                fname = outdir / f"slide-{n:03d}.png"
                page.screenshot(path=str(fname), full_page=False)
                rendered += 1
                title_short = h1[:50].strip() if h1 else "(no h1)"
                print(f"[{deck}] slide {n} : {title_short!r}")
            except Exception as e:
                print(f"[{deck}] slide {n} : ERROR {e}", file=sys.stderr)
                break
        browser.close()
    return rendered


def _current_page_info(page, no: int) -> dict:
    """Etat de la diapositive `no` dans le DOM rendu.

    Le DOM Slidev en mode dev porte PLUSIEURS `.slidev-page` (la courante
    et ses voisines de transition) : un selecteur appliqué au document
    entier compte les classes des voisines, pas celles de la diapositive
    demandee. La page courante est designee par son attribut
    `data-slidev-no` — c'est le seul marqueur stable mesure ici.
    """
    return page.evaluate(
        """(no) => {
          const pg = document.querySelector(`.slidev-page[data-slidev-no="${no}"]`);
          if (!pg) return { present: false };
          const r = pg.getBoundingClientRect();
          const txt = (pg.textContent || '').trim();
          const h1 = pg.querySelector('h1');
          return {
            present: true,
            visible: r.width > 0 && r.height > 0,
            loading: txt.startsWith('Loading slide'),
            text: txt.slice(0, 120),
            h1: h1 ? (h1.textContent || '').trim().slice(0, 60) : '',
            rect: { x: Math.round(r.x), y: Math.round(r.y), w: Math.round(r.width), h: Math.round(r.height) },
          };
        }""",
        no,
    )


def _measure_slide(page, no: int, classes: list[str]) -> dict:
    """Mesure au rendu : classes portees, style calcule, debordements.

    La presence d'une classe dans le DOM ne prouve pas qu'elle est
    EFFECTIVE : une regle ulterieure peut la neutraliser. On mesure donc
    le style calcule de la liste qu'elle cible, et on releve les elements
    visibles qui debordent du cadre de la diapositive.
    """
    return page.evaluate(
        """(args) => {
          const pg = document.querySelector(`.slidev-page[data-slidev-no="${args.no}"]`);
          if (!pg) return null;
          const out = { no: args.no, classes: {}, h1: '' };
          const h1 = pg.querySelector('h1');
          out.h1 = h1 ? (h1.textContent || '').trim() : '';
          for (const cls of args.classes) {
            out.classes[cls] = pg.querySelectorAll('.' + cls).length;
          }
          const target = pg.querySelector('.dense-list') || pg.querySelector('.xl-dense');
          if (target) {
            const ul = target.querySelector('ul');
            const cs = ul ? getComputedStyle(ul) : null;
            const r = target.getBoundingClientRect();
            out.target = {
              tag: target.tagName,
              cls: (target.className || '').toString().slice(0, 60),
              fontSize: cs ? cs.fontSize : null,
              lineHeight: cs ? cs.lineHeight : null,
              ul: ul ? {
                scrollH: ul.scrollHeight, clientH: ul.clientHeight,
                scrollW: ul.scrollWidth, clientW: ul.clientWidth,
              } : null,
              rect: { x: Math.round(r.x), y: Math.round(r.y),
                      w: Math.round(r.width), h: Math.round(r.height) },
            };
          }
          const pr = pg.getBoundingClientRect();
          const over = [];
          for (const el of pg.querySelectorAll('*')) {
            const r = el.getBoundingClientRect();
            if (r.width === 0 && r.height === 0) continue;
            if (r.bottom > pr.bottom + 1 || r.right > pr.right + 1 ||
                r.top < pr.top - 1 || r.left < pr.left - 1) {
              over.push({
                tag: el.tagName,
                cls: (el.className || '').toString().slice(0, 40),
                bottom: Math.round(r.bottom), right: Math.round(r.right),
              });
            }
          }
          out.frame = { x: Math.round(pr.x), y: Math.round(pr.y),
                        w: Math.round(pr.width), h: Math.round(pr.height) };
          out.out_of_frame_n = over.length;
          out.out_of_frame = over.slice(0, 5);
          return out;
        }""",
        {"no": no, "classes": classes},
    )


def render_matching(
    deck: str,
    base: str,
    outdir: Path,
    selector: str,
    viewport=(1440, 900),
    cap: int = 0,
    wait_ms: int = 250,
    settle_ms: int = 15000,
    manifest: Path | None = None,
) -> int:
    """Capture les diapositives dont le DOM rendu contient `selector`.

    Le parcours se fait par `window.__slidev__.nav.go(i)` (l'API du mode
    dev) et la lecture se fait DANS la page `.slidev-page[data-slidev-no]`
    correspondant a l'index : c'est la seule liste qui fasse foi sur la
    classe au rendu (le markdown indexe mal, et la question "la classe
    est-elle morte au rendu ?" se pose sur le DOM, pas sur le source).
    """
    outdir.mkdir(parents=True, exist_ok=True)
    rendered = 0
    classes = [c.strip().lstrip(".") for c in selector.split(",") if c.strip()]
    entries: list[dict] = []
    with sync_playwright() as p:
        browser = p.chromium.launch()
        context = browser.new_context(viewport={"width": viewport[0], "height": viewport[1]})
        page = context.new_page()
        page.goto(f"{base.rstrip('/')}/1?clicks=99", wait_until="domcontentloaded", timeout=60000)

        total = 0
        for _ in range(40):
            try:
                total = page.evaluate("() => window.__slidev__?.nav?.total ?? 0")
            except Exception:
                total = 0
            if total:
                break
            page.wait_for_timeout(1000)
        if not total:
            print(
                f"[{deck}] __slidev__.nav.total absent a {base} — le serveur est-il en mode dev ?",
                file=sys.stderr,
            )
            browser.close()
            return 0
        last = min(total, cap) if cap else total
        print(f"[{deck}] {total} diapositives rendues, parcours 1..{last}, selecteur {selector!r}")

        i = 1
        while i <= last:
            page.evaluate(f"() => window.__slidev__.nav.go({i})")
            info = {"present": False}
            deadline = time.time() + settle_ms / 1000
            while time.time() < deadline:
                page.wait_for_timeout(wait_ms)
                info = _current_page_info(page, i)
                if info.get("present") and info.get("visible") and not info.get("loading"):
                    break
            if not info.get("present"):
                print(f"[{deck}] slide {i} : page absente du DOM", file=sys.stderr)
                break
            n_match = page.evaluate(
                """(args) => {
                  const pg = document.querySelector(`.slidev-page[data-slidev-no="${args.no}"]`);
                  if (!pg) return 0;
                  return pg.querySelectorAll(args.sel).length;
                }""",
                {"no": i, "sel": selector},
            )
            if n_match:
                fname = outdir / f"slide-{i:03d}.png"
                page.screenshot(path=str(fname), full_page=False)
                rendered += 1
                m = _measure_slide(page, i, classes) or {"no": i}
                entries.append(m)
                target = m.get("target") or {}
                print(
                    f"[{deck}] slide {i} : {n_match} noeud(s) {selector} — {info.get('h1', '')!r}"
                    f" | classes={m.get('classes')} ul={target.get('fontSize')}/{target.get('lineHeight')}"
                    f" hors_cadre={m.get('out_of_frame_n')}",
                    flush=True,
                )
            i += 1
        browser.close()
    if manifest:
        manifest.parent.mkdir(parents=True, exist_ok=True)
        manifest.write_text(
            json.dumps(
                {"deck": deck, "base": base, "selector": selector,
                 "total_slides": total, "matched": entries},
                ensure_ascii=False,
                indent=2,
            ),
            encoding="utf-8",
        )
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
    parser.add_argument(
        "--cap",
        type=int,
        default=None,
        help=(
            "Nombre max de slides a scanner. defaut : 60 en mode plage, "
            "TOUTES les diapositives en mode --match."
        ),
    )
    parser.add_argument(
        "--slides",
        default=None,
        help=(
            "Liste explicite d'indices de diapositives a capturer (ex. '9,18,32'). "
            "Rend ces diapositives-la, dans l'ordre donne ; ignore --cap."
        ),
    )
    parser.add_argument(
        "--match",
        default=None,
        help=(
            "Selecteur CSS : capture les diapositives dont le DOM rendu contient "
            "ce selecteur (ex. '.dense-list'). Implique la navigation par "
            "window.__slidev__.nav.go ; ignore --cap et --slides."
        ),
    )
    parser.add_argument(
        "--wait-ms",
        type=int,
        default=250,
        help="Stabilisation DOM entre deux diapositives en mode --match (defaut 250ms)",
    )
    parser.add_argument(
        "--viewport",
        default="1440x900",
        help=(
            "Taille de la capture, 'LxH' (defaut 1440x900). Pour une preuve "
            "conforme au deck, utiliser le canvas du scanner (980x552 par "
            "defaut) : c'est la taille a laquelle scan_slidev_composition.py "
            "mesure les debordements. 980x552 est CANVAS_DEFAULT du scanner ; "
            "un deck peut le declarer dans son headmatter (canvasWidth / "
            "canvasHeight / aspectRatio)."
        ),
    )
    parser.add_argument(
        "--manifest",
        default=None,
        help=(
            "Fichier JSON de sortie (mode --match) : pour chaque diapositive "
            "capturee, classes portees, style calcule de la liste cible et "
            "elements debordant du cadre de la diapositive."
        ),
    )
    args = parser.parse_args()

    try:
        vw, vh = (int(x) for x in args.viewport.lower().split("x", 1))
    except ValueError:
        print(f"--viewport : taille illisible ({args.viewport!r}), attendu 'LxH'", file=sys.stderr)
        return 2
    viewport = (vw, vh)

    slides = None
    if args.slides:
        try:
            slides = [int(x) for x in args.slides.replace(" ", "").split(",") if x]
        except ValueError:
            print(f"--slides : liste d'indices illisible ({args.slides!r})", file=sys.stderr)
            return 2
        if not slides:
            print("--slides : liste vide", file=sys.stderr)
            return 2

    here = Path(__file__).resolve().parent
    outdir = Path(args.outdir) if args.outdir else here / "slide-renders" / args.deck
    t0 = time.time()
    if args.match:
        n = render_matching(
            args.deck,
            args.base,
            outdir,
            args.match,
            viewport=viewport,
            cap=args.cap or 0,
            wait_ms=args.wait_ms,
            manifest=Path(args.manifest) if args.manifest else None,
        )
    else:
        n = render(
            args.deck,
            args.base,
            outdir,
            viewport=viewport,
            cap=args.cap or 60,
            slides=slides,
        )
    elapsed = time.time() - t0
    print(f"[{args.deck}] {n} slides rendues dans {outdir} en {elapsed:.1f}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
