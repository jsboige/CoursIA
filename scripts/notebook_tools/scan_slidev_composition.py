#!/usr/bin/env python3
"""
scan_slidev_composition.py — garde-fou CI de composition des slides.

Mesure rendue (Playwright headless) sur un deck Slidev servi en dev mode
(expose window.slidev.nav). 3 signaux (cf issue #11923) :

  1. HORS_CANVAS — élément dont la bbox dépasse le canvas déclaré (défaut 980×552).

  2. CHEVAUCHEMENT (sur glyphes) — deux Range.selectNodeContents() qui
     s'intersectent de plus de 1 px dans les deux axes. Mesure sur les
     glyphes (jamais les boîtes), pour éviter le faux-positif du pattern
     overlay (boîte LI pleine largeur qui croise une image posée à droite).

  3. OCCUPATION (sur images) — dispersion / centre de gravité des images
     rapportés à la largeur du canvas, présence d'une bande sans image
     d'un côté pendant que la colonne centrale sature. Le cas fondateur :
     slide 5 S3-acculturation (img_006 + 2 logos en flux au centre, tiers
     droit vide).

Le rendu est ADVISORY — il ne remplace pas le QA visuel humain pour la
composition esthétique. Cette borne est imprimée à chaque invocation.

Usage :
    # 1. Démarrer le serveur (dans un autre terminal) :
    cd slides/S3-acculturation
    cp slides.md dev.md             # slidev dev cherche dev.md dans le cwd
    npx slidev dev --port 8767 --open false

    # 2. Lancer l'instrument :
    python scripts/notebook_tools/scan_slidev_composition.py \\
        --url http://localhost:8767/ \\
        --slides-md slides/S3-acculturation/slides.md \\
        --baseline-slide 5 --baseline-commit 6cabc826b

Sortie : JSON sur stdout, code retour 0 (RAS) / 1 (constats) / 2 (contrôle
positif raté — instrument cassé, à ne pas merger).
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

from playwright.sync_api import sync_playwright


CANVAS_DEFAULT = (980, 552)


def parse_headmatter_canvas(slides_md: Path) -> tuple[int, int]:
    """Lit canvasWidth/canvasHeight/aspectRatio du headmatter. DEFAULT = 980×552."""
    text = slides_md.read_text(encoding="utf-8", errors="replace").split("---", 2)
    if len(text) < 3:
        return CANVAS_DEFAULT
    head = text[1]
    canvas_w = CANVAS_DEFAULT[0]
    canvas_h = CANVAS_DEFAULT[1]
    for line in head.splitlines():
        s = line.strip()
        if s.startswith("canvasWidth:"):
            try:
                canvas_w = int(s.split(":", 1)[1].strip())
            except ValueError:
                pass
        elif s.startswith("canvasHeight:"):
            try:
                canvas_h = int(s.split(":", 1)[1].strip())
            except ValueError:
                pass
        elif s.startswith("aspectRatio:"):
            try:
                parts = s.split(":", 1)[1].strip().split("/")
                canvas_w = int(parts[0])
                canvas_h = int(parts[1]) if len(parts) > 1 else 9
            except (ValueError, IndexError):
                pass
    return canvas_w, canvas_h


def measure_slide(page, slide_idx: int, canvas_w: int, canvas_h: int) -> dict:
    """Mesure les 3 signaux sur la slide courante. Retourne un dict verdict."""
    page.wait_for_timeout(500)

    slide_title = page.evaluate(
        """() => {
            const h = document.querySelector('#slide-content h1, #slide-content h2');
            return h ? h.textContent.trim().slice(0, 80) : null;
        }"""
    )

    raw = page.evaluate(
        """([canvasW, canvasH]) => {
            const root = document.querySelector('#slide-content');
            if (!root) return null;

            // --- HORS_CANVAS ---
            const horsCanvas = [];
            root.querySelectorAll('*').forEach(el => {
                if (el.offsetParent === null) return;
                const r = el.getBoundingClientRect();
                if (r.width < 1 || r.height < 1) return;
                const overflowBottom = r.bottom > canvasH + 0.5;
                const overflowRight  = r.right  > canvasW + 0.5;
                const overflowTop    = r.top    < -0.5;
                const overflowLeft   = r.left   < -0.5;
                if (overflowBottom || overflowRight || overflowTop || overflowLeft) {
                    horsCanvas.push({
                        tag: el.tagName,
                        cls: (el.className || '').toString().slice(0, 80),
                        bbox: [Math.round(r.left), Math.round(r.top),
                               Math.round(r.right), Math.round(r.bottom)],
                    });
                }
            });

            // --- CHEVAUCHEMENT (sur glyphes via Range) ---
            const chevauchements = [];
            const textEls = Array.from(
                root.querySelectorAll('h1, h2, h3, h4, p, li, blockquote, td, th')
            );
            const imgEls = Array.from(root.querySelectorAll('img'));

            function glyphBBox(el) {
                if (!el.firstChild) return null;
                if (el.tagName === 'IMG') {
                    const r = el.getBoundingClientRect();
                    return { left: r.left, top: r.top, right: r.right, bottom: r.bottom };
                }
                const range = document.createRange();
                try {
                    range.selectNodeContents(el);
                } catch (e) {
                    return null;
                }
                const rects = range.getClientRects();
                if (rects.length === 0) return null;
                let L = rects[0].left, T = rects[0].top, R = rects[0].right, B = rects[0].bottom;
                for (let i = 1; i < rects.length; i++) {
                    const r = rects[i];
                    if (r.left   < L) L = r.left;
                    if (r.top    < T) T = r.top;
                    if (r.right  > R) R = r.right;
                    if (r.bottom > B) B = r.bottom;
                }
                if (R - L < 1 || B - T < 1) return null;
                return { left: L, top: T, right: R, bottom: B };
            }

            const allTargets = [
                ...textEls.map(e => ({ kind: 'text', el: e, key: e.tagName + '.' + (e.className||'').toString().slice(0,40) })),
                ...imgEls.map(e => ({ kind: 'img', el: e, key: 'img.' + (e.alt || (e.src.split('/').pop() || '?')).slice(0,60) })),
            ];
            const boxes = [];
            for (const t of allTargets) {
                const b = glyphBBox(t.el);
                if (b) boxes.push({ ...b, key: t.key, kind: t.kind });
            }
            for (let i = 0; i < boxes.length; i++) {
                for (let j = i + 1; j < boxes.length; j++) {
                    const a = boxes[i], b = boxes[j];
                    const overlapX = Math.min(a.right, b.right) - Math.max(a.left, b.left);
                    const overlapY = Math.min(a.bottom, b.bottom) - Math.max(a.top, b.top);
                    if (overlapX > 1 && overlapY > 1) {
                        chevauchements.push({
                            a: a.key, b: b.key,
                            a_bbox: [Math.round(a.left), Math.round(a.top), Math.round(a.right), Math.round(a.bottom)],
                            b_bbox: [Math.round(b.left), Math.round(b.top), Math.round(b.right), Math.round(b.bottom)],
                            overlap: [Math.round(overlapX), Math.round(overlapY)],
                        });
                    }
                }
            }

            // --- OCCUPATION (sur images) ---
            const imgs = Array.from(root.querySelectorAll('img'));
            const imgBoxes = [];
            for (const img of imgs) {
                const r = img.getBoundingClientRect();
                if (r.width < 4 || r.height < 4) continue;
                imgBoxes.push({ left: r.left, top: r.top, right: r.right, bottom: r.bottom });
            }
            let occupation = null;
            if (imgBoxes.length >= 1) {
                const xs = imgBoxes.map(b => b.left);
                const rs = imgBoxes.map(b => b.right);
                const minX = Math.min(...xs);
                const maxR = Math.max(...rs);
                const spanX = maxR - minX;
                const center = (minX + maxR) / 2;
                const canvasCenter = canvasW / 2;
                const centers = imgBoxes.map(b => (b.left + b.right) / 2);
                const cMin = Math.min(...centers), cMax = Math.max(...centers);
                const dispersion = imgBoxes.length > 1 ? (cMax - cMin) / canvasW : 0;
                const gapRight = canvasW - maxR;
                const gapLeft = minX;
                occupation = {
                    n_images: imgBoxes.length,
                    img_span: [Math.round(minX), Math.round(maxR)],
                    span_ratio: Math.round(spanX / canvasW * 1000) / 1000,
                    center_offset_pct: Math.round((center - canvasCenter) / canvasW * 1000) / 10,
                    gap_right_pct: Math.round(gapRight / canvasW * 1000) / 10,
                    gap_left_pct: Math.round(gapLeft / canvasW * 1000) / 10,
                    dispersion: Math.round(dispersion * 1000) / 1000,
                };
            }

            return { horsCanvas, chevauchements, occupation };
        }""",
        [canvas_w, canvas_h],
    )

    if raw is None:
        return {"slide": slide_idx, "error": "no #slide-content"}

    return {
        "slide": slide_idx,
        "title": slide_title,
        "canvas": [canvas_w, canvas_h],
        "hors_canvas": raw.get("horsCanvas", []),
        "chevauchements": raw.get("chevauchements", []),
        "occupation": raw.get("occupation"),
    }


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument(
        "--url",
        type=str,
        required=True,
        help="URL du serveur slidev dev déjà démarré (ex. http://localhost:8767/)",
    )
    p.add_argument(
        "--slides-md",
        type=Path,
        default=None,
        help="Chemin vers slides.md source — utilisé pour lire le canvas du headmatter "
             "ET pour générer un dev.md éphémère (slidev dev cherche dev.md dans le cwd)",
    )
    p.add_argument(
        "--baseline-slide",
        type=int,
        default=None,
        help="Numéro de slide (1-based) qui DOIT être signalée par contrôle positif",
    )
    p.add_argument(
        "--baseline-commit",
        type=str,
        default=None,
        help="SHA du commit baseline (affiché dans le rapport de contrôle positif)",
    )
    p.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Fichier de sortie JSON (défaut : stdout)",
    )
    p.add_argument(
        "--max-slide",
        type=int,
        default=0,
        help="Stop après N slides (0 = toutes)",
    )
    p.add_argument(
        "--wait-ms",
        type=int,
        default=400,
        help="Attente après chaque navigation (défaut 400ms)",
    )
    args = p.parse_args()

    if args.slides_md:
        canvas_w, canvas_h = parse_headmatter_canvas(args.slides_md)
    else:
        canvas_w, canvas_h = CANVAS_DEFAULT

    results = []
    with sync_playwright() as pw:
        browser = pw.chromium.launch(headless=True)
        ctx = browser.new_context(viewport={"width": canvas_w, "height": canvas_h})
        page = ctx.new_page()
        page.goto(args.url, wait_until="networkidle")
        page.wait_for_timeout(2500)  # laisser Slidev initialiser

        total = page.evaluate("() => window.__slidev__?.nav?.total ?? null")
        if not total:
            print(json.dumps({
                "error": f"__slidev__.nav.total absent à {args.url} — le serveur est-il en mode dev ?",
                "hint": "lancer `npx slidev dev --port <X> --open false` au préalable",
            }))
            browser.close()
            return 2

        i = 1
        while i <= total:
            if args.max_slide and i > args.max_slide:
                break
            # navigation par keyboard (fiable sur Slidev dev)
            while True:
                cur = page.evaluate("() => window.__slidev__?.nav?.currentSlideNo ?? null")
                if cur == i:
                    break
                if cur is not None and cur > i:
                    sys.stderr.write(f"[warn] past target: cur={cur} target={i}\n")
                    break
                # avancer d'une slide
                page.keyboard.press("ArrowRight")
                page.wait_for_timeout(120)
            page.wait_for_timeout(args.wait_ms)
            cur = page.evaluate("() => window.__slidev__?.nav?.currentSlideNo ?? null")
            if cur is not None and cur != i:
                sys.stderr.write(f"[warn] slide {i}: cur={cur}\n")
            r = measure_slide(page, i, canvas_w, canvas_h)
            if r.get("error"):
                break
            results.append(r)
            i += 1

        browser.close()

    n_total = len(results)
    n_hors = sum(1 for r in results if r.get("hors_canvas"))
    n_chev = sum(1 for r in results if r.get("chevauchements"))
    n_occ = sum(
        1 for r in results
        if r.get("occupation")
        and (r["occupation"].get("gap_right_pct", 0) > 25
             or r["occupation"].get("gap_left_pct", 0) > 25)
    )

    # contrôle positif
    ctrl_positif_ok = None
    ctrl_positif_msg = None
    if args.baseline_slide is not None:
        ctrl = next((r for r in results if r["slide"] == args.baseline_slide), None)
        if ctrl is None:
            ctrl_positif_ok = False
            ctrl_positif_msg = f"baseline slide {args.baseline_slide} absente du deck"
        else:
            signals = bool(ctrl.get("hors_canvas")) or bool(ctrl.get("chevauchements"))
            occ = ctrl.get("occupation") or {}
            # la slide 5 v3 a un débordement de 4 px (HORS_CANVAS)
            # la slide 5 v3 a une occupation gauche+droite étroite (img en flux au centre)
            # on accepte qu'UN de ces signaux la signale
            ctrl_positif_ok = signals or (occ.get("gap_left_pct", 0) + occ.get("gap_right_pct", 0) > 40)
            if not ctrl_positif_ok:
                ctrl_positif_msg = (
                    f"baseline slide {args.baseline_slide} NON signalee — instrument suspect "
                    f"(commit baseline {args.baseline_commit or '?'})"
                )

    report = {
        "canvas": [canvas_w, canvas_h],
        "url": args.url,
        "baseline_slide": args.baseline_slide,
        "baseline_commit": args.baseline_commit,
        "n_slides": n_total,
        "n_hors_canvas": n_hors,
        "n_chevauchements": n_chev,
        "n_occupation_flagged": n_occ,
        "controle_positif_ok": ctrl_positif_ok,
        "controle_positif_msg": ctrl_positif_msg,
        "borne": "ADVISORY only — ne remplace pas le QA visuel humain pour la composition",
        "results": results,
    }

    out_str = json.dumps(report, ensure_ascii=False, indent=2)
    if args.out:
        args.out.write_text(out_str, encoding="utf-8")
    print(out_str)

    if ctrl_positif_ok is False:
        return 2
    if n_hors or n_chev:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())