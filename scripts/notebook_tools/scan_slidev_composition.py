#!/usr/bin/env python3
"""
scan_slidev_composition.py — garde-fou CI de composition des slides.

Mesure rendue (Playwright headless) sur un deck Slidev servi en dev mode
(expose window.__slidev__.nav). 3 signaux (cf issue #11923) :

  1. HORS_CANVAS — élément dont la bbox dépasse le canvas déclaré (défaut 980×552).

  2. CHEVAUCHEMENT (sur glyphes) — deux Range.selectNodeContents() qui
     s'intersectent de plus de 1 px dans les deux axes. Mesure sur les
     glyphes (jamais les boîtes), pour éviter le faux-positif du pattern
     overlay (boîte LI pleine largeur qui croise une image posée à droite).

  3. OCCUPATION (sur images) — bande latérale sans image (> 25 % de la
     largeur du canvas) PENDANT que la colonne centrale sature (débordement
     bas ou bord frôlé). Le cas fondateur : slide 5 S3-acculturation
     @ 6cabc826b (img_006 + 2 logos en flux au centre, tiers droit vide).

Le rendu est ADVISORY — il ne remplace pas le QA visuel humain pour la
composition esthétique. Cette borne est imprimée à chaque invocation.

Anti-pièges (tous payés, cf #11923) :
  - Navigation par window.__slidev__.nav.go(i) (pas keyboard) ;
  - Stabilisation DOM avant mesure : currentSlideNo == i ET innerText stable
    sur 2 polls — pendant une transition, #slide-content first-match peut
    être la slide SORTANTE (défaut v1 : titre figé « Intelligence(s) » sur
    93 mesures, cf instrument-must-name-what-it-measured) ;
  - name-what-measured : chaque verdict porte text_head (60 premiers chars) ;
    une série de text_head identiques = avertissement STALE_STREAK ;
  - Le canvas par défaut est 980×552, lu du headmatter, jamais supposé ;
  - file=,line= mappés sur la ligne source de la slide (splitter fence-aware).

Usage :
    # 1. Démarrer le serveur (dans un autre terminal) :
    cd slides/S3-acculturation
    cp slides.md dev.md             # slidev dev cherche dev.md dans le cwd
    npx slidev dev.md --port 8767 --open false

    # 2. Lancer l'instrument :
    python scripts/notebook_tools/scan_slidev_composition.py \\
        --url http://localhost:8767/ \\
        --slides-md slides/S3-acculturation/slides.md \\
        --baseline-slide 5 --baseline-commit 6cabc826b

    # Mode annotations CI (GitHub Actions ::warning, file=,line=) :
    python scripts/notebook_tools/scan_slidev_composition.py ... --github-annotations

Sortie : JSON sur stdout, code retour 0 (RAS) / 1 (constats) / 2 (contrôle
positif raté — instrument cassé, à ne pas merger).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

from playwright.sync_api import sync_playwright


CANVAS_DEFAULT = (980, 552)
BORNE = "ADVISORY only — ne remplace pas le QA visuel humain pour la composition"


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


def split_slides_source(text: str) -> list[dict]:
    """Découpe slides.md en slides, fence-aware, avec lignes sources.

    Séparateurs = lignes `---` hors fences code. Les blocs entre séparateurs
    qui ne contiennent QUE du YAML (clé: valeur / commentaires) sont des
    frontmatter (globale ou par-slide), PAS des slides — une slide = premier
    bloc de contenu qui suit. Heuristique documentée : une slide dont tout le
    contenu ressemblerait à du YAML pur serait sautée (aucune dans le dépôt ;
    le désaccord de comptage vs nav.total est rapporté comme warning).

    Retourne [{no (1-based, aligné sur nav), start_line (1-based, première
    ligne non vide)}].
    """
    import re

    lines = text.split("\n")
    n = len(lines)
    fence = None
    seps = []  # 1-based line numbers of top-level '---'
    for i, line in enumerate(lines, 1):
        s = line.strip()
        if fence is not None:
            if s.startswith(fence):
                fence = None
            continue
        if s.startswith("```") or s.startswith("~~~"):
            fence = s[:3]
            continue
        if s == "---":
            seps.append(i)

    bounds = [0] + seps + [n + 1]
    blocks = []
    for k in range(len(bounds) - 1):
        a, b = bounds[k] + 1, bounds[k + 1] - 1
        blocks.append({
            "start": a,
            "lines": lines[a - 1:b] if a <= b else [],
        })

    yaml_re = re.compile(r"^\s*[A-Za-z_][\w\-]*\s*:")

    def is_yaml(block: dict) -> bool:
        ne = [l for l in block["lines"] if l.strip()]
        # un heading markdown `# X` + des puces ressemble lexicalement à du
        # YAML (commentaire + liste) — un VRAI frontmatter porte toujours au
        # moins une ligne `clé: valeur` (layout:, transition:, ...). Sans ça,
        # les 19 slides-divider du S3 étaient avalées comme frontmatter.
        if not any(yaml_re.match(l) for l in ne):
            return False
        return all(
            yaml_re.match(l) or l.strip().startswith("#") or l.lstrip().startswith("- ")
            for l in ne
        )

    slides: list[dict] = []
    for k, block in enumerate(blocks):
        if k == 0:
            continue  # avant le '---' d'ouverture : vide par convention
        if is_yaml(block):
            continue  # frontmatter (globale k==1 ou par-slide) : pas une slide
        if not any(l.strip() for l in block["lines"]):
            continue  # bloc vide entre séparateurs consécutifs
        start_line = next(
            i for i, l in enumerate(block["lines"], block["start"]) if l.strip()
        )
        slides.append({"no": len(slides) + 1, "start_line": start_line})
    return slides


def slide_start_lines(text: str) -> dict[int, int]:
    """no (1-based) -> ligne source de début de contenu. Vérifié par test."""
    return {s["no"]: s["start_line"] for s in split_slides_source(text)}


_READ_STATE_JS = """() => {
    const el = document.querySelector('#slide-content');
    return {
        cur: window.__slidev__?.nav?.currentSlideNo ?? null,
        present: !!el,
        digest: el ? [el.innerText.length, Array.from(el.innerText).slice(0, 60).join('')] : null,
    };
}"""


def wait_slide_stable(page, target: int, timeout_ms: int = 6000, poll_ms: int = 250) -> dict:
    """Attend que la slide `target` soit courante ET que son DOM soit stable.

    Stabilité = même digest (longueur innerText + 60 premiers chars) sur deux
    polls consécutifs. Pendant une transition Slidev, #slide-content peut
    être la slide sortante (first-match DOM) — mesurer à ce moment-là
    attribue les constats à la mauvaise slide (défaut v1).
    """
    import time

    deadline = time.time() + timeout_ms / 1000
    last = None
    stable_since = None
    while time.time() < deadline:
        st = page.evaluate(_READ_STATE_JS)
        if st["cur"] == target and st["present"]:
            if last is not None and st["digest"] == last:
                if stable_since is None:
                    stable_since = time.time()
                if time.time() - stable_since >= poll_ms / 1000:
                    return st
            else:
                stable_since = None
            last = st["digest"]
        else:
            last = None
            stable_since = None
        page.wait_for_timeout(poll_ms)
    return {"cur": None, "present": False, "digest": None, "timeout": True}


def measure_slide(page, slide_idx: int, canvas_w: int, canvas_h: int) -> dict:
    """Mesure les 3 signaux sur la slide courante stabilisée. Retourne un dict verdict."""
    state = wait_slide_stable(page, slide_idx)
    if state.get("timeout") or not state.get("present"):
        return {"slide": slide_idx, "error": f"slide {slide_idx} non stabilisée (cur={state.get('cur')})"}

    text_head = page.evaluate(
        """() => (document.querySelector('#slide-content')?.innerText || '')
                  .replace(/\\s+/g, ' ').slice(0, 60)"""
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
                if (b) boxes.push({ ...b, key: t.key, kind: t.kind, el: t.el });
            }
            for (let i = 0; i < boxes.length; i++) {
                for (let j = i + 1; j < boxes.length; j++) {
                    const a = boxes[i], b = boxes[j];
                    // FP structurel v1 : ancêtre/descendant (li contenant ul>li,
                    // blockquote contenant p) — le Range du parent couvre
                    // nécessairement l'enfant. Ce n'est pas un chevauchement.
                    if (a.el === b.el || a.el.contains(b.el) || b.el.contains(a.el)) continue;
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
            // content_bottom sur le CONTENU (glyphes + images), pas sur '*':
            // le footer de pagination touche le bas du canvas sur TOUTES les
            // slides paginées → condition verticale tautologique en v1 (42/93 FP).
            let contentBottom = 0;
            for (const b of [...boxes, ...imgBoxes]) {
                if (b.bottom > contentBottom) contentBottom = b.bottom;
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
                    content_bottom: Math.round(contentBottom),
                };
            }

            return { horsCanvas, chevauchements, occupation, contentBottom: Math.round(contentBottom) };
        }""",
        [canvas_w, canvas_h],
    )

    if raw is None:
        return {"slide": slide_idx, "error": "no #slide-content"}

    return {
        "slide": slide_idx,
        "text_head": text_head,
        "canvas": [canvas_w, canvas_h],
        "hors_canvas": raw.get("horsCanvas", []),
        "chevauchements": raw.get("chevauchements", []),
        "occupation": raw.get("occupation"),
    }


def occupation_flagged(r: dict, canvas_h: int) -> bool:
    """Bande latérale vide > 25 % PENDANT saturation verticale (débordement ou bord frôlé)."""
    occ = r.get("occupation")
    if not occ:
        return False
    side_empty = occ.get("gap_right_pct", 0) > 25 or occ.get("gap_left_pct", 0) > 25
    if not side_empty:
        return False
    bottom = occ.get("content_bottom", 0)
    overflow = bool(r.get("hors_canvas"))
    return overflow or bottom > canvas_h * 0.95


def github_annotations(report: dict, slides_md: Path) -> list[str]:
    """Rend les constats en ::warning file=,line= (format GitHub Actions)."""
    lines_by_slide = {int(k): v for k, v in (report.get("_slide_lines") or {}).items()}
    out: list[str] = []
    rel = slides_md.as_posix()
    for r in report.get("results", []):
        line = lines_by_slide.get(r["slide"], 1)
        head = (r.get("text_head") or "?")[:40].replace("\n", " ")
        for h in r.get("hors_canvas", [])[:3]:
            out.append(
                f"::warning file={rel},line={line}::[HORS_CANVAS] slide {r['slide']} ({head}) — "
                f"{h['tag']}.{h['cls'][:30]} bbox={h['bbox']}"
            )
        for c in r.get("chevauchements", [])[:3]:
            out.append(
                f"::warning file={rel},line={line}::[CHEVAUCHEMENT] slide {r['slide']} ({head}) — "
                f"{c['a']} × {c['b']} overlap={c['overlap']}px"
            )
        if occupation_flagged(r, report["canvas"][1]):
            occ = r["occupation"]
            out.append(
                f"::warning file={rel},line={line}::[OCCUPATION] slide {r['slide']} ({head}) — "
                f"gap_left={occ['gap_left_pct']}% gap_right={occ['gap_right_pct']}% bottom={occ.get('content_bottom')}/{report['canvas'][1]}"
            )
    out.append(f"::notice file={rel}::Plancher mécanique advisory ({BORNE})")
    return out


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--url", type=str, required=True,
                   help="URL du serveur slidev dev déjà démarré (ex. http://localhost:8767/)")
    p.add_argument("--slides-md", type=Path, default=None,
                   help="Chemin slides.md source — canvas du headmatter + mapping file=,line=")
    p.add_argument("--baseline-slide", type=int, default=None,
                   help="Numéro de slide (1-based) qui DOIT être signalée par contrôle positif")
    p.add_argument("--baseline-commit", type=str, default=None,
                   help="SHA du commit baseline (affiché dans le rapport de contrôle positif)")
    p.add_argument("--out", type=Path, default=None, help="Fichier de sortie JSON (défaut : stdout)")
    p.add_argument("--max-slide", type=int, default=0, help="Stop après N slides (0 = toutes)")
    p.add_argument("--wait-ms", type=int, default=400, help="Attente supplémentaire après stabilisation (défaut 400ms)")
    p.add_argument("--github-annotations", action="store_true",
                   help="Émet les constats en ::warning file=,line= (stdout, en plus du JSON sur --out)")
    args = p.parse_args()

    source_text = None
    if args.slides_md:
        canvas_w, canvas_h = parse_headmatter_canvas(args.slides_md)
        source_text = args.slides_md.read_text(encoding="utf-8", errors="replace")
    else:
        canvas_w, canvas_h = CANVAS_DEFAULT

    slide_lines = slide_start_lines(source_text) if source_text else {}

    results = []
    stale_streaks = []
    prev_head = None
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

        if slide_lines and total and len(slide_lines) != total:
            stale_streaks.append(
                f"source/désaccord de comptage : {len(slide_lines)} slides source vs {total} rendues — "
                "le mapping line= peut être décalé"
            )

        i = 1
        while i <= total:
            if args.max_slide and i > args.max_slide:
                break
            page.evaluate(f"() => window.__slidev__.nav.go({i})")
            page.wait_for_timeout(args.wait_ms)
            r = measure_slide(page, i, canvas_w, canvas_h)
            if r.get("error"):
                stale_streaks.append(f"slide {i}: {r['error']}")
                break
            # name-what-measured : une série de text_head identiques = mesure suspecte
            if prev_head is not None and r["text_head"] == prev_head:
                stale_streaks.append(f"slides {i-1}-{i}: text_head identique {r['text_head'][:40]!r} — mesure possiblement figée")
            prev_head = r["text_head"]
            results.append(r)
            i += 1

        browser.close()

    n_total = len(results)
    n_hors = sum(1 for r in results if r.get("hors_canvas"))
    n_chev = sum(1 for r in results if r.get("chevauchements"))
    n_occ = sum(1 for r in results if occupation_flagged(r, canvas_h))

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
            flagged_occ = occupation_flagged(ctrl, canvas_h)
            # la slide 5 @ 6cabc826b : débordement bas 4px (HORS_CANVAS) + images
            # en flux au centre, tiers droit vide (OCCUPATION) — un de ces signaux suffit
            ctrl_positif_ok = signals or flagged_occ
            if not ctrl_positif_ok:
                ctrl_positif_msg = (
                    f"baseline slide {args.baseline_slide} NON signalée — instrument suspect "
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
        "stale_warnings": stale_streaks,
        "borne": BORNE,
        "results": results,
        "_slide_lines": {str(k): v for k, v in slide_lines.items()},
    }

    out_str = json.dumps(report, ensure_ascii=False, indent=2)
    if args.out:
        args.out.write_text(out_str, encoding="utf-8")
    print(out_str)

    if args.github_annotations:
        for a in github_annotations(report, args.slides_md or Path("slides.md")):
            print(a)

    if ctrl_positif_ok is False:
        return 2
    if n_hors or n_chev or n_occ:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
