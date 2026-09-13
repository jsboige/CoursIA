#!/usr/bin/env python3
"""
scan_slidev_composition.py — garde-fou CI de composition des slides.

Mesure rendue (Playwright headless) sur un deck Slidev servi en dev mode
(expose window.__slidev__.nav). 4 signaux (cf issues #11923, #15351) :

  1. HORS_CANVAS — élément dont la bbox dépasse le canvas déclaré (défaut 980×552).

  2. CHEVAUCHEMENT (sur glyphes, texte × texte) — deux
     Range.selectNodeContents() qui s'intersectent de plus de 1 px dans les
     deux axes. Mesure sur les glyphes (jamais les boîtes), pour éviter le
     faux-positif du pattern overlay (boîte LI pleine largeur qui croise une
     image posée à droite).

  3. OCCUPATION (sur images) — bande latérale sans image (> 25 % de la
     largeur du canvas) PENDANT que la colonne centrale sature (débordement
     bas ou bord frôlé). Le cas fondateur : slide 5 S3-acculturation
     @ 6cabc826b (img_006 + 2 logos en flux au centre, tiers droit vide).

  4. RECOUVREMENT TEXTE × IMAGE (#15351) — du texte dont les glyphes sont
     repeints par une image peinte AU-DESSUS de lui. Prédicat en 4
     exigences : (a) bbox par nœud textuel (Range.getClientRects du Text
     node, pas la boîte du bloc) ; (b) bbox du CONTENU RENDU de l'image
     (naturalWidth/Height + object-fit/object-position — sous
     object-contain la boîte peut être bien plus large que l'image peinte) ;
     (c) image peinte au-dessus seulement (elementFromPoint sur 5 points de
     l'intersection, fallback ordre DOM/z-index) — une image DERRIÈRE le
     texte est le layout image-overlay voulu par la convention #221, pas un
     défaut ; (d) opacité effective : tout JPEG est opaque, un PNG n'est
     exempté que sur alpha effectivement présent dans la sous-zone
     intersectée (échantillonnage canvas 32×32 ; erreur canvas → opaque,
     fail-closed). Cas fondateur : PR #15224 @ 7f7b346f, slides /5 /7 /23 —
     w-[600px] right-[20px] repeint les glyphes sous lui alors que le
     scanner rendait « occupation 6 → 0 ». ADVISORY : ce signal ne modifie
     pas le code retour tant que le taux de faux positifs n'est pas mesuré
     sur les decks existants.

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

            // --- CHEVAUCHEMENT (sur glyphes via Range, texte × texte) ---
            // Les <img> n'y participent pas : un <img> est un void element
            // (jamais de firstChild) et le garde ci-dessous l'excluait de
            // fait depuis la v1 — le texte × image a son propre prédicat
            // (RECOUVREMENT ci-après), qui mesure le contenu rendu et
            // l'ordre de peinture au lieu de la boîte élément naïve.
            const chevauchements = [];
            // #15695 : paires qui franchissent le seuil Range (> 1 px) mais
            // sont éteintes par la porte de confirmation élément — comptées
            // pour que le résumé distingue « rien détecté » de « organe muet ».
            let chevauchementsEteints = 0;
            const textEls = Array.from(
                root.querySelectorAll('h1, h2, h3, h4, p, li, blockquote, td, th')
            );

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

            const allTargets = textEls.map(
                e => ({ kind: 'text', el: e, key: e.tagName + '.' + (e.className||'').toString().slice(0,40) })
            );
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
                        // Passe de confirmation (#15695) : le rect du Range
                        // absorbe le padding+bordure des enfants inline à
                        // boîte propre (<code>, <sup>, <kbd>…) et déborde la
                        // line-box d'environ 1.2 px — un effleurement de
                        // Range n'est pas un chevauchement rendu. Témoin
                        // fondateur : rects Range recouverts de 1.23 px
                        // pendant que les boîtes élément sont séparées de
                        // +1.57 px (trois mesures indépendantes VISUAL-OK).
                        // Les getBoundingClientRect() des éléments disent la
                        // vérité du rendu : s'ils ne se chevauchent pas, la
                        // paire n'existe pas à l'écran. Limite assumée : un
                        // enfant hors flux qui déborderait seul de la boîte
                        // de son élément voit son vrai recouvrement éteint
                        // par cette porte — le contrôle négatif (deux blocs
                        // absolus qui se recouvrent) n'y passe pas : leurs
                        // boîtes élément se chevauchent aussi.
                        const ra = a.el.getBoundingClientRect();
                        const rb = b.el.getBoundingClientRect();
                        const elOverlapX = Math.min(ra.right, rb.right) - Math.max(ra.left, rb.left);
                        const elOverlapY = Math.min(ra.bottom, rb.bottom) - Math.max(ra.top, rb.top);
                        if (elOverlapX > 0 && elOverlapY > 0) {
                            chevauchements.push({
                                a: a.key, b: b.key,
                                a_bbox: [Math.round(a.left), Math.round(a.top), Math.round(a.right), Math.round(a.bottom)],
                                b_bbox: [Math.round(b.left), Math.round(b.top), Math.round(b.right), Math.round(b.bottom)],
                                overlap: [Math.round(overlapX), Math.round(overlapY)],
                                // #15695 : les deux instruments côte à côte —
                                // le graze Range qui a franchi le seuil et la
                                // mesure élément qui confirme (ou, dans le
                                // résumé, l'absence de paire = boîtes
                                // élément disjointes).
                                element_overlap: [
                                    Math.round(elOverlapX * 100) / 100,
                                    Math.round(elOverlapY * 100) / 100,
                                ],
                            });
                        } else {
                            chevauchementsEteints++;
                        }
                    }
                }
            }

            // --- RECOUVREMENT TEXTE × IMAGE (#15351) ---
            // 4 exigences : (a) glyphes par nœud textuel, (b) bbox du
            // contenu rendu de l'image, (c) image peinte au-dessus
            // seulement, (d) opacité effective de la sous-zone peinte.
            // ADVISORY : signalé, jamais bloquant (mesure de FP en cours).
            const recouvrements = [];

            function parseObjPosPart(part, boxSize, paintedSize) {
                const kw = { left: '0%', top: '0%', right: '100%', bottom: '100%', center: '50%' };
                const v = kw[part] !== undefined ? kw[part] : part;
                if (v.endsWith('%')) return (boxSize - paintedSize) * (parseFloat(v) / 100);
                return parseFloat(v) || 0;
            }

            // (b) contenu rendu : object-fit contain/none/scale-down
            // letterboxent — seule la zone peinte repeint les glyphes.
            // fill et cover peignent toute la boîte élément.
            function renderedBox(img) {
                const r = img.getBoundingClientRect();
                const nw = img.naturalWidth, nh = img.naturalHeight;
                if (!nw || !nh || r.width < 4 || r.height < 4) return null;
                const cs = getComputedStyle(img);
                let pw = r.width, ph = r.height;
                const fit = cs.objectFit;
                if (fit === 'none') { pw = nw; ph = nh; }
                else if (fit === 'scale-down') {
                    const s = Math.min(1, r.width / nw, r.height / nh);
                    pw = nw * s; ph = nh * s;
                } else if (fit === 'contain') {
                    const s = Math.min(r.width / nw, r.height / nh);
                    pw = nw * s; ph = nh * s;
                }
                const parts = (cs.objectPosition || '50% 50%').split(/\\s+/);
                const ox = parseObjPosPart(parts[0] || '50%', r.width, pw);
                const oy = parseObjPosPart(parts[1] || '50%', r.height, ph);
                return {
                    left: r.left + ox, top: r.top + oy,
                    right: r.left + ox + pw, bottom: r.top + oy + ph,
                };
            }

            const imgRendues = [];
            root.querySelectorAll('img').forEach(img => {
                const b = renderedBox(img);
                if (b) imgRendues.push({ el: img, src: img.getAttribute('src') || '?', ...b });
            });

            if (imgRendues.length) {
                // (a) glyphes par nœud textuel : un rect par line-box, avec
                // le texte du nœud pour un constat actionnable.
                const walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT);
                const lignesTexte = [];
                let tn;
                while ((tn = walker.nextNode())) {
                    const contenu = (tn.textContent || '').trim();
                    if (!contenu) continue;
                    const rg = document.createRange();
                    rg.selectNodeContents(tn);
                    const rects = rg.getClientRects();
                    for (let k = 0; k < rects.length; k++) {
                        const rr = rects[k];
                        if (rr.width < 1 || rr.height < 1) continue;
                        lignesTexte.push({
                            el: tn.parentElement, text: contenu,
                            left: rr.left, top: rr.top, right: rr.right, bottom: rr.bottom,
                        });
                    }
                }
                for (const tb of lignesTexte) {
                    if (!tb.el) continue;
                    for (const ib of imgRendues) {
                        if (tb.el.contains(ib.el) || ib.el.contains(tb.el)) continue;
                        const ovX = Math.min(tb.right, ib.right) - Math.max(tb.left, ib.left);
                        const ovY = Math.min(tb.bottom, ib.bottom) - Math.max(tb.top, ib.top);
                        if (ovX <= 1 || ovY <= 1) continue;
                        const ix1 = Math.max(tb.left, ib.left), ix2 = Math.min(tb.right, ib.right);
                        const iy1 = Math.max(tb.top, ib.top), iy2 = Math.min(tb.bottom, ib.bottom);
                        // (c) peinte au-dessus ? elementFromPoint sur 5
                        // points de l'intersection. L'image-overlay légitime
                        // (#221 : .overlay-content z-index 2 > .overlay-img
                        // z-index 1) renvoie le texte — pas un défaut.
                        const pts = [
                            [(ix1 + ix2) / 2, (iy1 + iy2) / 2],
                            [ix1 + (ix2 - ix1) * .25, iy1 + (iy2 - iy1) * .25],
                            [ix1 + (ix2 - ix1) * .75, iy1 + (iy2 - iy1) * .25],
                            [ix1 + (ix2 - ix1) * .25, iy1 + (iy2 - iy1) * .75],
                            [ix1 + (ix2 - ix1) * .75, iy1 + (iy2 - iy1) * .75],
                        ];
                        let imgHits = 0, textHits = 0;
                        for (const [px, py] of pts) {
                            const eop = document.elementFromPoint(px, py);
                            if (!eop) continue;
                            if (ib.el === eop || ib.el.contains(eop)) imgHits++;
                            else if (tb.el === eop || tb.el.contains(eop) || eop.contains(tb.el)) textHits++;
                        }
                        let peinteDessus;
                        if (imgHits > 0 && imgHits >= textHits) peinteDessus = true;
                        else if (textHits > 0) peinteDessus = false;
                        else {
                            // 3e élément au-dessus des deux partout : ordre
                            // DOM (l'image APRÈS le texte est peinte après)
                            // départagé par z-index.
                            const rel = ib.el.compareDocumentPosition(tb.el);
                            const zOf = (e) => {
                                const z = getComputedStyle(e).zIndex;
                                return z === 'auto' ? 0 : (parseFloat(z) || 0);
                            };
                            peinteDessus = zOf(ib.el) > zOf(tb.el) ||
                                (zOf(ib.el) === zOf(tb.el) &&
                                 !!(rel & Node.DOCUMENT_POSITION_PRECEDING));
                        }
                        if (!peinteDessus) continue;
                        // (d) opacité effective : JPEG opaque ; PNG
                        // échantillonné sur la sous-zone NATURELLE mappée
                        // depuis la zone rendue intersectée ; erreur canvas
                        // → opaque (fail-closed : on signale, on ne devine
                        // pas une transparence qu'on n'a pas pu lire).
                        let alpha;
                        if (/\\.(jpe?g)(\\?|$)/i.test(ib.src)) {
                            alpha = 1.0;
                        } else {
                            alpha = -1;
                            try {
                                const c = document.createElement('canvas');
                                c.width = 32; c.height = 32;
                                const ctx = c.getContext('2d', { willReadFrequently: true });
                                const rw = ib.right - ib.left, rh = ib.bottom - ib.top;
                                const sx = (ix1 - ib.left) / rw * ib.el.naturalWidth;
                                const sy = (iy1 - ib.top) / rh * ib.el.naturalHeight;
                                const sw = (ix2 - ix1) / rw * ib.el.naturalWidth;
                                const sh = (iy2 - iy1) / rh * ib.el.naturalHeight;
                                if (sw >= 1 && sh >= 1) {
                                    ctx.drawImage(ib.el, sx, sy, sw, sh, 0, 0, 32, 32);
                                    const d = ctx.getImageData(0, 0, 32, 32).data;
                                    let op = 0, tot = 0;
                                    for (let q = 3; q < d.length; q += 4) { tot++; if (d[q] >= 250) op++; }
                                    alpha = op / tot;
                                }
                            } catch (e) { /* canvas taint : alpha reste -1 */ }
                        }
                        if (alpha >= 0 && alpha < 0.05) continue; // zone transparente : n'abîme rien
                        recouvrements.push({
                            texte: tb.text.slice(0, 60),
                            texte_bbox: [Math.round(tb.left), Math.round(tb.top), Math.round(tb.right), Math.round(tb.bottom)],
                            image: ib.src.split('/').pop(),
                            image_bbox_rendu: [Math.round(ib.left), Math.round(ib.top), Math.round(ib.right), Math.round(ib.bottom)],
                            overlap: [Math.round(ovX), Math.round(ovY)],
                            alpha_zone: Math.round(alpha * 1000) / 1000,
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

            return { horsCanvas, chevauchements, chevauchementsEteints, recouvrements, occupation, contentBottom: Math.round(contentBottom) };
        }""",
        [canvas_w, canvas_h],
    )

    if raw is None:
        return {"slide": slide_idx, "error": "no #slide-content"}

    hors = raw.get("horsCanvas", [])
    return {
        "slide": slide_idx,
        "text_head": text_head,
        "canvas": [canvas_w, canvas_h],
        "hors_canvas": hors,
        "container_only": bool(hors) and not any(h.get("tag") in CONTENT_TAGS for h in hors),
        "chevauchements": raw.get("chevauchements", []),
        "chevauchements_eteints": raw.get("chevauchementsEteints", 0),
        "recouvrements": raw.get("recouvrements", []),
        "occupation": raw.get("occupation"),
    }


CONTENT_TAGS = {
    "P", "LI", "H1", "H2", "H3", "H4", "H5", "H6", "TD", "TH", "BLOCKQUOTE",
    "PRE", "CODE", "IMG", "SVG", "CANVAS", "VIDEO", "IFRAME", "SPAN",
    # Inline text tags. A link/emphasis cut at the canvas edge IS visible
    # when its text extends past the visible region -- issue #15664 founded
    # this gap with deck 05-theorie-des-jeux slide 10 where `EM > A > A > A`
    # (the per-notebook anchor line) overflowed by 1 px and was reported as
    # `container_only: true`. These inherit the bbox of their parent block in
    # normal flow, so adding them does NOT inflate `n_elem` for slides
    # already counted via their parent P/LI/EM — the counter-test in
    # `tests/test_scan_slidev_composition.py` covers the regression risk.
    # `ABBR` is included because the deck-rendering layer uses it for
    # underlined glossary hits; without it, an inline abbreviation edge
    # cut would slip through.
    "A", "EM", "STRONG", "B", "I", "ABBR",
}


def content_overflow(r: dict) -> bool:
    """Un débordement est un défaut VISUEL seulement s'il coupe du contenu
    (texte, image, code). Un conteneur seul qui déborde (le classique
    `div.slidev-layout` à [0,0,980,587]) est une boîte CSS dont le dépassement
    n'est pas nécessairement visible — la slide n'est pas comptée.

    Les balises inline ``A``/``EM``/``STRONG``/``B``/``I``/``ABBR`` héritent
    en général de la bbox de leur bloc parent (P/LI/H*), donc l'ajouter ne
    change pas le verdict par slide — sauf quand le débordement touche
    l'inline lui-même (slide 10 @ #14888/#15661 deck 05-théorie-des-jeux :
    ``EM > A > A > A`` ancre multi-notebooks coupée à +1 px, rendue
    ``container_only: true`` alors que la coupure est techniquement réelle).
    """
    return any(h.get("tag") in CONTENT_TAGS for h in r.get("hors_canvas", []))


def occupation_flagged(r: dict, canvas_h: int) -> bool:
    """Composition déséquilibrée (image plaquée sur un bord / bande vide).

    Quatre formes calibrées par leurs faux négatifs (#13223) — un seuil qui
    n'attrape pas la slide à `gap_left_pct: 71.4` n'est pas un seuil, c'est un
    chemin de flagging mort. Un constat suffit, parmi :

      F1 — bande unilatérale marquée (gap >= 55 %) : slide 7 @ 166195bfc
            (gap_left_pct=71.4, gap_right_pct=2.0).
      F2 — bande modérée + décentrage (gap >= 40 % ET |offset| >= 25 %).
      F3 — image unique très décentrée (n_images==1 ET |offset| >= 30 %).
      F4 — régression préservée : gap >= 25 % + saturation verticale
            (débordement contenu ou content_bottom > 0.95*canvas_h). Couvre
            les compositions qui coupent réellement.

    Le seuil 55 % est volontairement plus strict que 40 % : il évite de
    ratisser les compositions « image centrée-légèrement décalée » qui ne
    sont pas un défaut de mise en page, tout en attrapant le cas fondateur.
    """
    occ = r.get("occupation")
    if not occ:
        return False
    gap_left = occ.get("gap_left_pct", 0)
    gap_right = occ.get("gap_right_pct", 0)
    offset = abs(occ.get("center_offset_pct", 0))
    n_images = occ.get("n_images", 0)
    # F1 — bande unilatérale marquée
    if gap_left >= 55 or gap_right >= 55:
        return True
    # F2 — bande modérée + décentrage cumulé
    if (gap_left >= 40 or gap_right >= 40) and offset >= 25:
        return True
    # F3 — image unique très décentrée (pas de dispersion pour s'auto-corriger)
    if n_images == 1 and offset >= 30:
        return True
    # F4 — ancienne forme préservée (gap >= 25 + saturation verticale)
    side_empty = gap_left > 25 or gap_right > 25
    if side_empty:
        overflow = content_overflow(r)
        bottom = occ.get("content_bottom", 0)
        if overflow or bottom > canvas_h * 0.95:
            return True
    return False


def github_annotations(report: dict, slides_md: Path) -> list[str]:
    """Rend les constats en ::warning file=,line= (format GitHub Actions)."""
    lines_by_slide = {int(k): v for k, v in (report.get("_slide_lines") or {}).items()}
    out: list[str] = []
    rel = slides_md.as_posix()
    for r in report.get("results", []):
        line = lines_by_slide.get(r["slide"], 1)
        head = (r.get("text_head") or "?")[:40].replace("\n", " ")
        if r.get("hors_canvas"):
            if content_overflow(r):
                for h in r.get("hors_canvas", [])[:3]:
                    out.append(
                        f"::warning file={rel},line={line}::[HORS_CANVAS] slide {r['slide']} ({head}) — "
                        f"{h['tag']}.{h['cls'][:30]} bbox={h['bbox']}"
                    )
            else:
                h = r["hors_canvas"][0]
                out.append(
                    f"::notice file={rel},line={line}::[HORS_CANVAS container-only] slide {r['slide']} ({head}) — "
                    f"boîte CSS {h['tag']}.{h['cls'][:30]} bbox={h['bbox']} sans contenu coupé"
                )
        for c in r.get("chevauchements", [])[:3]:
            out.append(
                f"::warning file={rel},line={line}::[CHEVAUCHEMENT] slide {r['slide']} ({head}) — "
                f"{c['a']} × {c['b']} overlap={c['overlap']}px "
                f"element_overlap={c.get('element_overlap')}px"
            )
        if r.get("chevauchements_eteints"):
            out.append(
                f"::notice file={rel},line={line}::[CHEVAUCHEMENT-FANTOME] slide {r['slide']} ({head}) — "
                f"{r['chevauchements_eteints']} effleurement(s) Range éteint(s) par la "
                f"confirmation élément (#15695) : boîtes élément disjointes, rien à l'écran"
            )
        for rv in r.get("recouvrements", [])[:3]:
            out.append(
                f"::warning file={rel},line={line}::[RECOUVREMENT-TEXTE-IMAGE] slide {r['slide']} — "
                f"«{rv['texte'][:40]}» repeint par {rv['image']} "
                f"overlap={rv['overlap']}px alpha={rv['alpha_zone']} "
                f"texte_bbox={rv['texte_bbox']} img_rendu={rv['image_bbox_rendu']}"
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
    # Import lazy : les fonctions pures (split, triage) restent importables
    # sans playwright — les tests unitaires n'en ont pas besoin (la mesure
    # navigateur est couverte par le contrôle positif, cf tests/).
    from playwright.sync_api import sync_playwright

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
    n_hors = sum(1 for r in results if content_overflow(r))
    n_chev = sum(1 for r in results if r.get("chevauchements"))
    n_eteints = sum(r.get("chevauchements_eteints") or 0 for r in results)
    n_rec = sum(1 for r in results if r.get("recouvrements"))
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
            signals = content_overflow(ctrl) or bool(ctrl.get("chevauchements"))
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
        "n_chevauchements_eteints": n_eteints,
        "n_recouvrements": n_rec,
        "n_occupation_flagged": n_occ,
        "recouvrement_borne": (
            "ADVISORY — signalé, non compté dans le code retour "
            "(taux de faux positifs à mesurer avant tout câblage bloquant)"
        ),
        "controle_positif_ok": ctrl_positif_ok,
        "controle_positif_msg": ctrl_positif_msg,
        "controle_positif_armed": args.baseline_slide is not None,
        "controle_positif_warning": (
            None if args.baseline_slide is not None
            else "scan sans contrôle positif armé : 'rien à signaler' est "
                 "indistinguable d'un chemin de flagging mort — passer "
                 "--baseline-slide <N> pour distinguer"
        ),
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
