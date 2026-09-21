#!/usr/bin/env python3
"""nb_view.py — vue structurelle compacte d'un notebook .ipynb (protocole FULL READ, leçon densité #13410/#17040).

Problème : un notebook avec images inline (base64) peut faire plusieurs MB —
la lecture JSON brute sature le contexte du reviewer.

Solution : vue dérivée qui préserve TOUTE la structure (ordre des cellules,
types, headers, sources, outputs textuels) mais remplace les payloads binaires
par des marqueurs compacts `[IMAGE png ~148KB]`. La détection de saccage
(doublons de sections, lectures mal placées) ne nécessite PAS les pixels —
seulement la séquence des cellules et leurs textes.

Usage :
    gh api repos/OWNER/REPO/contents/PATH.ipynb --jq .content | base64 -d > nb.ipynb
    python3 nb_view.py nb.ipynb [--max-src 600] [--max-out 300]

Sortie : une cellule par bloc — index, type, header/1re ligne, source (tronquée),
outputs (stream tronqué, images = marqueur, texte tronqué). Fin : résumé des
headers markdown + DOUBLONS détectés + gates #17040 (lectures successives).
"""
import json
import sys
import base64
import argparse


def fmt_bytes(n: int) -> str:
    for unit in ["B", "KB", "MB"]:
        if n < 1024:
            return f"{n:.0f}{unit}"
        n /= 1024
    return f"{n:.0f}GB"


def first_header(src: str) -> str | None:
    for line in src.splitlines():
        s = line.strip()
        if s.startswith("#"):
            return s
    return None


def out_summary(out: dict, max_out: int) -> str:
    t = out.get("output_type", "?")
    if t == "stream":
        txt = "".join(out.get("text", []))
        body = txt.strip().replace("\n", " ⏎ ")
        if len(body) > max_out:
            body = body[:max_out] + f"…(+{len(txt)-max_out}c)"
        return f"stream[{len(txt)}c]: {body}" if body else f"stream[{len(txt)}c]: (vide)"
    if t in ("display_data", "execute_result"):
        data = out.get("data", {})
        parts = []
        for mime, payload in data.items():
            if mime.startswith("image/") or mime == "application/pdf":
                if isinstance(payload, str):
                    approx = len(payload) * 3 // 4  # base64 → bytes
                    parts.append(f"[{mime} ~{fmt_bytes(approx)}]")
                else:
                    parts.append(f"[{mime} liste]")
            elif isinstance(payload, list):
                txt = "".join(payload)
                body = txt.strip().replace("\n", " ⏎ ")
                if len(body) > max_out:
                    body = body[:max_out] + f"…(+{len(txt)-max_out}c)"
                parts.append(f"{mime}[{len(txt)}c]: {body}" if body else f"{mime}[{len(txt)}c]: (vide)")
            elif isinstance(payload, str):
                body = payload.strip().replace("\n", " ⏎ ")
                if len(body) > max_out:
                    body = body[:max_out] + f"…(+{len(payload)-max_out}c)"
                parts.append(f"{mime}: {body}")
        return f"{t}: " + " | ".join(parts) if parts else f"{t}: (vide)"
    if t == "error":
        return f"ERROR: {out.get('ename','?')}: {out.get('evalue','')[:max_out]}"
    return t


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    ap.add_argument("--max-src", type=int, default=600, help="caractères max de source par cellule")
    ap.add_argument("--max-out", type=int, default=300, help="caractères max d'output texte")
    args = ap.parse_args()

    raw = open(args.path, "rb").read()
    nb = json.loads(raw)

    print(f"=== VUE NOTEBOOK {args.path} ({fmt_bytes(len(raw))} JSON brut, {len(nb['cells'])} cellules) ===")
    headers = []          # (index, header markdown)
    md_lectures = []      # cellules markdown dont le 1er mot ressemble à une « lecture »
    last_code_with_out = None

    for i, c in enumerate(nb["cells"]):
        ct = c["cell_type"]
        src = "".join(c.get("source", []))
        tag = f"[{i:02d} {ct.upper()[:4]}]"
        if ct == "markdown":
            h = first_header(src) or (src.strip().split("\n")[0][:70] if src.strip() else "(vide)")
            headers.append((i, h))
            print(f"{tag} H: {h[:90]}")
            body = src.strip()
            if len(body) > args.max_src:
                body = body[:args.max_src] + f"…(+{len(src)-args.max_src}c)"
            if body and body != h:
                for line in body.split("\n")[:8]:
                    print(f"       | {line[:100]}")
        elif ct == "code":
            ec = c.get("execution_count")
            head = src.strip().split("\n")[0][:70] if src.strip() else "(vide)"
            print(f"{tag} CODE exec={ec}: {head}")
            body = src.strip()
            if len(body) > args.max_src:
                body = body[:args.max_src] + f"…(+{len(src)-args.max_src}c)"
                print(f"       | {body[:args.max_src]}")
            outs = c.get("outputs", [])
            has_real_out = False
            for o in outs:
                s = out_summary(o, args.max_out)
                if not s.startswith(("stream[0c]", "stream[") ) or "[0c]" not in s:
                    has_real_out = True
                print(f"       OUT {s}")
            if outs and has_real_out:
                last_code_with_out = i
        else:
            print(f"{tag} {ct.upper()}: {src.strip()[:70]}")

    # --- Gates #17040 (assistés) ---
    print("\n=== SYNTHÈSE GATES #17040 ===")
    seen = {}
    dups = []
    for i, h in headers:
        key = h.strip().lower().rstrip("# ").strip()
        if len(key) > 4:
            if key in seen:
                dups.append((seen[key], i, h))
            else:
                seen[key] = i
    if dups:
        print(f"⚠️ HEADERS DOUBLÉS ({len(dups)}) :")
        for a, b, h in dups:
            print(f"   cellules {a} et {b} : « {h[:80]} »")
    else:
        print("✓ aucun header markdown dupliqué à l'identique")

    # lectures successives (2+ markdown non-header qui se suivent) — heuristique
    run = []
    runs = []
    for i, c in enumerate(nb["cells"]):
        if c["cell_type"] == "markdown":
            src = "".join(c.get("source", [])).strip()
            if src and not src.startswith("#"):
                run.append(i)
                continue
        if len(run) >= 2:
            runs.append(run)
        run = []
    if len(run) >= 2:
        runs.append(run)
    if runs:
        print(f"⚠️ SÉQUENCES de 2+ cellules markdown de prose consécutives (candidats lectures empilées, à consolider) : {[r for r in runs]}")
    else:
        print("✓ pas de séquence de 2+ cellules de prose consécutives")


if __name__ == "__main__":
    main()
