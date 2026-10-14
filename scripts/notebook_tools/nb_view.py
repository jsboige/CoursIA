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

Sortie : une cellule par bloc — index, type, header/1re ligne, source (tronquée
avec marqueur explicite), outputs (stream tronqué, images = marqueur, texte
tronqué). Fin : analyse structurelle (doublons de headers normalisés, lectures
empilées). Cette analyse ASSISTE les gates #17040, elle ne les remplace pas —
les critères 3 (narration d'exercice) et 4 (seuil de densité 1200) et la
vérification « valeurs citées présentes dans les outputs » restent à la lecture
humaine (protocole FULL READ).
"""
import json
import sys
import re
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


def norm_header(h: str) -> str:
    """Clé de dédoublonnage : retire marquage markdown + numérotation de tête.

    « ## 3. Interprétation » et « ## 4. Interprétation » → même clé
    « interprétation » (motif mesuré #17078 : sections répétées numérotées).
    """
    s = h.strip().lower()
    s = re.sub(r"^#+\s*", "", s)
    s = re.sub(r"^[\d\s\.\-\)\]\—–:;·]+", "", s)
    return s.strip()


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

    try:
        with open(args.path, "rb") as f:
            raw = f.read()
    except OSError as e:
        sys.exit(f"erreur : impossible de lire {args.path} : {e}")
    try:
        nb = json.loads(raw)
    except json.JSONDecodeError:
        sys.exit(f"erreur : {args.path} n'est pas un JSON valide (404/HTML de gh api, base64 non décodé ?)")
    if not isinstance(nb, dict) or "cells" not in nb or not isinstance(nb["cells"], list):
        sys.exit(f"erreur : {args.path} est un JSON valide mais pas un notebook (clé 'cells' absente)")

    print(f"=== VUE NOTEBOOK {args.path} ({fmt_bytes(len(raw))} JSON brut, {len(nb['cells'])} cellules) ===")
    headers = []          # (index, header markdown)
    code_with_out = set() # index des cellules code avec un output réel non vide

    for i, c in enumerate(nb["cells"]):
        ct = c.get("cell_type", "?")
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
                # corps intégral : unique point de troncature = max_src, TOUJOURS marqué
                for line in body.split("\n"):
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
            # output réel = non-stream, ou stream dont le texte agrégé est non vide
            # (pas de test de sous-chaîne sur le rendu : « [0c] » littéral serait mal classé)
            has_real_out = any(
                o.get("output_type") != "stream" or "".join(o.get("text", [])).strip()
                for o in outs
            )
            if has_real_out:
                code_with_out.add(i)
            for o in outs:
                print(f"       OUT {out_summary(o, args.max_out)}")
        else:
            print(f"{tag} {ct.upper()}: {src.strip()[:70]}")

    # --- Analyse structurelle (assiste les gates #17040, ne les remplace pas) ---
    print("\n=== ANALYSE STRUCTURELLE (assiste gates #17040 — ne les remplace pas) ===")
    seen = {}
    dups = []
    for i, h in headers:
        key = norm_header(h)
        if len(key) > 4:
            if key in seen:
                dups.append((seen[key], i, h))
            else:
                seen[key] = i
    if dups:
        print(f"⚠️ HEADERS DOUBLÉS après normalisation ({len(dups)}) — numérotation retirée :")
        for a, b, h in dups:
            print(f"   cellules {a} et {b} : « {h[:80]} »")
    else:
        print("✓ aucun header dupliqué (après retrait de la numérotation)")

    # séquences de 2+ cellules markdown de prose consécutives ;
    # si la 1re suit une cellule code POURVUE d'output réel → candidat « lectures
    # empilées » : critère 1 #17040 (max UNE lecture par output, immédiatement après)
    run = []
    runs = []
    for i, c in enumerate(nb["cells"]):
        if c.get("cell_type") == "markdown":
            src = "".join(c.get("source", [])).strip()
            if src and not src.startswith("#"):
                run.append(i)
                continue
        if len(run) >= 2:
            runs.append(run)
        run = []
    if len(run) >= 2:
        runs.append(run)
    stacked = []
    plain = []
    for r in runs:
        prev = r[0] - 1
        if prev >= 0 and prev in code_with_out:
            stacked.append(r)
        else:
            plain.append(r)
    if stacked:
        print(f"⚠️ LECTURES EMPI LÉES (critère 1 #17040) : 2+ cellules de prose consécutives juste après l'output de la cellule code : {stacked}")
    if plain:
        print(f"⚠️ séquences de 2+ cellules de prose consécutives (hors output, à consolider) : {plain}")
    if not stacked and not plain:
        print("✓ pas de séquence de 2+ cellules de prose consécutives")

    print("non vérifié ici : critère 1 placement exact (seules les empilées sont détectées), "
          "critère 2 valeurs citées présentes dans les outputs, critère 3 narration d'exercice, "
          "critère 4 seuil de densité 1200 — lecture humaine requise (FULL READ).")


if __name__ == "__main__":
    main()
