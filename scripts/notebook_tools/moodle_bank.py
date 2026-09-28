#!/usr/bin/env python3
"""Banque de QCM Moodle -> YAML diffable (issue #18223).

Deux sous-commandes :

    convert --src <dossier Rattrapages> --out <banque repo>
        Lit les exports XML Moodle du dossier (les .html/.doc/.pdf redondants
        sont ignores), deduplique les questions entre exports, classe chaque
        question par theme, applique les decisions du mainteneur (28/09) :
        publie IA (5 chapitres) + apprentissage profond, exclut C#/.NET,
        differe Big Data. Les images embarquees en base64 sont extraites vers
        <out>/images/. Rend un rapport : lues / publiées / exclues / différées /
        doublons / types non pris en charge.

    check --bank <banque repo>
        Valide chaque question commise : identifiant unique, énoncé non vide,
        au moins une option correcte, exactement une si choix unique,
        appariement complet, image presente si referencee. exit 1 sinon.

Les XML bruts restent sur le Drive (1,8 Mo, images base64) ; seul le produit
converti entre dans le depot. Le format vise a etre consomme tel quel par le
dispositif d'auto-evaluation de #18207 (fonction verifier(...)) sans conversion
supplementaire.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import html as htmllib
import os
import re
import sys
import xml.etree.ElementTree as ET

import yaml

# Ordre canonique de lecture : chronologique. En cas de doublon, la premiere
# occurrence rencontree gagne (source la plus ancienne citee dans `source`).
SOURCE_ORDER = [
    ("quiz-MSMEM4EN08", "MSMEM4EN08 2018"),
    ("quiz-INGPA-FIN4000", "INGPA-FIN4000 2020"),
    ("quiz-MSMIN5IN31-21-Questions IA", "MSMIN5IN31 IA 2021"),
    ("quiz-MSMIS5IN10", "MSMIS5IN10 eval seance 6 2022"),
    ("quiz-MSMIN5IN31-21-Questions JSBoige", "MSMIN5IN31 JSBoige 2022"),
]

# Classification (ordre = priorite). Decisions du mainteneur 28/09 :
#   publie    : chapitres IA 1-5 + evaluation seance apprentissage profond
#   exclu     : C# et .NET (pas de cours d'accueil dans le depot)
#   differe   : Big Data (jusqu'a creation d'une serie Big Data)
THEME_RULES = [
    (re.compile(r"evaluation\s+séance", re.I), "dl-evaluation-seance", "publie"),
    (re.compile(r"Programmation en C#", re.I), "csharp-dotnet", "exclu"),
    (re.compile(r"Big Data", re.I), "big-data", "differe"),
    (re.compile(r"1\.\s*Introduction", re.I), "ia-1-introduction-agents", "publie"),
    (re.compile(r"2\.\s*Résolution", re.I), "ia-2-resolution-problemes", "publie"),
    (re.compile(r"3\.\s*Logique", re.I), "ia-3-logique-bases-connaissances", "publie"),
    (re.compile(r"4\.\s*Systèmes probabilistes", re.I), "ia-4-systemes-probabilistes", "publie"),
    (re.compile(r"5\.\s*Apprentissage", re.I), "ia-5-apprentissage", "publie"),
]

THEME_ID_PREFIX = {
    "ia-1-introduction-agents": "ia1",
    "ia-2-resolution-problemes": "ia2",
    "ia-3-logique-bases-connaissances": "ia3",
    "ia-4-systemes-probabilistes": "ia4",
    "ia-5-apprentissage": "ia5",
    "dl-evaluation-seance": "dl",
}

SUPPORTED_TYPES = ("multichoice", "truefalse", "matching")


def html_to_text(s: str) -> str:
    s = re.sub(r"<br\s*/?>", "\n", s or "")
    s = re.sub(r"</p>\s*", "\n", s)
    # le <img> porte la reference de la figure extraite : la conserver en
    # texte AVANT le nettoyage des balises, sinon l'image commise devient
    # orpheline (aucun enonce ne la reference -- review NanoClaw #18263)
    s = re.sub(r'<img[^>]*\ssrc="([^"]+)"[^>]*>', r"[figure: \1]", s)
    s = re.sub(r"<[^>]+>", "", s)
    s = htmllib.unescape(s)
    return re.sub(r"[ \t]+", " ", s).strip()


def norm_key(s: str) -> str:
    s = html_to_text(s)
    return re.sub(r"\s+", " ", s).lower()


def source_label(filename: str) -> str | None:
    for prefix, label in SOURCE_ORDER:
        if filename.startswith(prefix):
            return label
    return None


def classify(category: str) -> tuple[str, str] | None:
    for rx, theme, decision in THEME_RULES:
        if rx.search(category):
            return theme, decision
    return None


def read_export(path: str, stats: dict) -> list[dict]:
    """Lit un export XML ; rend la liste brute des questions (non dedupliquees)."""
    fname = os.path.basename(path)
    label = source_label(fname)
    if label is None:
        stats.setdefault("skipped", []).append(f"{fname}: nom de quiz inconnu")
        return []
    src_idx = [i for i, (pref, _) in enumerate(SOURCE_ORDER) if fname.startswith(pref)][0]
    root = ET.parse(path).getroot()
    category = "(sans categorie)"
    out = []
    for q in root.findall("question"):
        qtype = q.get("type")
        if qtype == "category":
            category = (q.findtext("category/text") or "").replace("$course$/top/", "")
            continue
        if qtype not in SUPPORTED_TYPES:
            stats.setdefault("unsupported", []).append(f"{fname}: type={qtype}")
            continue
        out.append({
            "type": qtype,
            "name": html_to_text(q.findtext("name/text") or ""),
            "src_idx": src_idx,
            "order": len(out),
            "enonce": html_to_text(q.findtext("questiontext/text") or ""),
            "enonce_raw": q.findtext("questiontext/text") or "",
            "files": q.find("questiontext").findall("file") if q.find("questiontext") is not None else [],
            "generalfeedback": html_to_text(q.findtext("generalfeedback/text") or ""),
            "single": (q.findtext("single") or "true").strip().lower() in ("true", "1"),
            "answers": q.findall("answer"),
            "subquestions": q.findall("subquestion"),
            "category": category,
            "source": label,
        })
    stats.setdefault("read", []).append(f"{label}: {len(out)} questions")
    return out


def convert(src: str, out: str) -> int:
    files = []
    for d in (src, os.path.join(src, "Ajout Big Data"), os.path.join(src, "MSMIN - IA - Moodle - Banque de question")):
        if not os.path.isdir(d):
            continue
        for f in sorted(os.listdir(d)):
            if f.endswith(".xml") and source_label(f):
                files.append(os.path.join(d, f))
    # ordre canonique : SOURCE_ORDER definit la priorite du dedoublonnage
    files.sort(key=lambda p: [i for i, (pref, _) in enumerate(SOURCE_ORDER) if os.path.basename(p).startswith(pref)][0])

    stats: dict = {}
    raw = []
    for path in files:
        raw.extend(read_export(path, stats))

    # dedoublonnage : cle = enonce normalise + options normalisees triees
    seen: dict[str, str] = {}
    questions: list[dict] = []
    duplicates = 0
    for q in raw:
        key_parts = [norm_key(q["enonce"])]
        if q["subquestions"]:
            key_parts.extend(sorted(norm_key(s.findtext("text") or "") for s in q["subquestions"]))
        else:
            key_parts.extend(sorted(norm_key(a.findtext("text") or "") for a in q["answers"]))
        key = hashlib.sha1("|".join(key_parts).encode("utf-8")).hexdigest()
        if key in seen:
            duplicates += 1
            continue
        seen[key] = q["source"]
        questions.append(q)

    # classification + decisions
    published: dict[str, list[dict]] = {}
    counts = {"publie": 0, "exclu": 0, "differe": 0}
    unclassified: list[str] = []
    for q in questions:
        cls = classify(q["category"])
        if cls is None:
            unclassified.append(f"{q['source']} / {q['category'][:60]} : {q['enonce'][:50]}")
            continue
        theme, decision = cls
        q["theme"], q["decision"] = theme, decision
        counts[decision] += 1
        if decision == "publie":
            published.setdefault(theme, []).append(q)

    # extraction des images + ecriture des fichiers de banque
    img_dir = os.path.join(out, "images")
    os.makedirs(img_dir, exist_ok=True)
    total_images = 0
    written = {}
    for theme in sorted(published):
        # tri stable : ordre de lecture canonique (source, puis ordre dans l'export)
        qs = sorted(published[theme], key=lambda q: (q["src_idx"], q["order"]))
        prefix = THEME_ID_PREFIX[theme]
        records = []
        for i, q in enumerate(qs, start=1):
            qid = f"{prefix}-{i:03d}"
            rec = {"id": qid, "theme": theme, "type": q["type"], "source": q["source"]}
            enonce = q["enonce_raw"]
            # images embarquees : <file name base64> sous questiontext
            for f in q["files"]:
                name = f.get("name") or "image.png"
                data = (f.text or "").strip()
                try:
                    blob = base64.b64decode(data)
                except Exception:
                    stats.setdefault("bad_images", []).append(f"{qid}: base64 invalide ({name})")
                    continue
                ext = os.path.splitext(name)[1] or ".png"
                img_name = qid + ext
                with open(os.path.join(img_dir, img_name), "wb") as fh:
                    fh.write(blob)
                enonce = enonce.replace(f"@@PLUGINFILE@@/{name}", f"images/{img_name}")
                total_images += 1
            rec["enonce"] = html_to_text(enonce)
            if q["type"] in ("multichoice", "truefalse"):
                options = []
                for a in q["answers"]:
                    texte = a.findtext("text") or ""
                    if q["type"] == "truefalse":
                        texte = "Vrai" if texte.strip().lower() == "true" else "Faux"
                    options.append({
                        "texte": html_to_text(texte),
                        "correcte": float(a.get("fraction") or 0) > 0,
                    })
                n_correct = sum(1 for o in options if o["correcte"])
                rec["choix_unique"] = bool(q["single"] and n_correct == 1)
                rec["options"] = options
                feedbacks = [html_to_text(a.findtext("feedback/text") or "") for a in q["answers"]]
                feedbacks = [f for f in feedbacks if f]
            else:  # matching
                rec["appariements"] = [
                    {"gauche": html_to_text(s.findtext("text") or ""),
                     "droite": html_to_text(s.findtext("answer/text") or "")}
                    for s in q["subquestions"]
                ]
                feedbacks = []
            explication = q["generalfeedback"]
            if feedbacks:
                explication = (explication + "\n\n" if explication else "") + \
                    "Feedback par option :\n- " + "\n- ".join(feedbacks)
            if explication:
                rec["explication"] = explication
            records.append(rec)
        path = os.path.join(out, f"{theme}.yaml")
        with open(path, "w", encoding="utf-8", newline="\n") as fh:
            yaml.safe_dump(records, fh, allow_unicode=True, sort_keys=False, default_flow_style=False, width=100)
        written[theme] = len(records)

    total_pub = sum(written.values())
    print("=== Rapport de conversion ===")
    for line in stats.get("read", []):
        print(f"  LU        {line}")
    for line in stats.get("skipped", []):
        print(f"  IGNORE    {line}")
    for line in stats.get("unsupported", []):
        print(f"  TYPE-NON-PRISEN-CHARGE {line}")
    print(f"  QUESTIONS LUES          : {len(raw)}")
    print(f"  DOUBLONS EcartES        : {duplicates}")
    print(f"  QUESTIONS DISTINCTES    : {len(questions)}")
    print(f"  PUBLIEES                : {total_pub}")
    for theme, n in sorted(written.items()):
        print(f"    {theme:38s} {n:4d}")
    print(f"  EXCLUES (csharp-dotnet) : {counts['exclu']}")
    print(f"  DIFFEREES (big-data)    : {counts['differe']}")
    print(f"  IMAGES EXTRAITES        : {total_images}")
    for line in stats.get("bad_images", []):
        print(f"  IMAGE-INVALIDE {line}")
    for line in unclassified:
        print(f"  NON-CLASSEE  {line}")
    if unclassified:
        print("ECHEC: questions non classees")
        return 1
    return 0


def check(bank: str) -> int:
    errors = []
    warnings = []
    ids = set()
    total = 0
    per_theme = {}
    referenced = set()
    for fname in sorted(os.listdir(bank)):
        if not fname.endswith(".yaml"):
            continue
        theme = fname[:-5]
        with open(os.path.join(bank, fname), encoding="utf-8") as fh:
            records = yaml.safe_load(fh) or []
        per_theme[theme] = len(records)
        for rec in records:
            total += 1
            qid = rec.get("id")
            if not qid:
                errors.append(f"{fname}: question sans id")
                continue
            if qid in ids:
                errors.append(f"id duplique: {qid}")
            ids.add(qid)
            if rec.get("theme") != theme:
                errors.append(f"{qid}: theme={rec.get('theme')} != fichier {theme}")
            if not rec.get("enonce", "").strip():
                errors.append(f"{qid}: enonce vide")
            if not rec.get("source"):
                errors.append(f"{qid}: source absente")
            qtype = rec.get("type")
            if qtype in ("multichoice", "truefalse"):
                options = rec.get("options") or []
                if len(options) < 2:
                    errors.append(f"{qid}: moins de deux options")
                n_correct = sum(1 for o in options if o.get("correcte"))
                if n_correct < 1:
                    errors.append(f"{qid}: aucune option correcte")
                elif rec.get("choix_unique") and n_correct != 1:
                    errors.append(f"{qid}: choix_unique mais {n_correct} correctes")
                texts = [o.get("texte") for o in options]
                if any(not (t or "").strip() for t in texts):
                    errors.append(f"{qid}: option vide")
                # Defaut de SOURCE Moodle (pas du convertisseur) : meme texte d'option
                # en double exemplaire avec des cles contradictoires. La banque reste
                # fidele a la source ; le defaut est signale dans RELECTURE-2026-09.md,
                # donc ATTENTION sans echec.
                keys_by_text = {}
                for o in options:
                    keys_by_text.setdefault((o.get("texte") or "").strip(), set()).add(bool(o.get("correcte")))
                for text, flags in keys_by_text.items():
                    if len(flags) > 1:
                        warnings.append(f"{qid}: option dupliquee a cles contradictoires : {text[:40]}")
            elif qtype == "matching":
                pairs = rec.get("appariements") or []
                if not pairs:
                    errors.append(f"{qid}: aucun appariement")
                for p in pairs:
                    if not (p.get("gauche") or "").strip() or not (p.get("droite") or "").strip():
                        errors.append(f"{qid}: appariement incomplet")
            else:
                errors.append(f"{qid}: type inconnu {qtype}")
            enonce = rec.get("enonce") or ""
            for m in re.finditer(r"images/([^\s)>\]]+)", enonce):
                if not os.path.isfile(os.path.join(bank, "images", m.group(1))):
                    errors.append(f"{qid}: image absente images/{m.group(1)}")
                else:
                    referenced.add(m.group(1))
            # figure annoncee mais non embarquee dans la banque (lien externe
            # d'origine ou figure absente de l'export) : defaut de source,
            # signale dans RELECTURE-2026-09.md
            if re.search(r"figure", enonce, re.I) and "images/" not in enonce:
                warnings.append(f"{qid}: figure annoncee sans reference embarquee")
    # sens inverse : tout fichier de images/ doit etre reference par un enonce
    # (sinon le convertisseur a extrait une figure que personne ne peut voir)
    img_dir = os.path.join(bank, "images")
    if os.path.isdir(img_dir):
        for f in sorted(os.listdir(img_dir)):
            if f not in referenced:
                errors.append(f"images/{f}: fichier orphelin (aucun enonce ne le reference)")
    print(f"=== Verification banque : {total} questions, {len(per_theme)} themes ===")
    for theme, n in sorted(per_theme.items()):
        print(f"    {theme:38s} {n:4d}")
    if errors:
        for e in errors[:40]:
            print(f"  ERREUR {e}")
        print(f"TOTAL ERREURS: {len(errors)}")
        return 1
    if warnings:
        for w in warnings:
            print(f"  ATTENTION {w}")
        print(f"TOTAL ATTENTIONS: {len(warnings)} (defauts de source, cf RELECTURE)")
    print("OK: banque valide")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("convert", help="XML Moodle -> banque YAML")
    c.add_argument("--src", required=True, help="dossier Rattrapages (GDrive)")
    c.add_argument("--out", required=True, help="dossier de banque dans le depot")
    k = sub.add_parser("check", help="valide la banque commise")
    k.add_argument("--bank", required=True)
    args = ap.parse_args()
    if args.cmd == "convert":
        return convert(args.src, args.out)
    return check(args.bank)


if __name__ == "__main__":
    sys.exit(main())
