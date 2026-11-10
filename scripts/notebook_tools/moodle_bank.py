#!/usr/bin/env python3
"""Banque de QCM Moodle -> YAML diffable (issue #18223).

Deux sous-commandes :

    convert --src <dossier Rattrapages> --out <banque repo>
        Lit les exports XML Moodle du dossier (les .html/.doc/.pdf redondants
        sont ignores), deduplique les questions entre exports, classe chaque
        question par theme, applique les decisions du mainteneur (28/09) :
        publie IA (5 chapitres) + apprentissage profond, exclut C#/.NET,
        differe Big Data. Les figures non republiables suivent la
        PUBLICATION_POLICY (redessinees, remplacees par un tableau, ou
        neutralisees) ; les autres images embarquees en base64 sont extraites vers
        <out>/images/. Les decisions de relecture du mainteneur (06/10,
        #18285) sont reappliquees : questions retirees (RETIRED) et cles
        corrigees avec leur note (KEY_CORRECTIONS). Rend un rapport : lues / publiées / exclues / différées /
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

# `redraw_qcm_figures` vit dans ce meme dossier : le rendre importable quel
# que soit le point d'entree (CLI, tests, import direct).
_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

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

# Politique de publication des figures (revue ai-01 #18263, 2026-09-28).
# Trois figures des exports ne peuvent pas entrer en l'etat dans un depot
# public : la photographie d'une page du manuel Russell & Norvig (ia4-004),
# deux captures d'ecran de la meme table du manuel (ia4-006/007), une URL
# Dropbox personnelle (ia2-010). La politique vit ICI pour que le produit
# reste REPRODUCTIBLE : une re-conversion reapplique ces decisions au lieu de
# reintroduire les figures d'origine.
#   redrawn : le fichier source n'est pas extrait ; la figure est redessinee a
#             partir de ses seules valeurs par redraw_qcm_figures.py
#   table   : le fichier source n'est pas extrait ; la table du manuel est
#             restituee en tableau markdown (les nombres, pas la capture)
#   external: aucune extraction ; la reference externe de l'enonce est
#             remplacee par un marqueur neutre (jeton de partage personnel)
PUBLICATION_POLICY = {
    "ia4-004": "redrawn",
    "ia4-006": "table",
    "ia4-007": "table",
    "ia2-010": "external",
}

# Decisions du mainteneur du 2026-10-06 (#18285) sur la relecture
# RELECTURE-2026-09.md. Comme PUBLICATION_POLICY, elles vivent dans le
# convertisseur pour qu'une re-conversion les REAPPLIQUE : la source Moodle
# n'est pas reecrite, la banque l'est, et chaque correction laisse une note
# dans l'explication de la question.

# Questions retirees de la banque. Leur identifiant n'est pas reattribue : les
# questions suivantes gardent le leur (PUBLICATION_POLICY, KEY_CORRECTIONS et
# les consommateurs de #18207 les citent).
RETIRED = {
    "ia2-010": "doublon de ia2-027 (meme question, export 2020, figure embarquee)",
}

# Cles corrigees. `cles` : texte d'option -> valeur correcte ; `textes` : texte
# d'option -> texte corrige (quand la bonne reponse est absente des options) ;
# `dedoublonner` : retire le second exemplaire d'une option dupliquee dans la
# source. Chaque valeur a ete recalculee, le calcul est dans la note.
KEY_CORRECTIONS = {
    "ia2-018": {
        "cles": {"3.2": False},
        "note": "sous C1, Min choisit 2 puis 4 (0,8 × 2 + 0,2 × 4 = 2,4) ; sous C2, 1 puis 5 "
                "(0,9 × 1 + 0,1 × 5 = 1,4). Max retient 2,4. La valeur 3,2, cochée dans la "
                "source, ne se déduit d'aucune lecture de l'arbre.",
    },
    "ia2-019": {
        "cles": {"4.7": False},
        "note": "sous C1, Min choisit 5 puis 4 (0,8 × 5 + 0,2 × 4 = 4,8) ; sous C2, 8 puis 5 "
                "(0,9 × 8 + 0,1 × 5 = 7,7). Max retient 7,7. La valeur 4,7, cochée dans la "
                "source, ne se déduit d'aucune lecture de l'arbre.",
    },
    "ia3-015": {
        "cles": {"¬(¬p∧¬q)": False},
        "note": "¬(¬p∧¬q) équivaut à p∨q, et non à p⇒q (c'est-à-dire ¬p∨q). Contre-exemple : "
                "p vrai et q faux rendent p∨q vrai et p⇒q faux.",
    },
    "ia3-019": {
        "cles": {"¬(¬p∧¬q)": True},
        "note": "¬(¬p∧¬q) équivaut à p∨q, qui n'est pas équivalent à p⇒q (contre-exemple : "
                "p vrai et q faux). Cette option fait donc partie des réponses attendues.",
    },
    "ia4-011": {
        "cles": {"62/64": False, "59/64": True},
        "note": "chaque combinaison de trois symboles a une probabilité de 1/64. Gain espéré "
                "= (20 + 16 + 5 + 3)/64 + 2 × 3/64 (CERISE/CERISE/autre) + 1 × 9/64 "
                "(CERISE/autre/autre) = 59/64.",
    },
    "ia4-018": {
        "textes": {"378.92€": "389.47€"},
        "cles": {"389.47€": True},
        "note": "P(test réussi) = 0,8 × 0,7 + 0,35 × 0,3 = 0,665, donc P(bon état | réussi) = "
                "0,56/0,665 = 0,8421. Utilité espérée = 0,8421 × (2000 − 1500) + 0,1579 × "
                "(2000 − 700 − 1500) = 389,47 €. La valeur 378,92 € de la source ne se déduit "
                "d'aucun calcul cohérent avec l'énoncé.",
    },
    "ia5-002": {
        "dedoublonner": True,
        "note": "la source portait cette option en deux exemplaires, l'un compté juste, "
                "l'autre faux ; le second exemplaire est retiré.",
    },
    "ia5-007": {
        "cles": {"Arbres de décision": False},
        "note": "les arbres de décision sont un modèle non paramétrique : leur nombre de "
                "paramètres croît avec les données (Russell et Norvig ; documentation de "
                "scikit-learn, « Decision Trees »).",
    },
}


def apply_key_corrections(qid: str, rec: dict) -> dict:
    """Applique KEY_CORRECTIONS a une question deja convertie.

    Echoue BRUYAMMENT si une option visee n'existe pas : une source modifiee ne
    doit pas laisser passer une correction qui ne s'applique plus.
    """
    corr = KEY_CORRECTIONS.get(qid)
    if not corr:
        return rec
    options = rec["options"]
    for old, new in corr.get("textes", {}).items():
        hits = [o for o in options if o["texte"] == old]
        if len(hits) != 1:
            raise ValueError(f"{qid}: option a reecrire '{old}' trouvee {len(hits)} fois")
        hits[0]["texte"] = new
    if corr.get("dedoublonner"):
        seen: set[str] = set()
        kept = []
        for o in options:
            if o["texte"] in seen:
                continue
            seen.add(o["texte"])
            kept.append(o)
        if len(kept) == len(options):
            raise ValueError(f"{qid}: aucune option dupliquee a retirer")
        rec["options"] = options = kept
    for texte, valeur in corr.get("cles", {}).items():
        hits = [o for o in options if o["texte"] == texte]
        if len(hits) != 1:
            raise ValueError(f"{qid}: option a corriger '{texte}' trouvee {len(hits)} fois")
        hits[0]["correcte"] = valeur
    note = "Correction de la relecture d'octobre 2026 : " + corr["note"]
    rec["explication"] = (rec["explication"] + "\n\n" if rec.get("explication") else "") + note
    return rec

# Table de distribution conjointe du dentiste (Russell & Norvig, exemple du
# dentiste) : restituee en tableau markdown a la place de la capture d'ecran
# du manuel. Controle des valeurs attendues par les enonces : P(carie | mal
# aux dents) = 0.12/0.2 = 0.6 et P(non carie | pas mal aux dents) =
# 0.72/0.8 = 0.9, les deux cles correctes de ia4-006 et ia4-007.
DENTIST_TABLE = (
    "\n"  # ligne vide : le tableau suit l'intro comme bloc markdown
    "| Carie | Mal aux dents | Croche | P |\n"
    "|---|---|---|---|\n"
    "| V | V | V | 0.108 |\n"
    "| V | V | F | 0.012 |\n"
    "| V | F | V | 0.072 |\n"
    "| V | F | F | 0.008 |\n"
    "| F | V | V | 0.016 |\n"
    "| F | V | F | 0.064 |\n"
    "| F | F | V | 0.144 |\n"
    "| F | F | F | 0.576 |\n"
    "\n"
    "d'apres Russell et Norvig, Artificial Intelligence: A Modern Approach,"
    " exemple du dentiste."
)


def apply_publication_policy(policy: str, enonce: str, img_dir: str) -> str:
    """Remplace la reference de figure d'un enonce selon PUBLICATION_POLICY."""
    if policy == "table":
        return re.sub(r"\[figure: [^\]]*\]", DENTIST_TABLE, enonce)
    if policy == "external":
        return re.sub(r"\[figure: [^\]]*\]", "[figure externe non disponible]", enonce)
    # "redrawn" : le trace ne depend que des valeurs, il est regenerable.
    # Import local (l'organe check et les tests n'ont pas besoin de matplotlib)
    # et echec BRUYANT si l'environnement ne peut pas redessiner : jamais de
    # banque publiee avec une figure manquante.
    from redraw_qcm_figures import draw_ia4_004

    png = draw_ia4_004(img_dir)
    return re.sub(r"\[figure: [^\]]*\]", f"[figure: images/{os.path.basename(png)}]", enonce)


class BankDumper(yaml.SafeDumper):
    """Dumper de la banque : les enonces a tableau markdown sortent en bloc
    litteral (`|-`), lisibles et stables ; le reste garde le style courant."""


def _represent_str(dumper: yaml.SafeDumper, data: str):
    style = "|" if ("\n" in data and re.search(r"(?m)^\|", data)) else None
    return dumper.represent_scalar("tag:yaml.org,2002:str", data, style=style)


BankDumper.add_representer(str, _represent_str)


_SUPERSCRIPT_RE = re.compile(
    r'<span[^>]*style="[^"]*vertical-align:\s*super[^"]*"[^>]*>(.*?)</span>|<sup>(.*?)</sup>',
    re.S,
)


def _superscript(m: re.Match) -> str:
    texte = re.sub(r"<[^>]+>", "", m.group(1) if m.group(1) is not None else m.group(2)).strip()
    if not texte:
        return ""
    return "^" + texte if len(texte) == 1 else f"^({texte})"


def html_to_text(s: str) -> str:
    # exposants : les exports portent les puissances en
    # <span style="...vertical-align:super">d</span>. Les aplatir faisait de
    # O(b^d) un « O(bd) » et fabriquait des options en double (ia2-008, #18285).
    s = _SUPERSCRIPT_RE.sub(_superscript, s or "")
    s = re.sub(r"<br\s*/?>", "\n", s)
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
            if qid in RETIRED:
                stats.setdefault("retired", []).append(f"{qid}: {RETIRED[qid]}")
                continue
            rec = {"id": qid, "theme": theme, "type": q["type"], "source": q["source"]}
            enonce = q["enonce_raw"]
            politique = PUBLICATION_POLICY.get(qid, "")
            # images embarquees : <file name base64> sous questiontext.
            # Une question a politique n'extrait pas son fichier source : la
            # figure est redessinee ou remplacee par du texte plus bas.
            for f in [] if politique else q["files"]:
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
            if politique:
                rec["enonce"] = apply_publication_policy(politique, rec["enonce"], img_dir)
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
            records.append(apply_key_corrections(qid, rec))
        path = os.path.join(out, f"{theme}.yaml")
        with open(path, "w", encoding="utf-8", newline="\n") as fh:
            yaml.dump(records, fh, Dumper=BankDumper, allow_unicode=True,
                      sort_keys=False, default_flow_style=False, width=100)
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
    for line in stats.get("retired", []):
        print(f"  RETIREE   {line}")
    print(f"  CLES CORRIGEES          : {len(KEY_CORRECTIONS)} (#18285)")
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
                # Meme texte d'option en double exemplaire avec des cles
                # contradictoires : defaut de source a dedoublonner par
                # KEY_CORRECTIONS, ou perte de mise en forme a la conversion (les
                # exposants aplatis de ia2-008, #18285). ATTENTION sans echec.
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
