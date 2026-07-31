#!/usr/bin/env python3
"""
migrate_cost_frontmatter_to_metadata.py — Migre le bloc cost YAML de la cellule#0
(LEGACY) vers `nb.metadata['cost']` (CANONIQUE), PUIS retire le bloc frontmatter.

Issues #8904 (markdown-rendering `[frontmatter_supersize]`) + #8056 (cost canonique).

CONTEXTE — pourquoi un simple strip perd de l'information
---------------------------------------------------------
`check_cost_metadata.py` lit `metadata['cost']` D'ABORD (canonique), et ne retombe
sur la cellule `---YAML---` (LEGACY) que si metadata.cost est absent. Tant que
metadata.cost est un squelette scan-generé PLUS PAUVRE que le frontmatter
(cpu_min=0, reduced_pedagogical=null, reproducibility='MED' aplatissant 'HIGH'/'MEDIUM',
datee de 3 jours APRES le frontmatter), supprimer le frontmatter a l'aveugle = perte
des vraies valeurs mesurees (incident #8908/#8959/#8963 CHANGES_REQUESTED ai-01).

Cette migration fait l'UNION AVANT la suppression :
  merged = {**metadata_cost, **frontmatter_cost}
Le frontmatter (source riche/authoritative) gagne sur les champs chevauchants ;
metadata.cost garde ses champs propres (ex. `qcc_tokens_est`, absent du frontmatter).
Apres migration, metadata.cost porte toutes les valeurs mesurees ET les champs
propres — il devient veritablement canonique, et le frontmatter devient retirable
sans perte.

SEUIL DE COHERENCE (litmus anti-LIGHT, cf check_cost_metadata.py)
-----------------------------------------------------------------
La migration n'ecrit QUE si elle est cohérente :
  - cell#0 doit demarrer par `---` (sinon : deja migree -> skip idempotent)
  - metadata.cost DOIT exister (sinon : refuse — il faut d'abord le peupler via
    populate_quantconnect_cost.py ; on ne Migre pas vers du vide)
  - le frontmatter doit contenir un bloc `cost:` valide
Le re-dump utilise `json.dumps(indent=1, ensure_ascii=False)+'\\n'` (LF-only),
round-trip byte-identique au original hors des champs migrés (technique #8908).

Usage
-----
  # Dry-run (defaut) — affiche ce qui serait migré, champ par champ
  python scripts/audit/migrate_cost_frontmatter_to_metadata.py <notebook.ipynb>...

  # Appliquer
  python scripts/audit/migrate_cost_frontmatter_to_metadata.py <nb>... --apply \\
      --by myia-po-2023:CoursIA

  # Famille : tous les quantbooks d'un projet QC
  python scripts/audit/migrate_cost_frontmatter_to_metadata.py \\
      --project MyIA.AI.Notebooks/QuantConnect/projects/RiskParity --apply

FORME GenAI (#9089, follow-up de #9088)
---------------------------------------
Le path GenAI (migrate_genai_notebook) est un SUPERSET du path QC. Il gere les
3 axes ou la forme GenAI differe du quantbook QC :
  - frontmatter en cell#0 OU cell#1 (Audio/Image le portent en cell#1, apres
    la cell titre/navigation) ;
  - metadata.cost ABSENT -> CREE depuis le frontmatter (pas de scanner QC) ;
  - frontmatter MALFORME (closing `---` indente, avale par `notes: |`) ->
    parse tolerant yaml.safe_load.
De plus : un bloc top-level `notes:` migre vers `metadata.cost.notes` (guard
#8921-4, « cas Claudish » — un colocataire substantiel ne doit pas etre
silencieusement droppe avec le frontmatter), et les timestamps ISO auto-parses
par yaml.safe_load sont re-serializes en chaines ISO (json.dumps ne serialise
pas les datetime). Une cell frontmatter-only est SUPPRIMEE ; une cell
frontmatter + trailing H1 est strippee en gardant le H1.

`--shape` :
  - `auto` (defaut) : GenAI-first (superset) ; fallback QC pour un diagnostic
    plus fin sur les notebooks sans cell `--- cost:` (ex. deja migre ->
    skip-already-migrated). Un quantbook QC est traite de facon identique par
    les deux paths (union cost + strip).
  - `qc` : path QC strict (cell#0, metadata.cost present, bien forme) — refuse
    si metadata.cost absent (contrat quantbook : peupler via
    populate_quantconnect_cost.py d'abord).
  - `genai` : path GenAI uniquement.

Exit codes : 0 = ok (dry-run ou apply) ; 1 = au moins une erreur/defaut de coherence.
"""

import argparse
import json
import re
import sys
from pathlib import Path

import yaml

_FRONTMATTER_RE = re.compile(r"\A---\s*\n(.*?)\n---\s*\n", re.DOTALL)


def parse_frontmatter(cell_source: str):
    """Retourne (frontmatter_dict, match_span) ou (None, None) si cell#0 ne
    demarre pas par un bloc `---...---`."""
    m = _FRONTMATTER_RE.match(cell_source)
    if not m:
        return None, None
    try:
        data = yaml.safe_load(m.group(1)) or {}
    except yaml.YAMLError:
        return None, None
    return data, m.span()


def _as_str(src):
    return "".join(src) if isinstance(src, list) else (src or "")


def strip_frontmatter_preserving_type(raw_source):
    """Retire le bloc `---...---` en tete + les lignes vides suivantes, en
    PRESERVANT le format de `source` (list de strings ou string unique). Le
    format nbformat canonique est une list ; le collapser en string unique
    produit un churn massif (array -> echappement) qui n'est PAS byte-stable.

    Retourne (new_source, ok). ok=False si pas de frontmatter en tete, ou si le
    contenu restant ne demarre pas par un H1 (`#`).
    """
    if isinstance(raw_source, list):
        delim_idx = [i for i, el in enumerate(raw_source) if el.strip() == "---"]
        # Le frontmatter demarre a l'element 0 et se ferme au 2e `---`.
        if len(delim_idx) < 2 or delim_idx[0] != 0:
            return raw_source, False
        end = delim_idx[1]
        rest = raw_source[end + 1:]
        k = 0
        while k < len(rest) and rest[k].strip() == "":
            k += 1
        kept = rest[k:]
        if not kept or not kept[0].lstrip().startswith("#"):
            return raw_source, False
        return kept, True
    # Forme string
    fm, span = parse_frontmatter(raw_source)
    if fm is None:
        return raw_source, False
    kept = raw_source[span[1]:].lstrip("\n")
    if not kept.lstrip().startswith("#"):
        return raw_source, False
    return kept, True


def _lf_only(text: str) -> str:
    return text.replace("\r\n", "\n")


# ---------------------------------------------------------------------------
# GenAI shape (#9089, follow-up of #9088) — ADDITIVE, QC path unchanged.
#
# The GenAI shape differs from the QC quantbook shape on three axes:
#   1. frontmatter in cell#0 OR cell#1 (Audio/Image carry it in cell#1, after a
#      title/navigation cell);
#   2. `metadata.cost` usually ABSENT (no QC scanner populates it first) — the
#      frontmatter is the only source, so migration must CREATE it;
#   3. MALFORMED frontmatter possible (3 Audio notebooks: the closing `---` is
#      indented and swallowed by a `notes: |` block — no column-0 closer; a raw
#      whole-body `yaml.safe_load` is tolerant of this).
# Additionally: a top-level `notes:` colocataire migrates to
# `metadata.cost.notes` (guard #8921-4, "cas Claudish" — a substantive prose
# block must not be silently dropped with the frontmatter), and ISO timestamps
# auto-parsed by yaml.safe_load (e.g. `metadata_written: 2026-07-23T09:30Z`)
# are sanitized back to ISO strings (json.dumps cannot serialize datetimes).
# ---------------------------------------------------------------------------


def _sanitize(obj):
    """yaml.safe_load auto-parses ISO timestamps into datetime objects, which
    json.dumps cannot serialize. Convert them (and nested) back to ISO strings."""
    import datetime
    if isinstance(obj, dict):
        return {k: _sanitize(v) for k, v in obj.items()}
    if isinstance(obj, list):
        return [_sanitize(v) for v in obj]
    if isinstance(obj, (datetime.datetime, datetime.date)):
        return obj.isoformat()
    return obj


# Well-formed frontmatter WITH trailing capture: opening `---`, body, col-0
# closing `---`, optional trailing content. The body is parsed BETWEEN the
# delimiters (a raw whole-body parse sees the closing `---` as a YAML doc
# separator -> error).
_WF_RE_TRAILING = re.compile(r"\A---\s*\n(.*?)\n---\s*\n?(.*)\Z", re.DOTALL)


def parse_frontmatter_genai(src: str):
    """GenAI frontmatter parser. Returns (fm_dict, trailing_str) or (None, None).

    Well-formed (col-0 closing `---`): parse the body BETWEEN delimiters; the
    closing `---` is a YAML doc separator, so a raw whole-body parse fails.
    trailing = content after the closer (may be '' for frontmatter-only cells).

    Malformed (no col-0 closer, e.g. indented `---` swallowed by `notes: |`):
    tolerant whole-body `yaml.safe_load` (the indented closer becomes literal
    content); the whole cell is frontmatter -> trailing = ''.
    """
    m = _WF_RE_TRAILING.match(src)
    if m:
        try:
            data = yaml.safe_load(m.group(1)) or {}
            if isinstance(data, dict):
                return data, m.group(2)
        except yaml.YAMLError:
            pass
    # Malformed fallback: tolerant whole-body parse.
    body = re.sub(r"\A---\s*\n", "", src, count=1)
    try:
        data = yaml.safe_load(body)
    except yaml.YAMLError:
        return None, None
    if isinstance(data, dict):
        return data, ""
    return None, None


def find_genai_frontmatter_cell(nb: dict):
    """Return (idx, fm_dict, trailing_str, src_str) for the first markdown cell
    among #0/#1 whose source starts with `---` and parses to a dict with a
    `cost` key. None if no such cell."""
    for i in (0, 1):
        if i >= len(nb.get("cells", [])):
            continue
        c = nb["cells"][i]
        if c.get("cell_type") != "markdown":
            continue
        src = _as_str(c.get("source", ""))
        if not src.startswith("---"):
            continue
        fm, trailing = parse_frontmatter_genai(src)
        if isinstance(fm, dict) and isinstance(fm.get("cost"), dict):
            return i, fm, trailing, src
    return None


def migrate_notebook(path: Path, apply: bool, by: str):
    """Migre un notebook. Retourne un dict de rapport (status + detail)."""
    rel = str(path)
    try:
        original = path.read_text(encoding="utf-8")
        nb = json.loads(original)
    except Exception as exc:
        return {"path": rel, "status": "error", "detail": f"read/parse: {exc}"}

    cells = nb.get("cells", [])
    if not cells:
        return {"path": rel, "status": "error", "detail": "no cells"}
    cell0 = cells[0]
    if cell0.get("cell_type") != "markdown":
        return {"path": rel, "status": "error", "detail": "cell#0 not markdown"}

    raw_source = cell0.get("source", "")
    src = _as_str(raw_source)
    fm, span = parse_frontmatter(src)
    if fm is None:
        return {"path": rel, "status": "skip-already-migrated",
                "detail": "cell#0 has no `---` frontmatter (already migrated)"}
    if not isinstance(fm, dict) or "cost" not in fm:
        return {"path": rel, "status": "error",
                "detail": "frontmatter has no `cost:` block — not a cost migration target"}

    fm_cost = fm.get("cost") or {}
    if not isinstance(fm_cost, dict):
        return {"path": rel, "status": "error", "detail": "frontmatter cost not a dict"}

    meta = nb.setdefault("metadata", {})
    meta_cost = meta.get("cost")
    if not isinstance(meta_cost, dict) or not meta_cost:
        return {"path": rel, "status": "refused-no-metadata-cost",
                "detail": "metadata.cost absent — populate it first (populate_quantconnect_cost.py)"}

    # UNION : metadata d'abord (garde qcc_tokens_est etc.), frontmatter gagne sur overlap.
    merged = {**meta_cost, **fm_cost}

    # Champs reellement ecris (divergents) = ou metadata et frontmatter differaient.
    overwritten = {k: {"from": meta_cost.get(k), "to": fm_cost.get(k)}
                   for k in fm_cost if meta_cost.get(k) != fm_cost.get(k)}
    meta_only = sorted(k for k in meta_cost if k not in fm_cost)

    # Stripping du frontmatter : on retire le bloc ---...--- + les lignes vides
    # qui suivent immediatement, en PRESERVANT le format list/str de `source`
    # (collapser une list en string = churn non byte-stable).
    new_cell0_source, ok_strip = strip_frontmatter_preserving_type(raw_source)
    if not ok_strip:
        return {"path": rel, "status": "error",
                "detail": "after frontmatter, cell#0 does not start with a `#` H1 — aborting"}

    # Byte-stabilite : re-dumper l'original (sans modif) doit round-tripper.
    rt_original = _lf_only(json.dumps(json.loads(original), indent=1, ensure_ascii=False) + "\n")
    byte_stable_baseline = (rt_original == _lf_only(original))

    # Appliquer les modifs sur la structure.
    nb["cells"][0]["source"] = new_cell0_source
    meta["cost"] = merged

    new_content = _lf_only(json.dumps(nb, indent=1, ensure_ascii=False) + "\n")

    # Preuve d'equivalence : merged == {**meta_cost_original, **fm_cost}.
    expected = {**meta_cost, **fm_cost}
    equivalent = (merged == expected)

    # DIFF MINIMAL — invariant anti-churn : seuls cell#0 (source) et
    # metadata.cost peuvent changer. Toute autre cellule (code, outputs,
    # metadata de cellule) et tout autre champ de nb.metadata doivent etre
    # byte-identiques. C'est ce garde-fou qui aurait attrape un collapse
    # list->string (churn massif sur cell#0 detecte comme non-minimal sur les
    # METADATA de cell#0, et tout autre derivee).
    nb_original = json.loads(original)
    minimal_diff = True
    diff_detail = []
    cells_o = nb_original.get("cells", [])
    cells_n = nb.get("cells", [])
    if len(cells_o) != len(cells_n):
        minimal_diff = False
        diff_detail.append(f"cell count {len(cells_o)}->{len(cells_n)}")
    else:
        for i, (co, cn) in enumerate(zip(cells_o, cells_n)):
            if i == 0:
                # cell#0 : seul 'source' peut changer ; tout le reste identique.
                for k in co:
                    if k == "source":
                        continue
                    if co.get(k) != cn.get(k):
                        minimal_diff = False
                        diff_detail.append(f"cell#0 field '{k}' changed")
            else:
                if co != cn:
                    minimal_diff = False
                    diff_detail.append(f"cell#{i} changed")
    # metadata : seul 'cost' peut changer.
    meta_o = nb_original.get("metadata", {})
    meta_n = nb.get("metadata", {})
    for k in meta_o:
        if k == "cost":
            continue
        if meta_o.get(k) != meta_n.get(k):
            minimal_diff = False
            diff_detail.append(f"metadata field '{k}' changed")

    report = {
        "path": rel,
        "overwritten_fields": overwritten,
        "metadata_only_fields_preserved": meta_only,
        "byte_stable_baseline": byte_stable_baseline,
        "field_equivalent": equivalent,
        "minimal_diff": minimal_diff,
        "diff_detail": diff_detail,
        "new_cell0_starts_with_h1": new_cell0_source.lstrip().startswith("#")
        if isinstance(new_cell0_source, str)
        else (new_cell0_source[0].lstrip().startswith("#") if new_cell0_source else False),
    }

    if not apply:
        report["status"] = "dry-run"
        return report

    if not equivalent:
        report["status"] = "aborted-not-equivalent"
        return report
    if not minimal_diff:
        report["status"] = "aborted-non-minimal-diff"
        return report

    path.write_bytes(new_content.encode("utf-8"))
    report["status"] = "migrated"
    return report


def migrate_genai_notebook(path: Path, apply: bool, by: str):
    """Migre un notebook de la forme GenAI (#9089, follow-up de #9088).

    Differencie du path QC (migrate_notebook, inchange) sur :
      - frontmatter en cell#0 OU cell#1 ;
      - metadata.cost absent -> CREE depuis le frontmatter ;
      - frontmatter malforme (closing `---` indente) -> parse tolerant ;
      - notes: -> metadata.cost.notes (guard #8921-4) ;
      - cell frontmatter-only -> SUPPRIME la cell ; frontmatter+trailing -> garde le H1.

    Memes gates que le path QC : byte-stable round-trip, code-sha256 inchange,
    output-count inchange, diff minimal.
    """
    import copy
    import hashlib
    rel = str(path)
    try:
        original = path.read_text(encoding="utf-8")
        nb_o = json.loads(original)
    except Exception as exc:
        return {"path": rel, "status": "error", "detail": f"read/parse: {exc}"}

    found = find_genai_frontmatter_cell(nb_o)
    if found is None:
        return {"path": rel, "status": "skip-no-genai-frontmatter",
                "detail": "no `--- cost:` cell among #0/#1"}
    fm_idx, fm, trailing, fm_full_src = found
    fm_cost = _sanitize(fm.get("cost") or {})

    meta = nb_o.get("metadata", {})
    meta_cost = meta.get("cost")
    existing = meta_cost if isinstance(meta_cost, dict) else {}
    merged = {**existing, **fm_cost}
    # Guard #8921-4 : un bloc notes: substantiel migre vers metadata.cost.notes.
    notes = fm.get("notes")
    if isinstance(notes, str) and notes.strip() and "notes" not in merged:
        merged["notes"] = notes.strip()

    overwritten = {k: {"from": existing.get(k), "to": fm_cost.get(k)}
                   for k in fm_cost if existing.get(k) != fm_cost.get(k)}
    meta_only = sorted(k for k in existing if k not in fm_cost)

    nb_n = copy.deepcopy(nb_o)
    if trailing.strip():
        # frontmatter + trailing -> garder la cell, source = trailing (preserver list/str).
        old_cell = nb_n["cells"][fm_idx]
        if isinstance(old_cell.get("source"), list):
            old_cell["source"] = trailing.splitlines(keepends=True)
        else:
            old_cell["source"] = trailing
        removed = False
    else:
        # frontmatter-only -> supprimer la cell.
        del nb_n["cells"][fm_idx]
        removed = True
    nb_n.setdefault("metadata", {})["cost"] = merged

    # ---- GATES ----
    gates = {}
    # 1. byte-stable baseline (tolere un \n final manquant dans l'original).
    rt_orig = _lf_only(json.dumps(json.loads(original), indent=1, ensure_ascii=False) + "\n")
    norm_orig = _lf_only(original)
    if not norm_orig.endswith("\n"):
        norm_orig += "\n"
    gates["byte_stable_baseline"] = (rt_orig == norm_orig)

    # 2. code sha256 inchange (ensemble ; la cell supprimee est markdown).
    def _code_sha_set(nb):
        out = []
        for c in nb.get("cells", []):
            if c.get("cell_type") == "code":
                out.append(hashlib.sha256(_as_str(c.get("source", "")).encode("utf-8")).hexdigest())
        return out
    gates["code_sha_unchanged"] = (_code_sha_set(nb_o) == _code_sha_set(nb_n))

    # 3. output-count inchange (la cell frontmatter est markdown : pas d'outputs).
    def _output_count(nb):
        return sum(len(c.get("outputs") or []) for c in nb.get("cells", []))
    oc_o, oc_n = _output_count(nb_o), _output_count(nb_n)
    gates["output_count_unchanged"] = (oc_o == oc_n)
    gates["output_count"] = f"{oc_o}->{oc_n}"

    # 4. diff minimal : seuls la cell frontmatter (source) et metadata.cost changent.
    cells_o, cells_n = nb_o["cells"], nb_n["cells"]
    minimal, diff_detail = True, []
    if removed:
        keep_o = [c for j, c in enumerate(cells_o) if j != fm_idx]
        if len(keep_o) != len(cells_n):
            minimal = False
            diff_detail.append(f"len mismatch after removal {len(keep_o)} vs {len(cells_n)}")
        else:
            for j, (co, cn) in enumerate(zip(keep_o, cells_n)):
                if co != cn:
                    minimal = False
                    diff_detail.append(f"kept cell#{j} differs")
    else:
        if len(cells_o) != len(cells_n):
            minimal = False
            diff_detail.append("len changed without removal")
        else:
            for j, (co, cn) in enumerate(zip(cells_o, cells_n)):
                if j == fm_idx:
                    for k in co:
                        if k == "source":
                            continue
                        if co.get(k) != cn.get(k):
                            minimal = False
                            diff_detail.append(f"fm cell#{j} field {k} changed")
                elif co != cn:
                    minimal = False
                    diff_detail.append(f"cell#{j} changed")
    meta_o, meta_n = nb_o.get("metadata", {}), nb_n.get("metadata", {})
    for k in set(list(meta_o.keys()) + list(meta_n.keys())):
        if k == "cost":
            continue
        if meta_o.get(k) != meta_n.get(k):
            minimal = False
            diff_detail.append(f"metadata field {k} changed")
    gates["minimal_diff"] = minimal
    gates["diff_detail"] = diff_detail

    if removed:
        gates["kept_cell_starts_with_h1"] = "n/a (cell removed)"
    else:
        new_src = _as_str(nb_n["cells"][fm_idx].get("source", ""))
        gates["kept_cell_starts_with_h1"] = new_src.lstrip().startswith("#")

    new_content = _lf_only(json.dumps(nb_n, indent=1, ensure_ascii=False) + "\n")
    all_ok = (gates["byte_stable_baseline"] and gates["code_sha_unchanged"]
              and gates["output_count_unchanged"] and gates["minimal_diff"]
              and (removed or gates["kept_cell_starts_with_h1"]))

    report = {
        "path": rel,
        "fm_cell": f"#{fm_idx}",
        "action": "remove-cell" if removed else "strip-keep-trailing",
        "trailing_chars": len(trailing),
        "cost_keys": sorted(fm_cost.keys()),
        "overwritten_fields": overwritten,
        "metadata_only_fields_preserved": meta_only,
        "merged_cost_keys": len(merged),
        "notes_migrated": "notes" in merged and isinstance(fm.get("notes"), str),
        **gates,
    }
    if not apply:
        report["status"] = "dry-run-genai" if all_ok else "dry-run-genai-GATE-FAIL"
        return report
    if not all_ok:
        report["status"] = "aborted-genai-gate-fail"
        return report
    path.write_bytes(new_content.encode("utf-8"))
    report["status"] = "migrated-genai"
    return report


def _iter_project(project_dir: Path):
    yield from sorted(project_dir.glob("*.ipynb"))


def _dispatch(path: Path, apply: bool, by: str, shape: str):
    """Choisit le path QC (migrate_notebook) ou GenAI (migrate_genai_notebook)
    selon --shape.

    Le path GenAI est un SUPERSET du path QC : il gere cell#0 OU cell#1, le
    frontmatter malforme, la creation de metadata.cost si absent, ET migre
    `notes:` -> metadata.cost.notes (guard #8921-4). Un quantbook QC (cell#0
    bien forme + metadata.cost present) est traite de facon identique par les
    deux paths (union cost + strip). `auto` prefere donc GenAI (uniformise la
    migration notes sur tous les notebooks a frontmatter cost) et ne retombe
    sur QC que si GenAI ne reconnait pas de cell `--- cost:` (ex. notebook
    deja migre -> QC donne un skip-already-migrated plus specifique)."""
    if shape == "qc":
        return migrate_notebook(path, apply=apply, by=by)
    if shape == "genai":
        return migrate_genai_notebook(path, apply=apply, by=by)
    # auto : GenAI-first (superset), fallback QC pour un diagnostic plus fin.
    genai_dry = migrate_genai_notebook(path, apply=False, by=by)
    if genai_dry["status"] != "skip-no-genai-frontmatter":
        return migrate_genai_notebook(path, apply=apply, by=by)
    return migrate_notebook(path, apply=apply, by=by)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("notebooks", nargs="*", type=Path, help="Notebooks à migrer.")
    ap.add_argument("--project", type=Path,
                    help="Répertoire projet QC (migrer tous ses *.ipynb).")
    ap.add_argument("--apply", action="store_true", help="Écrire (défaut : dry-run).")
    ap.add_argument("--by", default="anonymous", help="machine:workspace (provenance).")
    ap.add_argument("--shape", choices=("auto", "qc", "genai"), default="auto",
                    help="Forme de frontmatter : qc (cell#0, metadata.cost present, "
                         "bien forme), genai (cell#0/#1, malforme, metadata.cost absent), "
                         "auto (defaut : qc si preconditions tiennent, sinon genai).")
    args = ap.parse_args(argv)

    paths = list(args.notebooks)
    if args.project:
        paths.extend(_iter_project(args.project))
    if not paths:
        ap.error("fournir au moins un notebook ou --project")

    counts = {}
    total_overwritten = 0
    rc = 0
    for p in paths:
        if not p.exists():
            print(f"  ERROR  {p} introuvable")
            counts["error"] = counts.get("error", 0) + 1
            rc = 1
            continue
        rep = _dispatch(p, apply=args.apply, by=args.by, shape=args.shape)
        st = rep["status"]
        counts[st] = counts.get(st, 0) + 1
        is_genai = st.endswith("-genai") or "genai" in st
        wrote = (args.apply and st in ("migrated", "migrated-genai"))
        marker = "WRITE" if wrote else ("DRY" if st.startswith("dry-run") else "SKIP")
        if st in ("error", "refused-no-metadata-cost", "aborted-not-equivalent",
                  "aborted-non-minimal-diff", "aborted-genai-gate-fail",
                  "dry-run-genai-GATE-FAIL"):
            rc = 1
        ow = rep.get("overwritten_fields", {})
        total_overwritten += len(ow)
        name = p.name
        fields = ",".join(sorted(ow)) if ow else "-"
        print(f"  [{marker:4s}] {st:28s} {name:26} overwrite=[{fields}] meta_only={rep.get('metadata_only_fields_preserved', [])}")
        if is_genai:
            print(f"          fm={rep.get('fm_cell')} act={rep.get('action')} "
                  f"byte_stable={rep.get('byte_stable_baseline')} "
                  f"code_sha={rep.get('code_sha_unchanged')} "
                  f"out_cnt={rep.get('output_count_unchanged')}({rep.get('output_count')}) "
                  f"minimal={rep.get('minimal_diff')} h1={rep.get('kept_cell_starts_with_h1')} "
                  f"notes_migrated={rep.get('notes_migrated')}")
        else:
            print(f"          byte_stable_baseline={rep.get('byte_stable_baseline')} "
                  f"field_equivalent={rep.get('field_equivalent')} "
                  f"minimal_diff={rep.get('minimal_diff')} "
                  f"h1={rep.get('new_cell0_starts_with_h1')}")

    mode = "APPLY" if args.apply else "DRY-RUN"
    print(f"\n[{mode}] by={args.by}  notebooks={len(paths)}  fields_overwritten={total_overwritten}")
    for k, v in sorted(counts.items()):
        print(f"  {k:28s} {v}")
    return rc


if __name__ == "__main__":
    sys.exit(main())
