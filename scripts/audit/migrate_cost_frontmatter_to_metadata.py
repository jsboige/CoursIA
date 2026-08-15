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


# ---------------------------------------------------------------------------
# Extension GenAI (#9089) — forme frontmatter cell#0|cell#1, metadata.cost
# souvent ABSENT (le frontmatter est l'unique source -> CRÉE), YAML MALFORMÉ
# toléré (closer `---` indenté et avalé par un bloc `notes: |`).
#
# La route QC (migrate_notebook) est LAISSÉE INTACTE : cell#0 stricte,
# metadata.cost pré-existant requis. Cette extension est activée par
# `--shape genai` (défaut `qc`). Complémentaire de #9088 (qui migre les 6
# notebooks GenAI actuels en one-shot) : ici on rend la logique durable.
# ---------------------------------------------------------------------------

import datetime as _datetime


def _sanitize_yaml_scalars(obj):
    """yaml.safe_load convertit `metadata_written: 2026-07-23T09:30Z` en un
    objet datetime/date non JSON-sérialisable. Reconvertit récursivement ces
    scalaires en chaînes ISO (round-trip JSON-safe)."""
    if isinstance(obj, dict):
        return {k: _sanitize_yaml_scalars(v) for k, v in obj.items()}
    if isinstance(obj, list):
        return [_sanitize_yaml_scalars(v) for v in obj]
    if isinstance(obj, (_datetime.datetime, _datetime.date)):
        return obj.isoformat()
    return obj


def _col0_closer_index(lines_with_endings):
    """Index du 2e `---` en colonne 0 (le closer du frontmatter), ou None si
    absent. Le 1er `---` (ligne 0) est l'open. Un `---` indenté (`  ---`,
    avalé dans un bloc `notes: |`) NE compte PAS comme closer colonne 0."""
    seen_open = False
    for i, ln in enumerate(lines_with_endings):
        if ln.rstrip("\r\n") == "---":
            if not seen_open:
                seen_open = True
                continue
            return i
    return None


def _parse_genai_frontmatter_cell(raw_source):
    """Parse une cellule markdown de frontmatter GenAI. Retourne
    (cost_dict, disposition, new_source) :

      - disposition == 'remove_cell' : cellule purement frontmatter (malformé
        sans closer col0, OU well-formed avec trailing vide) -> supprimer la
        cellule entière.
      - disposition == 'strip_keep_h1' : well-formed, un H1 suit le closer ->
        new_source = contenu trailing (à conserver, même format list/str que
        l'entrée).

    Retourne (None, None, None) si la cellule n'est pas un frontmatter cost
    valide (pas de `---` ouvrant, YAML non parsable, ou pas de bloc `cost:`).
    """
    is_list = isinstance(raw_source, list)
    text = "".join(raw_source) if is_list else (raw_source or "")
    if not text.startswith("---"):
        return None, None, None
    lines = text.splitlines(keepends=True)

    closer = _col0_closer_index(lines)
    if closer is not None:
        # Well-formed : body entre open (ligne 0) et closer.
        body = "".join(lines[1:closer])
        trailing_lines = lines[closer + 1:]
        k = 0
        while k < len(trailing_lines) and trailing_lines[k].strip() == "":
            k += 1
        trailing = trailing_lines[k:]
        if trailing and trailing[0].lstrip().startswith("#"):
            disposition = "strip_keep_h1"
            new_text = "".join(trailing)
        else:
            disposition = "remove_cell"
            new_text = None
    else:
        # Malformé : pas de closer col0. yaml.safe_load tolérant sur tout le
        # body (le `---` ouvrant est un séparateur de doc YAML valide).
        body = text
        disposition = "remove_cell"
        new_text = None

    try:
        data = yaml.safe_load(body)
    except yaml.YAMLError:
        return None, None, None
    if not isinstance(data, dict) or not isinstance(data.get("cost"), dict):
        return None, None, None

    cost = _sanitize_yaml_scalars(data["cost"])
    new_source = None
    if new_text is not None:
        new_source = new_text.splitlines(keepends=True) if is_list else new_text
    return cost, disposition, new_source


def _detect_genai_cost_cell(cells):
    """Cherche la cellule de frontmatter cost parmi cell#0 et cell#1 (forme
    GenAI : le frontmatter peut vivre en cell#1 après la cellule titre/nav).
    Retourne (index, cost, disposition, new_source) ou (None, None, None, None).
    """
    for i in range(min(2, len(cells))):
        c = cells[i]
        if c.get("cell_type") != "markdown":
            continue
        cost, disposition, new_source = _parse_genai_frontmatter_cell(c.get("source", ""))
        if cost is not None:
            return i, cost, disposition, new_source
    return None, None, None, None


def migrate_notebook_genai(path: Path, apply: bool, by: str):
    """Migre un notebook GenAI : frontmatter cell#0|cell#1, metadata.cost
    possiblement ABSENT (CRÉÉ depuis le frontmatter seul), YAML malformé toléré.

    Mêmes garanties que la route QC : byte-stabilité du re-dump, diff minimal
    (seuls la cellule frontmatter et metadata.cost changent), équivalence du
    merge. La disposition remove_cell supprime la cellule frontmatter (diff
    minimal adapté : cell count diminue d'exactement 1).
    """
    rel = str(path)
    try:
        original = path.read_text(encoding="utf-8")
    except Exception as exc:
        return {"path": rel, "status": "error", "detail": f"read/parse: {exc}"}
    try:
        nb_orig = json.loads(original)
    except Exception as exc:
        return {"path": rel, "status": "error", "detail": f"parse: {exc}"}
    cells = nb_orig.get("cells", [])
    if not cells:
        return {"path": rel, "status": "error", "detail": "no cells"}

    idx, fm_cost, disposition, new_source = _detect_genai_cost_cell(cells)
    if idx is None:
        return {"path": rel, "status": "skip-already-migrated",
                "detail": "no `---` cost frontmatter in cell#0/#1 (already migrated)"}

    meta = nb_orig.get("metadata", {})
    meta_cost = meta.get("cost")
    if isinstance(meta_cost, dict) and meta_cost:
        # UNION (même règle que QC) : metadata d'abord, frontmatter gagne.
        merged = {**meta_cost, **fm_cost}
        overwritten = {k: {"from": meta_cost.get(k), "to": fm_cost.get(k)}
                       for k in fm_cost if meta_cost.get(k) != fm_cost.get(k)}
        meta_only = sorted(k for k in meta_cost if k not in fm_cost)
        created = False
    else:
        # GenAI : metadata.cost absent -> CRÉÉ depuis le frontmatter seul.
        merged = {**fm_cost}
        overwritten = {}
        meta_only = []
        created = True

    # Copie de travail appliquant la disposition structurelle.
    nb2 = json.loads(original)
    meta2 = nb2.setdefault("metadata", {})
    if disposition == "remove_cell":
        del nb2["cells"][idx]
    else:  # strip_keep_h1
        nb2["cells"][idx]["source"] = new_source
    meta2["cost"] = merged

    expected = ({**meta_cost, **fm_cost}) if (isinstance(meta_cost, dict) and meta_cost) else {**fm_cost}
    equivalent = (merged == expected)

    # Byte-stabilité : préserve la convention de fin-de-fichier (trailing newline
    # ou non) du notebook original. Contrairement à la route QC (qui ajoute
    # toujours "\n"), la route GenAI détecte la convention -> re-dump truly
    # byte-stable (hors des champs migrés). Voir leçon json-dumps-indent1.
    lf_original = _lf_only(original)
    has_nl = lf_original.endswith("\n")
    rt_original = _lf_only(json.dumps(json.loads(original), indent=1, ensure_ascii=False))
    rt_original += "\n" if has_nl else ""
    byte_stable_baseline = (rt_original == lf_original)

    # DIFF MINIMAL (GenAI) : seuls (a) la cellule frontmatter [supprimée OU
    # source réécrite en H1 seul] et (b) metadata.cost peuvent changer.
    cells_o = nb_orig.get("cells", [])
    cells_n = nb2.get("cells", [])
    minimal_diff = True
    diff_detail = []
    if disposition == "remove_cell":
        kept_o = cells_o[:idx] + cells_o[idx + 1:]
        if kept_o != cells_n:
            minimal_diff = False
            diff_detail.append(f"cells differ beyond frontmatter removal "
                               f"(o={len(cells_o)} n={len(cells_n)} idx={idx})")
    else:  # strip_keep_h1
        if len(cells_o) != len(cells_n):
            minimal_diff = False
            diff_detail.append(f"cell count {len(cells_o)}->{len(cells_n)}")
        else:
            for i, (co, cn) in enumerate(zip(cells_o, cells_n)):
                if i == idx:
                    for k in co:
                        if k == "source":
                            continue
                        if co.get(k) != cn.get(k):
                            minimal_diff = False
                            diff_detail.append(f"cell#{i} field '{k}' changed")
                elif co != cn:
                    minimal_diff = False
                    diff_detail.append(f"cell#{i} changed")
    meta_o = nb_orig.get("metadata", {})
    for k in meta_o:
        if k == "cost":
            continue
        if meta_o.get(k) != meta2.get(k):
            minimal_diff = False
            diff_detail.append(f"metadata field '{k}' changed")

    report = {
        "path": rel,
        "frontmatter_cell": idx,
        "disposition": disposition,
        "created_metadata_cost": created,
        "overwritten_fields": overwritten,
        "metadata_only_fields_preserved": meta_only,
        "byte_stable_baseline": byte_stable_baseline,
        "field_equivalent": equivalent,
        "minimal_diff": minimal_diff,
        "diff_detail": diff_detail,
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
    new_content = _lf_only(json.dumps(nb2, indent=1, ensure_ascii=False))
    new_content += "\n" if has_nl else ""
    path.write_bytes(new_content.encode("utf-8"))
    report["status"] = "migrated"
    return report


def _iter_project(project_dir: Path):
    yield from sorted(project_dir.glob("*.ipynb"))


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("notebooks", nargs="*", type=Path, help="Notebooks à migrer.")
    ap.add_argument("--project", type=Path,
                    help="Répertoire projet QC (migrer tous ses *.ipynb).")
    ap.add_argument("--apply", action="store_true", help="Écrire (défaut : dry-run).")
    ap.add_argument("--shape", choices=("qc", "genai"), default="qc",
                    help="Forme de frontmatter : qc (cell#0, metadata.cost requis) "
                         "ou genai (cell#0/#1, cost créé, YAML malformé toléré). Défaut : qc.")
    ap.add_argument("--by", default="anonymous", help="machine:workspace (provenance).")
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
        rep = (migrate_notebook_genai(p, apply=args.apply, by=args.by)
               if args.shape == "genai"
               else migrate_notebook(p, apply=args.apply, by=args.by))
        st = rep["status"]
        counts[st] = counts.get(st, 0) + 1
        marker = "WRITE" if (args.apply and st == "migrated") else "DRY" if st == "dry-run" else "SKIP"
        if st in ("error", "refused-no-metadata-cost", "aborted-not-equivalent",
                  "aborted-non-minimal-diff"):
            rc = 1
        ow = rep.get("overwritten_fields", {})
        total_overwritten += len(ow)
        name = p.name
        fields = ",".join(sorted(ow)) if ow else "-"
        print(f"  [{marker:4s}] {st:26s} {name:24} overwrite=[{fields}] meta_only={rep.get('metadata_only_fields_preserved', [])}")
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
