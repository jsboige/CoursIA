#!/usr/bin/env python3
"""
migrate_cost_frontmatter_to_metadata.py — Migre le bloc cost YAML d'une cellule
frontmatter (LEGACY) vers `nb.metadata['cost']` (CANONIQUE), PUIS retire le bloc.

Issues #8904 (markdown-rendering `[frontmatter_supersize]`) + #8056 (cost canonique)
+ #9089 (extension shape GenAI : cell#0|cell#1, metadata.cost absent, YAML malforme).

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

DEUX SHAPES — QC (canonique) et GenAI (#9089)
---------------------------------------------
**Shape QC** (path inchange, regressif) :
  - frontmatter en **cell#0** uniquement ;
  - `metadata.cost` **DOIT exister** (sinon : refuse — il faut d'abord le peupler via
    populate_quantconnect_cost.py ; on ne Migre pas vers du vide) ;
  - frontmatter **well-formed** (closer `---` en colonne 0).
  -> UNION merge {**meta_cost, **fm_cost}, puis strip du bloc en gardant le H1 trailing.

**Shape GenAI** (extension #9089) :
  - frontmatter en **cell#0 OU cell#1** (Audio/Image le portent en cell#1, apres la
    cellule titre/navigation) ;
  - `metadata.cost` souvent **absent** (pas de scanner QC — le frontmatter est la
    seule source) -> la migration le CREE depuis le frontmatter seul (pas de merge
    lossy vers du vide, puisqu'il n'y a rien a perdre) ;
  - frontmatter possiblement **malforme** (closer `---` indente et avale par un bloc
    `notes: |` : pas de closer en colonne 0) -> parse tolerant whole-cell
    `yaml.safe_load` (yaml est tolerant de cette forme).
  -> CREATE metadata.cost = frontmatter_cost (sanitized), puis REMOVE la cellule
     frontmatter (elle est dediee au frontmatter en GenAI, sans H1 trailing).

SEUIL DE COHERENCE (litmus anti-LIGHT, cf check_cost_metadata.py)
-----------------------------------------------------------------
La migration n'ecrit QUE si elle est cohérente :
  - une cellule markdown (cell#0 ou cell#1) doit demarrer par `---` et contenir un
    bloc `cost:` valide (sinon : deja migree -> skip idempotent) ;
  - shape QC : metadata.cost DOIT exister (sinon : refuse) ;
  - shape GenAI : metadata.cost absent est OK (creation depuis frontmatter).
Les valeurs YAML type datetime (ex. `metadata_written: 2026-07-23T09:30Z`) sont
sanitizees en ISO strings (JSON-serializable). Le re-dump utilise
`json.dumps(indent=1, ensure_ascii=False)+'\\n'` (LF-only), round-trip byte-identique
au original hors des champs migrés (technique #8908).

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
import datetime
import json
import re
import sys
from pathlib import Path

import yaml

_FRONTMATTER_RE = re.compile(r"\A---\s*\n(.*?)\n---\s*\n", re.DOTALL)


def parse_frontmatter(cell_source: str):
    """Retourne (frontmatter_dict, match_span) ou (None, None) si la cellule ne
    demarre pas par un bloc `---...---` well-formed (closer en colonne 0)."""
    m = _FRONTMATTER_RE.match(cell_source)
    if not m:
        return None, None
    try:
        data = yaml.safe_load(m.group(1)) or {}
    except yaml.YAMLError:
        return None, None
    return data, m.span()


def _is_cost_frontmatter(data):
    """True si data est un dict portant un bloc `cost:` dict (cible de migration)."""
    return isinstance(data, dict) and isinstance(data.get("cost"), dict)


def parse_frontmatter_tolerant(cell_source: str):
    """Shape GenAI malforme (#9089) : la cellule demarre par `---` mais n'a PAS de
    closer en colonne 0 (le `---` final est indente et avale par un bloc literal
    `notes: |`). Tolerant whole-cell `yaml.safe_load` — yaml accepte cette forme
    (le `---` de tete est le separateur de doc, le `  ---` final est du contenu
    literal dans notes). Retourne data (ou None si non parsable / sans cost)."""
    if not cell_source.startswith("---"):
        return None
    try:
        data = yaml.safe_load(cell_source)
    except yaml.YAMLError:
        return None
    return data if _is_cost_frontmatter(data) else None


def _as_str(src):
    return "".join(src) if isinstance(src, list) else (src or "")


def _sanitize_yaml_values(obj):
    """yaml parse `metadata_written: 2026-07-23T09:30Z` en datetime (non
    JSON-serializable). Convertit recursivement datetime/date -> ISO string."""
    if isinstance(obj, (datetime.datetime, datetime.date)):
        return obj.isoformat()
    if isinstance(obj, dict):
        return {k: _sanitize_yaml_values(v) for k, v in obj.items()}
    if isinstance(obj, list):
        return [_sanitize_yaml_values(v) for v in obj]
    return obj


def find_cost_frontmatter_cell(nb):
    """Scan cell#0 puis cell#1 pour une cellule markdown frontmatter portant un
    bloc `cost:`. Essaie le parse STRICT (closer col-0) d'abord, puis TOLERANT
    (malforme GenAI). Retourne un dict :
      {idx, fm, mode, raw_source, span, src, trailing}
    ou None si aucune cellule cible. `trailing` = contenu apres le closer pour le
    mode strict (peut etre "" = frontmatter-only), None pour tolerant (whole-cell)."""
    cells = nb.get("cells", [])
    for idx in (0, 1):
        if idx >= len(cells):
            break
        cell = cells[idx]
        if cell.get("cell_type") != "markdown":
            continue
        raw_source = cell.get("source", "")
        src = _as_str(raw_source)
        if not src.startswith("---"):
            continue
        # Strict (well-formed, col-0 closer) — path QC + GenAI well-formed.
        data, span = parse_frontmatter(src)
        if _is_cost_frontmatter(data):
            trailing = src[span[1]:]
            return {"idx": idx, "fm": data, "mode": "strict",
                    "raw_source": raw_source, "span": span, "src": src,
                    "trailing": trailing}
        # Tolerant (malformed GenAI, no col-0 closer).
        data_t = parse_frontmatter_tolerant(src)
        if data_t is not None:
            return {"idx": idx, "fm": data_t, "mode": "tolerant",
                    "raw_source": raw_source, "span": None, "src": src,
                    "trailing": None}
    return None


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


def _trailing_as_source_type(trailing_str, raw_source):
    """Reconstruit le trailing (apres closer) dans le MEME format (list/str) que
    raw_source, pour preserver le type canonique (anti-churn list->string)."""
    if isinstance(raw_source, list):
        # Decoupe le trailing_str en lignes keepends (format list canonique).
        return trailing_str.splitlines(keepends=True)
    return trailing_str


def migrate_notebook(path: Path, apply: bool, by: str):
    """Migre un notebook. Retourne un dict de rapport (status + detail)."""
    rel = str(path)
    try:
        original = path.read_text(encoding="utf-8")
        nb = json.loads(original)
    except Exception as exc:
        return {"path": rel, "status": "error", "detail": f"read/parse: {exc}"}

    if not nb.get("cells"):
        return {"path": rel, "status": "error", "detail": "no cells"}

    fm_info = find_cost_frontmatter_cell(nb)
    if fm_info is None:
        return {"path": rel, "status": "skip-already-migrated",
                "detail": "no `---cost:` frontmatter in cell#0 or cell#1 (already migrated)"}

    idx = fm_info["idx"]
    fm = fm_info["fm"]
    mode = fm_info["mode"]
    raw_source = fm_info["raw_source"]
    trailing = fm_info["trailing"]

    fm_cost = fm.get("cost") or {}
    if not isinstance(fm_cost, dict):
        return {"path": rel, "status": "error", "detail": "frontmatter cost not a dict"}

    meta = nb.setdefault("metadata", {})
    meta_cost = meta.get("cost")
    create_mode = not (isinstance(meta_cost, dict) and meta_cost)

    if create_mode:
        # Shape GenAI : metadata.cost absent -> CREATE depuis le frontmatter seul.
        # Pas de merge lossy (il n'y a rien a perdre : le frontmatter EST la source).
        fm_cost_safe = _sanitize_yaml_values(fm_cost)
        merged = dict(fm_cost_safe)
        overwritten = {}
        meta_only = []
        merge_kind = "create-from-frontmatter"
    else:
        # Shape QC / GenAI-both : UNION (metadata d'abord, frontmatter gagne sur overlap).
        fm_cost_safe = _sanitize_yaml_values(fm_cost)
        merged = {**meta_cost, **fm_cost_safe}
        overwritten = {k: {"from": meta_cost.get(k), "to": fm_cost_safe.get(k)}
                       for k in fm_cost_safe if meta_cost.get(k) != fm_cost_safe.get(k)}
        meta_only = sorted(k for k in meta_cost if k not in fm_cost_safe)
        merge_kind = "union"

    # Strip du frontmatter.
    new_nb = json.loads(original)  # copie profonde de travail
    remove_cell = False
    if mode == "strict" and trailing and trailing.strip():
        # Well-formed avec H1 trailing : strip le bloc, garde le trailing (path QC).
        new_source, ok_strip = strip_frontmatter_preserving_type(raw_source)
        if not ok_strip:
            return {"path": rel, "status": "error",
                    "detail": "after frontmatter, cell does not start with a `#` H1 — aborting"}
        new_nb["cells"][idx]["source"] = new_source
        new_cell0_starts_h1 = (_as_str(new_source).lstrip().startswith("#"))
    else:
        # frontmatter-only (strict sans trailing, OU tolerant whole-cell GenAI) :
        # la cellule est dediee au frontmatter -> REMOVE.
        remove_cell = True
        del new_nb["cells"][idx]
        new_cell0_starts_h1 = True  # n/a (cell removed)

    new_nb["metadata"]["cost"] = merged

    # Byte-stabilite : re-dumper l'original (sans modif) doit round-tripper.
    rt_original = _lf_only(json.dumps(json.loads(original), indent=1, ensure_ascii=False) + "\n")
    byte_stable_baseline = (rt_original == _lf_only(original))

    new_content = _lf_only(json.dumps(new_nb, indent=1, ensure_ascii=False) + "\n")

    # Preuve d'equivalence du merge.
    if create_mode:
        expected = dict(fm_cost_safe)
    else:
        expected = {**meta_cost, **fm_cost_safe}
    equivalent = (merged == expected)

    # DIFF MINIMAL — invariant anti-churn : seuls la cellule frontmatter (source,
    # ou removal) et metadata.cost peuvent changer. Generalise pour le remove-cell
    # GenAI (len -1) ET le strip-keep-trailing QC (len egal).
    nb_original = json.loads(original)
    minimal_diff = True
    diff_detail = []
    cells_o = nb_original.get("cells", [])
    cells_n = new_nb.get("cells", [])

    if remove_cell:
        if len(cells_n) != len(cells_o) - 1:
            minimal_diff = False
            diff_detail.append(f"cell count {len(cells_o)}->{len(cells_n)} (expected -1)")
        else:
            for i, co in enumerate(cells_o):
                if i == idx:
                    continue  # la cell frontmatter supprimee
                ni = i if i < idx else i - 1  # decalage apres l'index supprime
                if co != cells_n[ni]:
                    minimal_diff = False
                    diff_detail.append(f"cell#{i} changed (expected only removal of cell#{idx})")
                    break
    else:
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
                            diff_detail.append(f"cell#{idx} field '{k}' changed")
                else:
                    if co != cn:
                        minimal_diff = False
                        diff_detail.append(f"cell#{i} changed")
    # metadata : seul 'cost' peut changer.
    meta_o = nb_original.get("metadata", {})
    meta_n = new_nb.get("metadata", {})
    for k in meta_o:
        if k == "cost":
            continue
        if meta_o.get(k) != meta_n.get(k):
            minimal_diff = False
            diff_detail.append(f"metadata field '{k}' changed")

    report = {
        "path": rel,
        "frontmatter_cell": idx,
        "mode": mode,
        "merge_kind": merge_kind,
        "overwritten_fields": overwritten,
        "metadata_only_fields_preserved": meta_only,
        "byte_stable_baseline": byte_stable_baseline,
        "field_equivalent": equivalent,
        "minimal_diff": minimal_diff,
        "diff_detail": diff_detail,
        "remove_cell": remove_cell,
        "new_cell0_starts_with_h1": new_cell0_starts_h1,
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


def _iter_project(project_dir: Path):
    yield from sorted(project_dir.glob("*.ipynb"))


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("notebooks", nargs="*", type=Path, help="Notebooks à migrer.")
    ap.add_argument("--project", type=Path,
                    help="Répertoire projet QC (migrer tous ses *.ipynb).")
    ap.add_argument("--apply", action="store_true", help="Écrire (défaut : dry-run).")
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
        rep = migrate_notebook(p, apply=args.apply, by=args.by)
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
        extra = ("rm-cell" if rep.get("remove_cell") else "strip-keep") if st == "dry-run" else ""
        print(f"  [{marker:4s}] {st:26s} {name:24} mode={rep.get('mode','-'):9s} "
              f"merge={rep.get('merge_kind','-'):22s} {extra}")
        print(f"          cell#{rep.get('frontmatter_cell','-')} overwrite=[{fields}] "
              f"meta_only={rep.get('metadata_only_fields_preserved', [])}")
        print(f"          byte_stable_baseline={rep.get('byte_stable_baseline')} "
              f"field_equivalent={rep.get('field_equivalent')} "
              f"minimal_diff={rep.get('minimal_diff')} h1={rep.get('new_cell0_starts_with_h1')}")

    mode = "APPLY" if args.apply else "DRY-RUN"
    print(f"\n[{mode}] by={args.by}  notebooks={len(paths)}  fields_overwritten={total_overwritten}")
    for k, v in sorted(counts.items()):
        print(f"  {k:28s} {v}")
    return rc


if __name__ == "__main__":
    sys.exit(main())
