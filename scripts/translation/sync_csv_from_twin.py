#!/usr/bin/env python3
"""Aligne la memoire de traduction d'un CSV sur le jumeau deja traduit.

Origine : PR #21496. Le CSV ``text_<lang>`` est la SOURCE de T4
(``render_notebook.py`` substitue les cellules markdown depuis cette colonne),
et ``hash_<lang>`` enregistre le texte du jumeau au moment de la synchro. Quand
une cellule du jumeau est corrigee sans que le CSV suive, deux derives
apparaissent :

- ``text_<lang>`` perime : le prochain re-rendu T4 reinjecte l'ancien texte ;
- ``text_<lang>`` **concatene** : l'ancien texte suivi du nouveau. Le hash ne
  correspond plus, la longueur double, et le re-rendu T4 ecrirait les deux
  versions bout a bout dans le carnet. Cette forme est mesurable : le texte du
  CSV se termine par le texte du jumeau sans lui etre egal.

Cet outil enregistre dans le CSV une traduction **deja presente et relue** dans
le jumeau. Il n'invoque aucun moteur de traduction (T3 est gate, #10043) : il
constate. Il ne restaure pas un texte perdu — quand le CSV porte un contenu
absent du jumeau, il le signale (``CSV_ONLY_CONTENT``) et n'ecrit pas.

Cas legacy (#27148) : des CSV portent un ``text_<lang>`` qui est **l'anglais
d'origine du carnet, d'avant la francisation** (titres courts type
"## Initial configuration"), alors que le jumeau porte la traduction complete
de la source francaise actuelle. La garde ``CSV_ONLY_CONTENT`` les refuse a
raison en temps normal ; le mode ``--realign-legacy <motif>`` les aligne
explicitement depuis le jumeau (le jumeau est la traduction relue), avec un
motif non vide journalise dans le rapport. Ce mode s'utilise dans une PR
portant le **double verrou** du protocole translation-override (#10332) :
label ``translation-override`` ET commentaire ``[TRANSLATION-OVERRIDE] <motif>``
— c'est le guard GitHub qui l'exige des deux, l'outil documente le contrat.
Chaque alignement legacy rapporte un apercu du texte remplace
(``replaced_preview``) pour qualifier le residu : anglais pre-francisation vs
derive ordinaire du jumeau corrige apres ecriture CSV.

Perimetre : cellules **markdown** uniquement. Pour une cellule de code, le CSV
ne porte que les commentaires traduits, pas la source : la recopier serait une
falsification du contrat T1.

Le CSV est ecrit sans reordonner ni reformater : le round-trip des lignes
inchangees doit etre byte-identique, sinon l'outil refuse (rc 2) et n'ecrit
rien.

Usage :
    python scripts/translation/sync_csv_from_twin.py \\
        --csv translations/genai/finetuning.csv \\
        --pivot <carnet pivot>.ipynb --twin <carnet jumeau>_en.ipynb \\
        [--lang en] [--cells id1,id2] [--apply] [--realign-legacy MOTIF] [--json]

Sortie : 0 si tout est en phase (ou si ``--apply`` a aligne), 1 si une cellule
cible reste hors phase en mode ``--check``, 2 si l'entree est inutilisable.
"""
from __future__ import annotations

import argparse
import csv
import io
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from extract_cells_to_csv import cell_hash  # noqa: E402  (source unique du hash)

TARGET_COLS = ("src_hash", "text_", "hash_", "src_hash_")


def _cells(nb: dict) -> dict[str, tuple[str, str]]:
    """cell_id -> (texte source, cell_type)."""
    out: dict[str, tuple[str, str]] = {}
    for cell in nb.get("cells") or []:
        cid = cell.get("id")
        if not cid:
            continue
        out[cid] = ("".join(cell.get("source") or []), cell.get("cell_type") or "")
    return out


def _read_csv(path: pathlib.Path) -> tuple[list[str], list[dict[str, str]], bytes]:
    raw = path.read_bytes()
    newline = "\r\n" if b"\r\n" in raw else "\n"
    text = raw.decode("utf-8")
    reader = csv.DictReader(io.StringIO(text, newline=""))
    fieldnames = list(reader.fieldnames or [])
    rows = list(reader)
    # Invariant : un round-trip du CSV non modifie doit etre byte-identique.
    buf = io.StringIO()
    writer = csv.DictWriter(buf, fieldnames=fieldnames, lineterminator=newline)
    writer.writeheader()
    writer.writerows(rows)
    round_trip_ok = buf.getvalue().encode("utf-8") == raw
    return fieldnames, rows, raw if round_trip_ok else b""


def classify(row: dict[str, str], twin_text: str, lang: str) -> str:
    """Verdict pour une ligne au regard du texte du jumeau."""
    csv_text = (row.get(f"text_{lang}") or "").strip()
    twin = (twin_text or "").strip()
    if not twin:
        return "NO_TWIN_TEXT"
    if csv_text == twin:
        return "IN_SYNC"
    if csv_text.endswith(twin):
        return "CONCATENATED"
    if twin in csv_text:
        return "CONTAINS_TWIN"
    if not csv_text:
        return "CSV_EMPTY"
    return "CSV_ONLY_CONTENT"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--csv", required=True, type=pathlib.Path)
    ap.add_argument("--pivot", required=True, type=pathlib.Path)
    ap.add_argument("--twin", required=True, type=pathlib.Path)
    ap.add_argument("--lang", default="en", help="langue cible (defaut en)")
    ap.add_argument("--cells", default=None,
                    help="liste d'ids de cellules separees par des virgules (defaut : toutes)")
    ap.add_argument("--apply", action="store_true", help="ecrire les alignements (defaut : constat seul)")
    ap.add_argument("--realign-legacy", default=None, metavar="MOTIF",
                    help="aligner aussi les CSV_ONLY_CONTENT (anglais pre-francisation, "
                         "#27148) depuis le jumeau ; MOTIF non vide exigé et journalisé — "
                         "la PR porte le double verrou #10332 (label translation-override "
                         "+ commentaire [TRANSLATION-OVERRIDE])")
    ap.add_argument("--json", action="store_true", help="sortie machine")
    args = ap.parse_args(argv)
    realign = args.realign_legacy is not None
    if realign and not args.realign_legacy.strip():
        print("ERROR : --realign-legacy exige un motif non vide (audit trail, #10332).",
              file=sys.stderr)
        return 2

    try:
        fieldnames, rows, raw_ok = _read_csv(args.csv)
    except OSError as exc:
        print(f"ERROR : lecture CSV : {exc}", file=sys.stderr)
        return 2
    if not raw_ok:
        print("ERROR : round-trip CSV non byte-identique, ecriture refusee "
              "(format inattendu).", file=sys.stderr)
        return 2

    pivot = _cells(json.loads(args.pivot.read_text(encoding="utf-8")))
    twin = _cells(json.loads(args.twin.read_text(encoding="utf-8")))
    pivot_rel = args.pivot.as_posix()
    pivot_posix = pathlib.PurePosixPath(pivot_rel).as_posix()

    def _row_vise_pivot(brut: object) -> bool:
        """Vrai si la ligne CSV vise exactement le carnet pivot demande.

        Jamais le seul basename : dans partner-course.csv, quatre carnets
        distincts partagent ``research.ipynb`` -- le filtre historique par
        basename reecrivait les lignes des autres carnets avec le jumeau
        du pivot (#27148, c.7026312711). Discriminant = chemin complet :
        egalite exacte, ou suffixe dont le cote le plus court porte au
        moins un repertoire (pivot absolu vs ligne relative au depot, et
        inversement).
        """
        nb = str(brut or "").strip()
        if not nb:
            return False
        if nb == pivot_posix:
            return True
        if "/" in nb and pivot_posix.endswith("/" + nb):
            return True
        if "/" in pivot_posix and nb.endswith("/" + pivot_posix):
            return True
        return False
    wanted = {c.strip() for c in args.cells.split(",")} if args.cells else None
    lang = args.lang

    for col in (f"text_{lang}", f"hash_{lang}", f"src_hash_{lang}", "src_hash"):
        if col not in fieldnames:
            print(f"ERROR : colonne {col!r} absente du CSV.", file=sys.stderr)
            return 2

    report: list[dict[str, object]] = []
    changed = 0
    changed_legacy = 0
    alignable = ("CONCATENATED", "CSV_EMPTY", "NO_TWIN_TEXT")
    if realign:
        alignable = alignable + ("CSV_ONLY_CONTENT",)
    for row in rows:
        if not _row_vise_pivot(row.get("notebook")):
            continue
        cid = row.get("cell_id") or ""
        if wanted is not None and cid not in wanted:
            continue
        twin_text, twin_type = twin.get(cid, ("", ""))
        pivot_text, _ = pivot.get(cid, ("", ""))
        if twin_type != "markdown":
            report.append({"cell": cid, "verdict": "SKIP_NOT_MARKDOWN"})
            continue
        verdict = classify(row, twin_text, lang)
        entry = {
            "cell": cid,
            "verdict": verdict,
            "csv_len": len((row.get(f"text_{lang}") or "").strip()),
            "twin_len": len(twin_text.strip()),
        }
        if verdict in alignable and args.apply:
            if verdict == "NO_TWIN_TEXT":
                entry["verdict"] = "SKIP_NO_TWIN_TEXT"
                report.append(entry)
                continue
            if verdict == "CSV_ONLY_CONTENT":
                # Qualification du residu (#27148, demande 3) : apercu du texte
                # remplace — anglais pre-francisation vs derive ordinaire.
                replaced = (row.get(f"text_{lang}") or "").strip()
                entry["replaced_preview"] = replaced[:80]
            row[f"text_{lang}"] = twin_text
            row[f"hash_{lang}"] = cell_hash(twin_text)
            row["src_hash"] = cell_hash(pivot_text)
            row[f"src_hash_{lang}"] = cell_hash(pivot_text)
            changed += 1
            entry["verdict"] = "ALIGNED_LEGACY" if verdict == "CSV_ONLY_CONTENT" else "ALIGNED"
            entry["from"] = verdict
            if verdict == "CSV_ONLY_CONTENT":
                changed_legacy += 1
        report.append(entry)

    if args.apply and changed:
        buf = io.StringIO()
        newline = "\r\n" if b"\r\n" in args.csv.read_bytes() else "\n"
        writer = csv.DictWriter(buf, fieldnames=fieldnames, lineterminator=newline)
        writer.writeheader()
        writer.writerows(rows)
        args.csv.write_bytes(buf.getvalue().encode("utf-8"))

    blocking = [r for r in report
                if r["verdict"] in ("CONCATENATED", "CSV_ONLY_CONTENT", "CONTAINS_TWIN", "CSV_EMPTY")]
    if args.json:
        payload: dict[str, object] = {"cells": report, "aligned": changed,
                                      "out_of_phase": len(blocking)}
        if realign:
            payload["realign_legacy_motif"] = args.realign_legacy
            payload["aligned_legacy"] = changed_legacy
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        print(f"lignes evaluees : {len(report)}  alignees : {changed}  hors phase : {len(blocking)}")
        if realign:
            print(f"mode realign-legacy ({changed_legacy} legacy) : {args.realign_legacy}")
        for r in report:
            if r["verdict"] != "IN_SYNC":
                extra = f" (csv {r.get('csv_len')} vs jumeau {r.get('twin_len')})" if "csv_len" in r else ""
                if "replaced_preview" in r:
                    extra += f" remplace : {r['replaced_preview']!r}"
                print(f"  [{r['verdict']}] {r['cell']}{extra}")

    return 0 if not blocking else 1


if __name__ == "__main__":
    sys.exit(main())
