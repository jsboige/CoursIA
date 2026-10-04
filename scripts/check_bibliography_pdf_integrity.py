#!/usr/bin/env python3
"""Valide l'integrite des PDF du gisement bibliographique partage.

Ce script repond a un besoin mesure : le 2026-09-26, un diagnostic concluait que
le gisement `G:/Mon Drive/MyIA/IA/Bibliographie IA` etait « systemiquement
corrompu », sur 4 PDF sur 4 illisibles (`pypdf.errors.PdfStreamError: Stream has
ended unexpectedly`, `EOF marker not found`). Verifie le 2026-09-30, les quatre
memes fichiers se lisent normalement.

L'ecart vient d'une confusion que ce script existe pour lever : un PDF servi par
le client Google Drive n'est pas toujours **hydrate** (le fichier est streame a
la demande). Une lecture qui echoue sur un fichier non hydrate ne dit rien de
l'etat du fichier sur le disque du gisement. Le script distingue donc trois
verdicts la ou le diagnostic d'origine n'en avait qu'un :

  - `OK`                : lecture reussie sur place
  - `OK_AFTER_HYDRATE`  : lecture echouee sur place, reussie apres copie locale
                          (artefact d'hydratation, le fichier est intact)
  - `CORRUPT`           : lecture echouee dans les deux cas (le seul rouge)

Sans cette distinction, un gisement sain peut etre declare corrompu, et une
issue de blocage peut survivre a sa propre cause.

Le script verifie aussi une **ancre d'identite** quand on lui en fournit une
(`--anchors`). C'est la seconde moitie du meme incident : le diagnostic du
2026-09-26 comparait un `sha1` mesure a un `sha256[:8]` annonce, et concluait du
mismatch que « les fichiers ont ete retelecharges ou corrompus ». La comparaison
portait sur deux algorithmes differents ; les quatre fichiers etaient
byte-identiques. Une ancre de 8 caracteres hexadecimaux est donc confrontee aux
trois empreintes, et le rapport **nomme l'algorithme qui a matche** au lieu de
rendre un booleen.

Usage:
  python scripts/check_bibliography_pdf_integrity.py --files A.pdf B.pdf
  python scripts/check_bibliography_pdf_integrity.py --root "G:/Mon Drive/MyIA/IA/Bibliographie IA"
  python scripts/check_bibliography_pdf_integrity.py --root <dir> --sample 60 --json out.json
  python scripts/check_bibliography_pdf_integrity.py --root <dir> --anchors ancres.json

Options:
  --files PATH ...     Valider ces fichiers precis (prioritaire sur --root)
  --root PATH          Racine du gisement a parcourir
  --anchors PATH       JSON {"<chemin ou basename>": "<8 hex>"} des ancres d'identite
  --sample N           Ne valider qu'un echantillon deterministe de N fichiers
                       (tirage par pas regulier sur la liste triee)
  --max-seconds S      Budget global ; le parcours s'arrete proprement entre deux
                       fichiers une fois le budget consomme (defaut 300)
  --json PATH          Ecrire le rapport structure
  --quiet              Ne pas afficher le detail par fichier

Limite connue : il n'y a pas de delai par fichier. Une lecture bloquee par le
client Drive peut immobiliser le parcours ; le budget global n'est verifie
qu'entre deux fichiers. Lancez un parcours large en tache de fond.
"""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import random
import shutil
import sys
import tempfile
import time
from pathlib import Path

VERDICT_OK = "OK"
VERDICT_HYDRATED = "OK_AFTER_HYDRATE"
VERDICT_CORRUPT = "CORRUPT"
VERDICT_MISSING = "IO_ERROR"

ANCHOR_NONE = "NO_ANCHOR"
ANCHOR_MISMATCH = "MISMATCH"
# Ordre de confrontation d'une ancre de 8 hex : le nom rendu dit QUEL algorithme
# a matche. Comparer un sha1 a un sha256[:8] rend un mismatch qui n'en est pas un.
ANCHOR_ALGOS = (("sha256", "MATCH_SHA256_8"), ("sha1", "MATCH_SHA1_8"),
                ("md5", "MATCH_MD5_8"))

DEFAULT_ROOT = "G:/Mon Drive/MyIA/IA/Bibliographie IA"


def _try_parse(path: Path) -> tuple[bool, int, str]:
    """Tente une lecture pypdf. Renvoie `(succes, pages, message)`."""
    try:
        from pypdf import PdfReader
    except ImportError:  # pragma: no cover - dependance d'environnement
        raise SystemExit("ERREUR: pypdf manquant. Installer via `pip install pypdf`.")
    try:
        reader = PdfReader(str(path))
        return True, len(reader.pages), ""
    except Exception as exc:
        return False, 0, "%s: %s" % (type(exc).__name__, str(exc)[:160])


def _hash(path: Path, algo: str) -> str:
    h = hashlib.new(algo)
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _resolve_anchor(path: Path, anchors: dict[str, str]) -> str | None:
    """Retrouve l'ancre d'un fichier par chemin exact, puis par nom de base."""
    for key in (str(path), path.name):
        if key in anchors:
            return str(anchors[key]).strip()
    return None


def check_anchor(path: Path, anchors: dict[str, str] | None) -> tuple[str, str]:
    """Confronte le fichier a son ancre declaree. Rend `(statut, algorithme)`.

    Le statut nomme l'algorithme qui a matche, jamais un simple booleen : c'est
    la comparaison `sha1` contre `sha256[:8]` qui a fait declarer corrompu un
    gisement intact.
    """
    if not anchors:
        return ANCHOR_NONE, ""
    expected = _resolve_anchor(path, anchors)
    if not expected:
        return ANCHOR_NONE, ""
    want = expected.strip().lower()
    for algo, label in ANCHOR_ALGOS:
        try:
            if _hash(path, algo)[:len(want)] == want:
                return label, algo
        except (OSError, ValueError):
            continue
    return ANCHOR_MISMATCH, ""


def validate_pdf(path: Path, hydrate_dir: Path | None = None,
                 anchors: dict[str, str] | None = None) -> dict:
    """Valide un PDF ; retente apres copie locale si la lecture sur place echoue.

    La copie locale force le client Drive a hydrater le fichier entier : c'est
    ce qui separe un fichier corrompu d'une lecture servie en streaming.
    """
    if not path.is_file():
        return {"path": str(path), "verdict": VERDICT_MISSING, "pages": 0,
                "size": 0, "sha1": "", "anchor": ANCHOR_NONE, "anchor_algo": "",
                "error": "fichier absent ou illisible"}

    size = path.stat().st_size
    anchor, anchor_algo = check_anchor(path, anchors)
    ok, pages, err = _try_parse(path)
    if ok:
        return {"path": str(path), "verdict": VERDICT_OK, "pages": pages,
                "size": size, "sha1": _hash(path, "sha1"), "anchor": anchor,
                "anchor_algo": anchor_algo, "error": ""}

    first_error = err
    if hydrate_dir is not None:
        try:
            hydrate_dir.mkdir(parents=True, exist_ok=True)
            local = hydrate_dir / ("hydrate-%d.pdf" % random.getrandbits(48))
            shutil.copy2(str(path), str(local))
            ok2, pages2, _ = _try_parse(local)
            try:
                local.unlink()
            except OSError:
                pass
            if ok2:
                return {"path": str(path), "verdict": VERDICT_HYDRATED, "pages": pages2,
                        "size": size, "sha1": _hash(path, "sha1"), "anchor": anchor,
                        "anchor_algo": anchor_algo, "error": first_error}
        except Exception as exc:  # copie impossible : on garde le verdict du lecteur
            first_error = "%s | copie locale: %s" % (first_error, type(exc).__name__)

    return {"path": str(path), "verdict": VERDICT_CORRUPT, "pages": 0,
            "size": size, "sha1": _hash(path, "sha1"), "anchor": anchor,
            "anchor_algo": anchor_algo, "error": first_error}


def _collect_pdfs(root: Path, sample: int | None) -> list[Path]:
    pdfs = sorted(p for p in root.rglob("*.pdf") if p.is_file())
    if sample is not None and 0 < sample < len(pdfs):
        step = len(pdfs) / float(sample)
        pdfs = [pdfs[min(len(pdfs) - 1, int(i * step))] for i in range(sample)]
    return pdfs


def _force_utf8_streams() -> None:
    """Evite le mojibake cp1252 sur les sorties console Windows."""
    if sys.platform != "win32":
        return
    for name in ("stdout", "stderr"):
        stream = getattr(sys, name, None)
        if getattr(stream, "buffer", None) is None:
            continue
        try:
            setattr(sys, name, io.TextIOWrapper(stream.buffer, encoding="utf-8",
                                                errors="replace"))
        except Exception:
            pass


def main() -> int:
    _force_utf8_streams()
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--files", nargs="*", default=None,
                    help="fichiers a valider (prioritaire sur --root)")
    ap.add_argument("--root", default=DEFAULT_ROOT, help="racine du gisement")
    ap.add_argument("--anchors", default=None,
                    help="JSON {\"<chemin ou basename>\": \"<8 hex>\"} des ancres")
    ap.add_argument("--sample", type=int, default=None,
                    help="echantillon deterministe de N fichiers")
    ap.add_argument("--max-seconds", type=float, default=300.0, help="budget global")
    ap.add_argument("--json", default=None, help="chemin du rapport JSON")
    ap.add_argument("--quiet", action="store_true", help="pas de detail par fichier")
    args = ap.parse_args()

    anchors = None
    if args.anchors:
        try:
            anchors = json.loads(Path(args.anchors).read_text(encoding="utf-8"))
        except Exception as exc:
            sys.stderr.write("ERREUR: ancres illisibles (%s): %s\n"
                             % (type(exc).__name__, exc))
            return 2

    started = time.time()
    if args.files:
        targets = [Path(p) for p in args.files]
    else:
        root = Path(args.root)
        if not root.is_dir():
            sys.stderr.write("ERREUR: racine introuvable: %s\n" % root)
            return 2
        targets = _collect_pdfs(root, args.sample)

    results: list[dict] = []
    covered = 0
    with tempfile.TemporaryDirectory(prefix="biblio-hydrate-") as tmp:
        hydrate_dir = Path(tmp)
        for path in targets:
            if time.time() - started > args.max_seconds:
                sys.stderr.write(
                    "[budget] %d fichiers couverts sur %d en %.0f s -- parcours arrete\n"
                    % (covered, len(targets), time.time() - started))
                break
            res = validate_pdf(path, hydrate_dir, anchors)
            results.append(res)
            covered += 1
            if not args.quiet:
                ancre = ("  [%s]" % res["anchor"]) if res["anchor"] != ANCHOR_NONE else ""
                print("%-17s %6s p. %8.2f Mo  %s%s"
                      % (res["verdict"], res["pages"], res["size"] / 1e6,
                         path.name[:70], ancre))

    counts: dict[str, int] = {}
    anchors_seen: dict[str, int] = {}
    for r in results:
        counts[r["verdict"]] = counts.get(r["verdict"], 0) + 1
        if r["anchor"] != ANCHOR_NONE:
            anchors_seen[r["anchor"]] = anchors_seen.get(r["anchor"], 0) + 1

    print("\n%d fichier(s) valide(s) en %.0f s" % (len(results), time.time() - started))
    for verdict in (VERDICT_OK, VERDICT_HYDRATED, VERDICT_CORRUPT, VERDICT_MISSING):
        if counts.get(verdict):
            print("  %-17s %d" % (verdict, counts[verdict]))
    if len(results) < len(targets):
        print("  NON COUVERT        %d (budget epuise)" % (len(targets) - len(results)))
    for status, n in sorted(anchors_seen.items()):
        print("  ancre %-15s %d" % (status, n))

    corrupted = [r for r in results if r["verdict"] == VERDICT_CORRUPT]
    for r in corrupted:
        print("\n  CORROMPU  %s\n            %s" % (r["path"], r["error"]))

    mismatched = [r for r in results if r["anchor"] == ANCHOR_MISMATCH]
    for r in mismatched:
        print("\n  ANCRE EN DEFAUT  %s\n                   sha1 mesure = %s"
              % (r["path"], r["sha1"]))

    if args.json:
        payload = {"root": args.root, "scanned": len(results), "targets": len(targets),
                   "counts": counts, "anchors": anchors_seen, "results": results}
        Path(args.json).write_text(json.dumps(payload, indent=2, ensure_ascii=False),
                                   encoding="utf-8")
        print("\nrapport JSON: %s" % args.json)

    return 1 if (corrupted or mismatched) else 0


if __name__ == "__main__":
    sys.exit(main())