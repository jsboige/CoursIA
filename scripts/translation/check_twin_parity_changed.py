#!/usr/bin/env python3
"""Garde de parite jumeau FR/<lang> scopee au diff d'une PR (#19116).

Motivation mesuree (#18844, 2026-10-04) : une PR notebook-only qui casse la
parite d'un jumeau ``xxx_<lang>.ipynb`` (re-execution native au lieu du
re-rendu T4) n'est vue par AUCUNE jambe -- ``Scripts Tests (CPU)`` ne se
declenche pas (filtre ``scripts/**``) et ``translation-parity.yml`` ne tourne
que sur ``schedule``/``workflow_dispatch``. Le défaut atterrit sur ``main``
vert, puis rougit la prochaine PR de scripts qui n'y est pour rien.

Ce garde evalue UNIQUEMENT les paires touchees par le diff de la PR : pour
chaque notebook modifie, il considere la paire ``(xxx.ipynb,
xxx_<lang>.ipynb)`` si le notebook est le jumeau, ou toutes les paires
``(xxx.ipynb, xxx_<lang>.ipynb)`` existantes si le notebook est la source FR.
Re-executer seulement le FR casse aussi la parite (l'EN garde ses anciennes
sorties) : la paire est donc evaluee des qu'UN des deux membres change.

Les verdicts bloquants et la mecanique d'invariants sont ceux de
``check_translation_parity.py`` (Epic #10038 grain B), reutilise en
librairie : CODE_DRIFT / STRUCTURE_DRIFT / OUTPUT_FABRICATED bloquent,
FR_CONTAM reste advisory sauf ``--strict-fr``.

Codes de sortie :
    0  aucune paire touchee, ou toutes les paires touchees passent ;
    1  au moins une anomalie bloquante sur une paire touchee ;
    2  incident d'entree (git/JSON illisible) -- neutre au check-run via
       ``warn_rc=(2,)`` dans le registre fast-lane, jamais un faux vert.

Temoin positif (fondateur, #18844) : tete ``c4c53386af`` -- le jumeau EN
``medical_chatbot_en.ipynb`` re-execute nativement, cellule ``d0d7a23d`` a
41 sorties contre 48 au FR. Temoin negatif : ``#19115`` (tete
``f43225aeef``) -- re-rendu T4 du meme jumeau, la paire passe.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path, PurePosixPath
from typing import List, Optional, Set, Tuple

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import check_translation_parity as ctp  # noqa: E402

BLOCKING_VERDICTS = {"CODE_DRIFT", "STRUCTURE_DRIFT", "OUTPUT_FABRICATED"}


def changed_notebooks(repo_root: Path, diff_range: str) -> Optional[List[str]]:
    """Notebooks (chemins POSIX relatifs) modifies par ``diff_range``.

    Rend ``None`` sur incident git (l'appelant sort en 2) : un diff illisible
    n'est pas une absence de défaut.
    """
    proc = subprocess.run(
        ["git", "diff", "--name-only", "--diff-filter=AMR", diff_range],
        cwd=repo_root, capture_output=True, text=True, encoding="utf-8",
        errors="replace",
    )
    if proc.returncode != 0:
        print(f"ERROR: git diff illisible ({diff_range}) : {proc.stderr.strip()}",
              file=sys.stderr)
        return None
    return [line.strip() for line in proc.stdout.splitlines()
            if line.strip().endswith(".ipynb")]


def derive_candidate_pairs(changed: List[str]) -> Set[Tuple[str, str, str]]:
    """Paires ``(source, translation, lang)`` candidates pour les chemins donnes.

    Pure : aucune lecture disque. Un jumeau ``xxx_<lang>.ipynb`` modifie
    candidate sa source ; une source ``xxx.ipynb`` modifiee candidate tous
    ses jumeaux existants potentiels (le filtre disque tranchera).
    """
    candidates: Set[Tuple[str, str, str]] = set()
    for path in changed:
        if not path.endswith(".ipynb"):
            continue
        posix = PurePosixPath(path)
        stem = posix.stem
        parent = str(posix.parent) if str(posix.parent) != "." else ""
        suffix_match = ctp._SUFFIX_RE.match(stem)
        if suffix_match and suffix_match.group("lang") in ctp.TARGET_LANGS:
            src_stem = suffix_match.group("stem")
            src = f"{parent}/{src_stem}.ipynb" if parent else f"{src_stem}.ipynb"
            candidates.add((src, path, suffix_match.group("lang")))
        else:
            for lang in ctp.TARGET_LANGS:
                trd = f"{parent}/{stem}_{lang}.ipynb" if parent \
                    else f"{stem}_{lang}.ipynb"
                candidates.add((path, trd, lang))
    return candidates


def existing_pairs(repo_root: Path,
                   candidates: Set[Tuple[str, str, str]]
                   ) -> List[Tuple[Path, Path, str, str]]:
    """Filtre les candidates dont les DEUX membres existent sur disque.

    Rend ``[(source_path, translation_path, stem, lang)]`` trié pour un
    rapport déterministe.
    """
    kept = []
    for src_rel, trd_rel, lang in sorted(candidates):
        src = repo_root / Path(src_rel)
        trd = repo_root / Path(trd_rel)
        if src.is_file() and trd.is_file():
            kept.append((src, trd, src.stem, lang))
    return kept


def evaluate_pair(repo_root: Path, src: Path, trd: Path,
                  strict_fr: bool) -> Tuple[List[dict], List[dict]]:
    """Evalue une paire avec les invariants du porte-parole.

    Rend ``(blocking, advisory)`` — anomalies serialisables. Une lecture
    illisible d'un membre est bloquante (READ_ERROR), jamais silencieuse.
    """
    src_cells, src_err = ctp.load_cells(src)
    trd_cells, trd_err = ctp.load_cells(trd)
    if src_err or trd_err:
        return ([{"verdict": "READ_ERROR", "cell_id": "",
                  "detail": {"error": src_err or trd_err,
                             "source": str(src), "translation": str(trd)}}], [])
    anomalies = ctp.check_invariants(src_cells, trd_cells, strict_fr=strict_fr)
    blocking_verdicts = set(BLOCKING_VERDICTS)
    if strict_fr:
        blocking_verdicts.add("FR_CONTAM")
    blocking = []
    advisory = []
    for a in anomalies:
        record = {"verdict": a.verdict, "cell_id": a.cell_id,
                  "detail": a.detail}
        (blocking if a.verdict in blocking_verdicts else advisory).append(record)
    return blocking, advisory


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description="Parite jumeau FR/<lang> scopee au diff de la PR (#19116).")
    p.add_argument("--repo-root", type=Path, default=Path("."),
                   help="Racine du depot (defaut : cwd).")
    p.add_argument("--diff", type=str, default="origin/main...HEAD",
                   help="Plage de diff git (defaut : origin/main...HEAD).")
    p.add_argument("--strict-fr", action="store_true",
                   help="Promouvoir FR_CONTAM d'advisory a bloquant.")
    p.add_argument("--json-only", action="store_true",
                   help="Sortie JSON seule (sans resume lisible).")
    args = p.parse_args(argv)

    repo_root = args.repo_root.resolve()
    if not repo_root.is_dir():
        print(f"ERROR: --repo-root introuvable : {repo_root}", file=sys.stderr)
        return 2

    changed = changed_notebooks(repo_root, args.diff)
    if changed is None:
        return 2

    candidates = derive_candidate_pairs(changed)
    pairs = existing_pairs(repo_root, candidates)

    report = {
        "diff": args.diff,
        "changed_notebooks": len(changed),
        "pairs_evaluated": len(pairs),
        "pairs": [],
    }
    blocking_total = 0
    for src, trd, stem, lang in pairs:
        blocking, advisory = evaluate_pair(repo_root, src, trd, args.strict_fr)
        blocking_total += len(blocking)
        report["pairs"].append({
            "source": str(src.relative_to(repo_root)),
            "translation": str(trd.relative_to(repo_root)),
            "stem": stem,
            "lang": lang,
            "blocking": blocking,
            "advisory": advisory,
        })

    if args.json_only:
        print(json.dumps(report, ensure_ascii=False, indent=1))
    else:
        print(f"[twin-parity] diff={args.diff} : {len(changed)} notebook(s) "
              f"modifie(s), {len(pairs)} paire(s) jumeau touchee(s)")
        for entry in report["pairs"]:
            status = "OK" if not entry["blocking"] else "KO"
            extra = f" (+{len(entry['advisory'])} advisory)" if entry["advisory"] else ""
            print(f"  [{status}] {entry['stem']} ({entry['lang']})"
                  f" : {len(entry['blocking'])} bloquant(s){extra}")
            for a in entry["blocking"]:
                detail = json.dumps(a["detail"], ensure_ascii=False)
                print(f"      {a['verdict']} cellule={a['cell_id']} {detail[:200]}")
        print(f"[twin-parity] verdict : "
              f"{'FAIL' if blocking_total else 'PASS'} "
              f"({blocking_total} anomalie(s) bloquante(s))")

    return 1 if blocking_total else 0


if __name__ == "__main__":
    sys.exit(main())
