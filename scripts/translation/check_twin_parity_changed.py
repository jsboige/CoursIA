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

Volet registre (#24911) : la derivation par suffixe est aveugle aux paires
C#↔Python declarees dans ``scripts/notebook_tools/twin_pairs.d/`` -- leurs
noms ne portent AUCUN suffixe de langue, donc un cote modifie ne candidate
que des jumeaux ``_en``/``_es`` inexistants, le filtre disque ecarte tout, et
le garde rend un faux vert qu'une PR a paye (#24869 : enrichissement C# seul
de ``Z3-04-Strings-Regex``, garde SUCCESS, cron rouge 24 h plus tard). Le
garde consulte donc AUSSI le registre : toute paire declaree dont un membre
apparait dans le diff est evaluee par l'organe du cron (``check_pair`` +
``_classify_per_pair``), et rougit seulement sur un drift INTRODUIT par la
PR -- un drift pre-existant au base reste advisory, c'est l'etat que le cron
suit deja sur main.

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
sys.path.insert(0, str(HERE.parent / "notebook_tools"))

import check_translation_parity as ctp  # noqa: E402
import check_twin_parity as nbtp  # noqa: E402 -- organe du cron (#24911)

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


# ---------------------------------------------------------------------------
# Volet registre twin_pairs.d (#24911)
# ---------------------------------------------------------------------------


def default_registry_dir(repo_root: Path) -> Path:
    """Registre canonique du depot evalue (cf ``nbtp.DEFAULT_REGISTRY``)."""
    return repo_root / "scripts" / "notebook_tools" / "twin_pairs.d"


def derive_registry_pairs(registry_dir: Path,
                          changed: List[str]) -> Tuple[List[dict], Optional[str]]:
    """Paires declarees au registre dont un membre apparait dans ``changed``.

    Rend ``(matches, incident)``. Un registre absent ne change rien (depot
    sans paires declarees) ; un registre present mais illisible est un
    INCIDENT remonte a l'appelant (sortie 2) : on ne rend pas un faux vert
    sur des paires qu'on n'a pas pu lire. Le ``except Exception`` est
    delibere -- tout echec de lecture (PyYAML absent, YAML malforme,
    entree non dict) a la meme consequence fail-closed, jamais un crash ni
    un silence.
    """
    if registry_dir is None or not registry_dir.exists():
        return [], None
    changed_set = {p.replace("\\", "/") for p in changed}
    try:
        pairs = nbtp.load_registry(registry_dir)
    except Exception as exc:  # fail-closed : incident, pas faux vert
        return [], f"registre illisible ({registry_dir}) : {exc}"
    matches = []
    for pair in pairs:
        if not isinstance(pair, dict):
            continue
        members = {str(pair.get(k, "")).replace("\\", "/")
                   for k in ("python", "csharp")}
        if members & changed_set:
            matches.append(pair)
    return matches, None


def base_ref_of(diff_range: str) -> str:
    """Ref de base d'une plage git : membre gauche de ``A...B`` ou ``A..B``."""
    for sep in ("...", ".."):
        if sep in diff_range:
            return diff_range.split(sep, 1)[0]
    return diff_range


def evaluate_registry_pair(repo_root: Path, pair: dict, base_ref: str) -> dict:
    """Verdict per-pair du cron, rejoue sur une paire touchee par le diff.

    Reutilise l'organe du cron (``check_pair`` a HEAD et au base, puis
    ``_classify_per_pair``) : la paire declenche le rouge seulement si la PR
    INTRODUIT le drift (cote touche non rescelle, attestation perdue,
    numerotation cassee) ; un drift pre-existant au base reste advisory --
    c'est l'etat que le cron ``twin-parity-cron`` suit deja sur main.
    """
    head = nbtp.check_pair(repo_root, pair, "HEAD")
    base = nbtp.check_pair(repo_root, pair, base_ref)
    verdict = nbtp._classify_per_pair(
        base["status"], head["status"],
        base_drift=set(base["drift_sides"]), head_drift=set(head["drift_sides"]),
        base_no_baseline=base["no_baseline"], head_no_baseline=head["no_baseline"])
    details = list(head["details"])
    if verdict != "OK":
        details.append(
            f"base={base['status']} (cotes en drift : "
            f"{', '.join(base['drift_sides']) or 'aucun'}) -> "
            f"head={head['status']} : {verdict}")
    return {
        "name": head["name"],
        "family": head["family"],
        "parity_level": head["parity_level"],
        "python": head["python"],
        "csharp": head["csharp"],
        "verdict": verdict,
        "blocking": verdict == "DRIFT_INTRODUCED",
        "head_status": head["status"],
        "base_status": base["status"],
        "drift_sides": head["drift_sides"],
        "no_baseline": head["no_baseline"],
        "details": details,
    }


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
    p.add_argument("--registry", type=Path, default=None,
                   help="Registre twin_pairs.d a consulter (defaut : "
                        "<repo-root>/scripts/notebook_tools/twin_pairs.d).")
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
        "registry_pairs": [],
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

    # Volet registre (#24911) : paires declarees touchees par le diff.
    registry_dir = args.registry if args.registry else default_registry_dir(repo_root)
    reg_pairs, reg_incident = derive_registry_pairs(registry_dir, changed)
    if reg_incident:
        print(f"ERROR: {reg_incident}", file=sys.stderr)
        return 2
    for pair in reg_pairs:
        try:
            entry = evaluate_registry_pair(repo_root, pair,
                                           base_ref_of(args.diff))
        except Exception as exc:  # fail-closed : incident, pas faux vert
            print(f"ERROR: evaluation registre impossible "
                  f"({pair.get('name', '?')}) : {exc}", file=sys.stderr)
            return 2
        if entry["blocking"]:
            blocking_total += 1
        report["registry_pairs"].append(entry)

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
        for entry in report["registry_pairs"]:
            status = "KO" if entry["blocking"] else "OK"
            print(f"  [{status}] {entry['name']} ({entry['parity_level']}, registre)"
                  f" : {entry['verdict']}")
            for d in entry["details"]:
                print(f"      {d[:200]}")
        print(f"[twin-parity] registre : {len(report['registry_pairs'])} "
              f"paire(s) declaree(s) touchee(s)")
        print(f"[twin-parity] verdict : "
              f"{'FAIL' if blocking_total else 'PASS'} "
              f"({blocking_total} anomalie(s) bloquante(s))")

    return 1 if blocking_total else 0


if __name__ == "__main__":
    sys.exit(main())
