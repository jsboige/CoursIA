#!/usr/bin/env python3
"""Detecte les aveux de mode degrade NOUVEAUX dans les sorties commitees (#11754).

Pourquoi cet outil existe
-------------------------
Le cas fondateur (PR #11443, commit 66e2a429bb) : une re-execution Papermill
lancee depuis un worktree (mode de travail recommande) n'a pas le ``.env``
(gitignore). Le notebook ne plante pas -- il imprime son aveu en clair ::

    OpenAI API key non configuree - comparaison skippee

-- et rend un ``execution_count`` parfaitement monotone avec 0 erreur. La
cellule 26 passe de 12 sorties / 1,35 Mo a 4 sorties / 491 Ko : les deux
modeles OpenAI TTS ont disparu du livrable, et TOUS les gates structurels
sont restes verts. Le volume TOTAL de la PR augmentait meme (5,40 -> 5,86 Mo)
: un detecteur de volume global n'aurait rien vu non plus.

Le signal orthogonal, que seul cet organe lit : la **confession textuelle**.
Les notebooks en degradation gracieuse disent eux-memes qu'ils ont saute une
branche -- il suffit de lire leurs sorties et de comparer a la base de fusion.

Recouvrement assume avec check_render_volume_delta.py (#11656)
--------------------------------------------------------------
Ce dernier porte deja un ``UNAVAILABLE_SIGNAL`` sur trois motifs
(``non disponible`` / ``not available`` / ``importerror``). Les motifs ci-dessous
sont ses angles morts constates sur le cas fondateur (aucun des trois ne
matche ``non configuree - comparaison skippee``) :

    NON_CONFIGURED : 32 occurrences preexistantes sur le corpus (2026-08-19)
    SKIPPED        : 27
    NOT_FOUND      : 43  (dont le tell du worktree : ``WARNING: .env non trouve``)
    UNAVAILABLE_FR : 16  (``indisponible``, distinct de ``non disponible``)

Ces comptes prouvent le deuxieme principe de conception : **la comparaison
se fait contre la base de fusion** (multiset de lignes confession base vs
head). Un scan absolu du seul head produirait ~118 findings herites -- du
bruit qui tuerait l'organe a sa naissance. Seules les confessions ABSENTES
a la base et presentes a la tete sont signalees (stance frozen-inheritance,
cf. h1_hygiene_scan #11840 / pip-leak-guard #6314).

Comment ca marche
-----------------
1. Extrait le texte des sorties commitees (stream, traceback d'erreur,
   text/plain des execute_result/display_data) -- le meme extracteur que
   ``_summarize_unavailable`` de check_render_volume_delta.

2. Par ligne physique, applique les patterns nommes ci-dessus. Une ligne
   matchee = une confession ``(pattern, ligne normalisee)``.

3. Diff multiset notebook-wide base vs head (pas par index de cellule : les
   index glissent aux insertions). Les confessions nouvelles sont les
   findings ; l'attribution de cellule est lue sur le head.

4. Chaque finding nomme ce qu'il a mesure : pattern, cellule head, ligne
   d'aveu, volume d'octets de sorties de la cellule (base ~ head par index
   quand les tailles alignent, head sinon), totaux notebook base/head.

5. Exemptions et codes de sortie (mirroir #11656 / #8655) :
   - notebook NOUVEAU a la base : exempt (tout est ajoute, rien n'est une
     degradation d'un existant) ;
   - ref git invalide : rc=2 (fail loud -- jamais de fallback silencieux qui
     rendrait « pas regarde » et « rien trouve » indistinguables) ;
   - rc=0 sans finding, rc=1 avec findings quand ``--check``.

Usage
-----
    python detect_degraded_mode.py NB.ipynb --check
    python detect_degraded_mode.py NB.ipynb --base <merge-base> --head <ref> --check
    python detect_degraded_mode.py NB1.ipynb NB2.ipynb --base <sha> --json

Voir aussi
----------
check_render_volume_delta.py -- l'organe frere : volume relatif par famille
    MIME (catche -96/-99 %) ; celui-ci catche les degradations a volume
    conserve, declares en texte
Issue #11754 -- cahier des charges + mesure du cas fondateur
PR #11443 commit 66e2a429bb -- la fixture vivante (controle positif)
h1_hygiene_scan.py -- la stance frozen-inheritance dont cet organe herite
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

# --- Patterns d'aveu (calibres sur corpus 2026-08-19, cf docstring) ----------

CONFESSION_PATTERNS: dict[str, re.Pattern[str]] = {
    "NON_CONFIGURED": re.compile(r"non\s+configur", re.IGNORECASE),
    "SKIPPED": re.compile(r"\bskipp", re.IGNORECASE),
    "NOT_FOUND": re.compile(r"non\s+trouv|introuvable", re.IGNORECASE),
    "UNAVAILABLE_FR": re.compile(r"indisponible", re.IGNORECASE),
}

# Lignes d'aveu tronquees a cette longueur dans les rapports (les sorties
# audio/base64 adjacentes n'ont rien d'utile pour le lecteur).
MAX_LINE_LEN = 160


def _iter_output_payloads(cell: dict):
    """Rend le texte de chaque sortie : stream.text, error.traceback,
    data['text/plain']. Meme extraction que _summarize_unavailable de
    check_render_volume_delta (les deux organes doivent voir les memes
    payloads ou leur recouvrement documente est un mensonge)."""
    for outp in (cell.get("outputs") or []):
        if outp.get("output_type") == "stream":
            text = outp.get("text")
            if isinstance(text, str):
                yield text
            elif isinstance(text, (list, tuple)):
                yield "".join(t for t in text if isinstance(t, str))
        elif outp.get("output_type") == "error":
            tb = outp.get("traceback")
            if isinstance(tb, (list, tuple)):
                yield "\n".join(t for t in tb if isinstance(t, str))
        else:
            data = outp.get("data")
            if isinstance(data, dict):
                tp = data.get("text/plain")
                if isinstance(tp, str):
                    yield tp
                elif isinstance(tp, (list, tuple)):
                    yield "".join(t for t in tp if isinstance(t, str))


def _normalize_line(line: str) -> str:
    """Cle de multiset : espaces collapses, casefold. Les timings et
    compteurs varient d'une exec a l'autre autour d'un aveu identique --
    mais l'aveu lui-meme (sa ligne) est stable ; on ne normalise PAS les
    chiffres pour rester honnete : si la ligne differe, elle est nouvelle."""
    return re.sub(r"\s+", " ", line).strip().casefold()


def extract_confessions(nb: dict) -> list[tuple[str, str, int]]:
    """[(pattern_name, ligne normalisee, index de cellule)] -- ordre de
    lecture, doublons conserves (le multiset compte les occurrences)."""
    found: list[tuple[str, str, int]] = []
    for idx, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        for payload in _iter_output_payloads(cell):
            for raw_line in payload.splitlines():
                if not raw_line.strip():
                    continue
                for name, rx in CONFESSION_PATTERNS.items():
                    if rx.search(raw_line):
                        found.append((name, _normalize_line(raw_line), idx))
                        break  # une ligne = une confession, pattern gagnant unique
    return found


def _cell_output_bytes(nb: dict, idx: int) -> int:
    if not (0 <= idx < len(nb.get("cells", []))):
        return 0
    return sum(len(json.dumps(o, ensure_ascii=False)) for o in (nb["cells"][idx].get("outputs") or []))


def _notebook_output_bytes(nb: dict) -> int:
    return sum(
        len(json.dumps(o, ensure_ascii=False))
        for c in nb.get("cells", [])
        for o in (c.get("outputs") or [])
    )


def _repo_rel_path(nb_path: Path) -> str:
    """Chemin POSIX relatif a la racine du repo qui contient le notebook.
    ``git show <ref>:<path>`` n'accepte pas de chemin absolu (et encore
    moins un chemin Windows a contre-obliques) -- le ref-path est toujours
    relatif a la racine. Les tests topologie appellent scan_notebook avec
    un chemin absolu dans un tmp repo distinct du cwd."""
    nb_abs = nb_path if nb_path.is_absolute() else (Path.cwd() / nb_path)
    proc = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True, text=True, encoding="utf-8", check=False,
        cwd=str(nb_abs.parent),
    )
    if proc.returncode != 0:
        return nb_path.as_posix()
    toplevel = Path(proc.stdout.strip())
    return nb_abs.resolve().relative_to(toplevel.resolve()).as_posix()


def _read_notebook_at_ref(nb_path: Path, ref: str) -> dict | None:
    rel = _repo_rel_path(nb_path)
    proc = subprocess.run(
        ["git", "show", f"{ref}:{rel}"],
        capture_output=True, text=True, encoding="utf-8", check=False,
        cwd=str(nb_path.parent),
    )
    if proc.returncode != 0:
        return None
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        return None


def _path_exists_at_ref(nb_path: Path, ref: str) -> bool:
    rel = _repo_rel_path(nb_path)
    proc = subprocess.run(
        ["git", "cat-file", "-e", f"{ref}:{rel}"],
        capture_output=True, check=False, cwd=str(nb_path.parent),
    )
    return proc.returncode == 0


def _ref_resolves(nb_path: Path, ref: str) -> bool:
    return subprocess.run(
        ["git", "rev-parse", "--verify", "--quiet", f"{ref}^{{commit}}"],
        capture_output=True, check=False, cwd=str(nb_path.parent),
    ).returncode == 0


def scan_notebook(nb_path: Path, base_ref: str, head_ref: str | None = None) -> dict:
    """Diff des confessions d'un notebook entre base_ref et head_ref."""
    if head_ref is None:
        try:
            nb_head = json.loads(nb_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as e:
            return {"notebook": str(nb_path), "error": f"head unreadable: {e}"}
        head_label = "working_tree"
    else:
        nb_head = _read_notebook_at_ref(nb_path, head_ref)
        if nb_head is None:
            return {"notebook": str(nb_path), "error": f"head_ref {head_ref} unreadable"}
        head_label = head_ref

    # Garde anti-auto-desarmement (mirroir #8655/#8662) : un ref de base
    # invalide ferait passer le notebook pour NOUVEAU -> exemption -> rc=0
    # silencieux sur toute la PR.
    if not _ref_resolves(nb_path, base_ref):
        return {"notebook": str(nb_path), "error": f"base_ref {base_ref} introuvable (ref git invalide)"}

    if not _path_exists_at_ref(nb_path, base_ref):
        return {
            "notebook": str(nb_path), "base_ref": base_ref, "head_ref": head_label,
            "new_file": True, "findings": [],
            "stats": {"findings_count": 0},
        }

    nb_base = _read_notebook_at_ref(nb_path, base_ref)
    if nb_base is None:
        return {"notebook": str(nb_path), "error": f"base_ref {base_ref} unreadable"}

    conf_base = extract_confessions(nb_base)
    conf_head = extract_confessions(nb_head)

    # Diff multiset : une confession est heritee ssi la base compte la meme
    # (pattern, ligne) au moins autant de fois. Les nouvelles = head - base.
    base_multiset = Counter((name, line) for name, line, _ in conf_base)
    head_multiset = Counter((name, line) for name, line, _ in conf_head)
    new_keys = head_multiset - base_multiset  # Counter soustraction : max(0, h-b)

    findings = []
    for (name, line), _count in sorted(new_keys.items()):
        cell_idx = next(i for n, l, i in conf_head if (n, l) == (name, line))
        # Volume de la cellule coupable : base par index si le notebook a la
        # meme longueur (insertions/suppositions de cellules sinon deplacent
        # tout), head sinon. Les DEUX chiffres nomment ce qui a ete mesure.
        base_cell_bytes = (
            _cell_output_bytes(nb_base, cell_idx)
            if len(nb_base.get("cells", [])) == len(nb_head.get("cells", [])) else None
        )
        raw_line = line[:MAX_LINE_LEN]
        findings.append({
            "kind": "DEGRADED_CONFESSION",
            "pattern": name,
            "cell_index": cell_idx,
            "line": raw_line,
            "cell_output_bytes_base": base_cell_bytes,
            "cell_output_bytes_head": _cell_output_bytes(nb_head, cell_idx),
        })

    return {
        "notebook": str(nb_path), "base_ref": base_ref, "head_ref": head_label,
        "findings": findings,
        "stats": {
            "findings_count": len(findings),
            "base_confessions_total": sum(base_multiset.values()),
            "head_confessions_total": sum(head_multiset.values()),
            "notebook_output_bytes_base": _notebook_output_bytes(nb_base),
            "notebook_output_bytes_head": _notebook_output_bytes(nb_head),
        },
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Detecte les aveux de mode degrade NOUVEAUX dans les sorties "
                    "commitees d'un notebook, contre la base de fusion (#11754).")
    parser.add_argument("notebooks", nargs="+", type=Path,
                        help="notebook(s) .ipynb a comparer")
    parser.add_argument("--base", default="origin/main",
                        help="ref de base de fusion (defaut origin/main ; en CI "
                             "passez le merge-base, jamais origin/main deux-points)")
    parser.add_argument("--head", default=None,
                        help="ref de tete (defaut : arbre de travail)")
    parser.add_argument("--check", action="store_true",
                        help="rc=1 si des findings existent (mode gate)")
    parser.add_argument("--json", action="store_true",
                        help="sortie JSON machine-lisible (stdout)")
    args = parser.parse_args(argv)

    results = []
    rc = 0
    for nb_path in args.notebooks:
        result = scan_notebook(nb_path, args.base, args.head)
        if "error" in result:
            rc = 2
            results.append(result)
            continue
        if result["findings"]:
            rc = rc if rc == 2 else (1 if args.check else 0)
        results.append(result)

    payload = {
        "tool": "detect_degraded_mode",
        "issue": 11754,
        "base_ref": args.base,
        "head_ref": args.head or "working_tree",
        "results": results,
        "findings_total": sum(r.get("stats", {}).get("findings_count", 0) for r in results),
        "errors_total": sum(1 for r in results if "error" in r),
    }

    if args.json:
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        for r in results:
            if "error" in r:
                print(f"ERROR {r['notebook']}: {r['error']}", file=sys.stderr)
                continue
            tag = "NEW FILE (exempt)" if r.get("new_file") else "OK"
            print(f"{r['notebook']}: {r['stats']['findings_count']} nouvelle(s) confession(s) "
                  f"[heritees base={r['stats']['base_confessions_total']} "
                  f"head={r['stats']['head_confessions_total']}] "
                  f"[volume {r['stats']['notebook_output_bytes_base']} -> "
                  f"{r['stats']['notebook_output_bytes_head']} o] {tag}")
            for f in r["findings"]:
                bb = f["cell_output_bytes_base"]
                bb_s = f"{bb}" if bb is not None else "?"
                print(f"  {f['pattern']} cell {f['cell_index']} "
                      f"[cell bytes {bb_s} -> {f['cell_output_bytes_head']}] : {f['line']}")
        if payload["errors_total"]:
            print(f"{payload['errors_total']} erreur(s) structurelle(s) -- voir stderr",
                  file=sys.stderr)
        total = payload["findings_total"]
        verdict = "DEGRADED-MODE SIGNAL" if total else "aucun signal"
        print(f"\nVerdict: {verdict} ({total} finding(s))")

    return rc


if __name__ == "__main__":
    sys.exit(main())
