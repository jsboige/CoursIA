"""Verifie, sur l'arbre de FUSION, que les attestations jumelles decrivent
le contenu que `main` va porter.

Pourquoi cette garde existe
---------------------------
Le squash-merge re-hashe l'arbre : un blob atteste sur la branche peut ne
jamais atterrir sur `main`. Le test
`scripts/notebook_tools/tests/test_twin_registry_integrity.py::
test_audit_shas_exist_in_file_history` verifie que le sha atteste par la
DERNIERE attestation d'une paire est un blob que le carnet a reellement eu
dans son historique, sous le path declare. Un sha qui n'atterrit jamais sur
`main` le fait rougir.

La CI de PR ne voit pas cette classe : elle travaille sur `refs/pull/N/merge`,
ou les commits intermediaires restent joignables. Seul l'ARBRE DE FUSION
revele l'orphelin.

Ce que fait l'organe
--------------------
Pour chaque paire dont la PR touche le registre (`twin_pairs.d/`) :

1. l'arbre de fusion est calcule (`git merge-tree --write-tree base head`) --
   c'est lui, et non la base et la tete isolees, qui repond a « `main` sera-t-il
   rouge apres ce merge ? » ;
2. la DERNIERE attestation de la paire est lue dans cet arbre ;
3. chaque sha atteste (`python_sha`, `csharp_sha`, `rust_sha`) est compare au
   blob que l'arbre de fusion porte au path declare.

Verdicts : `OK` / `MISMATCH` / `NODESC` / `CONFLICT` / `PATH-ABSENT`.

Fail-closed
-----------
Une lecture impossible (erreur git, timeout, sortie vide) rend le code 2 :
« je n'ai pas pu lire » n'est jamais « c'est propre ». Le code 1 signifie que
la lecture a reussi et qu'un defaut a ete trouve ; le code 0 que tout est
conforme.

Usage
-----
    python scripts/notebook_tools/check_twin_attestation_squash.py \
        --base origin/main --head <sha|ref> [--repo .] [--json]
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

#: Le module frere qui porte les decisions partagees avec l'organe epingle
#: `check_twin_parity.py` (regle du registre : `twin_parity_base`).
sys.path.insert(0, str(Path(__file__).resolve().parent))

import twin_parity_base

#: Repertoire du registre des paires jumelles (relatif a la racine du depot).
REGISTRY = "scripts/notebook_tools/twin_pairs.d"

#: Bornes de temps : une garde qui depasse n'a pas repondu, elle n'a pas
#: le droit de laisser croire que tout va bien.
GIT_TIMEOUT = 120

#: Cles de sha d'une attestation : le nom du cote, puis ``_sha``.
SHA_KEYS = ("python", "csharp", "rust")

_HEX40 = re.compile(r"^[0-9a-f]{40}$")


class Unreadable(Exception):
    """La mesure n'a pas pu etre faite (erreur git, timeout, sortie vide)."""


def _git(repo: Path, args: list[str], timeout: int = GIT_TIMEOUT) -> str:
    """Execute une lecture git ; leve `Unreadable` si elle echoue."""
    try:
        proc = subprocess.run(
            ["git", "-C", str(repo), *args],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        raise Unreadable(f"timeout sur `git {' '.join(args)}` ({timeout}s)") from None
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout or "").strip()[:200]
        raise Unreadable(f"git {' '.join(args)} rc={proc.returncode} : {detail}")
    return proc.stdout


def _git_merged_tree(repo: Path, base: str, head: str) -> tuple[str, str | None]:
    """Calcule l'arbre de fusion `base` + `head`.

    Rend (arbre, incident). `incident` vaut None en cas de succes, sinon la
    raison pour laquelle l'arbre n'est pas definissable (conflit inclus).
    """
    try:
        proc = subprocess.run(
            ["git", "-C", str(repo), "merge-tree", "--write-tree", base, head],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=GIT_TIMEOUT,
        )
    except subprocess.TimeoutExpired:
        raise Unreadable("timeout sur `git merge-tree --write-tree`") from None
    out = (proc.stdout or "").strip()
    if proc.returncode != 0:
        detail = (proc.stderr or out or "").strip()[:200]
        return "", f"merge-tree rc={proc.returncode} : {detail}"
    if not out:
        raise Unreadable("`git merge-tree --write-tree` a rendu une sortie vide")
    tree = out.splitlines()[0].strip()
    if not _HEX40.match(tree):
        raise Unreadable(f"arbre de fusion illisible : {tree[:60]!r}")
    return tree, None


def _touched_pairs(repo: Path, base: str, head: str) -> list[str]:
    """Paires dont la PR touche le registre."""
    merge_base = _git(repo, ["merge-base", base, head]).strip()
    if not merge_base:
        raise Unreadable(f"merge-base vide entre {base} et {head}")
    out = _git(repo, ["diff", "--name-only", merge_base, head, "--", REGISTRY])
    pairs = set()
    prefix = REGISTRY.split("/")
    for path in out.split():
        parts = path.split("/")
        if parts[:3] != prefix:
            continue
        if len(parts) >= 5:
            # <REGISTRY>/<slug>/<fichier>.yaml  ->  <slug>
            slug = parts[3]
        elif len(parts) == 4 and parts[3].endswith(".yaml"):
            # <REGISTRY>/<slug>.yaml  ->  <slug>  (le descripteur de la paire ;
            # son nom porte l'extension, il n'est PAS le nom de la paire).
            slug = parts[3][: -len(".yaml")]
        else:
            continue
        if twin_parity_base.est_documentation_registre(slug):
            # `_schema.yaml` est la DOCUMENTATION du format, pas le
            # descripteur d'une paire (regle du lecteur canonique,
            # `check_twin_parity.load_registry`). Lue comme une paire, elle
            # n'a ni descripteur ni attestations : la garde rendait NODESC
            # sur une PR conforme (mesure du 26/11 sur #28276).
            continue
        pairs.add(slug)
    return sorted(pairs)


def _tree_blobs(repo: Path, tree: str) -> dict[str, str]:
    """Tous les blobs de l'arbre : chemin -> sha (une seule lecture)."""
    out = _git(repo, ["ls-tree", "-r", tree])
    blobs: dict[str, str] = {}
    for line in out.splitlines():
        head, _, path = line.partition("\t")
        parts = head.split()
        if len(parts) == 3 and parts[1] == "blob" and path:
            blobs[path] = parts[2]
    return blobs


def _cat_files(repo: Path, tree: str, paths: list[str]) -> dict[str, str | None]:
    """Contenu de plusieurs fichiers de l'arbre, en UNE lecture (batch).

    La lecture se fait en OCTETS : la taille annoncee par `cat-file` est une
    taille en octets, et les carnets portent des caractere non-ASCII -- un
    decodage par caracteres decalerait la lecture sur le fichier suivant.

    Les chemins sont passes sur un FICHIER, pas sur un tube : mesure du
    2026-11-23 sur ce depot, `cat-file --batch` mis en lecture sur un tube
    ecrit par le parent met 115 s la ou le meme lot par fichier met 3,7 s
    (le tube n'est pas vu comme ferme par git avant chaque ecriture).
    """
    if not paths:
        return {}
    payload = b"".join(f"{tree}:{path}\n".encode("utf-8") for path in paths)
    handle = tempfile.NamedTemporaryFile(prefix="twin-attest-", suffix=".txt",
                                         delete=False)
    tmp_path = handle.name
    try:
        with handle:
            handle.write(payload)
        with open(tmp_path, "rb") as stdin:
            try:
                proc = subprocess.run(
                    ["git", "-C", str(repo), "cat-file", "--batch"],
                    stdin=stdin,
                    capture_output=True,
                    timeout=GIT_TIMEOUT,
                )
            except subprocess.TimeoutExpired:
                raise Unreadable(
                    "timeout sur `git cat-file --batch`"
                ) from None
    finally:
        try:
            os.unlink(tmp_path)
        except OSError:
            pass
    if proc.returncode != 0:
        detail = (proc.stderr or b"").decode("utf-8", "replace").strip()[:200]
        raise Unreadable(f"git cat-file rc={proc.returncode} : {detail}")
    out = proc.stdout or b""
    files: dict[str, str | None] = {}
    pos = 0
    for path in paths:
        newline = out.find(b"\n", pos)
        if newline == -1:
            raise Unreadable("sortie `cat-file --batch` tronquee")
        header = out[pos:newline].decode("utf-8", "replace")
        pos = newline + 1
        parts = header.split()
        if parts and parts[-1] == "missing":
            files[path] = None
            continue
        if len(parts) < 3:
            raise Unreadable(f"en-tete `cat-file` illisible : {header[:80]}")
        size = int(parts[2])
        files[path] = out[pos:pos + size].decode("utf-8", "replace")
        pos += size + 1
    return files


def _descriptor_paths(raw: str | None) -> dict[str, str]:
    """Paths declares par le descripteur de la paire."""
    if not raw:
        return {}
    paths: dict[str, str] = {}
    for side in SHA_KEYS:
        match = re.search(
            rf"^\s*{side}:\s*\"?([^\"\n]+)\"?\s*$", raw, re.MULTILINE
        )
        if match:
            paths[side] = match.group(1).strip()
    return paths


def _attested_shas(raw: str | None) -> dict[str, str]:
    """Shas attestes par l'attestation, cote par cote."""
    if not raw:
        return {}
    found: dict[str, str] = {}
    for side in SHA_KEYS:
        match = re.search(rf"^{side}_sha:\s*([0-9a-f]{{40}})", raw, re.MULTILINE)
        if match:
            found[side] = match.group(1)
    return found


def check(repo: Path, base: str, head: str) -> dict:
    """Verdict d'ensemble sur l'arbre de fusion."""
    # Les deux refs doivent resoudre : une ref inconnue est une MESURE
    # IMPOSSIBLE (code 2), pas un conflit de fusion (code 1).
    for ref in (base, head):
        _git(repo, ["rev-parse", "--verify", "--quiet", f"{ref}^{{commit}}"])
    tree, incident = _git_merged_tree(repo, base, head)
    if incident:
        return {
            "verdict": "CONFLICT",
            "base": base,
            "head": head,
            "tree": None,
            "pairs": [],
            "reason": incident,
        }
    pairs = _touched_pairs(repo, base, head)
    if not pairs:
        return {
            "verdict": "OK",
            "base": base,
            "head": head,
            "tree": tree,
            "pairs": [],
            "reason": "",
        }
    blobs = _tree_blobs(repo, tree)
    # Derniere attestation de chaque paire : la numerotation est append-only,
    # le tri lexicographique des noms est donc l'ordre chronologique.
    wanted: list[str] = []
    attestations: dict[str, str] = {}
    for pair in pairs:
        prefix = f"{REGISTRY}/{pair}/"
        names = sorted(
            path for path in blobs
            if path.startswith(prefix) and path.endswith(".yaml")
        )
        if names:
            attestations[pair] = names[-1]
            wanted.append(names[-1])
        wanted.append(f"{REGISTRY}/{pair}.yaml")
    contents = _cat_files(repo, tree, wanted)

    entries: list[dict] = []
    for pair in pairs:
        entry = {"pair": pair, "verdict": "OK",
                 "attestation": attestations.get(pair), "details": []}
        paths = _descriptor_paths(contents.get(f"{REGISTRY}/{pair}.yaml"))
        if not paths:
            entry["verdict"] = "NODESC"
            entry["details"].append(
                f"descripteur {REGISTRY}/{pair}.yaml illisible dans l'arbre de fusion"
            )
            entries.append(entry)
            continue
        attestation = attestations.get(pair)
        if not attestation:
            entry["verdict"] = "NODESC"
            entry["details"].append(f"aucune attestation dans {REGISTRY}/{pair}/")
            entries.append(entry)
            continue
        attested = _attested_shas(contents.get(attestation))
        if not attested:
            entry["verdict"] = "NODESC"
            entry["details"].append(f"attestation {attestation} sans sha de cote")
            entries.append(entry)
            continue
        for side, sha in sorted(attested.items()):
            declared = paths.get(side)
            if not declared:
                entry["verdict"] = "MISMATCH"
                entry["details"].append(
                    f"{side}_sha atteste mais path non declare dans le descripteur"
                )
                continue
            blob = blobs.get(declared)
            if blob is None:
                entry["verdict"] = "MISMATCH"
                entry["details"].append(
                    f"{side}_sha atteste {sha[:12]} mais {declared} est absent de "
                    "l'arbre de fusion"
                )
                continue
            if blob != sha:
                entry["verdict"] = "MISMATCH"
                entry["details"].append(
                    f"{side}_sha atteste {sha[:12]} / arbre de fusion {blob[:12]} "
                    f"({declared})"
                )
        entries.append(entry)

    bad = [e for e in entries if e["verdict"] != "OK"]
    return {
        "verdict": "MISMATCH" if bad else "OK",
        "base": base,
        "head": head,
        "tree": tree,
        "pairs": entries,
        "reason": (
            "; ".join(
                f"{e['pair']} {e['verdict']} : {' ; '.join(e['details'])}"
                for e in bad
            )
            if bad else ""
        ),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Verifie que les attestations jumelles d'une PR decrivent "
            "l'arbre de fusion (garde pre-merge, fail-closed)."
        )
    )
    parser.add_argument("--base", default="origin/main", help="base de fusion")
    parser.add_argument("--head", required=True, help="tete de la PR (sha ou ref)")
    parser.add_argument("--repo", default=".", help="racine du depot")
    parser.add_argument("--json", action="store_true", help="sortie structuree")
    args = parser.parse_args(argv)

    repo = Path(args.repo).resolve()
    try:
        report = check(repo, args.base, args.head)
    except Unreadable as exc:
        report = {
            "verdict": "UNREADABLE",
            "base": args.base,
            "head": args.head,
            "tree": None,
            "pairs": [],
            "reason": str(exc),
        }

    verdict = report["verdict"]
    if args.json:
        print(json.dumps(report, ensure_ascii=False, sort_keys=True))
    else:
        print(f"verdict : {verdict}")
        if report.get("tree"):
            print(f"arbre de fusion : {report['tree']}")
        for entry in report["pairs"]:
            detail = (" ; ".join(entry["details"])) if entry["details"] else ""
            print(f"  {entry['pair']} [{entry['verdict']}] {detail}")
        if report.get("reason"):
            print(f"raison : {report['reason']}")

    if verdict == "UNREADABLE":
        # Fail-closed : « je n'ai pas pu lire » n'est jamais « c'est propre ».
        return 2
    if verdict != "OK":
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
