#!/usr/bin/env python3
"""Attestations de parite orphelines -- le verrou en amont du rouge de `main`.

ORIGINE -- issue #27969 (demande du coordinateur, tour c0020) ; mesures
#27954, #27924, #27860, #27773.

Une attestation de parite (`scripts/notebook_tools/twin_pairs.d/<paire>/NNNN-*.yaml`)
atteste le sha GIT d'un jumeau a un instant donne. Quand elle est prise sur un
etat de branche **intermediaire** -- c'est-a-dire avant la derniere modification
du carnet dans la branche -- elle cite un blob qui n'arrive jamais sur `main` :
le squash ecrit l'ARBRE de la branche, pas son HISTORIQUE.

Le blob cite existe dans l'historique de la branche, donc le test de branche est
vert ; apres le squash, il n'existe plus sur `main`, et
`scripts/notebook_tools/tests/test_twin_registry_integrity.py::test_audit_shas_exist_in_file_history`
le classe « fabrique » et rougit `main` -- au detriment de TOUTE la flotte.

Ce test de `main` ne voit l'orphelin qu'**apres** la fusion : c'est le verrou
en amont qui manque. Cet organe le refuse AVANT le merge.

CLASSIFICATION
    FUSION : le sha cite est le blob du jumeau dans l'arbre de FUSION
             (base x tete) -> accept. C'est le critere qui dit ce que
             l'attestation vaudra apres le merge : le squash ecrit l'arbre de
             la fusion, pas l'arbre de la tete, et ces deux arbres peuvent
             differer.
    MAIN   : le sha cite est un blob REJOIGNABLE depuis la base -> accept
             (attestation d'un etat anterieur deja sur `main`).
    ORPHAN : ni l'un ni l'autre -> **refus** (si c'est la derniere attestation
             de la paire ET qu'elle est introduite ou modifiee par la PR).

PERIMETRE
    Seules les attestations **ajoutees ou modifiees** par la revision examinee
    sont examinees (`git diff --diff-filter=AM base...head` sur le registre). Une
    attestation deja presente sur la base n'est jamais un motif de refus : un
    heritage se repare ailleurs, pas ici.

QUI PEUT ROUGIR
    `test_audit_shas_exist_in_file_history` ne lit que la **derniere**
    attestation d'une paire (« Scope = dernier audit uniquement »). Une
    attestation **intermediaire** orpheline ne rougit donc pas `main` : la
    suivante la remplace. Le refus porte donc sur la **derniere attestation de
    chaque paire touchee** (index zero-pade le plus haut entre la base et la
    revision examinee) ; les attestations intermediaires orphelines sortent en
    **avertissement**, jamais en rouge.

REUTILISATION (organ-first)
    Ni la lecture du blob a un ref, ni la recherche de joignabilite ne sont
    reimplementees : l'organe passe par `check_twin_parity._git_blob_sha` et
    `check_twin_parity._blob_ancestor_in`, deja cables par l'audit de parite et
    par `check_twin_parity --update`.

SORTIE
    0 : aucune attestation orpheline
    1 : au moins une attestation orpheline (bloquant)
    2 : incident (git illisible, YAML illisible, base introuvable) -- neutre

Usage:
    python scripts/ci/check_twin_attestation_orphans.py --base origin/main --head HEAD
    python scripts/ci/check_twin_attestation_orphans.py --base origin/main --head HEAD --gate
    python scripts/ci/check_twin_attestation_orphans.py --base origin/main --head HEAD --json
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))

try:  # pragma: no cover - l'import est surveille par le test
    from check_twin_parity import _blob_ancestor_in, _git_blob_sha
except Exception as exc:  # pragma: no cover
    print(f"INCIDENT : import de check_twin_parity impossible : {exc}", file=sys.stderr)
    raise SystemExit(2)

import yaml  # noqa: E402

REGISTRY_REL = "scripts/notebook_tools/twin_pairs.d"
SHA_KEYS = ("python_sha", "csharp_sha")


class Incident(RuntimeError):
    """Erreur d'instrument (git illisible, YAML illisible) -- jamais un verdict."""


def _git(repo: Path, *args: str) -> str:
    proc = subprocess.run(
        ["git", "-C", str(repo), *args],
        capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        raise Incident(f"git {' '.join(args)} : {proc.stderr.strip() or 'rc!=0'}")
    return proc.stdout


def _git_show(repo: Path, ref: str, rel_path: str) -> str:
    proc = subprocess.run(
        ["git", "-C", str(repo), "show", f"{ref}:{rel_path}"],
        capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        raise Incident(f"git show {ref}:{rel_path} : {proc.stderr.strip() or 'rc!=0'}")
    return proc.stdout


def repo_root(explicit: str | None) -> Path:
    if explicit:
        return Path(explicit).resolve()
    proc = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                          capture_output=True, text=True,
                          encoding="utf-8", errors="replace")
    if proc.returncode != 0 or not proc.stdout.strip():
        raise Incident("git rev-parse --show-toplevel : depot introuvable")
    return Path(proc.stdout.strip()).resolve()


def changed_attestations(repo: Path, base: str, head: str) -> list[str]:
    """Chemins des attestations AJOUTEES ou MODIFIEES par `base...head`.

    Seuls les fichiers a DEUX composants sous le registre (`<paire>/<fichier>.yaml`)
    comptent : les `<paire>.yaml` a la racine du registre sont les fichiers
    d'intention, pas des attestations.
    """
    out = _git(repo, "diff", "--name-only", "--diff-filter=AM",
               f"{base}...{head}", "--", REGISTRY_REL)
    prefix = REGISTRY_REL.rstrip("/") + "/"
    paths = []
    for line in out.splitlines():
        line = line.strip()
        if not line.startswith(prefix):
            continue
        rest = line[len(prefix):].split("/")
        if len(rest) == 2 and rest[1].endswith(".yaml"):
            paths.append(line)
    return sorted(paths)


def _ordinal(name: str) -> int:
    """Index zero-pade du nom d'attestation (cle de tri du journal, #14911)."""
    prefix = name.split("-", 1)[0]
    return int(prefix) if prefix.isdigit() else -1


def attestations_of_pair(repo: Path, ref: str, pair: str) -> list[str]:
    """Noms des attestations de la paire, tels que la revision les voit.

    Le tri est celui du journal de parite (`sorted(glob("*.yaml"))`) : l'index
    zero-pade d'abord, le nom ensuite.
    """
    out = _git(repo, "ls-tree", "-r", "--name-only", ref,
               "--", f"{REGISTRY_REL}/{pair}")
    prefix = f"{REGISTRY_REL}/{pair}/"
    names = []
    for line in out.splitlines():
        line = line.strip()
        if line.startswith(prefix) and line.endswith(".yaml"):
            names.append(line[len(prefix):])
    return sorted(names, key=lambda n: (_ordinal(n), n))


def read_attestation(repo: Path, ref: str, rel_path: str) -> dict:
    raw = _git_show(repo, ref, rel_path)
    data = yaml.safe_load(raw)
    if not isinstance(data, dict):
        raise Incident(f"{rel_path} : contenu YAML inattendu ({type(data).__name__})")
    return data


def pair_notebooks(repo: Path, ref: str, pair: str) -> dict:
    """Chemins des deux jumeaux declares par le registre de la paire.

    Le registre (`<paire>.yaml` a la racine du registre) est une LISTE ; la
    premiere entree porte les chemins. Si le registre est absent a la revision
    examinee, on le lit a la base.
    """
    rel = f"{REGISTRY_REL}/{pair}.yaml"
    for candidat in (ref,):
        try:
            raw = _git_show(repo, candidat, rel)
        except Incident:
            continue
        data = yaml.safe_load(raw)
        if isinstance(data, list) and data and isinstance(data[0], dict):
            entree = data[0]
            return {"python": entree.get("python"), "csharp": entree.get("csharp")}
        if isinstance(data, dict):
            return {"python": data.get("python"), "csharp": data.get("csharp")}
    raise Incident(f"registre de la paire introuvable : {rel}")


_MERGED_TREES: dict[tuple[str, str, str], str | None] = {}


def merged_tree(repo: Path, base: str, head: str) -> str | None:
    """Arbre de la FUSION (base x tete), ou None si la fusion est en conflit.

    `git merge-tree --write-tree` calcule le meme arbre que la fusion que
    la plateforme executera. C'est LA reference : le squash ecrit l'arbre de
    la fusion, pas l'arbre de la tete (cf. `classify_sha`).

    Un conflit renvoie None : l'organe ne se prononce pas (avertissement, pas
    de rouge) -- une PR en conflit n'est pas encore mergeable, et son
    attestation sera re-emise apres resolution.
    """
    cle = (str(repo), base, head)
    if cle in _MERGED_TREES:
        return _MERGED_TREES[cle]
    proc = subprocess.run(
        ["git", "-C", str(repo), "merge-tree", "--write-tree", base, head],
        capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    arbre = proc.stdout.strip().splitlines()[0].strip() if proc.stdout.strip() else None
    if proc.returncode != 0 or not arbre or not re.fullmatch(r"[0-9a-f]{40}", arbre):
        arbre = None
    _MERGED_TREES[cle] = arbre
    return arbre


def classify_sha(repo: Path, base: str, head: str, notebook: str, sha: str) -> str:
    """FUSION / MAIN / ORPHAN pour un sha atteste.

    **FUSION** : le blob du jumeau dans l'arbre de FUSION (base x tete) est le
    sha cite. C'est le seul critere qui dit ce que l'attestation vaudra APRES
    le merge : le squash n'ecrit pas l'arbre de la tete, il ecrit l'arbre de
    la fusion, et cet arbre peut differer de la tete (mesure : la paire
    GameTheory-04h, attestation 0011, sha cite `f7b32a1e`, blob de la fusion
    `9ceb8e28` -- l'ecart est ne de la fusion avec la base, pas d'une
    modification ulterieure du carnet).

    **MAIN** : le sha est un blob joignable depuis la base (etat anterieur
    deja sur `main`).

    **ORPHAN** : ni l'un ni l'autre -> le sha ne sera dans l'historique de
    `main` ni apres la fusion : le test de `main` le classera « fabrique ».
    """
    arbre = merged_tree(repo, base, head)
    if arbre is None:
        # Fusion en conflit : l'organe ne peut pas dire ce que le merge
        # ecrira. Il ne se prononce pas (avertissement, pas de rouge).
        return "CONFLIT"
    blob_fusion = _git_blob_sha(repo, notebook, arbre)
    if blob_fusion and blob_fusion == sha:
        return "FUSION"
    if _blob_ancestor_in(repo, sha, base):
        return "MAIN"
    return "ORPHAN"


def examine(repo: Path, base: str, head: str) -> dict:
    """Verdict par attestation examinee (fonction pure cote git).

    QUI PEUT ROUGIR, et pourquoi (precision du coordinateur, tour c0020) :

    `test_audit_shas_exist_in_file_history` ne lit que la **derniere**
    attestation d'une paire (« Scope = dernier audit uniquement »). Une
    attestation **intermediaire** orpheline ne rougit donc pas `main` : elle
    sera lue, mais remplacée par la suivante. Refuser une telle attestation
    condamnerait une PR legitime (le cas #27335 : 0034-0036 orphelines, puis
    0037 aux blobs de la tete).

    Le predicat bloquant porte donc sur la **derniere attestation de chaque
    paire touchee**, apres fusion avec la base (l'index zero-pade le plus
    haut entre `main` et la PR) :

      * si cette derniere attestation est **introduite ou modifiee par la
        PR** et qu'elle est orpheline -> **refus** ;
      * si elle est **heritee de la base** -> jamais un motif de refus (la
        dette se repare ailleurs, sinon la PR qui la repare ne passerait pas) ;
      * les attestations **intermediaires** orphelines -> **avertissement**,
        jamais un rouge.
    """
    changed = changed_attestations(repo, base, head)
    par_paire: dict[str, list[str]] = {}
    for rel_path in changed:
        par_paire.setdefault(rel_path.split("/")[-2], []).append(rel_path)

    resultats = []
    bloquantes = []
    avertissements = []
    for pair in sorted(par_paire):
        noms_base = attestations_of_pair(repo, base, pair)
        noms_head = attestations_of_pair(repo, head, pair)
        union = sorted(set(noms_base) | set(noms_head), key=lambda n: (_ordinal(n), n))
        active = union[-1] if union else None
        jumeaux = pair_notebooks(repo, head, pair)
        for rel_path in par_paire[pair]:
            nom = rel_path.split("/")[-1]
            data = read_attestation(repo, head, rel_path)
            entree = {
                "attestation": rel_path,
                "pair": pair,
                "active": nom == active,
                "sha": {},
                "etats": {},
            }
            for cle in SHA_KEYS:
                sha = data.get(cle)
                if not isinstance(sha, str) or len(sha) != 40:
                    continue
                notebook = jumeaux.get("python" if cle.startswith("python") else "csharp")
                if not notebook:
                    continue
                etat = classify_sha(repo, base, head, notebook, sha)
                entree["sha"][cle] = sha
                entree["etats"][cle] = etat
            resultats.append(entree)
            for cle, etat in sorted(entree["etats"].items()):
                if etat in ("FUSION", "MAIN"):
                    continue
                element = {"attestation": rel_path, "cle": cle, "sha": entree["sha"][cle],
                           "active": entree["active"], "etat": etat}
                if etat == "ORPHAN" and entree["active"]:
                    bloquantes.append(element)
                else:
                    avertissements.append(element)
    return {
        "base": base,
        "head": head,
        "examines": len(resultats),
        "attestations": resultats,
        "orphelines": bloquantes,
        "avertissements": avertissements,
        "gate_fail": bool(bloquantes),
    }


def render(rapport: dict) -> str:
    lignes = []
    examines = rapport["examines"]
    if examines == 0:
        lignes.append(
            "Aucune attestation ajoutee ou modifiee par la revision examinee "
            "(rien a comparer) : verdict vert.")
        return "\n".join(lignes)
    for entree in rapport["attestations"]:
        details = [f"{cle}={etat}" for cle, etat in sorted(entree["etats"].items())]
        orpheline = any(e == "ORPHAN" for e in entree["etats"].values())
        role = "derniere" if entree["active"] else "intermediaire"
        marqueur = "ORPHAN" if orpheline else "ok"
        lignes.append(f"[{marqueur}][{role}] {entree['attestation']} : " + ", ".join(details))
    lignes.append(f"Attestations examinees : {examines} ; "
                  f"orphelines bloquantes : {len(rapport['orphelines'])} ; "
                  f"avertissements : {len(rapport['avertissements'])}")
    if rapport["avertissements"]:
        lignes.append("")
        lignes.append("Avertissements (attestations intermediaires orphelines : "
                      "elles ne rougissent pas `main`, qui ne lit que la derniere "
                      "attestation de la paire) :")
        for element in rapport["avertissements"]:
            lignes.append(f"  {element['attestation']} : {element['cle']}={element['sha']} "
                          f"({element.get('etat', 'ORPHAN')})")
    if rapport["orphelines"]:
        lignes.append("")
        lignes.append("REFUS -- attestation orpheline apres squash : retirer, ou "
                      "resceller en derniere operation.")
        for element in rapport["orphelines"]:
            lignes.append(f"  {element['attestation']} : {element['cle']}={element['sha']} "
                          f"(blob absent de l'historique de la base et different du "
                          f"blob de l'arbre de fusion)")
    return "\n".join(lignes)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", default="origin/main",
                        help="revision de base (defaut: origin/main)")
    parser.add_argument("--head", default="HEAD",
                        help="revision examinee (defaut: HEAD)")
    parser.add_argument("--repo-root", default=None,
                        help="racine du depot (defaut: git rev-parse --show-toplevel)")
    parser.add_argument("--gate", action="store_true",
                        help="mode porte : inchange (le perimetre est deja le diff)")
    parser.add_argument("--json", action="store_true", help="sortie structuree")
    args = parser.parse_args(argv)

    try:
        repo = repo_root(args.repo_root)
        rapport = examine(repo, args.base, args.head)
    except Incident as exc:
        print(f"INCIDENT : {exc}", file=sys.stderr)
        return 2

    if args.json:
        print(json.dumps(rapport, ensure_ascii=False, indent=2))
    else:
        print(render(rapport))

    return 1 if rapport["gate_fail"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
