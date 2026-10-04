#!/usr/bin/env python3
"""Collision d'index du registre twin-pairs ENTRE revisions (`main` x PRs).

ORIGINE -- mesure c.76 du 2026-09-25 (adjoint `myia-po-2025:CoursIA-2`).

`scripts/notebook_tools/twin_pairs.d/<paire>/NNNN-<date>-<lane>.yaml` porte un
index zero-padded qui est la CLE DE TRI du journal (#14911). Le garde
`test_audit_index_unique_and_no_identical_duplicates_per_pair` en exige
l'unicite par paire. Mais ce garde ne voit QU'UN ARBRE A LA FOIS : il itere le
repertoire tel qu'il est checkout. Or le `by` de lane fait partie du NOM de
fichier -- deux lanes qui prennent le meme `NNNN` produisent deux noms
DIFFERENTS, donc:

  * aucune collision textuelle dans git (deux noms distincts, souvent deux
    fichiers disjoints) ;
  * `MERGEABLE` -- et souvent `CLEAN` -- cote plateforme ;
  * et pourtant, une fois la premiere mergee, `main` rougit sur le garde.

La troisieme PR mesuree le 2026-09-25 (`#17795`) n'avait meme AUCUNE PR ouverte
en face : elle collisionnait avec `main` seul, et elle etait `BLOCKED`, donc
invisible a tout balayage qui n'enumere que les candidates `CLEAN`. Aucune
dose de vigilance ne ferme cet angle mort : il faut un organe qui lise
PLUSIEURS revisions et compare leurs index.

CE QUE CET ORGANE MESURE
------------------------
Pour chaque (paire, index), il rassemble les NOMS DE FICHIERS vus dans chaque
revision passee en argument, et applique UNE regle:

    union = tous les noms vus pour ce (paire, index)
    si une revision contient deja toute l'union  ->  rien a signaler
    sinon, si |union| > 1                        ->  COLLISION INTER-REVISIONS

Le cas « une revision contient deja l'union » est le doublon INTRA-revision
(celui que le garde CI attrape) : il est rapporte separement, et seulement
sous `--in-tree`, parce que c'est le garde qui en fait rougir `main` -- pas ce
script.

Le nom identique vu des DEUX cotes n'est PAS une collision : c'est le meme
fichier, herite par la branche. C'est le faux positif qu'une comparaison
d'ensembles naif produit en masse, et c'est pourquoi la regle porte sur
l'union couverte par une revision, pas sur l'intersection entre revisions.

CE QU'IL NE MESURE PAS
----------------------
  * La redondance de CONTENU entre deux audits d'index differents (jugement
    humain).
  * La CONTIGUITE des index : un trou (`0012` -> `0017`) est VALIDE -- le
    garde CI ne teste pas la contiguite (`test_twin_registry_integrity.py`
    l.375). Une reparation d'index est donc un `git mv` PUR : aucun contenu a
    toucher, aucun notebook a re-executer.
  * Une PR dont la reference ne lui est PAS passee. Il ne devine rien : le
    perimetre couvert est celui qu'on lui donne, et il l'affiche.

Portee de lecture (denominateur imprime meme quand la reponse est zero :
« rien trouve » et « rien regarde » ne doivent jamais avoir la meme sortie).

Usage:
    # la tete locale (worktree) va-t-elle collisionner avec main ?
    python scripts/notebook_tools/check_twin_index_collisions.py --worktree

    # une PR precise, une fois sa ref recuperee
    git fetch origin +refs/pull/17648/head:refs/remotes/pr/17648
    python scripts/notebook_tools/check_twin_index_collisions.py \
        --head refs/remotes/pr/17648

    # plusieurs PRs entre elles, plus le doublon intra-revision
    python scripts/notebook_tools/check_twin_index_collisions.py \
        --head refs/remotes/pr/17648 --head refs/remotes/pr/17754 --in-tree
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_twin_parity import audit_index  # noqa: E402

REGISTRY_REL = "scripts/notebook_tools/twin_pairs.d"
WORKTREE_REF = "worktree"


class GitError(RuntimeError):
    pass


def _git(repo: Path, *args: str) -> str:
    proc = subprocess.run(
        ["git", "-C", str(repo), *args],
        capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        raise GitError("git %s: %s" % (" ".join(args), proc.stderr.strip() or "rc!=0"))
    return proc.stdout


def registry_of_ref(ref: str, repo: Path, registry_rel: str = REGISTRY_REL) -> dict:
    """{paire: {index: [noms]}} tel que le voit `ref`, SANS checkout.

    Seuls comptent les fichiers a DEUX composants sous le registre
    (`<paire>/<nom>.yaml`) : les `<paire>.yaml` a la racine du registre sont
    les fichiers d'intention legacy, et le garde CI les ignore (il itere les
    repertoires). Les lire ici fabriquerait un verdict que le garde ne rend
    pas.
    """
    prefix = registry_rel.rstrip("/") + "/"
    out = _git(repo, "ls-tree", "-r", "--name-only", ref, "--", registry_rel)
    reg: dict = defaultdict(lambda: defaultdict(list))
    for line in out.splitlines():
        line = line.strip()
        if not line or not line.startswith(prefix):
            continue
        rest = line[len(prefix):].split("/")
        if len(rest) != 2 or not rest[1].endswith(".yaml"):
            continue
        reg[rest[0]][audit_index(rest[1])].append(rest[1])
    return {p: {k: sorted(v) for k, v in d.items()} for p, d in reg.items()}


def registry_of_worktree(repo: Path, registry_rel: str = REGISTRY_REL) -> dict:
    """Meme forme, lue sur le DISQUE (fichiers non commites inclus)."""
    base = repo / registry_rel
    reg: dict = defaultdict(lambda: defaultdict(list))
    if not base.is_dir():
        return {}
    for pair_dir in sorted(p for p in base.iterdir() if p.is_dir()):
        for f in sorted(pair_dir.glob("*.yaml")):
            reg[pair_dir.name][audit_index(f.name)].append(f.name)
    return {p: {k: sorted(v) for k, v in d.items()} for p, d in reg.items()}


def find_conflicts(refs: dict) -> dict:
    """Applique la regle de collision a `{ref: {paire: {index: [noms]}}}`.

    Rend `{"cross_ref": [...], "intra_ref": [...]}`. Fonction pure : c'est elle
    que les tests exercent, sans git.
    """
    cross: list = []
    intra: list = []
    if not refs:
        return {"cross_ref": cross, "intra_ref": intra}
    pairs = sorted({p for reg in refs.values() for p in reg})
    for pair in pairs:
        idxs = sorted({i for reg in refs.values() for i in reg.get(pair, {})})
        for idx in idxs:
            by_ref = {r: set(refs[r].get(pair, {}).get(idx, ())) for r in refs}
            union: set = set()
            for names in by_ref.values():
                union |= names
            if len(union) < 2:
                continue
            covering = sorted(r for r, names in by_ref.items() if names >= union)
            if covering:
                intra.append({"pair": pair, "index": idx,
                              "refs": covering, "names": sorted(union)})
            else:
                cross.append({
                    "pair": pair, "index": idx,
                    "by_ref": {r: sorted(n)
                               for r, n in sorted(by_ref.items()) if n}})
    return {"cross_ref": cross, "intra_ref": intra}


def exit_code(cross: list, intra: list, *, in_tree: bool) -> int:
    """Contrat de sortie, isole de l'affichage pour etre testable sans git.

    Une collision inter-revisions bloque TOUJOURS : c'est le merge qui la
    creerait, et aucun autre organe ne la voit. Un doublon intra-revision n'est
    bloquant que sur demande explicite (`--in-tree`) : il est deja le predicat
    du garde CI, et le compter deux fois ferait rougir deux organes pour un
    defaut.
    """
    if cross:
        return 1
    if intra and in_tree:
        return 1
    return 0


# --- #18683 : classification semantique des collisions inter-revisions -------
# Le verdict de l'organe est binaire (`cross_ref` = collisions inter-revisions,
# peu importe combien de PRs sont impliquees). L'issue #18683 demande une
# **classification semantique** directement utilisable par un humain au merge
# gate :
#
#   ON-MAIN   la base porte deja l'index et une tete le RE-porte -> main
#                 passera au rouge des le premier merge. C'est un refus : le
#                 merge rendrait le garde CI definitif
#                 `test_audit_index_unique_and_no_identical_duplicates_per_pair`
#                 DRIFT-INTRO sur une autre PR qui n'a rien demande.
#                 Renumeroter la tete AVANT merge.
#   MULTI-PR  la base NE porte PAS l'index, mais deux ou plusieurs tetes
#                 differentes le portent. La premiere mergee gagne, la
#                 seconde renumerote. Avertissement, pas refus : c'est de
#                 la concurrence de lanes, pas une dette heritee.
#
# La classification regarde quelles refs apparaissent dans `by_ref` :
# si args.base est dans by_ref, c'est ON-MAIN ; sinon c'est MULTI-PR.
# Ce contrat est isole du subprocess git -- la fonction prend la liste
# `cross_ref` deja classee et la base_ref, et rend la meme liste avec un
# champ `verdict` supplementaire. Pure, testable, independante de git.
def classify_ordinal_collisions(cross_ref, *, base_ref):
    """Re-classe chaque `cross_ref` en `ON-MAIN` (refus) ou `MULTI-PR`
    (avertissement), selon que `base_ref` apparait dans `by_ref`.

    Predicat distinct du `--in-tree` intra-revision : la `intra_ref`
    (doublon dans la meme revision) releve du garde CI, pas de ce script
    (cf. docstring lignes 35-38).
    """
    out = []
    for c in cross_ref:
        verdict = "ON-MAIN" if base_ref in c.get("by_ref", {}) else "MULTI-PR"
        out.append({**c, "verdict": verdict})
    return out


def ordinal_correction_gist(pair, index, *, by_ref, base_ref):
    """Geste de correction nomme dans l'issue #18683, isole pour les tests.

    ON-MAIN : la tete doit renumeroter SON fichier vers le premier index
              libre (max(main)+1), par `git mv` PUR (aucune re-execution,
              aucun contenu a toucher -- la contiguite n'est pas testee,
              cf check_twin_index_collisions.py docstring l. 49-51).
    MULTI-PR : la derniere tete mergee doit renumeroter ; la premiere
              mergee passe.
    """
    if base_ref in by_ref:
        return (f"renumeroter la tete vers le premier index libre de '{pair}' "
                f"(max sur base + 1) par `git mv` PUR : "
                f"`git mv scripts/notebook_tools/twin_pairs.d/{pair}/"
                f"{index}-*.yaml scripts/notebook_tools/twin_pairs.d/{pair}/"
                f"<next>-2026-10-01-myia-ai-01-CoursIA-2.yaml` "
                "puis committer.")
    return (f"la premiere tete mergee de '{pair}' index {index} gagne ; "
            f"la seconde renumerote apres merge. Le geste est le meme qu'ON-MAIN "
            f"(git mv PUR) une fois l'ordre de merge connu.")


def main(argv: list | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Collisions d'index twin-pairs entre revisions (main x PRs).")
    ap.add_argument("--base", default="origin/main",
                    help="revision de reference (defaut: origin/main)")
    ap.add_argument("--head", action="append", default=[],
                    help="revision a confronter (repetable). Ex: refs/remotes/pr/17648")
    ap.add_argument("--worktree", action="store_true",
                    help="ajoute l'arbre de travail (fichiers non commites inclus)")
    ap.add_argument("--in-tree", action="store_true",
                    help="signale AUSSI le doublon intra-revision, et en fait "
                         "un verdict bloquant (predicat du garde CI)")
    ap.add_argument("--json", action="store_true", help="verdict machine")
    ap.add_argument("--repo", default=None, help="racine du depot (defaut: auto)")
    ap.add_argument("--registry", default=REGISTRY_REL,
                    help="chemin du registre, relatif a la racine")
    args = ap.parse_args(argv)

    repo = Path(args.repo).resolve() if args.repo else Path(
        _git(Path.cwd(), "rev-parse", "--show-toplevel").strip())

    refs: dict = {}
    unreadable: dict = {}
    wanted = [args.base, *args.head]
    for ref in wanted:
        try:
            refs[ref] = registry_of_ref(ref, repo, args.registry)
        except GitError as exc:
            unreadable[ref] = str(exc)
    if args.worktree:
        refs[WORKTREE_REF] = registry_of_worktree(repo, args.registry)

    if len(refs) < 2:
        # Jamais un OK silencieux : sans deux revisions DISTINCTES et lisibles,
        # il n'y a rien a comparer, et « je n'ai pas pu lire » n'est pas « c'est
        # propre ». Le cas « une seule revision, demandee deux fois » merite son
        # propre mot -- sinon le lecteur cherche une panne git inexistante.
        if len(refs) == 1 and not unreadable:
            print("ERREUR: une seule revision DISTINCTE (%s) -- fournir --head."
                  % next(iter(refs)))
        else:
            print("ERREUR: moins de deux revisions lisibles -- rien a comparer.")
        for ref, err in sorted(unreadable.items()):
            print("   ILLISIBLE %s : %s" % (ref, err))
        print("VERDICT: INDETERMINE (0 comparaison effectuee)")
        return 2

    result = find_conflicts(refs)
    cross, intra = result["cross_ref"], result["intra_ref"]
    # `on_base` : le doublon est-il de la dette de la base, ou la base va-t-elle
    # l'heriter au merge ? La distinction n'est pas cosmetique -- c'est elle qui
    # dit si le geste attendu est « reparer un herite » ou « ne pas merger ».
    for c in intra:
        c["on_base"] = args.base in c["refs"]

    unreadable_note = (", ".join("%s illisible" % r for r in sorted(unreadable))
                       or "aucune")
    if args.json:
        # Classification semantique (#18683) : pour chaque cross_ref, un verdict
        # ON-MAIN (refus) ou MULTI-PR (avertissement) selon que args.base est
        # dans by_ref. Pure, sans git -- la fonction vit dans ce module pour
        # etre au plus pres de l'organe que merge_ready 5bis appelle deja.
        cross_classified = classify_ordinal_collisions(cross, base_ref=args.base)
        print(json.dumps({
            "refs": sorted(refs),
            "unreadable": unreadable,
            "n_pairs": len({p for reg in refs.values() for p in reg}),
            "n_files": sum(len(v) for reg in refs.values()
                           for d in reg.values() for v in d.values()),
            "cross_ref": cross_classified,
            "intra_ref": intra,
            "base_ref": args.base,
            "in_tree_checked": bool(args.in_tree),
        }, indent=2, sort_keys=True))
    else:
        print("revisions comparees : %d   (%s ; %s)"
              % (len(refs), ", ".join(sorted(refs)), unreadable_note))
        # Le compte de fichiers est une SOMME SUR LES REVISIONS (un fichier
        # herite est compte une fois par revision qui le porte) : c'est un
        # volume de lecture, pas une taille de registre.
        print("paires lues : %d   fichiers lus : %d (somme sur les revisions)"
              % (len({p for reg in refs.values() for p in reg}),
                 sum(len(v) for reg in refs.values()
                     for d in reg.values() for v in d.values())))

    if not args.json:
        if cross:
            print("")
            print("COLLISIONS INTER-REVISIONS (%d)" % len(cross))
            # Classification semantique (#18683) au plus pres de l'organe
            for c in cross:
                verdict = "ON-MAIN" if args.base in c.get("by_ref", {}) else "MULTI-PR"
                print("   %s / index %s   [%s]" % (c["pair"], c["index"], verdict))
                for ref, names in c["by_ref"].items():
                    print("      %-28s %s" % (ref, ", ".join(names)))
                print("      geste: %s" % ordinal_correction_gist(
                    c["pair"], c["index"], by_ref=c["by_ref"], base_ref=args.base))
            print("")
            print("Le merge produira deux fichiers au meme index dans cette paire.")
            print("Le POSTERIEUR cede l'index : renommer SON fichier vers le premier")
            print("index libre, par `git mv` PUR (aucun contenu a toucher, aucune")
            print("re-execution : la contiguite n'est pas testee).")
        if intra:
            print("")
            print("DOUBLONS INTRA-REVISION (%d)%s" % (
                len(intra), "" if args.in_tree else " -- signales, non bloquants"))
            for c in intra:
                # Ce qui compte pour le merge n'est pas « ou le doublon vit »
                # mais « la base va-t-elle l'HERITER ». Un doublon porte par la
                # base est de la dette preexistante ; porte par une tete, il
                # entre sur `main` au merge.
                origin = ("DEJA sur %s" % args.base if args.base in c["refs"]
                          else "INTRODUIT par %s -- %s l'aura apres merge"
                               % (", ".join(c["refs"]), args.base))
                print("   %s / index %s   (deux noms dans %s) -- %s"
                      % (c["pair"], c["index"], ", ".join(c["refs"]), origin))
            if not args.in_tree:
                print("   C'est le predicat du garde CI sur CETTE revision (pas un")
                print("   effet du merge) : relancer avec --in-tree pour en faire un")
                print("   verdict bloquant, ou laisser le garde CI le porter.")

    # UNE seule ligne de verdict : un « OK » qui suivrait un « DOUBLON » se
    # lirait comme un acquittement du doublon.
    rc = exit_code(cross, intra, in_tree=args.in_tree)
    if not args.json:
        print("")
        if cross:
            n_on_main = sum(1 for c in cross if args.base in c.get("by_ref", {}))
            n_multi = len(cross) - n_on_main
            verdict_suffix = ""
            if n_on_main and n_multi:
                verdict_suffix = " (ON-MAIN=%d refus, MULTI-PR=%d avertissement)" % (
                    n_on_main, n_multi)
            elif n_on_main:
                verdict_suffix = " (ON-MAIN=%d refus)" % n_on_main
            elif n_multi:
                verdict_suffix = " (MULTI-PR=%d avertissement)" % n_multi
            print("VERDICT: COLLISION (%d inter-revisions)%s" % (len(cross), verdict_suffix))
        elif intra and args.in_tree:
            print("VERDICT: COLLISION (%d intra-revision)" % len(intra))
        elif intra:
            print("VERDICT: OK inter-revisions -- %d doublon(s) intra-revision "
                  "signale(s) ci-dessus, non bloquant(s) sans --in-tree."
                  % len(intra))
        else:
            print("VERDICT: OK -- aucune paire de revisions ne partage un index "
                  "non couvert.")
    return rc


if __name__ == "__main__":
    sys.exit(main())
