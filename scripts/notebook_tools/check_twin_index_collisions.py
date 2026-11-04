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

    # mode PORTE (utilise par la porte CI bloquante, #23208) : cette revision
    # INTRODUIT-elle une collision ? sort 1 si oui, 0 sinon. Les doublons
    # herites de la base ne bloquent pas -- la PR qui les repare doit passer.
    python scripts/notebook_tools/check_twin_index_collisions.py \
        --base "$BASE_SHA" --head "$HEAD_SHA" --gate
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
from twin_open_claims import collisions_by_ordinal  # noqa: E402

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


# --- mode PORTE (#23208) : la PR ne doit pas INTRODUIRE de collision ---------
# Le mode `--gate` est le predicat d'une PORTE CI bloquante : il ne demande
# pas « le registre est-il propre ? » (question sans base de comparaison), mais
# « cette PR aggrave-t-elle l'etat ? » -- seule question qui peut etre posee a
# une PR sans condamner la flotte.
#
# Ce qui BLOQUE :
#   * une collision inter-revisions (`cross_ref`) : deux revisions portent le
#     meme (paire, index) sous deux noms differents -> le MERGE cree deux
#     fichiers au meme index. Aucune revision ne couvrait l'union, donc ni la
#     base ni la tete ne portait la dette telle quelle : elle est introduite.
#   * un doublon intra-revision (`intra_ref`) que la BASE ne porte pas : la
#     tete ajoute un second nom pour un index deja pris -> `main` rougira au
#     merge sur le garde CI d'unicite.
#
# Ce qui ne BLOQUE PAS : un doublon HERITE de la base (`on_base`), que la PR
# ne fait qu'aggraver ou repare. Bloquer la pour ce motif condamnerait toute
# PR touchant le registre tant que la base porte la dette -- et la PR qui la
# REPARE (le renumerotage) doit passer.
def gate_verdict(cross: list, intra: list, *, base_ref: str) -> dict:
    """Verdict du mode PORTE. Pure : prend les listes deja classees.

    Rend `{"fail": bool, "reasons": [...]}`. Chaque raison porte le couple
    (paire, index), les noms en jeu et le geste de correction -- un garde qui
    dit QUOI est en cause vaut mieux qu'un garde qui dit « collision ».
    """
    reasons: list = []
    for c in cross:
        by_ref = c.get("by_ref", {})
        verdict = "ON-MAIN" if base_ref in by_ref else "MULTI-PR"
        reasons.append({
            "kind": "cross_ref",
            "pair": c["pair"],
            "index": c["index"],
            "verdict": verdict,
            "names": sorted({n for names in by_ref.values() for n in names}),
            "gist": ordinal_correction_gist(
                c["pair"], c["index"], by_ref=by_ref, base_ref=base_ref),
        })
    for c in intra:
        if base_ref in c.get("refs", []):
            # Dette de la base : la PR ne l'introduit pas. La PR qui la repare
            # doit passer, et une PR qui ne la touche pas n'est pas concernee.
            # Le sort de la dette appartient a la PR de rebaseline dediee.
            continue
        reasons.append({
            "kind": "intra_ref",
            "pair": c["pair"],
            "index": c["index"],
            "names": list(c.get("names", [])),
            "gist": (
                "renumeroter le fichier de la tete vers le premier index libre "
                "de la paire par `git mv` PUR (aucun contenu a toucher, "
                "aucune re-execution) : l'index %s est deja pris par %s"
                % (c["index"], ", ".join(c.get("names", [])))
            ),
        })
    return {"fail": bool(reasons), "reasons": reasons}


# --- verdicts OPEN-PR : l'ordinal revendique par une AUTRE PR ouverte -------
# La porte de base juge une PR contre SA base au push, et l'arbre de fusion
# ( `--merged`, cf. `merged_gate_reasons`) repond a « que portera `main` apres
# ce merge ? ». Ni l'un ni l'autre ne voit ce qui n'est pas encore merge :
# deux PRs qui prennent le meme ordinal pendant que ni l'une ni l'autre
# n'est mergee passent donc TOUTES LES DEUX, et la collision n'apparait
# qu'apres coup -- sur `main`, en rouge fleet-wide.
#
# Mesure fondatrice (#22299) : au push de #24010 (2026-11-01/02), sa base ne
# portait pas encore les ordinals `0024`-`0027` apportes par #23832 -- encore
# OUVERTE -- : la porte a rendu un VERT. Les deux PRs sont passees ; `main` a
# recu trois doublons (`0024`, `0025`, `0026`) que #24518 a dus renumeroter
# deux jours plus tard.
#
# Ce verdict porte sur ce que l'API sait et que le git ne sait pas encore : les
# ordinals REVENDIQUES par les PRs ouvertes. Il est BLOQUANT -- l'ordinal se
# renumerote avant le merge, pas apres -- et son geste est le meme `git mv`
# PUR que les autres verdicts.
def open_pr_reasons(claims_by_pr: dict, *, head_pr: int | None) -> list[dict]:
    """Verdicts OPEN-PR : un ordinal revendique par CETTE PR et par une autre.

    Pure : prend les revendications `{pr: [claims]}` et le numero de la PR
    interrogee. Sans `head_pr`, aucune raison n'est produite : une collision
    entre deux PRs qui ne sont pas celle-ci ne se decide pas ici (chacune la
    verra a son tour, a son propre push).
    """
    if head_pr is None:
        return []
    out: list[dict] = []
    for c in collisions_by_ordinal(claims_by_pr or {}):
        if int(head_pr) not in [int(p) for p in c["prs"]]:
            continue
        autres = [p for p in c["prs"] if int(p) != int(head_pr)]
        out.append({
            "kind": "open_pr",
            "pair": c["pair"],
            "index": c["index"],
            "names": list(c["names"]),
            "prs": list(c["prs"]),
            "gist": (
                "l'ordinal %s de la paire '%s' est deja revendique par la PR "
                "#%s, ENCORE OUVERTE : renumeroter VOTRE fichier vers le "
                "premier index libre de la paire par `git mv` PUR (aucun "
                "contenu a toucher, aucune re-execution). Attendre le merge "
                "ferait porter la collision par `main`."
                % (c["index"], c["pair"], ", #".join(str(p) for p in autres))
            ),
        })
    return out


def merged_gate_reasons(base_reg: dict, merged_reg: dict) -> list:
    """Raisons portees par l'ARBRE DE FUSION : ce que le MERGE rend visible.

    Fonction pure : prend les deux registres deja lus. Le registre de
    l'arbre de fusion dit ce que `main` portera **apres** le merge -- la
    seule revision qui repond a « `main` sera-t-il rouge apres ce merge ? ».
    Le registre de la base dit ce que `main` porte **avant**.

    Un doublon de l'arbre de fusion ne bloque que s'il n'existait PAS dans la
    base sous les memes noms :
      * dette de la base, inchangee par le merge -> la PR la REPAIRE, elle
        doit passer (une PR de renumerotation ne peut pas etre bloquee par
        la dette qu'elle supprime) ;
      * un nom que le merge AJOUTE a un index deja double, ou un index que
        le merge rend double -> le MERGE INTRODUIT la collision, elle bloque.

    Le predicat est donc : `len(noms fusion) >= 2` ET `noms fusion - noms
    base` non vide.
    """
    reasons: list = []
    for pair in sorted(set(merged_reg) | set(base_reg)):
        base_pair = base_reg.get(pair, {})
        merged_pair = merged_reg.get(pair, {})
        for index in sorted(merged_pair):
            names = set(merged_pair[index])
            if len(names) < 2:
                continue
            added = names - set(base_pair.get(index, ()))
            if not added:
                # Dette de la base, inchangee : le merge ne l'aggrave pas.
                continue
            reasons.append({
                "kind": "merged_ref",
                "pair": pair,
                "index": index,
                "names": sorted(names),
                "added": sorted(added),
                "gist": (
                    "l'arbre de fusion porte deux noms a l'index %s dans "
                    "'%s' (%s) : le MERGE rend `main` rouge sur le garde "
                    "d'unicite. Renumeroter le fichier que la tete ajoute "
                    "(%s) vers le premier index libre de la paire par "
                    "`git mv` PUR (aucun contenu a toucher, aucune "
                    "re-execution)."
                    % (index, pair, ", ".join(sorted(names)),
                       ", ".join(sorted(added)))
                ),
            })
    return reasons


def merge_tree_sha(base: str, head: str, repo: Path) -> str:
    """SHA de l'arbre resultat du MERGE de `base` et `head`.

    `git merge-tree --write-tree` calcule le merge sans toucher l'index ni
    l'arbre de travail. Il echoue (rc != 0) quand le merge CONFLIT : c'est
    le seul cas ou l'arbre de fusion n'est pas definissable, et l'appelant
    en fait un skip (« je n'ai pas pu lire » n'est pas « c'est propre »).

    Necessite git >= 2.38. En dessous, `merge-tree` ne connait pas
    `--write-tree` : l'appelant recoit alors une GitError et applique la
    meme politique de skip.
    """
    out = _git(repo, "merge-tree", "--write-tree", base, head).strip()
    if not out:
        raise GitError("merge-tree --write-tree : aucune sortie")
    return out.splitlines()[0].strip()


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
    ap.add_argument("--gate", action="store_true",
                    help="mode PORTE : sort 1 si cette PR INTRODUIT une "
                         "collision d'index (les collisions heritees de la "
                         "base ne bloquent pas : la PR qui les repare doit "
                         "passer). Impose --head.")
    ap.add_argument("--merged", action="store_true",
                    help="juge l'ARBRE DE FUSION (base x tete) au lieu de la "
                         "seule union base+tete : c'est la seule revision qui "
                         "dit si `main` sera rouge apres le merge. Ne bloque "
                         "que les doublons que le MERGE INTRODUIT. Impose "
                         "--head.")
    ap.add_argument("--open-claims", default=None,
                    help="fichier JSON des revendications d'ordinal des PRs "
                         "ouvertes (produit par twin_open_claims.py). Ajoute "
                         "les verdicts OPEN-PR : un ordinal revendique par une "
                         "AUTRE PR ouverte est refuse ici, avant le merge.")
    ap.add_argument("--head-pr", type=int, default=None,
                    help="numero de la PR interrogee (verdicts OPEN-PR)")
    ap.add_argument("--repo", default=None, help="racine du depot (defaut: auto)")
    ap.add_argument("--registry", default=REGISTRY_REL,
                    help="chemin du registre, relatif a la racine")
    args = ap.parse_args(argv)

    if args.gate and not args.head:
        print("ERREUR: --gate exige --head (la porte compare la base a la "
              "tete de la PR ; sans tete, il n'y a rien a confronter).")
        print("VERDICT: INDETERMINE (0 comparaison effectuee)")
        return 2
    if args.merged and not args.head:
        print("ERREUR: --merged exige --head (l'arbre de fusion se calcule "
              "entre la base et la tete ; sans tete, il n'y a rien a "
              "fusionner).")
        print("VERDICT: INDETERMINE (0 comparaison effectuee)")
        return 2

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

    # Mode PORTE : le verdict porte sur ce que CETTE revision AGGRAVE, pas sur
    # l'etat absolu du registre. C'est la seule question qui peut etre posee a
    # une PR sans condamner la flotte (#23208).
    gate = gate_verdict(cross, intra, base_ref=args.base) if args.gate else None

    # Verdicts OPEN-PR : les ordinals revendiques par les PRs OUVERTES. Ni la
    # base x tete ni l'arbre de fusion ne les voient : les deux ne portent que
    # des revisions MERGEES (cf. `open_pr_reasons`).
    open_reasons: list = []
    open_note = ""
    if args.open_claims:
        try:
            payload = json.loads(
                Path(args.open_claims).read_text(encoding="utf-8"))
        except (OSError, ValueError) as exc:
            # « je n'ai pas pu lire » n'est pas « c'est propre » : le motif est
            # AFFICHE, et les verdicts OPEN-PR ne sont pas rendus. La porte de
            # base (base x tete) et l'arbre de fusion restent, eux, appliques.
            open_note = ("revendications OPEN-PR illisibles (%s) -- non "
                         "utilisees" % exc)
        else:
            claims_by_pr: dict = {}
            for row in (payload.get("claims") or []):
                claims_by_pr.setdefault(str(row.get("pr")), []).append(row)
            open_reasons = open_pr_reasons(claims_by_pr, head_pr=args.head_pr)
            if gate is not None and open_reasons:
                deja_vus = {(r["pair"], r["index"]) for r in gate["reasons"]}
                for r in open_reasons:
                    if (r["pair"], r["index"]) in deja_vus:
                        continue
                    gate["reasons"].append(r)
                gate["fail"] = bool(gate["reasons"])

    # Arbre de FUSION : la seule revision qui repond a « `main` sera-t-il
    # rouge apres ce merge ? ». L'union base+tete ne repond pas a la
    # question : elle voit l'etat de la base AU PUSH, et une collision
    # introduite sur `main` ENTRETEMPS par une autre PR lui est invisible.
    # L'arbre de fusion, lui, porte les DEUX et revele ce que le merge
    # rend visible (mesure du 2026-11-03 : #23832 et #24010 ont alloue les
    # memes ordinals 0024-0026 et sont passees tous les deux).
    merged_ref = None
    merged_reasons: list = []
    merged_unreadable = None
    if args.merged:
        try:
            merged_ref = merge_tree_sha(args.base, args.head[0], repo)
            merged_reg = registry_of_ref(merged_ref, repo, args.registry)
            merged_reasons = merged_gate_reasons(refs.get(args.base, {}),
                                                 merged_reg)
        except GitError as exc:
            # Merge en conflit : l'arbre de fusion n'est pas definissable.
            # « je n'ai pas pu lire » n'est pas « c'est propre » -- le motif
            # est expose dans le rapport, et l'appelant decide (la porte de
            # merge applique le skip ; le gate CI se contente de le dire).
            merged_unreadable = str(exc)
    if gate is not None and merged_reasons:
        deja_vus = {(r["pair"], r["index"]) for r in gate["reasons"]}
        for r in merged_reasons:
            if (r["pair"], r["index"]) in deja_vus:
                continue  # deja signale par le jugement base+tete
            gate["reasons"].append(r)
        gate["fail"] = bool(gate["reasons"])

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
            "gate": bool(args.gate),
            "gate_fail": bool(gate and gate["fail"]),
            "gate_reasons": (gate or {}).get("reasons", []),
            "open_pr_reasons": open_reasons,
            "open_pr_note": open_note,
            "merged_checked": bool(args.merged),
            "merged_ref": merged_ref,
            "merged_unreadable": merged_unreadable,
            "merged_reasons": merged_reasons,
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
        if open_note:
            print("")
            print("REVENDICATIONS OPEN-PR : %s" % open_note)
        if open_reasons:
            print("")
            print("COLLISIONS AVEC UNE PR OUVERTE (%d)" % len(open_reasons))
            for r in open_reasons:
                print("   %s / index %s   (PR #%s)"
                      % (r["pair"], r["index"], ", #".join(
                          str(p) for p in r["prs"])))
                for name in r["names"]:
                    print("      %s" % name)
                print("      geste: %s" % r["gist"])

        if args.merged:
            print("")
            if merged_unreadable:
                print("ARBRE DE FUSION : ILLISIBLE")
                print("   %s" % merged_unreadable)
                print("   (le merge est en conflit : la revision fusionnee n'est")
                print("    pas definissable. « je n'ai pas pu lire » n'est pas")
                print("    « c'est propre » -- la porte de merge applique un skip.)")
            else:
                print("ARBRE DE FUSION : %s" % merged_ref[:12])
                if merged_reasons:
                    print("   %d collision(s) INTRODUITE(S) par le merge :"
                          % len(merged_reasons))
                    for r in merged_reasons:
                        print("   %s / index %s   (%s)"
                              % (r["pair"], r["index"], r["kind"]))
                        print("      noms en jeu : %s" % ", ".join(r["names"]))
                        print("      geste : %s" % r["gist"])
                else:
                    print("   aucune collision introduite par le merge")

    # UNE seule ligne de verdict : un « OK » qui suivrait un « DOUBLON » se
    # lirait comme un acquittement du doublon.
    rc = exit_code(cross, intra, in_tree=args.in_tree)
    if args.gate:
        # La PORTE a son propre verdict : elle ne juge que l'aggravation.
        rc = 1 if gate["fail"] else 0
        if not args.json:
            print("")
            if gate["fail"]:
                print("PORTE : REFUSEE -- cette revision INTRODUIT %d collision(s) "
                      "d'index." % len(gate["reasons"]))
                for r in gate["reasons"]:
                    print("   %s / index %s   (%s)"
                          % (r["pair"], r["index"], r["kind"]))
                    print("      noms en jeu : %s" % ", ".join(r["names"]))
                    print("      geste : %s" % r["gist"])
                print("   Un `git mv` PUR suffit (aucun contenu a toucher, aucune")
                print("   re-execution) : renumeroter le fichier de la tete vers le")
                print("   premier index libre de la paire.")
            else:
                print("PORTE : VERTE -- cette revision n'introduit aucune collision")
                print("d'index (les doublons herites de %s ne sont pas de son fait)."
                      % args.base)
    if not args.json:
        print("")
        if args.gate:
            # En mode PORTE, la seule ligne de verdict qui compte est celle de
            # la porte : un « OK » absolu suivi d'un refus de porte se lirait
            # comme un acquittement.
            if gate["fail"]:
                print("VERDICT: PORTE REFUSEE -- %d collision(s) d'index "
                      "introduite(s) par cette revision." % len(gate["reasons"]))
            else:
                print("VERDICT: PORTE VERTE -- aucune collision d'index "
                      "introduite par cette revision.")
        elif cross:
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
