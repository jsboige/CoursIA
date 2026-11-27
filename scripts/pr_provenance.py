"""Provenance Git des tetes de PR -- ce qu'une PR change hors de `main`.

Extraction de `scripts/check_lane_claim.py` (#21436). Les trois fonctions
publiques gardent le contrat des fonctions `_pr_*` d'origine, que le lecteur
de claims continue d'appeler sous son nom (`_pr_head_commit`,
`_pr_files_changed_against_main`, `_pr_files_against_main`).

Pourquoi ce module : le tapis lourd (`pick_idle_grain.py --belt --diagnostic`)
passait la moitie de sa phase de claims -- la phase dominante, mesuree le
27/11 -- dans `_pr_files_against_main` : 50 appels, 517 s sous profil, 10,3 s
par appel et 56,5 s au pire, sur 43 tetes. Chaque appel lancait `4 + 4m`
processus `git` (m = fusions a deux parents hors `main` de la branche) : quatre
pour la tete, les chemins ordinaires et la liste des fusions, puis par fusion
un `rev-list --parents`, deux `merge-base --is-ancestor` et un `git diff`.
Sous la charge du tapis, un processus `git` coute de 0,7 a 1,3 s.

Quatre reductions, sans changer le resultat :

* un seul `git log --first-parent` rend les chemins des commits ordinaires ET
  les parents de chaque fusion (il en fallait trois) ;
* les ancetres de `main` se lisent dans UN `git rev-list <main>`, memoise pour
  le processus, des la premiere fusion : il remplace tous les
  `merge-base --is-ancestor`, dont une reponse negative (le cas courant d'un
  parent de PR) coute de 1,3 a 2,2 s au repos ;
* un seul `git diff-tree --stdin` rend le diff de chaque fusion contre son
  SEUL parent de comparaison. Le premier jet passait par
  `git log --no-walk --stdin -m`, qui calcule aussi le diff contre l'autre
  parent -- les changements de `main` : 380 Ko de noms pour 2,5 Ko utiles sur
  #26915, et 2,9 s contre 0,3 s sur cette fusion. La ligne lue est
  `<fusion> <parent de comparaison>` : dans l'autre sens, Git compare a
  l'envers et un renommage rend l'ancien nom pour le nouveau ;
* un resultat etabli est memoise par (repertoire, tete, identifiant de
  `main`) : pendant un tirage, la meme PR est examinee pour chacun des
  numeros qu'elle cite. `reset_memos()` vide ces memoires (les tests).

La plomberie Git n'active pas la detection de renommage par defaut et ignore
`diff.renames` (mesure du 27/11, git 2.51), alors que la porcelaine de
`git diff` la detecte et lit cette cle. `_renames_args` lit donc la cle et la
traduit en option, pour que le lot rende exactement les noms du `git diff`
isole qu'il remplace.

Contrat commun : `None` = provenance non etablie (objet introuvable,
`origin/main` absent, panne Git) -- l'appelant garde alors les chemins de
l'API, fail-CLOSED ; une liste vide = la PR ne change aucun chemin hors de
`main` ; une sortie de `git` illisible vaut `None`, jamais une liste
amputee.
"""

from __future__ import annotations

import os
import re
import subprocess

# Meme borne que `_GH_OPEN_PRS_TIMEOUT_S` du lecteur de claims ; le lecteur
# lui passe sa valeur, celle-ci ne sert qu'aux appels directs.
_DEFAULT_TIMEOUT_S = int(os.environ.get("CHECK_LANE_CLAIM_GH_TIMEOUT", "60"))

_MEMO_MAX = 4096

_HEAD_RE = re.compile(r"[0-9a-fA-F]{40,64}")
# En-tete d'un bloc de `git diff-tree --name-status -z --stdin` : l'oid du
# premier <tree-ish> du couple, seul sur son jeton.
_OID_RE = re.compile(rb"[0-9a-f]{40,64}")
# Statuts d'un diff a deux arbres : un seul chemin, ou l'ancien puis le nouveau.
_STATUS_ONE = frozenset({b"A", b"D", b"M", b"T"})
_STATUS_TWO = frozenset({b"R", b"C"})

# (repertoire, tete) -> oid resolu ; (repertoire, tete, main) -> chemins.
# Seuls les succes y entrent : un echec se retente a l'appel suivant.
_HEAD_MEMO: dict[tuple[str, str], str] = {}
_FILES_MEMO: dict[tuple[str, str, str], list[str]] = {}
# (repertoire, main) -> commits accessibles depuis `main` ; une seule entree.
_ANCESTORS_MEMO: dict[tuple[str, str], frozenset[str]] = {}
# (repertoire) -> options de renommage du `diff-tree` ; une seule entree.
_RENAMES_MEMO: dict[str, tuple[str, ...]] = {}

_FAIL = (OSError, UnicodeDecodeError, subprocess.SubprocessError)


def reset_memos() -> None:
    _HEAD_MEMO.clear()
    _FILES_MEMO.clear()
    _ANCESTORS_MEMO.clear()
    _RENAMES_MEMO.clear()


def _root() -> str:
    try:
        return os.getcwd()
    except OSError:
        return ""


def _git(*args: str, timeout: int, data: bytes | None = None,
         ) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", *args], capture_output=True, check=False, input=data,
        timeout=timeout,
    )


def _ok(proc: subprocess.CompletedProcess) -> bool:
    """Commande reussie, et sortie decodable (strictement) comme a l'origine."""
    if proc.returncode != 0:
        return False
    proc.stdout.decode("utf-8")
    proc.stderr.decode("utf-8")
    return True


def _oid(proc: subprocess.CompletedProcess) -> str | None:
    """Stdout decode et rtrimme d'une commande reussie, sinon `None`."""
    return proc.stdout.decode("utf-8").strip() if _ok(proc) else None


def _memo_put(memo: dict, key, value) -> None:
    if len(memo) >= _MEMO_MAX:
        memo.clear()
    memo[key] = value


def head_commit(pr: dict, timeout: int = _DEFAULT_TIMEOUT_S) -> str | None:
    """OID de tete de la PR, ou `None` si l'objet n'est pas etablissable.

    L'objet est cherche dans le depot local (repertoire courant), puis ramene
    par sa ref de pull quand il manque (#25243). `None` est un echec de
    provenance, jamais une preuve : les appelants conservent leur mesure de
    repli. Un succes est memoise ; un echec ne l'est pas.
    """
    head = pr.get("headRefOid")
    if not isinstance(head, str) or not _HEAD_RE.fullmatch(head):
        return None
    key = (_root(), head.lower())
    hit = _HEAD_MEMO.get(key)
    if hit is not None:
        return hit
    resolved = _resolve_head(head, pr.get("number"), timeout)
    if resolved is not None:
        _memo_put(_HEAD_MEMO, key, resolved)
    return resolved


def _resolve_head(head: str, number: object, timeout: int) -> str | None:
    try:
        if _ok(_git("cat-file", "-e", f"{head}^{{commit}}", timeout=timeout)):
            return head
        if not isinstance(number, int) or number <= 0:
            return None
        if not _ok(_git("fetch", "--no-tags", "origin", f"refs/pull/{number}/head",
                        timeout=timeout)):
            return None
        resolved = _oid(_git("rev-parse", "--verify", "FETCH_HEAD", timeout=timeout))
        if resolved is None or resolved.lower() != head.lower():
            return None
        return resolved
    except _FAIL:
        return None


def files_changed_against_main(pr: dict, timeout: int = _DEFAULT_TIMEOUT_S
                               ) -> list[str] | None:
    """#26725 -- chemins ou la PR change, du point de divergence a sa tete.

    `git diff --name-only origin/main...<tete>`, l'equivalent local du
    `compare/main...<tete>` de GitHub : la reference est le point de
    divergence, pas la tete de `main`, donc ce que `main` a change depuis
    ne compte pas. Mesure du 15/11 sur #25029 -- 4326 fichiers annonces par
    `/pulls/25029/files`, 707 en diff a deux points (l'avancement de `main`
    y entre), **7** ici : ses 7 carnets `Chaines-08` et rien d'autre.

    `None` = provenance non etablie (objet de tete introuvable, `origin/main`
    absent, panne Git) : l'appelant garde la liste de l'API, fail-CLOSED.
    """
    head = head_commit(pr, timeout)
    if head is None:
        return None
    try:
        diff = _git("diff", "--name-only", "-z", f"origin/main...{head}", "--",
                    timeout=timeout)
        if diff.returncode != 0:
            return None
        return [path.decode("utf-8") for path in diff.stdout.split(b"\0") if path]
    except _FAIL:
        return None


def files_against_main(pr: dict, timeout: int = _DEFAULT_TIMEOUT_S
                       ) -> list[str] | None:
    """Return paths touched by first-parent PR commits absent from main.

    The PR-files API describes the branch diff against its declared base. For a
    stacked branch that has absorbed main, this can include files changed only
    by main. The head commit is supplied by GraphQL; a missing local object is
    fetched by its pull ref. The first-parent, non-merge log lists ordinary PR
    commits absent from main; merge commits are compared with a main ancestor
    parent so their conflict resolutions and additions are retained without
    counting files simply imported from main. Git has no 100-file API ceiling.

    ``None`` means provenance could not be established. Callers then retain
    the API paths (fail-closed); an unavailable ref or Git error must never
    release an implicit occupation. An empty list means there is no path
    touched by an ordinary first-parent commit or contributed by a merge.
    """
    head = pr.get("headRefOid")
    if not isinstance(head, str) or not _HEAD_RE.fullmatch(head):
        return None
    try:
        main_oid = _oid(_git("rev-parse", "--verify", "origin/main", timeout=timeout))
    except _FAIL:
        return None
    if main_oid is None:
        return None
    key = (_root(), head.lower(), main_oid)
    hit = _FILES_MEMO.get(key)
    if hit is not None:
        return list(hit)
    paths = _walk(head, main_oid, timeout)
    if paths is None:
        # Echec de lecture : la ref de pull de la PR peut ramener l'objet dans
        # le clone -- pour les lectures suivantes seulement. La provenance
        # reste non etablie : `head_commit` n'accepte que la tete annoncee, et
        # le parcours n'est pas rejoue (contrat d'origine, fail-CLOSED).
        head_commit(pr, timeout)
        return None
    _memo_put(_FILES_MEMO, key, paths)
    return list(paths)


def _parse_log(raw: bytes) -> list[tuple[str, list[str], list[str]]] | None:
    """Depouille le log combine : (oid, parents, chemins), dans l'ordre du flux.

    Un enregistrement par commit : oid et parents encadres de deux marqueurs,
    puis un NUL, un saut de ligne, un nom par NUL. L'en-tete se termine sur
    ce NUL, qui n'est pas un espace blanc pour `bytes.split()` : le
    deroulement se fait donc sur le NUL, jamais sur la fin de ligne. Une
    sortie qui n'a pas cette forme vaut `None` (fail-CLOSED).
    """
    records: list[tuple[str, list[str], list[str]]] = []
    for record in raw.split(b"\x01"):
        if not record:
            continue
        header, sep, names_blob = record.partition(b"\x00")
        if not sep:
            return None
        oid, sep2, parents_blob = header.partition(b"\x02")
        if not sep2 or not oid:
            return None
        pieces = names_blob.split(b"\0")
        if pieces and pieces[0].startswith(b"\n"):
            pieces[0] = pieces[0][1:]
        records.append((
            oid.decode("utf-8"),
            [p.decode("utf-8") for p in parents_blob.split()],
            [n.decode("utf-8") for n in pieces if n],
        ))
    return records


def _ancestors(main_oid: str, timeout: int) -> frozenset[str] | None:
    """Commits accessibles depuis `main`, lus en une fois et memoises.

    Un parent est sur `main` ssi il figure dans `git rev-list <main>`. Cette
    lecture remplace les `merge-base --is-ancestor` un par parent : au repos,
    une reponse negative -- le cas courant, un parent de PR n'est pas sur
    `main` -- coute de 1,3 a 2,2 s, contre 1,4 a 1,8 s pour la liste entiere,
    payee une seule fois par processus (#21436).
    """
    key = (_root(), main_oid)
    found = _ANCESTORS_MEMO.get(key)
    if found is not None:
        return found
    try:
        listed = _oid(_git("rev-list", main_oid, timeout=timeout))
    except _FAIL:
        return None
    if listed is None:
        return None
    found = frozenset(listed.split())
    _ANCESTORS_MEMO.clear()
    _memo_put(_ANCESTORS_MEMO, key, found)
    return found


def _renames_args(timeout: int) -> tuple[str, ...] | None:
    """Options qui rendent a `diff-tree` les renommages de `git diff`.

    La plomberie n'en detecte aucun par defaut et ignore `diff.renames` :
    mesure du 27/11 (git 2.51), `-c diff.renames=true diff-tree` liste encore
    l'ancien et le nouveau nom, la ou la porcelaine n'en liste qu'un. La cle
    est donc lue ici et traduite en option, faute de quoi le lot ne rendrait
    pas les noms du `git diff` isole qu'il remplace. Une valeur que Git
    refuserait vaut `None` : la porcelaine echouerait de meme.
    """
    hit = _RENAMES_MEMO.get(_root())
    if hit is not None:
        return hit
    try:
        proc = _git("config", "--get", "diff.renames", timeout=timeout)
    except _FAIL:
        return None
    if proc.returncode == 1:
        args: tuple[str, ...] | None = ("-M",) if not proc.stdout.strip() else None
    elif proc.returncode == 0:
        value = proc.stdout.decode("utf-8").strip().lower()
        if value in ("copies", "copy"):
            args = ("-C",)
        elif value in ("true", "yes", "on", "1", ""):
            # "" = cle posee sans valeur, que Git lit comme « renommages ».
            args = ("-M",)
        elif value in ("false", "no", "off", "0"):
            args = ("--no-renames",)
        else:
            args = None
    else:
        return None
    if args is None:
        return None
    _RENAMES_MEMO.clear()
    _memo_put(_RENAMES_MEMO, _root(), args)
    return args


def _pair_diffs(pairs: list[tuple[str, str]], timeout: int
                ) -> dict[str, set[str]] | None:
    """Chemins changes entre chaque (fusion, parent de comparaison), en UN processus.

    Une ligne de `git diff-tree -r --name-status -z --stdin` se lit, par la
    documentation de la commande : « When a single commit is given, it compares
    the commit with its parents. The remaining commits, when given, are used as
    if they are parents of the first commit. » La ligne est donc
    `<fusion> <parent de comparaison>`. Le sens compte, mesure du 27/11 : la
    ligne inverse `<parent> <fusion>` est lue comme un commit (le parent) dont
    la fusion serait le parent suppose, et le diff sort a l'envers -- un
    renommage y rend l'ancien nom pour le nouveau, et la PR perdrait le sien.
    Le test d'une fusion qui renomme arrete ce cas.

    La sortie emet, pour chaque couple dont le diff n'est pas vide, l'oid de
    la fusion -- l'en-tete -- puis des enregistrements `statut, chemin`
    (`ancien, nouveau` pour un renommage ou une copie). Un couple sans
    difference n'emet rien : son absence du resultat vaut diff vide. `None`
    si la commande echoue, si un en-tete nomme une fusion hors du lot ou deja
    vue, ou si un enregistrement sort de cette forme.
    """
    args = _renames_args(timeout)
    if args is None:
        return None
    wanted = {merge for merge, _ in pairs}
    data = "".join(f"{merge} {parent}\n" for merge, parent in pairs).encode("ascii")
    try:
        proc = _git("diff-tree", *args, "-r", "--name-status", "-z", "--stdin",
                    timeout=timeout, data=data)
    except _FAIL:
        return None
    if proc.returncode != 0:
        return None
    blocks: dict[str, set[str]] = {}
    current: str | None = None
    tokens = proc.stdout.split(b"\0")
    total = len(tokens)

    def path_at(index: int) -> str:
        """Le jeton `index` comme chemin : absent ou vide, la sortie est refusee."""
        if index >= total or not tokens[index]:
            raise IndexError("chemin absent")
        return tokens[index].decode("utf-8")

    index = 0
    try:
        while index < total:
            token = tokens[index]
            index += 1
            if not token:
                continue
            if _OID_RE.fullmatch(token):
                merge = token.decode("ascii")
                if merge not in wanted or merge in blocks:
                    return None
                blocks[merge] = set()
                current = merge
                continue
            if current is None:
                return None
            letter, score = token[:1], token[1:]
            if letter in _STATUS_ONE:
                if score:
                    return None
                blocks[current].add(path_at(index))
                index += 1
            elif letter in _STATUS_TWO:
                if not score.isdigit():
                    return None
                path_at(index)     # l'ancien nom : present, non retenu
                # La porcelaine ne liste que le nouveau nom d'un renommage.
                blocks[current].add(path_at(index + 1))
                index += 2
            else:
                return None
    except (IndexError, UnicodeDecodeError):
        return None
    return blocks


def _walk(head: str, main_oid: str, timeout: int) -> list[str] | None:
    """Le calcul proprement dit, pour une tete dont l'objet est connu."""
    try:
        log = _git("log", "--first-parent", "--format=%x01%H%x02%P", "--name-only",
                   "-z", f"origin/main..{head}", "--", timeout=timeout)
        if log.returncode != 0:
            return None
        records = _parse_log(log.stdout)
        if records is None:
            return None
        paths: set[str] = set()
        merges: list[tuple[str, list[str]]] = []
        for oid, parents, names in records:
            if len(parents) < 2:
                paths.update(names)
            else:
                merges.append((oid, parents))
        if not merges:
            return sorted(paths)

        # Une fusion peut porter le seul changement de la PR (resolution de
        # conflit, choix `ours`, fichier cree pendant la resolution). Chacune
        # est comparee a UN parent : le premier parent deja sur `main`, ou la
        # tete de `main` quand plusieurs y sont.
        ancestors = _ancestors(main_oid, timeout)
        if ancestors is None:
            return None
        comparisons: dict[str, str] = {}
        for merge, parents in merges:
            main_parents = [p for p in parents if p in ancestors]
            # Plusieurs parents peuvent deja etre sur `main` alors que la
            # fusion choisit deliberement le contenu d'un parent ancien :
            # egaler un ancetre ne prouve pas l'heritage de l'arbre de
            # `main`. On compare alors a la tete courante de `main`, ce qui
            # retient a bon compte des chemins de `main` et n'en libere pas.
            comparisons[merge] = (
                main_oid if len(main_parents) > 1
                else (main_parents or [parents[0]])[0]
            )

        # L'en-tete d'un bloc etant l'oid de la fusion, toutes les fusions
        # tiennent dans un seul lot, fussent-elles comparees au meme parent.
        contribution = _pair_diffs(list(comparisons.items()), timeout)
        if contribution is None:
            return None
        for names in contribution.values():
            paths.update(names)
        return sorted(paths)
    except _FAIL:
        return None
