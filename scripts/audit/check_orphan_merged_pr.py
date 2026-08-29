#!/usr/bin/env python3
"""check_orphan_merged_pr.py — detecte les PR dont le contenu n'a jamais atteint main.

Classe de defaut visee (#10981) : une PR est mergee avec ``base != main`` (dans
une jambe de stack). Son contenu n'atteint ``main`` QUE si la jambe y arrive
ensuite. Un squash-merge de la jambe produit un commit neuf sur ``main`` et ne
rend PAS la branche ancetre de main : tout ce qui atterrit ensuite sur la
branche est mort-ne. Sequence reelle du 2026-08-14 (orphelin #10972, site casse
en prod) :

    16:23:30  advisory sur #10972 : base=feature/c10923-quarto-normalize,
              open_prs_to_main=1 -> « stack legitime »       <-- VRAI a cet instant
    16:41:15  #10965 (cette base -> main) mergee en --squash
    16:41:39  #10972 mergee DANS cette base, 24 s plus tard  <-- orphelin cree

L'advisory (base_not_main.py) ne mesure qu'au moment ``pull_request`` ; le
verdict « stack legitime » devient faux 18 minutes plus tard sans re-declencher
l'advisory. Ce detecteur est POST-MERGE : il re-examine chaque PR MERGED dont
``baseRefName != main`` et verifie que son ``mergeCommit`` est ancetre de
``origin/main``. C'est le controle que l'advisory deleguait a l'humain
(« verifier au moment du merge ») sans que rien ne l'execute.

Trois filtres anti-faux-positifs :

1. **mergeCommit ancetre de main** -> propre : le contenu est arrive (jambe
   mergee en --merge preserve-SHA, ou contenu porte directement).
2. **Jambe en vol** : une PR OUVERTE de la base vers ``main`` existe -> le
   contenu va arriver, ce n'est pas un orphelin (verdict stable, pas de course).
3. **Existence par chemin** (#12723, refonte) : un chemin LIVRE par la PR qui
   EXISTE sur main est livre, quel que soit son contenu actuel — l'ancienne
   comparaison d'identite du lot entier labellisait a tort les contenus
   re-atterris puis evolues (FP reels #11931/#11638). Un chemin absent dont le
   basename vit ailleurs sur main est un RENOMMAGE, pas une perte. Les fichiers
   REMOVED par la PR ne sont pas exige sur main. Le label retire aussi bien
   qu'il se pose : une PR labellisee redevue propre (re-atterri, renomme, en
   vol) est de-labellisee avec note de resolution.

Un finding est donc : *PR MERGED, base != main, mergeCommit non-ancetre de
main, aucune PR ouverte de la base vers main, et le contenu manque encore a
main*. L'orphelinage est un etat STABLE une fois avere : un balayage quotidien
suffit (latence J+1 acceptable, l'issue le dit explicitement).

Adjudications (#11159) : un orphelin tranche « ne pas recuperer » (motif ecrit,
versionne dans ``orphan_adjudications.json``, cle = mergeCommit immuable) passe
en statut ``ADJUGE`` distinct — liste separement et compte, jamais efface du
rapport, label retire. Le registre ne desarme pas le detecteur : un nouvel
orphelin non adjuge ressort toujours en ``ORPHAN``.

Usage :
    py scripts/audit/check_orphan_merged_pr.py --days 14
    py scripts/audit/check_orphan_merged_pr.py --from-json prs.json --repo-path <repo>
    py scripts/audit/check_orphan_merged_pr.py --days 30 --strict
    py scripts/audit/check_orphan_merged_pr.py --days 7 --json-out out.json --apply
    py scripts/audit/check_orphan_merged_pr.py --days 7 --adjudications <chemin>

Exit codes :
    0 — advisory par defaut : n'echoue jamais, meme avec des findings
    1 — findings ET `--strict`
    2 — erreur d'execution (git absent, depot invalide, JSON illisible)
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

LABEL_NAME = "orphaned-delivery"
LABEL_COLOR = "b60205"  # dark red — "le contenu de cette PR n'a jamais atteint main"
LABEL_DESC = "PR mergee dont le mergeCommit n'est pas ancetre de main : contenu orphelin (#10981)"

MARKER_START = "<!-- ORPHANED-DELIVERY:START -->"
MARKER_END = "<!-- ORPHANED-DELIVERY:END -->"


class GitError(RuntimeError):
    """Echec d'une commande git — remonte en exit 2, jamais en finding."""


def run_git(repo: Path, *args: str, check: bool = True) -> str:
    """Execute git dans `repo` et rend stdout strippe."""
    proc = subprocess.run(
        ["git", "-C", str(repo), *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if check and proc.returncode != 0:
        raise GitError(f"git {' '.join(args)} -> {proc.returncode}: {proc.stderr.strip()}")
    return proc.stdout.strip()


def parse_ts(value: str) -> datetime:
    """Parse un horodatage ISO 8601 (gh mergedAt) en datetime aware."""
    text = value.strip()
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    parsed = datetime.fromisoformat(text)
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return parsed


def commit_exists(repo: Path, commit: str) -> bool:
    """Vrai si le commit existe localement (objet git present)."""
    proc = subprocess.run(
        ["git", "-C", str(repo), "cat-file", "-e", f"{commit}^{{commit}}"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    return proc.returncode == 0


def is_ancestor(repo: Path, commit: str, base_ref: str) -> bool:
    """Vrai si `commit` est ancetre (ou egal) de `base_ref`."""
    proc = subprocess.run(
        ["git", "-C", str(repo), "merge-base", "--is-ancestor", commit, base_ref],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if proc.returncode == 0:
        return True
    if proc.returncode == 1:
        return False
    raise GitError(f"git merge-base --is-ancestor -> {proc.returncode}: {proc.stderr.strip()}")


# Statuts REST d'un fichier de PR qui livrent du contenu sur la branche cible.
# "removed" retire du contenu : son absence de main est la livraison elle-meme,
# jamais une perte (#12723).
DELIVERED_FILE_STATUSES = ("added", "modified", "changed", "renamed", "copied",
                           "unchanged", "")


def normalize_pr_files(pr_files: list | None) -> list[dict]:
    """Normalise les fichiers d'une PR en entrees {path, status}.

    Accepte les entrees REST ({filename, status, previous_filename} -- la seule
    source du statut, champ ``filename`` et non ``path``), les entrees GraphQL
    de ``gh --json files`` ({path, additions, deletions} -- sans statut,
    assimilees a "modified") et les chaines nues des fixtures.
    """
    out: list[dict] = []
    for f in pr_files or []:
        if isinstance(f, str):
            out.append({"path": f, "status": "modified"})
        elif isinstance(f, dict):
            # REST rend `filename` (pulls/{n}/files), GraphQL rend `path` --
            # ne lire que `path` fait disparaitre TOUS les fichiers REST et
            # rendrait n'importe quelle PR "clean" (faux negatif massif,
            # attrape en live-run : #12423 rendu propre alors que MGS-26 est
            # absent de main).
            path = f.get("path") or f.get("filename")
            if path:
                out.append({"path": path,
                            "status": (f.get("status") or "modified").lower()})
    return out


def base_tree_index(repo: Path, base_ref: str) -> tuple[set[str], dict[str, list[str]]]:
    """(paths, basename->paths) de l'arbre de base, sans toucher aux blobs.

    ``git ls-tree -r --name-only`` ne lit que les objets tree : compatible
    checkout blobless du workflow (aucun fetch a la demande).
    """
    paths: set[str] = set()
    by_basename: dict[str, list[str]] = {}
    for line in run_git(repo, "ls-tree", "-r", "--name-only", base_ref).splitlines():
        p = line.strip()
        if p:
            paths.add(p)
            by_basename.setdefault(p.rsplit("/", 1)[-1], []).append(p)
    return paths, by_basename


def classify_delivered_paths(
    repo: Path, base_ref: str, pr_files: list | None,
    base_tree: tuple[set[str], dict[str, list[str]]] | None = None,
) -> dict:
    """Filtre 3 refondu (#12723) : EXISTENCE par chemin, pas identite du lot.

    L'ancien filtre comparait l'identite de TOUS les fichiers de la PR contre
    main : un contenu re-atterri puis evolue par des commits ulterieurs (le cas
    reel #11931/#11638) passait pour orphelin -- 2 faux positifs labellises en
    prod. #12723 : « comparer les chemins, pas les SHA ». Un chemin livre qui
    EXISTE sur main (quel que soit son contenu actuel) est livre ; seul un
    chemin absent de l'arbre est perdu. Un chemin absent mais dont le basename
    vit ailleurs sur main est un RENOMMAGE, pas une perte (sur-accuser desarme
    le garde apres deux faux positifs).

    Rend {"lost": [paths], "renamed": {path: [hits]}, "present": int}.
    """
    if base_tree is None:
        base_tree = base_tree_index(repo, base_ref)
    tree_paths, by_basename = base_tree
    lost: list[str] = []
    renamed: dict[str, list[str]] = {}
    present = 0
    for f in normalize_pr_files(pr_files):
        if f["status"] not in DELIVERED_FILE_STATUSES:
            continue  # removed : absence = livraison
        p = f["path"]
        if p in tree_paths:
            present += 1
        else:
            hits = by_basename.get(p.rsplit("/", 1)[-1], [])
            if hits:
                renamed[p] = hits
            else:
                lost.append(p)
    return {"lost": lost, "renamed": renamed, "present": present}


def open_prs_to_main(repo: str, base: str) -> int:
    """PRs ouvertes dont la tete est `base` et qui visent `main` (le stack)."""
    proc = subprocess.run(
        ["gh", "pr", "list", "--repo", repo, "--state", "open",
         "--search", f'head:"{base}" base:main', "--json", "number"],
        capture_output=True, text=True, encoding="utf-8",
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"gh pr list -> {proc.returncode}: {proc.stderr.strip() or proc.stdout.strip()}"
        )
    data = json.loads(proc.stdout or "[]")
    return len(data)


def gh_rest_files(repo_slug: str, number: int) -> list[dict]:
    """Fichiers REST d'une PR : [{path, status, previous_filename?}].

    Seule source du statut par fichier (added/modified/removed/renamed) —
    ``gh --json files`` (GraphQL) ne l'expose pas. Sans statut, un fichier
    removed par la PR serait exige present sur main.
    """
    return _gh_json([
        "api", f"repos/{repo_slug}/pulls/{number}/files?per_page=100",
    ]) or []


def analyse_pr(repo: Path, pr: dict, base_ref: str, repo_slug: str,
               adjudications: dict | None = None,
               base_tree: tuple[set[str], dict[str, list[str]]] | None = None,
               files_fetch=None) -> dict:
    """Analyse une PR mergee. Rend un dict de resultat avec `status` explicite.

    Statuts :
      ``orphan``      — mergeCommit non-ancetre de main, jambe morte, chemins livres absents de main (finding)
      ``adjudge``     — orphelin adjuge « ne pas recuperer » (#11159, motif ecrit dans le registre)
      ``clean``       — ancetre de main, ou chemins livres presents sur main (re-atterris, meme evolues)
      ``renamed``     — chemins absents mais renommes ailleurs sur main : pas une perte (#12723)
      ``in_flight``   — jambe encore ouverte vers main (stack legitime en vol)
      ``skipped``     — base == main, ou mergeCommit manquant / introuvable

    ``files_fetch`` (live) fournit les fichiers REST statut-par-statut ;
    absent (fixtures ``--from-json``), on lit ``pr["rest_files"]``/``pr["files"]``.
    """
    number = pr.get("number")
    base = (pr.get("baseRefName") or "").strip()
    head = (pr.get("headRefName") or "").strip()
    merged_at = pr.get("mergedAt")
    merge_commit = (pr.get("mergeCommit") or {}).get("oid") if isinstance(
        pr.get("mergeCommit"), dict) else None
    title = pr.get("title", "")

    result = {"number": number, "head": head, "base": base, "merged_at": merged_at,
              "title": title, "issue_refs": parse_issue_refs(pr.get("body", ""))}

    if not base or base == "main":
        return {**result, "status": "skipped", "reason": "base is main"}
    if not merge_commit:
        return {**result, "status": "skipped", "reason": "no mergeCommit"}
    if not commit_exists(repo, merge_commit):
        return {**result, "status": "skipped", "reason": f"mergeCommit {merge_commit[:9]} unreachable locally"}

    # Filtre 1 : ancetre de main -> le contenu est arrive.
    if is_ancestor(repo, merge_commit, base_ref):
        return {**result, "status": "clean", "reason": "mergeCommit is ancestor of base"}

    # Filtre 2 : jambe encore ouverte vers main -> le contenu va arriver.
    if repo_slug:
        inflight = open_prs_to_main(repo_slug, base)
        if inflight > 0:
            return {**result, "status": "in_flight", "open_prs_to_main": inflight,
                    "reason": f"base '{base}' still has {inflight} open PR(s) towards main"}

    # Filtre 3 (#12723) : EXISTENCE par chemin des fichiers LIVRES.
    pr_files = pr.get("rest_files") or pr.get("files")
    if files_fetch is not None and not pr.get("rest_files"):
        pr_files = files_fetch(repo_slug, number)
    cls = classify_delivered_paths(repo, base_ref, pr_files, base_tree)
    if not cls["lost"]:
        if cls["renamed"]:
            return {**result, "status": "renamed", "merge_commit": merge_commit,
                    "renamed": cls["renamed"], "paths": sorted(cls["renamed"]),
                    "reason": "absent de main mais renomme ailleurs (pas une perte)"}
        return {**result, "status": "clean", "merge_commit": merge_commit,
                "paths": [f["path"] for f in normalize_pr_files(pr_files)],
                "reason": "chemins livres presents sur main (re-atterris)"}

    # Adjudication (#11159) : la cle est le mergeCommit (immuable), jamais le
    # numero de PR ni la branche (reutilisables). Statut distinct, compte, et
    # le motif est reporte pour qu'un adjudicataire puisse se dedire.
    if adjudications and merge_commit in adjudications:
        adj = adjudications[merge_commit]
        return {**result, "status": "adjudge", "merge_commit": merge_commit,
                "paths": cls["lost"], "motif": adj["motif"],
                "adjudicated_by": adj["adjudicated_by"],
                "adjudicated_at": adj["date"]}

    return {**result, "status": "orphan", "merge_commit": merge_commit,
            "paths": cls["lost"], "renamed": cls["renamed"],
            "recovery": f"git merge origin/{head}"}


def load_prs(args: argparse.Namespace) -> list[dict]:
    """Charge les PR mergees depuis un JSON local (`--from-json`) ou via `gh`."""
    if args.from_json:
        path = Path(args.from_json)
        if not path.is_file():
            raise GitError(f"--from-json: fichier introuvable: {path}")
        data = json.loads(path.read_text(encoding="utf-8"))
        return data if isinstance(data, list) else data.get("prs", [])

    cmd = [
        "gh", "pr", "list", "--state", "merged", "--limit", str(args.limit),
        "--json", "number,title,baseRefName,headRefName,mergedAt,mergeCommit,files,body",
    ]
    if args.repo:
        cmd += ["--repo", args.repo]
    proc = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8",
                          errors="replace")
    if proc.returncode != 0:
        raise GitError(f"gh pr list -> {proc.returncode}: {proc.stderr.strip()}")
    return json.loads(proc.stdout or "[]")


def filter_by_age(prs: list[dict], days: int, now: datetime | None = None) -> list[dict]:
    """Ne garde que les PR mergees dans la fenetre demandee (0 = sans limite)."""
    if days <= 0:
        return prs
    reference = now or datetime.now(timezone.utc)
    kept = []
    for pr in prs:
        raw = pr.get("mergedAt")
        if not raw:
            continue
        if (reference - parse_ts(raw)).days <= days:
            kept.append(pr)
    return kept


def load_adjudications(path: Path | None) -> dict[str, dict]:
    """Charge le registre d'adjudications (#11159) : mergeCommit -> {motif, ...}.

    Un orphelin adjuge (« ne pas recuperer », motif ecrit) passe du statut
    ORPHAN a ADJUGE, liste separement et compte. Le registre est versionne
    dans le depot (fichier, pas label GitHub) precisement pour obliger au
    motif et passer en revue de PR. Toute entree sans motif est refusee
    (RuntimeError -> exit 2) : une adjudication de complaisance reste visible.
    """
    if path is None or not path.is_file():
        return {}
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"registre d'adjudications illisible: {exc}") from exc
    if not isinstance(raw, dict):
        raise RuntimeError("registre d'adjudications: objet attendu (mergeCommit -> entree)")
    registry: dict[str, dict] = {}
    for commit, entry in raw.items():
        if not isinstance(entry, dict):
            raise RuntimeError(f"adjudication {commit[:12]}: entree non-objet")
        motif = str(entry.get("motif", "")).strip()
        if not motif:
            raise RuntimeError(f"adjudication {commit[:12]}: motif obligatoire")
        registry[commit] = {
            "motif": motif,
            "adjudicated_by": str(entry.get("adjudicated_by", "")).strip(),
            "date": str(entry.get("date", "")).strip(),
        }
    return registry


_ISSUE_REF_RE = re.compile(
    r"(?i)\b(closes?|fixes?|resolves?|see|refs?)\s+(?:\[)?#(\d+)")
_CLOSE_VERBS = ("close", "closes", "fix", "fixes", "resolve", "resolves")


def parse_issue_refs(body: str | None) -> dict:
    """Refs d'issues du body : {"closes": [n], "see": [n]} (#12723).

    Le signal d'orphelin doit atteindre l'issue d'ORIGINE (Closes/Fixes) —
    c'est elle qu'une lane consulte pour conclure « livre ». Les refs See/Refs
    (epics) servent de repli quand la PR n'enferme aucune issue.
    """
    closes: list[int] = []
    see: list[int] = []
    for m in _ISSUE_REF_RE.finditer(body or ""):
        n = int(m.group(2))
        if m.group(1).lower() in _CLOSE_VERBS:
            if n not in closes:
                closes.append(n)
        elif n not in see:
            see.append(n)
    return {"closes": closes, "see": see}


def issue_signal_targets(refs: dict) -> list[int]:
    """Issues a notifier : les Closes/Fixes d'abord, See en repli."""
    return refs["closes"] or refs["see"]


def head_branch_alive(repo_slug: str, head: str) -> bool | None:
    """La branche source vit-elle encore au remote (reparation possible) ?

    None = indetermine (head vide) ; ni le checkout ni les blobs ne sont
    requis : ls-remote interroge le remote seul.
    """
    if not head:
        return None
    proc = subprocess.run(
        ["git", "ls-remote", "--heads",
         f"https://github.com/{repo_slug}.git", head],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )
    return bool(proc.stdout.strip())


def format_report(results: list[dict]) -> str:
    """Rapport texte : les findings d'abord, puis un recapitulatif compte."""
    orphans = [r for r in results if r["status"] == "orphan"]
    adjudges = [r for r in results if r["status"] == "adjudge"]
    inflight = [r for r in results if r["status"] == "in_flight"]
    lines: list[str] = []

    for r in orphans:
        lines.append(f"ORPHAN  PR #{r['number']}  base={r['base']}  head={r['head']}")
        lines.append(f"        merge: {r['merged_at']}  mergeCommit={r['merge_commit'][:12]}  |  {r['title'][:70]}")
        for p in r.get("paths", [])[:5]:
            lines.append(f"          ~ {p}")
        lines.append(f"        recuperation : {r.get('recovery', '')}")
        lines.append("")

    for r in adjudges:
        lines.append(f"ADJUGE  PR #{r['number']}  mergeCommit={r['merge_commit'][:12]}  |  {r['title'][:70]}")
        lines.append(f"        adjuge par: {r.get('adjudicated_by', '?')}  le {r.get('adjudicated_at', '?')}")
        lines.append(f"        motif: {r.get('motif', '')[:120]}")
        lines.append("")

    lines.append(
        "Analysees: {total} | orphelins: {o} | adjuges: {a} | en vol: {f} | renommees: {r} | propres: {c} | ignorees: {s}".format(
            total=len(results),
            o=len(orphans),
            a=len(adjudges),
            f=len(inflight),
            r=sum(1 for r in results if r["status"] == "renamed"),
            c=sum(1 for r in results if r["status"] == "clean"),
            s=sum(1 for r in results if r["status"] == "skipped"),
        )
    )
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# gh wiring for --apply (label + comment), mirrors scripts/base_not_main.py
# ---------------------------------------------------------------------------

def _gh_json(args: list[str]) -> object:
    proc = subprocess.run(["gh", *args], capture_output=True, text=True,
                          check=False, encoding="utf-8")
    if proc.returncode != 0:
        raise RuntimeError(f"gh failed ({proc.returncode}): {proc.stderr.strip() or proc.stdout.strip()}")
    if not proc.stdout.strip():
        return None
    return json.loads(proc.stdout)


def ensure_label(repo: str) -> None:
    subprocess.run(
        ["gh", "label", "create", LABEL_NAME, "--repo", repo,
         "--color", LABEL_COLOR, "--description", LABEL_DESC, "--force"],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


def existing_comment(repo: str, number: int) -> int | None:
    """Id NUMERIQUE REST du commentaire marker-guarde, ou None.

    #12723 (diag) : lister via ``gh pr view --json comments`` rend des ids
    GraphQL (IC_...) inutilisables dans l'URL REST du PATCH -> 404 silencieux.
    C'est exactement le bug qui a gelee le registre orphan-branch-scan 9 jours
    (rapports « updated » imprimes sans jamais atterrir). On liste donc en
    REST, dont les ids sont numeriques.
    """
    comments = _gh_json([
        "api", f"repos/{repo}/issues/{number}/comments?per_page=100",
    ]) or []
    for c in comments:
        if MARKER_START in (c.get("body") or ""):
            return c["id"]
    return None


def update_comment(repo: str, comment_id: int, body: str) -> bool:
    proc = subprocess.run(
        ["gh", "api", f"repos/{repo}/issues/comments/{comment_id}",
         "-X", "PATCH", "-f", f"body={body}"],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )
    if proc.returncode != 0:
        print(f"[orphan-apply] WARN comment PATCH {comment_id} -> "
              f"{proc.returncode}: {proc.stderr.strip()[:120]}")
        return False
    return True


def post_comment(repo: str, number: int, body: str) -> None:
    subprocess.run(
        ["gh", "pr", "comment", str(number), "--repo", repo, "--body", body],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


def build_comment(r: dict) -> str:
    lines = [
        MARKER_START,
        "## Contenu orphelin — chemins livres jamais arrives sur `main` (#10981, #12723)",
        "",
        f"Cette PR a ete mergee dans `{r['base']}` (base != `main`) et son "
        f"`mergeCommit` **{r['merge_commit'][:12]}** n'est pas ancetre de "
        f"`main`. Chemins livres **absents de `main`** :",
        "",
    ]
    for p in r.get("paths", [])[:5]:
        lines.append(f"- `{p}`")
    if len(r.get("paths", [])) > 5:
        lines.append(f"- ... et {len(r['paths']) - 5} autre(s)")
    if r.get("renamed"):
        lines += ["", "Chemins absents mais **renommes** sur main (pas une perte) :"]
        for p, hits in list(r["renamed"].items())[:3]:
            lines.append(f"- `{p}` -> {', '.join('`' + h + '`' for h in hits[:2])}")
    alive = r.get("head_alive")
    head = r.get("head", "")
    if alive is True:
        lines += ["", f"Branche source `{head}` : **vivante au remote** — la reparation "
                  f"peut partir de la (`{r.get('recovery', '')}` puis PR vers `main`)."]
    elif alive is False:
        lines += ["", f"Branche source `{head}` : absente du remote — le contenu doit "
                  f"etre retrouve depuis le mergeCommit {r['merge_commit'][:12]}."]
    targets = issue_signal_targets(r.get("issue_refs") or {})
    if targets:
        lines += ["", f"Signal depose sur : {', '.join('#' + str(t) for t in targets)}"]
    lines.append(MARKER_END)
    return "\n".join(lines)


def build_issue_comment(r: dict, issue: int) -> str:
    refs = r.get("issue_refs") or {}
    kind = "Closes" if issue in (refs.get("closes") or []) else "See"
    return "\n".join([
        MARKER_START,
        f"## Livrable jamais arrive sur `main` — PR #{r['number']} mergee hors `main` (#12723)",
        "",
        f"La PR #{r['number']} (`{r['title'][:80]}`) porte `{kind} #{issue}`"
        f" vers cette issue, mais elle a ete mergee dans `{r['base']}` et son "
        f"contenu n'a **jamais atteint `main`** :",
        "",
        *[f"- `{p}`" for p in r.get("paths", [])[:5]],
        "",
        f"Ne PAS conclure « livre » pour cette partie tant que ces chemins "
        f"sont absents de `main` (details et reparation sur la PR #{r['number']}).",
        MARKER_END,
    ])


def _post_issue_comment(repo: str, issue: int, body: str) -> None:
    subprocess.run(
        ["gh", "issue", "comment", str(issue), "--repo", repo, "--body", body],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


def labeled_merged_prs(repo: str) -> list[int]:
    """Numeros des PRs mergees portant encore le label (jeu borne)."""
    data = _gh_json(["pr", "list", "--repo", repo, "--state", "merged",
                     "--label", LABEL_NAME, "--json", "number",
                     "--limit", "100"]) or []
    return [p.get("number") for p in data if p.get("number")]


def unlabel_repaired(repo: str, repo_path: Path, base_ref: str,
                     orphan_numbers: set[int], dry_run: bool,
                     base_tree=None, files_fetch=None,
                     adjudications: dict | None = None) -> None:
    """#12723 : le label doit dire « contenu TOUJOURS absent », pas « absent un
    jour ». Les PRs labellisees devenues propres (re-atterrissage, renommage,
    jambe en vol) — y compris les faux positifs de l'ancien filtre identite
    (#11931, #11638) et les PRs sorties de la fenetre --days — sont
    re-verifiees par contenu puis de-labellisees, avec note de resolution."""
    for n in labeled_merged_prs(repo):
        if n in orphan_numbers:
            continue
        pr = _gh_json(["pr", "view", str(n), "--repo", repo, "--json",
                       "number,baseRefName,headRefName,mergedAt,mergeCommit,files,body"]) or {}
        if not pr:
            continue
        res = analyse_pr(repo_path, pr, base_ref, repo, adjudications,
                         base_tree=base_tree, files_fetch=files_fetch)
        # adjuge aussi : la decision « ne pas recuperer » est tranchee — garder
        # le label rouge ferait passer une adjudication pour un orphelin non
        # traite (meme regle que le passage adjuge de apply_findings).
        if res["status"] not in ("clean", "renamed", "in_flight", "adjudge"):
            continue
        if dry_run:
            print(f"[orphan-apply] #{n} label={LABEL_NAME} removed "
                  f"({res['status']}, dry-run)")
            continue
        subprocess.run(
            ["gh", "pr", "edit", str(n), "--repo", repo, "--remove-label", LABEL_NAME],
            capture_output=True, text=True, check=False, encoding="utf-8",
        )
        detail = (f"Adjudication (#11159) : {res.get('motif', '')} — "
                  f"par {res.get('adjudicated_by', '?')}."
                  if res["status"] == "adjudge" else
                  f"Re-verification par contenu : {res['reason']}.")
        body = "\n".join([
            MARKER_START,
            f"## Resolu — le contenu est desormais couvert ({res['status']}, #12723)",
            "",
            detail,
            MARKER_END,
        ])
        cid = existing_comment(repo, n)
        if cid is not None:
            update_comment(repo, cid, body)
        else:
            post_comment(repo, n, body)
        print(f"[orphan-apply] #{n} label={LABEL_NAME} removed ({res['status']})")


def apply_findings(repo: str, orphans: list[dict], adjudges: list[dict],
                   dry_run: bool, repo_path: Path | None = None,
                   base_ref: str = "origin/main",
                   base_tree=None, files_fetch=None,
                   adjudications: dict | None = None) -> None:
    """Label + commentaire marker-guarde sur les orphelins (upsert, pas de spam).

    Les PR adjugees (#11159) reçoivent l'inverse : le label ``orphaned-delivery``
    est RETIRE (la decision « ne pas recuperer » est tranchee — garder le label
    rouge ferait passer une adjudication pour un orphelin non traite). Le
    commentaire historique reste, marker-guarde, pour que l'adjudicataire puisse
    relire et se dedire.

    #12723 : chaque orphelin signale AUSSI l'issue d'origine (marker-guarde),
    et les PRs labellisees redevues propres sont de-labellisees.
    """
    if not orphans and not adjudges and not repo_path:
        return
    if not dry_run:
        ensure_label(repo)
    for r in adjudges:
        number = r["number"]
        if dry_run:
            print(f"[orphan-apply] #{number} label={LABEL_NAME} removed (adjudge, dry-run)")
            continue
        subprocess.run(
            ["gh", "pr", "edit", str(number), "--repo", repo, "--remove-label", LABEL_NAME],
            capture_output=True, text=True, check=False, encoding="utf-8",
        )
        print(f"[orphan-apply] #{number} label={LABEL_NAME} removed (adjudge)")
    for r in orphans:
        number = r["number"]
        if dry_run:
            print(f"[orphan-apply] #{number} label={LABEL_NAME} (dry-run)")
            continue
        if "head_alive" not in r:
            r["head_alive"] = head_branch_alive(repo, r.get("head", ""))
        body = build_comment(r)
        cid = existing_comment(repo, number)
        if cid is not None:
            update_comment(repo, cid, body)
            print(f"[orphan-apply] #{number} comment updated ({cid})")
        else:
            post_comment(repo, number, body)
            print(f"[orphan-apply] #{number} comment posted")
        subprocess.run(
            ["gh", "pr", "edit", str(number), "--repo", repo, "--add-label", LABEL_NAME],
            capture_output=True, text=True, check=False, encoding="utf-8",
        )
        for issue in issue_signal_targets(r.get("issue_refs") or {}):
            ibody = build_issue_comment(r, issue)
            icid = existing_comment(repo, issue)
            if icid is not None:
                update_comment(repo, icid, ibody)
            else:
                _post_issue_comment(repo, issue, ibody)
            print(f"[orphan-apply] #{number} issue signal upserted (#{issue})")
    if repo_path is not None:
        unlabel_repaired(repo, repo_path, base_ref,
                         {r["number"] for r in orphans}, dry_run,
                         base_tree=base_tree, files_fetch=files_fetch,
                         adjudications=adjudications)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo-path", default=".", help="racine du depot git (defaut: .)")
    parser.add_argument("--base-ref", default="origin/main", help="ref de base (defaut: origin/main)")
    parser.add_argument("--days", type=int, default=14,
                        help="fenetre d'anciennete des merges, en jours (0 = sans limite)")
    parser.add_argument("--adjudications", type=Path, default=None,
                        help="registre d'adjudications JSON (#11159, defaut: <repo>/scripts/audit/orphan_adjudications.json)")
    parser.add_argument("--limit", type=int, default=200, help="nombre de PR demandees a gh")
    parser.add_argument("--repo", default=None, help="slug owner/name passe a gh")
    parser.add_argument("--from-json", default=None,
                        help="lire les PR depuis un JSON local au lieu d'appeler gh")
    parser.add_argument("--json-out", default=None, help="ecrire le resultat complet en JSON")
    parser.add_argument("--strict", action="store_true",
                        help="exit 1 si au moins un orphelin (defaut: advisory, exit 0)")
    parser.add_argument("--apply", action="store_true",
                        help="label orphaned-delivery + commentaire sur les PR orphelines")
    parser.add_argument("--dry-run", action="store_true",
                        help="avec --apply : loguer sans appliquer")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    repo = Path(args.repo_path).resolve()

    try:
        if not (repo / ".git").exists() and not (repo / ".git").is_file():
            run_git(repo, "rev-parse", "--git-dir")
        repo_slug = args.repo or (subprocess.run(
            ["gh", "repo", "view", "--json", "nameWithOwner", "-q", ".nameWithOwner"],
            capture_output=True, text=True, encoding="utf-8").stdout.strip()
            or "jsboige/CoursIA")
        adjudications_path = args.adjudications or (
            repo / "scripts" / "audit" / "orphan_adjudications.json")
        adjudications = load_adjudications(adjudications_path)
        prs = filter_by_age(load_prs(args), args.days)
        # Un seul walk d'arbre pour toutes les PRs (#12723) ; fetch REST des
        # statuts de fichiers uniquement pour les PRs candidates (filtres 1-2
        # passes) — l'appel vit dans analyse_pr via files_fetch.
        base_tree = base_tree_index(repo, args.base_ref)
        files_fetch = None if args.from_json else gh_rest_files
        results = [analyse_pr(repo, pr, args.base_ref, repo_slug, adjudications,
                              base_tree=base_tree, files_fetch=files_fetch)
                   for pr in prs]
    except GitError as exc:
        print(f"ERREUR: {exc}", file=sys.stderr)
        return 2
    except json.JSONDecodeError as exc:
        print(f"ERREUR: JSON illisible: {exc}", file=sys.stderr)
        return 2
    except RuntimeError as exc:
        print(f"ERREUR: {exc}", file=sys.stderr)
        return 2

    print(format_report(results))

    if args.json_out:
        try:
            Path(args.json_out).write_text(
                json.dumps({"results": results}, indent=2, ensure_ascii=False),
                encoding="utf-8",
            )
        except OSError as exc:
            print(f"ERREUR: --json-out non ecrivable: {exc}", file=sys.stderr)
            return 2

    orphans = [r for r in results if r["status"] == "orphan"]
    adjudges = [r for r in results if r["status"] == "adjudge"]
    if args.apply:
        try:
            apply_findings(repo_slug, orphans, adjudges, args.dry_run,
                           repo_path=repo, base_ref=args.base_ref,
                           base_tree=base_tree, files_fetch=files_fetch,
                           adjudications=adjudications)
        except RuntimeError as exc:
            print(f"ERREUR: {exc}", file=sys.stderr)
            return 2

    return 1 if (orphans and args.strict) else 0


if __name__ == "__main__":
    sys.exit(main())
