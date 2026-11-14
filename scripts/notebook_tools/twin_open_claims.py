"""Revendications d'ordinal d'attestation twin portees par les PRs ouvertes.

L'index `NNNN` du nom de fichier est la CLE DE TRI du journal d'une paire, et
il doit etre UNIQUE par paire. Deux lanes qui attestent la meme paire le meme
jour allouent le meme ordinal : aucun conflit git, aucun nom identique,
`MERGEABLE` et souvent `CLEAN` -- et pourtant `main` finit par porter deux
fichiers au meme ordinal.

Pourquoi ce module existe (#22299)
-----------------------------------
La porte `check_twin_index_collisions.py --gate` juge une PR contre **sa base
au push**. Mesure fondatrice : au push de #24010 (2026-11-01/02), sa base ne
portait pas encore les ordinals `0024`-`0027` apportes par #23832 -- encore
OUVERTE a ce moment -- : la porte a rendu un VERT. Les deux PRs sont passees,
et `main` a recu trois doublons (`0024`, `0025`, `0026`) que #24518 a dus
renumeroter le 2026-11-04.

La porte ne peut pas voir ce que l'API seule sait : **les ordinals revendiques
par les PRs ouvertes**. Ce module les rend, sans fetch : l'ordinal est dans le
NOM du fichier, donc la liste des fichiers d'une PR suffit.

Ce que le module est, et ce qu'il n'est pas
--------------------------------------------
* `claims_from_files` -- pur : les fichiers d'une PR -> les ordinals qu'elle
  REVENDIQUE. Seuls les statuts `added` et `renamed` revendiquent un ordinal :
  une PR qui MODIFIE une attestation existante garde le sien et n'en prend pas
  un nouveau (sinon le registre se signalerait lui-meme).
* `collect_open_claims` -- lecture de l'API : les ordinals revendiques par
  toutes les PRs ouvertes, PR par PR.
* `collisions_by_ordinal` -- pur : les (paire, ordinal) revendiques par deux
  PRs ou plus.

La couverture de la lecture, et son defaut mesure
--------------------------------------------------
Lire les PRs ouvertes suppose de les **TOUTES** lire : une revendication
hors lecture est une revendication **invisible**, donc un VERT faux. La
premiere version lisait `gh pr list --limit 200` -- un plafond **fige**.

Mesure fondatrice (2026-11-04, `jsboige/CoursIA`) : le parc comptait **241**
PRs ouvertes, et la PR **#24340** se situait au **rang 204** -- soit **hors**
du lot (le plafond fige etait 200). Sa revendication d'ordinal
(`search-03-informed` / `0027`) n'était pas lue par la couche OPEN-PR de la
porte : le verdict OPEN-PR ne la voyait pas.

Le plafond est donc **derive du compte exact** des PRs ouvertes (API search)
**plus une marge** (`READ_MARGIN`), et une lecture **tronquee** leve
`GhError` au lieu de rendre un resultat partiel : « je n'ai pas pu tout lire »
n'est pas « c'est propre ».

La marge n'est pas un caprice : `total_count` est servi par un **index qui a
du retard** sur l'etat reel (de quelques secondes a quelques minutes). S'il
sous-compte, un plafond calcule sur ce compte tronque la liste, et l'ecart
est **invisible** : `len(rows) == total`. `gh pr list` rend les PRs **les plus
recentes** d'abord -- ce sont donc les plus anciennes qui disparaissent, ce
qui est exactement le defaut que ce module corrige. Avec la marge, le lot
revient **plein** (`len(rows) >= eff`), et un lot plein prouve la troncature
quel que soit le compte de l'index.

Ce module NE decide pas si une PR peut merger : il produit la MATIERE. La
porte (`check_twin_index_collisions.py --open-claims`) en tire le verdict, et
c'est elle qui reste l'organe unique du verdict.

La fenetre residuelle -- et pourquoi elle est INTRINSIQUE (#26464, limite 2)
-----------------------------------------------------------------------------
Lire les revendications des PRs ouvertes **restreint** la course, ne la
**ferme pas**. La fenetre qui reste : deux branches qui partent du meme `main`
au meme instant, **avant que l'une ne soit ouverte et visible par l'index de
recherche** -- chacune calcule le meme plancher et emet le meme `NNNN`. Le
module ne peut pas la refermer : il faudrait une **reservation atomique cote
serveur** (une seule branche obtient l'ordinal), hors de portee d'un fix local.
Defaut **INTRINSIQUE cote depot** (#25742), pas un oubli du module.

La remediation est au garde, pas ici : le doublon ainsi produit est attrape
APRES coup par l'integrite
`test_audit_index_unique_and_no_identical_duplicates_per_pair`
(`tests/test_twin_registry_integrity.py`), et la renumeration de la paire est
le redecollage connu (pass #24518). Ce module ne la previent pas ; il
documente la fenetre et renvoie au garde.

Contrat de restitution : stdout ne porte QUE le JSON -- la ligne de verdict
part sur stderr. Un rapport machine melange a une ligne de texte n'est plus un
JSON, et le parseur du consumer echoue sur un fichier casse.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

REGISTRY_PREFIX = "scripts/notebook_tools/twin_pairs.d/"

# Marge demandee AU-DELA du compte exact des PRs ouvertes. Elle couvre le
# retard de l'index de la recherche (`total_count` sous-compte pendant
# quelques minutes) : sans elle, un index en retard tronque la liste sans
# qu'aucun ecart ne soit visible. 50 PRs est tres au-dessus du bruit mesure
# (le parc du depot est de l'ordre de 250 PRs ouvertes).
READ_MARGIN = 50

# `scripts/notebook_tools/twin_pairs.d/<paire>/<NNNN>-<date>-<lane>.yaml`
_CLAIM_RE = re.compile(
    r"^scripts/notebook_tools/twin_pairs\.d/(?P<pair>[^/]+)/"
    r"(?P<index>\d{4})-[^/]*\.yaml$"
)

# Statuts qui REVENDIQUENT un ordinal : le fichier n'existait pas dans la base
# de la PR. `modified` n'en revendique pas (l'ordinal appartient deja a la
# paire, sur `main` ou dans une base).
NEW_STATUSES = ("added", "renamed")


class GhError(RuntimeError):
    """La lecture de l'API a echoue : ce n'est pas « aucune revendication »."""


def parse_claim(path: str) -> dict | None:
    """Chemin de fichier -> revendication {pair, index, path}, ou None.

    Un chemin hors registre (ou dont l'ordinal n'est pas numerique) ne
    revendique rien : c'est un non-fait, pas une panne.
    """
    norm = (path or "").replace("\\", "/")
    m = _CLAIM_RE.match(norm)
    if not m:
        return None
    return {
        "pair": m.group("pair"),
        "index": m.group("index"),
        "path": norm,
    }


def claims_from_files(files, *, statuses=NEW_STATUSES) -> list[dict]:
    """Fichiers d'une PR -> ordinals revendiques.

    `files` : iterable de dicts `{"path": ..., "status": ...}`. Un fichier
    sans statut connu ne revendique rien (fail-closed cote faux positif : on
    ne bloque pas sur une information absente).
    """
    out: list[dict] = []
    for row in files or []:
        status = str((row or {}).get("status") or "").lower()
        if statuses and status not in statuses:
            continue
        claim = parse_claim(str((row or {}).get("path") or ""))
        if claim:
            claim["status"] = status
            out.append(claim)
    return out


def collisions_by_ordinal(claims_by_pr: dict) -> list[dict]:
    """{pr: [claims]} -> les (paire, ordinal) revendiques par 2 PRs ou plus.

    Pur. Deux conditions, et la seconde est celle de l'organe historique :

    1. la revendication est PORTEE par deux PRs DISTINCTES -- une PR unique ne
       peut pas collisionner avec elle-meme ;
    2. les NOMS vus pour cet ordinal sont au moins deux -- deux PRs qui
       revendiquent le meme ordinal **sous le meme nom de fichier** ne
       produisent qu'un seul fichier sur `main` : git refuse le merge
       (`add/add`) et un humain tranche. C'est un conflit de merge, pas un
       doublon d'index, et la regle de l'organe l'exclut deja (le nom
       identique vu des deux cotes n'est pas une collision).
    """
    owners: dict = {}
    for pr, claims in (claims_by_pr or {}).items():
        for claim in claims or []:
            key = (claim["pair"], claim["index"])
            owners.setdefault(key, {}).setdefault(int(pr), []).append(
                os.path.basename(str(claim.get("path") or "")))
    out: list[dict] = []
    for (pair, index), by_pr in sorted(owners.items()):
        if len(by_pr) < 2:
            continue
        names = sorted({n for paths in by_pr.values() for n in paths})
        if len(names) < 2:
            # meme nom des deux cotes : conflit git `add/add`, pas un doublon.
            continue
        out.append({
            "pair": pair,
            "index": index,
            "prs": sorted(by_pr),
            "names": names,
        })
    return out


def _gh(args: list[str], *, cwd: Path | None = None) -> str:
    """Appelle `gh` et rend sa sortie. Leve `GhError` si elle echoue."""
    proc = subprocess.run(
        ["gh", *args],
        cwd=str(cwd) if cwd else None,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if proc.returncode != 0:
        raise GhError(
            "gh %s -> rc=%d : %s"
            % (" ".join(args[:3]), proc.returncode,
               (proc.stderr or proc.stdout or "").strip()[:300]))
    return proc.stdout


def repo_slug(cwd: Path | None = None) -> str:
    """`owner/repo` du depot courant."""
    out = _gh(["repo", "view", "--json", "nameWithOwner",
               "-q", ".nameWithOwner"], cwd=cwd).strip()
    if not out:
        raise GhError("gh repo view n'a rien rendu")
    return out


def open_pr_total(slug: str, *, cwd: Path | None = None) -> int:
    """Nombre EXACT de PRs ouvertes du depot.

    L'API search rend `total_count` : c'est le nombre reel, independamment de
    toute pagination. C'est la mesure qui remplace le plafond fige de 200
    (mesure : 241 PRs ouvertes au 2026-11-04, #24340 au rang 204, soit **hors**
    du lot de 200 -> invisible pour la couche OPEN-PR).

    L'index qui sert ce compte a du retard sur l'etat reel : c'est pourquoi
    `open_prs_touching_registry` ajoute `READ_MARGIN` par-dessus.
    """
    raw = _gh(["api",
               "search/issues?q=repo:%s+type:pr+state:open&per_page=1" % slug],
              cwd=cwd)
    try:
        payload = json.loads(raw)
    except (json.JSONDecodeError, ValueError) as exc:
        raise GhError("l'API search n'a pas rendu du JSON : %s" % exc) from exc
    total = (payload or {}).get("total_count")
    if not isinstance(total, int) or total < 0:
        raise GhError("l'API search n'a pas rendu de total_count : %r" % total)
    return total


def open_prs_touching_registry(slug: str, *, limit: int | None = None,
                               cwd: Path | None = None) -> list[int]:
    """Numeros des PRs ouvertes dont les fichiers touchent le registre twin.

    Le filtre se fait sur les CHEMINS (deja connus de `gh pr list`), donc une
    seule requete suffit pour ecarter la quasi-totalite du parc.

    **Le plafond de lecture n'est jamais fige** : il vaut le compte EXACT des
    PRs ouvertes (`open_pr_total`) **plus `READ_MARGIN`**, de sorte qu'aucune
    revendication ne puisse disparaitre dans un lot tronque. La marge est ce
    qui rend la troncature **visible** : `total_count` est servi par un index
    qui a du retard, donc un compte qui sous-compte tronque la liste sans
    qu'aucun ecart ne se voie (`len(rows) == total`). Un lot **plein**
    (`len(rows) >= eff`) prouve la troncature, quel que soit le compte.

    Une liste rendue plus courte que le compte est une lecture **incomplete** :
    elle leve `GhError` (fail-closed) plutot que de rendre un resultat
    partiel -- sauf si un second compte montre que l'ecart vient d'une
    fermeture survenue entre les deux appels.
    """
    total = open_pr_total(slug, cwd=cwd)
    eff = (total if limit is None else max(int(limit), total)) + READ_MARGIN
    raw = _gh(["pr", "list", "--repo", slug, "--state", "open",
               "--json", "number,files", "--limit", str(eff)], cwd=cwd)
    try:
        rows = json.loads(raw)
    except (json.JSONDecodeError, ValueError) as exc:
        raise GhError("gh pr list n'a pas rendu du JSON : %s" % exc) from exc
    read = len(rows or [])
    if read >= eff:
        # le lot est PLEIN : la liste est tronquee, quoi que dise le compte de
        # l'index. C'est le seul test qui survit a un `total_count` en retard.
        raise GhError(
            "liste des PRs ouvertes tronquee : %d lue(s) pour un plafond de %d "
            "(total_count de l'index : %d -- l'index a du retard)"
            % (read, eff, total))
    if read < total:
        # soit une PR s'est fermee entre les deux appels, soit la liste est
        # tronquee : le second compte tranche.
        total_after = open_pr_total(slug, cwd=cwd)
        if read < total_after:
            raise GhError(
                "liste des PRs ouvertes tronquee : %d lue(s) pour %d ouverte(s)"
                % (read, total_after))
    out: list[int] = []
    for row in rows or []:
        paths = [str((f or {}).get("path") or "")
                 for f in (row.get("files") or [])]
        if any(p.replace("\\", "/").startswith(REGISTRY_PREFIX)
               for p in paths):
            out.append(int(row["number"]))
    return sorted(out)


def pr_new_claims(slug: str, number: int, *, cwd: Path | None = None
                  ) -> list[dict]:
    """Ordinals revendiques par la PR `number` (fichiers ajoutes/renommes)."""
    raw = _gh(["api", "--paginate", "-H", "Accept: application/vnd.github+json",
               "repos/%s/pulls/%d/files" % (slug, number)], cwd=cwd)
    try:
        rows = json.loads(raw)
    except (json.JSONDecodeError, ValueError) as exc:
        raise GhError("gh api pulls/%d/files n'a pas rendu du JSON : %s"
                      % (number, exc)) from exc
    if isinstance(rows, dict):  # pagination : l'API rend une liste par page
        rows = rows.get("items") or []
    files = [{"path": r.get("filename"), "status": r.get("status")}
             for r in rows or []]
    return claims_from_files(files)


def collect_open_claims(slug: str, *, cwd: Path | None = None,
                         limit: int | None = None) -> dict:
    """Les ordinals revendiques par chaque PR ouverte qui touche le registre.

    Rend `{"prs": {num: [claims]}}`. Une PR dont la lecture echoue est
    **absente** du rendu, et l'appelant doit pouvoir dire « incomplet » :
    c'est pourquoi `collect_open_claims` leve `GhError` des que la liste des
    PRs candidates n'a pas pu etre lue.
    """
    numbers = open_prs_touching_registry(slug, limit=limit, cwd=cwd)
    prs: dict = {}
    for number in numbers:
        try:
            claims = pr_new_claims(slug, number, cwd=cwd)
        except GhError:
            continue  # PR illisible : elle ne peut pas etre accusee a tort
        if claims:
            prs[str(number)] = claims
    return {"prs": prs}


def claims_to_flat_list(claims_by_pr: dict) -> list[dict]:
    """Aplatit `{"prs": {num: [claims]}}` en une liste porteuse du `pr`."""
    out: list[dict] = []
    for number, claims in (claims_by_pr.get("prs") or {}).items():
        for claim in claims or []:
            out.append({"pr": int(number), **claim})
    return out


def main(argv: list | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Revendications d'ordinal d'attestation twin par les PRs "
                    "ouvertes (organe complementaire de la porte d'index).")
    ap.add_argument("--repo", default=None,
                    help="owner/repo (defaut: depot courant)")
    ap.add_argument("--pr", type=int, default=None,
                    help="numero de la PR a interroger (claims d'une PR)")
    ap.add_argument("--json", action="store_true", help="sortie machine")
    args = ap.parse_args(argv)

    slug = args.repo
    if not slug:
        try:
            slug = repo_slug()
        except GhError as exc:
            print("ERREUR: %s" % exc, file=sys.stderr)
            print("VERDICT: INDETERMINE (API illisible)", file=sys.stderr)
            return 2

    try:
        if args.pr is not None:
            claims = pr_new_claims(slug, args.pr)
            payload = {"prs": {str(args.pr): claims}}
        else:
            payload = collect_open_claims(slug)
    except GhError as exc:
        print("ERREUR: %s" % exc, file=sys.stderr)
        print("VERDICT: INDETERMINE (API illisible)", file=sys.stderr)
        return 2

    flat = claims_to_flat_list(payload)
    if args.json:
        print(json.dumps({"claims": flat}, indent=2, sort_keys=True))
    else:
        for row in flat:
            print("PR #%d revendique %s / %s (%s)"
                  % (row["pr"], row["pair"], row["index"], row["path"]))
        print("VERDICT: %d revendication(s) sur %d PR(s)"
              % (len(flat), len(payload.get("prs") or {})))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
