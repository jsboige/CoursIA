#!/usr/bin/env python3
"""Garde de PROVENANCE des carnets neufs (#23174) — check-run advisory.

« Un check-run sur toute PR qui **ajoute** un `.ipynb` verifie que l'issue
servie a attendu son tour : elle doit avoir ete servie par un tirage du
tapis (journal de tirage, `draw_id`), ou creee au moins 48 h avant la PR. »

Ce que la garde mesure, et rien d'autre :

  * la PR ajoute-t-elle un **carnet neuf** ? (statut `added`, pas `renamed`)
  * l'issue **servie** existe-t-elle, et depuis quand ?
  * a-t-elle ete servie par un **tirage** du tapis (`draw_id`) ?
  * a-t-elle **attendu son tour** (>= 48 h avant l'ouverture de la PR) ?

Exemptions (posees par l'issue) :

  * PRs **etudiantes et externes** (auteur hors flotte) ;
  * **demenagements** (`RENAMED`) : un carnet deplace n'est pas un carnet
    neuf ;
  * **jumeaux `_en`** : la version anglaise d'un carnet deja cree n'est pas
    un carnet neuf.

Verdict : **ADVISORY**. Le job sort TOUJOURS en 0 et porte son verdict par
des annotations `::warning::` et par le resume de job — un garde qui
rouge sur une PR ne doit jamais bloquer une livraison (doctrine des
advisories du depot). `--strict` (usage local) rend 1 sur un constat, pour
que la mesure soit utilisable hors CI.

Le journal de tirage est un fichier **local a la machine** : en CI il est
rarement present. Le critere du tirage est alors **NON EVALUABLE**, et le
verdict repose sur le critere de l'age — le script le DIT, il ne pretend
pas avoir mesure ce qu'il n'a pas mesure.

Usage :

    python scripts/ci/check_creation_provenance.py --pr 23180
    python scripts/ci/check_creation_provenance.py --pr 23180 --strict
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import pathlib
import re
import subprocess
import sys

REPO = "jsboige/CoursIA"
COORDINATION_DIR = pathlib.Path(__file__).resolve().parent.parent / "coordination"
if str(COORDINATION_DIR) not in sys.path:
    sys.path.insert(0, str(COORDINATION_DIR))

# Les formes de reference d'une issue servie, dans le body d'une PR.
_SERVED_RE = re.compile(
    r"(?i)\b(?:closes|see|part of|fixes|refs)\s+#(\d+)")

# 48 h : le delai d'attente impose par l'issue.
AGE_MIN_H = 48.0

# Les logins de la flotte : les PRs des autres auteurs sont hors perimetre.
FLEET_PREFIXES = ("jsboige", "myia-")


class InstrumentError(RuntimeError):
    """Panne d'INSTRUMENT : le defaut vient de `gh` ou du reseau, pas du code.

    C'est la seule classe que la garde a le droit d'absorber en UNKNOWN
    (#14849). Un defaut de code, lui, doit remonter.
    """


class GhError(RuntimeError):
    """`gh` a echoue SANS signature de transport : argument invalide, PR
    inexistante, depot non autorise. C'est un **verdict sur l'entree**, pas
    une panne de transport -- le motif ne doit donc pas annoncer un
    « instrument injoignable »."""


# Les signatures d'une panne de TRANSPORT, dans le stderr de `gh`.
#
# `could not resolve HOST` (DNS) -- et surtout PAS `Could not resolve to a
# PullRequest`, qui est le message d'un 404 GraphQL : un verdict sur l'entree.
# Le motif a ete mesure trop large a la premiere ecriture, et le test
# `test_gh_discrimine_le_transport_du_verdict_d_entree` l'a attrape.
_TRANSPORT_RE = re.compile(
    r"rate limit|timeout|timed out|could not resolve host|"
    r"connection (?:refused|reset|aborted)|temporary failure|"
    r"bad gateway|service unavailable|\b50[234]\b",
    re.IGNORECASE)


def _gh(args: list[str], timeout: int = 120) -> str:
    out = subprocess.run(["gh", *args], capture_output=True, text=True,
                         encoding="utf-8", timeout=timeout, check=False)
    if out.returncode != 0:
        err = (out.stderr or "").strip()
        message = f"gh {' '.join(args[:3])} a echoue : {err[:300]}"
        classe = InstrumentError if _TRANSPORT_RE.search(err) else GhError
        raise classe(message)
    return out.stdout


def _gh_json(args: list[str], timeout: int = 120):
    """Le JSON rendu par `gh`.

    Un stdout illisible est un defaut de l'**instrument**, pas du code : une
    reponse tronquee ou polluee par un message d'erreur pendant une famine
    leve `JSONDecodeError`, qui est une `ValueError` et echapperait donc au
    `try` de `main()` -- produisant exactement le rouge de transport que
    cette garde existe pour supprimer. Le discriminant n'est pas la classe
    d'exception, c'est la **provenance** du defaut (revue du 2026-10-29,
    PR #23283).
    """
    raw = _gh(args, timeout)
    try:
        return json.loads(raw)
    except json.JSONDecodeError as exc:
        raise InstrumentError(
            f"gh {' '.join(args[:3])} a rendu un JSON illisible : "
            f"{exc}") from exc


def pr_files(pr: int) -> list[dict]:
    """Les fichiers de la PR avec leur STATUT GitHub (`added`, `renamed`...)."""
    return _gh_json(["api", f"repos/{REPO}/pulls/{pr}/files", "--paginate"])


def pr_meta(pr: int) -> dict:
    return _gh_json(["pr", "view", str(pr), "--repo", REPO, "--json",
                     "number,title,author,createdAt,body,headRepositoryOwner"])


def issue_created(number: int) -> str | None:
    """La date de creation de l'issue, ou `None` si elle n'existe pas.

    `None` veut dire « gh a rendu un verdict : cette issue est introuvable ».
    Une panne d'INSTRUMENT, elle, **remonte** : la confondre avec un 404
    transformait une famine d'API en constat ferme -- « d'age non mesure » --
    et la PR conforme etait accusee d'avoir court-circuite la file, par une
    requete posterieure au correctif cense le supprimer (revue du
    2026-10-29, PR #23283).
    """
    try:
        data = _gh_json(["issue", "view", str(number), "--repo", REPO,
                         "--json", "createdAt"])
    except GhError:
        return None
    return data.get("createdAt")


def is_fleet(pr: dict) -> bool:
    """La PR est-elle dans le perimetre de la flotte ?

    Le discriminant est l'**auteur** : les PRs etudiantes et externes
    (un compte qui n'est pas de la flotte) sont hors perimetre. Le depot
    d'origine n'entre pas dans le critere : une PR de flotte ouverte depuis
    un fork d'organisation reste de la flotte.
    """
    login = ((pr.get("author") or {}).get("login") or "")
    return login.startswith(FLEET_PREFIXES)


def new_notebooks(files: list[dict]) -> tuple[list[str], list[str]]:
    """Les `.ipynb` VRAIMENT neufs, et les demenagements exclus.

    Trois exemptions, toutes posees par l'issue :

      * un **demenagement** : GitHub rapporte un deplacement comme
        `added` + `removed` quand la similarite est sous son seuil ; le
        carnet n'est pas neuf, il a change de place. On le reconnait a
        l'egalite du NOM de fichier entre un `added` et un `removed` de la
        meme PR ;
      * un **jumeau `_en`** : la version anglaise d'un carnet deja cree ;
      * un `renamed` pur : jamais ajoute.

    Le rendu est `(carnets_neufs, demenagements)`.
    """
    supprimes = {f.get("filename", "").rsplit("/", 1)[-1]
                 for f in files if f.get("status") == "removed"}
    neufs: list[str] = []
    demenages: list[str] = []
    for f in files:
        path = f.get("filename") or ""
        if not path.endswith(".ipynb"):
            continue
        if f.get("status") != "added":
            continue
        nom = path.rsplit("/", 1)[-1]
        if nom.endswith("_en.ipynb"):
            continue
        if nom in supprimes:
            demenages.append(path)
            continue
        neufs.append(path)
    return neufs, demenages


def draws_for(issue: int, journal_path: str | None) -> dict:
    """Les tirages du tapis qui ont vu cette issue.

    Le journal est inter-processus et **local a la machine** : son absence
    n'est pas une absence de tirages, c'est une absence de MESURE. Le
    resultat le dit.
    """
    try:
        import tirage_journal
    except Exception:  # noqa: BLE001 - module absent = critere non evaluable
        return {"disponible": False, "retenue": None, "vues": 0,
                "raison": "module de journal indisponible"}
    path = pathlib.Path(journal_path) if journal_path else None
    try:
        records = tirage_journal.read_journal(path)
    except Exception as exc:  # noqa: BLE001 - journal illisible = non evaluable
        return {"disponible": False, "retenue": None, "vues": 0,
                "raison": f"journal illisible : {type(exc).__name__}"}
    if not records:
        return {"disponible": False, "retenue": None, "vues": 0,
                "raison": "journal vide ou absent"}
    retenue = None
    vues = 0
    for r in records:
        if r.retained == issue:
            retenue = {"draw_id": r.draw_id, "lane": r.lane, "ts": r.ts,
                       "mode": r.mode}
        if issue in (r.candidates or []):
            vues += 1
    return {"disponible": True, "retenue": retenue, "vues": vues,
            "raison": ""}


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Garde de provenance des carnets neufs")
    ap.add_argument("--pr", type=int, required=True)
    ap.add_argument("--journal", default=os.environ.get("TIRAGE_JOURNAL_PATH"),
                    help="chemin du journal de tirage (defaut : "
                         "$TIRAGE_JOURNAL_PATH, sinon le chemin local)")
    ap.add_argument("--strict", action="store_true",
                    help="sortir 1 sur un constat (usage local ; le job CI "
                         "sort toujours 0)")
    ap.add_argument("--json", default=None)
    args = ap.parse_args(argv)

    rapport: dict = {"pr": args.pr, "constats": [], "exemptions": []}

    def note(texte: str) -> None:
        print(f"::warning::creation-provenance: {texte}")

    def non_evalue(detail: str, genre: str) -> int:
        """Sortie UNKNOWN : le job est advisory et sort TOUJOURS 0.

        Un organe injoignable rend UNKNOWN, jamais un rouge (#14849) --
        sans quoi une famine d'API accuse la PR d'un defaut qu'elle n'a
        pas. Le `--strict` ne convertit pas davantage une panne en
        constat : il sanctionne un verdict, et il n'y a pas de verdict ici.
        """
        rapport["statut"] = "UNKNOWN"
        rapport["instrument"] = detail
        motif = f"{genre} : provenance NON EVALUEE -- {detail}"
        rapport["exemptions"].append(motif)
        note(motif)
        _emit(rapport, args)
        return 0

    try:
        meta = pr_meta(args.pr)
        files = pr_files(args.pr)
    except InstrumentError as exc:
        return non_evalue(str(exc).strip()[:240],
                          "instrument injoignable (gh/API)")
    except GhError as exc:
        # `gh` a rendu un verdict sur l'entree (PR inexistante, argument
        # refuse). Rien n'a ete mesure, mais l'instrument n'est pas
        # injoignable : le motif le dit tel quel.
        return non_evalue(str(exc).strip()[:240],
                          "gh a echoue sans signature de transport "
                          "(verdict d'entree ou invocation)")
    except (OSError, subprocess.TimeoutExpired) as exc:
        return non_evalue(str(exc).strip()[:240],
                          "instrument injoignable (gh/API)")
    except RuntimeError as exc:
        # Panne non classee : on reste conservateur (UNKNOWN, pas de rouge),
        # mais on n'affirme pas qu'elle est de transport.
        return non_evalue(str(exc).strip()[:240],
                          "panne d'instrument non classee")

    rapport["pr_meta"] = {"titre": meta.get("title"),
                          "auteur": (meta.get("author") or {}).get("login"),
                          "creee": meta.get("createdAt")}

    # 1. PR etrangere a la flotte -> hors perimetre.
    if not is_fleet(meta):
        motif = ("PR etudiante ou externe (auteur "
                 f"{(meta.get('author') or {}).get('login')}) : hors perimetre")
        rapport["statut"] = "EXEMPTE"
        rapport["exemptions"].append(motif)
        note(motif)
        _emit(rapport, args)
        return 0

    # 2. La PR ajoute-t-elle un carnet neuf ?
    ajoutes = [f.get("filename") for f in files
               if (f.get("filename") or "").endswith(".ipynb")
               and f.get("status") == "added"]
    neufs, demenages = new_notebooks(files)
    jumeaux = [p for p in ajoutes if p.rsplit("/", 1)[-1].endswith("_en.ipynb")]
    rapport["carnets_ajoutes"] = ajoutes
    rapport["jumeaux_en_exemptes"] = jumeaux
    rapport["demenagements_exemptes"] = demenages
    if not neufs:
        motif = ("aucun carnet neuf dans la PR"
                 + (f" ({len(demenages)} deménagement(s) exempté(s))"
                    if demenages else "")
                 + (f" ({len(jumeaux)} jumeau(x) `_en`)" if jumeaux else ""))
        rapport["statut"] = "EXEMPTE"
        rapport["exemptions"].append(motif)
        note(motif)
        _emit(rapport, args)
        return 0

    # 3. Quelle issue est servie ?
    body = meta.get("body") or ""
    m = _SERVED_RE.search(body)
    if not m:
        motif = ("aucune issue servie identifiee dans le body "
                 "(Closes/See/Part of/Fixes #N) : la provenance du carnet "
                 "neuf n'est pas etablie")
        rapport["statut"] = "SIGNALE"
        rapport["constats"].append(motif)
        note(motif)
        _emit(rapport, args)
        return 1 if args.strict else 0
    issue = int(m.group(1))
    rapport["issue_servie"] = issue

    # 4. L'issue a-t-elle attendu son tour ?
    #    La lecture de l'age est un SECOND appel reseau, posterieur au `try`
    #    ci-dessus : sans ce garde-fou, une famine qui epargne `pr_files`
    #    mais frappe `issue_created` rendait `age non mesure` -- un constat
    #    ferme -- au lieu d'un UNKNOWN. Revu le 2026-10-29 (PR #23283).
    try:
        created = issue_created(issue)
    except InstrumentError as exc:
        return non_evalue(str(exc).strip()[:240],
                          "instrument injoignable (gh/API)")
    except (OSError, subprocess.TimeoutExpired) as exc:
        return non_evalue(str(exc).strip()[:240],
                          "instrument injoignable (gh/API)")
    except RuntimeError as exc:
        return non_evalue(str(exc).strip()[:240],
                          "panne d'instrument non classee")
    age_h = None
    if created and meta.get("createdAt"):
        age_h = (dt.datetime.fromisoformat(meta["createdAt"])
                 - dt.datetime.fromisoformat(created)
                 ).total_seconds() / 3600.0
    rapport["age_heures"] = age_h

    # 5. L'issue a-t-elle ete servie par un tirage ?
    tirage = draws_for(issue, args.journal)
    rapport["tirage"] = tirage

    verdict, motif = decide(issue, age_h, tirage)
    rapport["verdict"] = verdict
    # `statut` est pose sur TOUS les chemins : un consommateur de `--json`
    # doit pouvoir distinguer CONFORME de « pas de statut » sans repliquer
    # la logique de `decide` (revue du 2026-10-29, PR #23283).
    rapport["statut"] = ("SIGNALE" if verdict.startswith("SIGNALE")
                         else "CONFORME")
    if verdict.startswith("SIGNALE"):
        rapport["constats"].append(motif)
        note(motif)
    else:
        print(f"::notice::creation-provenance: PR #{args.pr} — {motif}")

    _emit(rapport, args)
    return 1 if (args.strict and rapport["constats"]) else 0


def decide(issue: int, age_h: float | None, tirage: dict) -> tuple[str, str]:
    """Le verdict, en fonction pure : elle se teste sans reseau.

    Deux conformites, une seule sanction :

      * **l'age** : l'issue existe depuis au moins 48 h a l'ouverture de la
        PR — elle a attendu son tour ;
      * **le tirage** : l'issue a ete servie par un tirage nomme du tapis
        (`draw_id`), ce qui vaut attente : le tapis l'a proposee.

    En l'absence des DEUX, le carnet neuf n'a pas attendu son tour : il est
    signale. Un journal de tirage absent rend le second critere NON
    EVALUABLE — et le motif le dit, il ne pretend pas l'avoir mesure.
    """
    if age_h is not None and age_h >= AGE_MIN_H:
        return ("CONFORME (age)",
                f"issue #{issue} creee {age_h:.1f} h avant la PR "
                f"(>= {AGE_MIN_H:.0f} h) : elle a attendu son tour")
    if tirage.get("disponible") and tirage.get("retenue"):
        r = tirage["retenue"]
        return ("CONFORME (tirage)",
                f"issue #{issue} servie par le tirage {r['draw_id']} "
                f"(lane {r['lane']}, {r['ts']}) : elle a ete servie par le "
                "tapis")
    base = (f"issue #{issue} servie {age_h:.1f} h avant la PR"
            if age_h is not None else f"issue #{issue} d'age non mesure")
    motif = (f"{base} (< {AGE_MIN_H:.0f} h) et aucun tirage nomme dans le "
             "journal disponible : le carnet neuf n'a pas attendu son tour")
    if not tirage.get("disponible"):
        motif += (f" [critere du tirage non evaluable : "
                  f"{tirage.get('raison')}]")
    return ("SIGNALE", motif)


def _emit(rapport: dict, args) -> None:
    if args.json:
        pathlib.Path(args.json).write_text(
            json.dumps(rapport, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8")
    print()
    print("## Provenance des carnets neufs")
    print()
    print(f"- PR : #{rapport['pr']}")
    if rapport.get("pr_meta", {}).get("titre"):
        print(f"- titre : {rapport['pr_meta']['titre']}")
        print(f"- auteur : {rapport['pr_meta'].get('auteur')} "
              f"(ouverte le {rapport['pr_meta'].get('creee')})")
    if rapport.get("carnets_ajoutes"):
        print(f"- carnets ajoutes : {', '.join(rapport['carnets_ajoutes'])}")
    if rapport.get("issue_servie"):
        print(f"- issue servie : #{rapport['issue_servie']}")
    if rapport.get("age_heures") is not None:
        print(f"- age de l'issue : {rapport['age_heures']:.1f} h")
    if rapport.get("statut") == "UNKNOWN":
        print("- **verdict : UNKNOWN** (instrument injoignable : la "
              "provenance n'a pas ete mesuree)")
    if rapport.get("verdict"):
        print(f"- **verdict : {rapport['verdict']}**")
    for e in rapport.get("exemptions", []):
        print(f"- exemption : {e}")
    for c in rapport.get("constats", []):
        print(f"- constat : {c}")


if __name__ == "__main__":
    raise SystemExit(main())
