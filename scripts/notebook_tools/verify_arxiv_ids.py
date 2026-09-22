#!/usr/bin/env python3
"""Verifier les IDs arXiv via l'API arXiv et poser un verdict par ID.

Pour chaque ID : GET https://export.arxiv.org/api/query?id_list=<ID>, recupere
title/authors/published, et pose un verdict parmi **trois** -- dont deux
seulement sont des mesures :

| verdict     | ce que l'API a rendu                            | mesurable |
|-------------|-------------------------------------------------|-----------|
| `ok`        | une entree pour cet ID                          | oui       |
| `notfound`  | une reponse valide, **aucune** entree pour l'ID | oui -> ID-FANTOME |
| `transport` | rien d'exploitable (HTTP, corps vide, XML)      | **non**   |

Pourquoi ce contrat, et ce qu'il repare (mesure du 2026-09-21, EPIC #11168)
--------------------------------------------------------------------------

La version precedente comparait `totalResults` au nombre d'IDs de la requete et
declarait « garde-fou » tout ecart. Or l'API rend `totalResults=0`
**legitimement** pour un ID inexistant : un ID-FANTOME etait donc rapporte dans
la meme classe qu'une panne reseau, et **l'outil ne pouvait structurellement
jamais prononcer le verdict `ID-FANTOME`** -- la classe meme que l'EPIC #11168
existe pour detecter.

Symetriquement, un lot de 90 IDs interroge pendant une limitation de debit
d'arXiv (HTTP 406) est sorti en `ok:false` **avec un code de sortie 0** : un
audit qui aurait lu ces lignes comme « ID inexistants » aurait fait supprimer
des citations valides, soit exactement le defaut que ce module doit empecher.

Trois consequences, tenues par la construction :

1. **Une requete ne porte qu'un seul ID.** Un total ne peut pas departager
   « cet ID n'existe pas » de « la requete a mal tourne » ; une entree nommee,
   si.
2. **Le verdict se decide sur la presence d'une entree pour l'ID demande**,
   jamais sur `totalResults`.
3. **Un `transport` ne rend aucun verdict, et sort en code 2.** Les codes
   d'echec transitoires (406, 429, 5xx) sont reessayes avec repli exponentiel
   avant d'etre declares.

Codes de sortie : `0` = tous les IDs mesures ; `2` = au moins un non mesurable.
"""
import argparse
import json
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path

NS = {"a": "http://www.w3.org/2005/Atom"}
API = "https://export.arxiv.org/api/query"
UA = "CoursIA-rescan/1.0 (+https://github.com/jsboige/CoursIA)"

#: Code de sortie quand au moins un ID n'a pas pu etre mesure.
TRANSPORT_EXIT = 2

#: Statuts d'echec transitoire : reessayes avant d'etre declares.
RETRY_STATUS = frozenset({406, 429, 500, 502, 503, 504})


class TransportError(RuntimeError):
    """L'API n'a rendu aucune reponse exploitable : aucun verdict n'est possible."""


def _normalise(arxiv_id):
    """Forme comparable d'un ID : sans suffixe de version, en minuscules.

    L'API rend `1706.03762v7` pour l'ID demande `1706.03762` -- comparer les
    formes brutes ferait passer tout article versionne pour absent.
    """
    aid = (arxiv_id or "").strip()
    aid = re.sub(r"^https?://arxiv\.org/abs/", "", aid)
    aid = re.sub(r"v\d+$", "", aid)
    return aid.lower()


def _fetch(url, tries, base_delay):
    """GET avec reessais sur echec transitoire.

    Leve `TransportError` quand aucune tentative n'a rendu de corps exploitable.
    """
    last = "aucune tentative"
    for attempt in range(1, tries + 1):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": UA})
            with urllib.request.urlopen(req, timeout=30) as resp:
                body = resp.read()
            if not body:
                raise TransportError("corps vide (la reponse n'est pas une mesure)")
            return body
        except urllib.error.HTTPError as e:
            last = f"HTTP {e.code} {e.reason}"
            if e.code not in RETRY_STATUS:
                raise TransportError(last) from e
        except (urllib.error.URLError, TransportError, OSError) as e:
            last = f"{type(e).__name__}: {e}"
        if attempt < tries:
            time.sleep(base_delay * (2 ** (attempt - 1)))
    raise TransportError(f"{last} (apres {tries} tentatives)")


def _record(arxiv_id, verdict, title=None, authors=None, published=None, error=None):
    return {
        "id": arxiv_id,
        "verdict": verdict,
        "title": title,
        "authors": authors or [],
        "published": published,
        "error": error,
    }


def query_one(arxiv_id, tries=4, base_delay=3.0):
    """Mesure un ID unique.

    Leve `TransportError` si l'API n'a rien rendu d'exploitable -- dans ce cas
    aucun verdict n'est prononce, ni `ok` ni `notfound`.
    """
    url = f"{API}?id_list={urllib.parse.quote(arxiv_id)}"
    body = _fetch(url, tries, base_delay)
    try:
        root = ET.fromstring(body)
    except ET.ParseError as e:
        raise TransportError(f"XML illisible: {e}") from e
    for entry in root.findall("a:entry", NS):
        eid = entry.findtext("a:id", default="", namespaces=NS)
        if _normalise(eid) != _normalise(arxiv_id):
            continue
        title = re.sub(
            r"\s+", " ", entry.findtext("a:title", default="", namespaces=NS) or ""
        ).strip()
        authors = [
            a.findtext("a:name", default="", namespaces=NS).strip()
            for a in entry.findall("a:author", NS)
        ]
        published = entry.findtext("a:published", default="", namespaces=NS).strip()
        return _record(arxiv_id, "ok", title, authors, published)
    # Reponse valide, aucune entree nommee pour cet ID : c'est une mesure.
    return _record(arxiv_id, "notfound")


def verify_ids(ids, delay=3.0, tries=4, base_delay=3.0):
    """Mesure une liste d'IDs, un par requete, avec delai entre les appels."""
    results = []
    for index, arxiv_id in enumerate(ids):
        try:
            results.append(query_one(arxiv_id, tries=tries, base_delay=base_delay))
        except TransportError as e:
            results.append(_record(arxiv_id, "transport", error=str(e)))
        if delay and index + 1 < len(ids):
            time.sleep(delay)
    return results


def _read_ids(raw):
    p = Path(raw)
    if p.exists():
        return [
            line.strip()
            for line in p.read_text(encoding="utf-8").splitlines()
            if line.strip() and not line.startswith("#")
        ]
    return [s.strip() for s in raw.split(",") if s.strip()]


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--ids", required=True,
                    help="Liste d'IDs separes par des virgules, OU chemin d'un fichier (un ID par ligne)")
    ap.add_argument("--out", default=None, help="JSON de sortie")
    ap.add_argument("--delay", type=float, default=3.0,
                    help="Delai entre deux IDs (arXiv demande >= 3 s)")
    ap.add_argument("--tries", type=int, default=4,
                    help="Tentatives par ID avant de declarer le transport")
    ap.add_argument("--base-delay", type=float, default=3.0,
                    help="Delai de base du repli exponentiel entre tentatives")
    args = ap.parse_args(argv)

    ids = _read_ids(args.ids)
    print(f"[verify] {len(ids)} IDs a mesurer (un par requete, delai {args.delay}s)")
    results = verify_ids(ids, delay=args.delay, tries=args.tries,
                         base_delay=args.base_delay)

    counts = {"ok": 0, "notfound": 0, "transport": 0}
    for r in results:
        counts[r["verdict"]] += 1
    print(f"[verify] ok={counts['ok']} notfound={counts['notfound']} "
          f"transport={counts['transport']}")
    for r in results:
        if r["verdict"] == "ok":
            title = r["title"][:80] + "..." if len(r["title"]) > 80 else r["title"]
            year = (r["published"] or "")[:4]
            print(f"  arXiv:{r['id']:>14}  OK      ({year}, {len(r['authors'])} auth)  {title}")
        elif r["verdict"] == "notfound":
            print(f"  arXiv:{r['id']:>14}  ABSENT  aucune entree pour cet ID -> ID-FANTOME")
        else:
            print(f"  arXiv:{r['id']:>14}  NON MESURE  {r['error']}")

    if args.out:
        Path(args.out).parent.mkdir(parents=True, exist_ok=True)
        Path(args.out).write_text(
            json.dumps(results, indent=2, ensure_ascii=False), encoding="utf-8"
        )
        print(f"[verify] -> {args.out}")

    if counts["transport"]:
        print(
            f"[verify] ECHEC -- {counts['transport']} ID(s) non mesurables : "
            "aucun verdict n'a ete prononce pour eux. Ne PAS lire ces lignes "
            "comme des ID inexistants (defaut repare le 2026-09-21, EPIC #11168).",
            file=sys.stderr,
        )
        return TRANSPORT_EXIT
    return 0


if __name__ == "__main__":
    sys.exit(main())
