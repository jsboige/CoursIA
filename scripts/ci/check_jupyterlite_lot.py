#!/usr/bin/env python3
"""Garde post-deploiement : verifie que le lot JupyterLite est bien en ligne.

Issue #27550 (pli 2.2 de l'Epic #27543). Le deploiement publie un site
JupyterLite sous `/jupyterlite/` du site Quarto, avec un `manifest.json` qui
liste, pour chaque carnet du lot, ses deux URLs publiques :

- `files` : le carnet brut, servi tel quel -- c'est elle qui prouve que le
  carnet est reellement publie ;
- `lab` : la page JupyterLite qui ouvre le carnet (execution dans le
  navigateur).

Ce garde lit le manifeste **du site publie** (pas celui du depot : le
manifeste est un artefact de construction) et sonde chaque URL. Un carnet
absent du manifeste mais present dans le site n'est pas vu par ce garde :
c'est le role de la construction, qui verifie que le site publie exactement
le lot.

Exit codes :
  0 -- tous les liens du lot resolvent (2xx/3xx), ou aucun lot publie
  1 -- au moins un lien du lot est casse (404/410/autre 4xx-5xx)
  2 -- instrument casse (manifeste illisible, reseau indisponible)
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import sys
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass, field
from typing import List

EXIT_OK = 0
EXIT_BROKEN_LINK = 1
EXIT_INSTRUMENT = 2

#: Racine du site publie (le manifeste porte des chemins deja prefixes par
#: le nom du depot -- `/CoursIA/jupyterlite/...`).
DEFAULT_BASE_URL = "https://jsboige.github.io/CoursIA"

#: Chemin du manifeste sur le site publie.
CHEMIN_MANIFESTE = "/jupyterlite/manifest.json"

USER_AGENT = "coursia-jupyterlite-lot-guard/1.0 (+#27550)"
TIMEOUT_SECONDS = 20.0
PROBE_WORKERS = 8


@dataclass
class CheckResult:
    """Resultat agrege d'une passe."""
    manifest_url: str = ""
    found: bool = False
    checked: int = 0
    ok: int = 0
    broken: List[dict] = field(default_factory=list)
    instrument_errors: List[str] = field(default_factory=list)

    def to_dict(self) -> dict:
        return {
            "manifest_url": self.manifest_url,
            "found": self.found,
            "checked": self.checked,
            "ok": self.ok,
            "broken": self.broken,
            "instrument_errors": self.instrument_errors,
        }


def _origine(base_url: str) -> str:
    """Origine (scheme + hote) d'une racine de site."""
    split = urllib.parse.urlsplit(base_url)
    return "%s://%s" % (split.scheme, split.netloc)


def _url_manifeste(base_url: str, chemin: str) -> str:
    """URL absolue du manifeste sur le site publie."""
    if chemin.startswith("http://") or chemin.startswith("https://"):
        return chemin
    return base_url.rstrip("/") + "/" + chemin.lstrip("/")


def _url_carnet(base_url: str, chemin: str) -> str:
    """URL absolue d'un carnet du manifeste.

    Les chemins du manifeste sont **originaux** (ils portent deja le prefixe
    du depot : `/CoursIA/jupyterlite/files/x.ipynb`) : on les colle a
    l'origine, pas a la racine du site -- les deux ne doivent pas se
    cumuler.
    """
    if chemin.startswith("http://") or chemin.startswith("https://"):
        return chemin
    if chemin.startswith("/"):
        return _origine(base_url) + chemin
    return base_url.rstrip("/") + "/" + chemin.lstrip("/")


def _probe(url: str, timeout: float = TIMEOUT_SECONDS):
    """Sonde une URL : rend le status HTTP, ou un message d'erreur.

    Le chemin est quote : une URL publiee peut porter des espaces ou des
    caracteres accentues.
    """
    split = urllib.parse.urlsplit(url)
    path = urllib.parse.quote(split.path, safe="/%")
    request = urllib.request.Request(
        urllib.parse.urlunsplit((split.scheme, split.netloc, path, "", "")),
        headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            return response.status
    except urllib.error.HTTPError as exc:
        return exc.code
    except (urllib.error.URLError, OSError, ValueError) as exc:
        return "%s: %s" % (type(exc).__name__, exc)


def run_check(base_url: str = DEFAULT_BASE_URL,
              chemin_manifeste: str = CHEMIN_MANIFESTE,
              timeout: float = TIMEOUT_SECONDS) -> CheckResult:
    """Execute la passe complete : manifeste -> URLs du lot."""
    result = CheckResult()
    manifest_url = _url_manifeste(base_url, chemin_manifeste)
    result.manifest_url = manifest_url

    request = urllib.request.Request(
        manifest_url, headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            data = json.loads(response.read().decode("utf-8", "replace"))
    except urllib.error.HTTPError as exc:
        if exc.code == 404:
            # Aucun lot publie : le deploiement n'a pas inclus JupyterLite
            # (job de construction en echec, ou lot pas encore deploye).
            # Ce n'est pas un lien casse : rien n'est annonce.
            result.found = False
            return result
        result.instrument_errors.append("manifeste illisible (%s) : %s"
                                         % (manifest_url, exc))
        return result
    except (urllib.error.URLError, OSError, ValueError) as exc:
        result.instrument_errors.append("manifeste injoignable (%s) : %s"
                                         % (manifest_url, exc))
        return result

    carnets = data.get("carnets") or []
    if not isinstance(carnets, list):
        result.instrument_errors.append("manifeste mal forme : 'carnets' n'est pas une liste")
        return result
    result.found = True

    cibles = []
    for carnet in carnets:
        if not isinstance(carnet, dict):
            continue
        for cle in ("files", "lab"):
            chemin = carnet.get(cle)
            if not chemin:
                result.instrument_errors.append(
                    "carnet sans URL '%s' dans le manifeste : %s"
                    % (cle, carnet.get("chemin", "?")))
                continue
            cibles.append((cle, carnet.get("chemin", "?"), _url_carnet(base_url, chemin)))

    with concurrent.futures.ThreadPoolExecutor(max_workers=PROBE_WORKERS) as pool:
        statuts = list(pool.map(lambda cible: _probe(cible[2], timeout), cibles))

    for (cle, chemin, url), status in zip(cibles, statuts):
        if isinstance(status, str):
            result.instrument_errors.append("sonde impossible : %s (%s)" % (url, status))
            continue
        result.checked += 1
        if 200 <= status < 400:
            result.ok += 1
        else:
            result.broken.append({"kind": cle, "notebook": chemin,
                                   "url": url, "status": status})
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Verifie que le lot JupyterLite publie est en ligne "
                    "(garde post-deploiement, issue #27550).")
    parser.add_argument("--base-url", default=DEFAULT_BASE_URL,
                        help=f"racine du site publie (defaut : {DEFAULT_BASE_URL})")
    parser.add_argument("--manifest", default=CHEMIN_MANIFESTE,
                        help=f"chemin du manifeste (defaut : {CHEMIN_MANIFESTE})")
    parser.add_argument("--timeout", type=float, default=TIMEOUT_SECONDS,
                        help=f"timeout HTTP par requete, secondes "
                             f"(defaut : {TIMEOUT_SECONDS:g})")
    parser.add_argument("--json", action="store_true",
                        help="sortie JSON (verdict + detail des liens casses)")
    args = parser.parse_args(argv)

    result = run_check(args.base_url, args.manifest, args.timeout)

    if args.json:
        print(json.dumps(result.to_dict(), indent=2, ensure_ascii=False))
    else:
        if not result.found:
            print("[jupyterlite-lot] SKIP -- aucun manifeste publie a %s "
                  "(lot non deploye, rien a verifier)" % result.manifest_url)
        else:
            print("[jupyterlite-lot] checked=%d ok=%d broken=%d"
                  % (result.checked, result.ok, len(result.broken)))
            for entry in result.broken:
                print("[jupyterlite-lot] BROKEN %s %s %s (%s)"
                      % (entry["status"], entry["kind"], entry["url"], entry["notebook"]))
        for err in result.instrument_errors:
            print("[jupyterlite-lot] INSTRUMENT %s" % err, file=sys.stderr)

    if result.instrument_errors:
        return EXIT_INSTRUMENT
    if result.broken:
        return EXIT_BROKEN_LINK
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
