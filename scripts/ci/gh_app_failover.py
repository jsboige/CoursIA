"""Bascule UNIQUE vers le jeton App de la lane sur epuisement de quota GitHub.

#27012 point 3 (fournée FREINS n°2). Mesure fondatrice (lane
``myia-po-2027:CoursIA``, tour de table du 16/11) : 13 PRs devaient un sweep
B.0 apres un rate-limit du seau partage ; 10 restaient sans sweep parce que
l'organe sortait en ``CalledProcessError`` sans rien dire d'actionnable.

Ce module est le funnel d'appel gh des organes qui le branchent
(``check_unaddressed_nits.gh_json``) : il route d'abord par le cache ETag
persistent (``gh_etag``, #26260), puis par ``gh`` en subprocess. Sur un echec
403/429 de type rate-limit, il tente **une seule fois par process** la
bascule vers le jeton de l'App d'installation de la lane
(``coursia-lane-<lane>``, plan #17437 : un seau de quota PAR lane, distinct
du login partage ``jsboige``), reessaie l'appel une fois, et imprime un
message sur stderr.

Proprietes :

- **jamais ``gh auth switch``** : le jeton est epingle dans
  ``os.environ["GH_TOKEN"]`` du process courant uniquement (doctrine
  ``gh_identity`` -- l'etat global du trousseau ne se corrompt pas) ;
- **une bascule seule** : le drapeau ``_STATE`` interdit toute seconde forge,
  meme si la premiere a echoue -- pas de boucle de retries ;
- **le jeton n'est jamais affiche** ni ecrit sur disque (meme discipline que
  ``github_app_token.py``) ;
- un echec NON rate-limit (403 permissions, 404, timeout) remonte
  l'exception d'origine, intacte : la bascule ne masque que l'epuisement de
  quota ;
- si la PEM de l'App de la lane n'est pas deposee sur le siege, la bascule
  est impossible : le message de remédiation la nomme, et l'exception
  d'origine remonte.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

try:
    import gh_identity
except ImportError:  # charge via importlib dans les tests (hors scripts/)
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))
    import gh_identity

try:
    import gh_etag
except ImportError:  # meme shim que gh_identity
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))
    import gh_etag

try:
    import github_app_token
except ImportError:  # la forge vit dans scripts/secrets/
    sys.path.insert(
        0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "secrets"))
    import github_app_token

REPO = "jsboige/CoursIA"
KEY_DIR = Path(__file__).resolve().parents[2] / ".secrets" / "github-apps"
API_ROOT = "https://api.github.com"

# Une bascule SEULE par process (#27012 point 3) : le drapeau est pose AVANT
# la tentative, meme si elle echoue -- un jeton App incapable de forger ne
# doit pas declencher une boucle de forges a chaque appel suivant.
_STATE: dict = {"failover_done": False, "app_id": None}


def lane_of_host(hostname: str | None = None) -> str:
    """Lane de la machine locale : ``myia-po-2028`` -> ``po-2028``.

    S'appuie sur ``gh_identity.machine_hostname`` (``COMPUTERNAME`` prime sur
    Windows) ; les hotes hors convention ``myia-<lane>`` n'ont pas d'App de
    lane (echec BRUYANT plutot qu'une devine).
    """
    host = (hostname if hostname is not None
            else gh_identity.machine_hostname()).lower()
    if not host.startswith("myia-") or host == "myia":
        raise RuntimeError(
            f"hostname '{host}' ne designe pas une lane (convention myia-<lane>) : "
            "pas d'App de lane a forger pour la bascule de quota.")
    return host[len("myia-"):]


def app_slug(lane: str) -> str:
    """Slug de l'App d'installation de la lane (prefixe #17437)."""
    return f"coursia-lane-{lane}"


def pem_path(lane: str | None = None) -> Path:
    return KEY_DIR / f"{app_slug(lane if lane is not None else lane_of_host())}.pem"


def _fetch_app_id(slug: str) -> int:
    """Id numerique de l'App via l'endpoint PUBLIC ``/apps/<slug>``.

    Endpoint non authentifie (quota anonyme par IP) : un appel par process,
    mis en cache. Le JWT de forge exige l'id AVANT toute authentification --
    c'est le seul pont, il ne peut pas passer par le jeton epuise.
    """
    if _STATE["app_id"] is not None:
        return int(_STATE["app_id"])
    req = urllib.request.Request(
        f"{API_ROOT}/apps/{slug}",
        headers={"Accept": "application/vnd.github+json",
                 "User-Agent": "coursia-gh-app-failover"},
    )
    try:
        with urllib.request.urlopen(req, timeout=30) as reponse:
            data = json.loads(reponse.read())
    except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as exc:
        raise RuntimeError(
            f"resolution de l'App '{slug}' impossible (endpoint public /apps) : "
            f"{exc}. Deposer .secrets/github-apps/{slug}.pem et verifier l'App."
        ) from exc
    app_id = data.get("id")
    if not app_id:
        raise RuntimeError(
            f"endpoint /apps/{slug} n'a pas rendu d'id : {str(data)[:200]}")
    _STATE["app_id"] = int(app_id)
    return int(app_id)


def forge_app_token() -> str:
    """Forge le jeton d'installation de l'App de la lane (jamais affiche)."""
    slug = app_slug(lane_of_host())
    key = pem_path()
    if not key.is_file():
        raise RuntimeError(
            f"cle privee absente : {key}. La bascule exige la PEM de l'App "
            f"{slug} (github_app_manifest.py --serve, plan #17437) -- sans "
            "elle, le seau de quota de la lane est inaccessible depuis ce siege.")
    app_id = _fetch_app_id(slug)
    jwt_token = github_app_token.build_jwt(
        str(app_id), github_app_token._read_private_key(key), int(time.time()))
    installation = github_app_token.resolve_installation(jwt_token, REPO, None)
    data = github_app_token.mint(jwt_token, installation)
    return data["token"]


def _rate_limited(exc: BaseException) -> bool:
    """403/429 d'epuisement de quota, au motif texte rendu par ``gh``.

    ``gh`` ne rend pas le code HTTP a l'appelant : il imprime le motif du
    serveur sur stderr (``API rate limit exceeded``, ``secondary rate
    limit``). La detection est celle de ``gh_identity`` (source unique),
    appliquee aux deux sorties.
    """
    stderr = getattr(exc, "stderr", None) or ""
    stdout = getattr(exc, "stdout", None) or ""
    return gh_identity.is_rate_limit_error(f"{stderr}\n{stdout}")


def _switch_to_app_token() -> bool:
    """Tente la bascule unique ; True si le retry peut partir sur l'App."""
    print(
        gh_identity.rate_limit_banner("rate-limit detecte sur l'appel gh -- "
                                      "tentative de bascule vers le jeton App "
                                      "de la lane (#27012 point 3)"),
        file=sys.stderr)
    try:
        token = forge_app_token()
    except (RuntimeError, github_app_token.ForgeError,
            github_app_token.ForgeUnreachable) as exc:
        print(
            f"[RATE-LIMIT] bascule IMPOSSIBLE sur ce siege : {exc} -- "
            "l'erreur d'origine remonte ; le sweep est a rejouer une fois le "
            "quota regenere (rate_limit reset ~1 h) ou la PEM deposee.",
            file=sys.stderr)
        return False
    os.environ["GH_TOKEN"] = token  # env du process, jamais gh auth switch
    print(
        f"[RATE-LIMIT] bascule effectuee vers {app_slug(lane_of_host())} -- "
        "les appels suivants de la passe utilisent le seau de quota de la lane.",
        file=sys.stderr)
    return True


def _attempt(fn) -> object:
    """Un essai, avec la bascule unique puis UN re-essai sur rate-limit."""
    try:
        return fn()
    except subprocess.CalledProcessError as exc:
        if _STATE["failover_done"] or not _rate_limited(exc):
            raise
        _STATE["failover_done"] = True
        if not _switch_to_app_token():
            raise
        return fn()


def call(args: list, *, timeout: float, on_304=None) -> object:
    """Le funnel d'appel gh : ETag conditionnel d'abord, ``gh`` ensuite.

    Les chemins ``api repos/...`` sans drapeau passent par l'ETag persiste
    partage par machine (``gh_etag``) : un 304 est une preuve serveur que le
    chemin est inchange, aucun corps n'est servi sans reponse du serveur.
    ``on_304`` (optionnel) compte ces touches pour la passe appelante. Tout
    echec non-304 leve les memes exceptions que le chemin direct, apres la
    chance unique de bascule de quota decrite en tete de module.
    """
    etag_path = gh_etag.etag_applicable(args)
    if etag_path is not None:
        body, served_by_304 = _attempt(
            lambda: gh_etag.conditional_get(etag_path, timeout=timeout))
        if served_by_304 and on_304 is not None:
            on_304()
        return body
    out = _attempt(lambda: subprocess.run(
        ["gh", *args], capture_output=True, text=True, encoding="utf-8",
        check=True, timeout=timeout,
    ).stdout)
    return json.loads(out)
