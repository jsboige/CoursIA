"""Funnel B.0 : threads inline, bundle des surfaces typees, join des dismissals.

Module NEUF extrait de ``scripts/check_unaddressed_nits.py`` dans #27319 : il
porte son propre plafond de taille (modele ``scripts/ci/nit_markers.py``,
#27882) pour que le funnel puisse grossir sans faire grossir l'organe —
l'APPROVE coordinateur sur #27319 etait bloque par le cliquet (+339 lignes
au-dela du plafond 6712) tant que le funnel vivait dans l'organe.

Contenu (deplace sans changement de comportement, contrats par surface
inchanges) :

- ``ThreadsIncomplete`` / ``review_threads`` : 3e surface B.0 (threads
  inline, absente de ``gh pr view --json``), paginee (#17437), mode strict
  #22757.
- ``_reviews_author_of_rest`` : join ``id numerique -> login`` des reviews
  par le REST historique (chemin de repli du bundle).
- ``_pr_review_bundle`` : surfaces typees + threads + join en UNE requete
  GraphQL multi-curseurs (#22757 tranche appels).
- ``improper_dismissals`` : auteurs de review dont la reserve a ete
  dismissee par quelqu'un d'autre (join timeline REST x reviews).

Contrat de couplage (pourquoi ce module ne ressemble pas a nit_markers) :
les collaborateurs de l'organe — ``REPO``, ``gh_json``, ``_author_login``,
``_typed_author_surfaces``, ``LIFT_OVERRIDE_LOGINS`` et le rebind
``review_threads`` — sont resolus AU MOMENT DE L'APPEL a travers le module
organe passe a ``wire()``, jamais importes par valeur. Les tests
monkeypatchent l'organe (``mod.gh_json``, ``mod.review_threads`` via
importlib) : la resolution tardive fait passer ces patches dans le funnel.
Chaque instance chargee de l'organe possede SA copie privee de ce module
(chargee par chemin dans le corps de l'organe, nom unique derive du nom de
l'instance) : deux organes concurrents dans un meme processus pytest ne se
croisent jamais.
"""

import subprocess
import sys

_ORGAN = None


def wire(organ_namespace) -> None:
    """Branche le namespace organe (appele par lui-meme juste apres chargement).

    ``organ_namespace`` est le module organe ou un proxy LIVE sur ses
    globales : les attributs doivent se relire a chaque acces (les
    monkeypatchs de tests remplacent ``gh_json`` / ``review_threads`` APRES
    le chargement).
    """
    global _ORGAN
    _ORGAN = organ_namespace


def _O():
    if _ORGAN is None:
        raise RuntimeError(
            "b0_funnel non cable : l'organe doit appeler wire() apres son "
            "chargement (cf scripts/check_unaddressed_nits.py, bloc #27319)."
        )
    return _ORGAN


class ThreadsIncomplete(RuntimeError):
    """Pagination des threads inline interrompue : préfixe, pas un résultat.

    Levée par ``review_threads(strict=True)`` quand la lecture ne s'est pas
    terminée proprement (``hasNextPage`` absent ou non booléen, curseur figé,
    plafond de 50 pages) : le préfixe collecté n'est JAMAIS un résultat
    complet, l'appelant doit refuser de conclure — jamais rendre un verdict
    B.0 sur le préfixe (relecture ai-01 2026-11-19 sur #22757).
    """


def review_threads(pr: int, strict: bool = False) -> list[dict]:
    """Threads inline (3e surface, absente de `gh pr view --json`).

    #17437 (relecture ai-01 2026-11-13, point non bloquant) : la connexion
    PAGINE (`after` + `pageInfo`) comme les deux autres surfaces typees.
    `first:100` seul rendait les 100 threads les PLUS ANCIENS et laissait
    les suivants invisibles — un thread inline non resolu posterieur a la
    100e position sortait de l'analyse. Meme plafond dur (50 pages = 5000
    threads) ; un curseur fige arrete la boucle au lieu de boucler.

    #22757 (relecture ai-01 2026-11-19) : ``strict=True`` est le mode du
    REPLI du bundle — chaque interruption anormale (``hasNextPage`` absent
    ou non booléen, curseur figé, plafond) lève ``ThreadsIncomplete`` au
    lieu de rendre le préfixe collecté. Le comportement historique
    (avertissement + préfixe rendu) est préservé pour les appels existants.
    """
    o = _O()
    query = """
    query($owner:String!,$repo:String!,$n:Int!,$tAfter:String){
      repository(owner:$owner,name:$repo){
        pullRequest(number:$n){
          reviewThreads(first:100,after:$tAfter){
            pageInfo{hasNextPage endCursor}
            nodes{
              isResolved isOutdated path line
              comments(first:1){nodes{author{login __typename} body createdAt}}
            }}
        }
      }
    }"""
    owner, name = o.REPO.split("/")
    nodes: list[dict] = []
    after: str | None = None
    for _ in range(50):
        args = [
            "api", "graphql", "-f", f"query={query}",
            "-F", f"owner={owner}", "-F", f"repo={name}", "-F", f"n={pr}",
        ]
        if after:
            args += ["-F", f"tAfter={after}"]
        data = o.gh_json(args)
        conn = data["data"]["repository"]["pullRequest"]["reviewThreads"]
        nodes.extend(n for n in (conn.get("nodes") or [])
                     if isinstance(n, dict))
        info = conn.get("pageInfo") or {}
        has_next = info.get("hasNextPage")
        if not isinstance(has_next, bool):
            # pageInfo sans booléen hasNextPage : la connexion n'est PAS
            # prouvée terminée (relecture ai-01 2026-11-19 sur #22757) —
            # toléré en historique, refusé en strict.
            if strict:
                raise ThreadsIncomplete(
                    f"PR #{pr}: pageInfo sans booléen hasNextPage sur "
                    "reviewThreads — préfixe non concluable.")
            break
        if not has_next:
            break
        nxt = info.get("endCursor")
        if not nxt or nxt == after:
            if strict:
                raise ThreadsIncomplete(
                    f"PR #{pr}: curseur de pagination figé sur "
                    "reviewThreads — préfixe non concluable.")
            print(f"  [!] PR #{pr}: curseur de pagination fige sur "
                  "reviewThreads — threads suivants non analyses.",
                  file=sys.stderr)
            break
        after = nxt
    else:
        if strict:
            raise ThreadsIncomplete(
                f"PR #{pr}: plafond de pagination atteint (50 pages) sur "
                "reviewThreads — préfixe non concluable.")
        print(f"  [!] PR #{pr}: plafond de pagination atteint (50 pages) sur "
              "reviewThreads — threads suivants non analyses.", file=sys.stderr)
    out = []
    for t in nodes:
        first = (t.get("comments") or {}).get("nodes") or [{}]
        c = first[0]
        out.append({
            "resolved": bool(t.get("isResolved")),
            "outdated": bool(t.get("isOutdated")),
            "path": t.get("path"),
            "line": t.get("line"),
            "author": o._author_login(c) or "?",
            "body": c.get("body", ""),
            "createdAt": c.get("createdAt"),
        })
    return out


# #22757 (tranche appels) -- bundle des surfaces typees + threads en UNE
# requete GraphQL. Le funnel mesurait 7-11 appels gh par PR evaluee (dont 3
# GraphQL : typed-surfaces, reviewThreads, plus le couple REST
# reviews+timeline de improper_dismissals) ; deux des trois GraphQL
# interrogeaient le MEME pullRequest avec les memes curseurs de pagination.
# Le bundle les fusionne : auteur type + comments + reviews (+ databaseId)
# + reviewThreads dans une seule pagination multi-curseurs.
#
# Contrats preserves PAR SURFACE (aucun verdict B.0 ne change) :
# - `typed` : exactement la forme de `_typed_author_surfaces` (cles
#   author/comments/reviews, champs identiques, SANS databaseId) ; payload
#   inattendu, curseur fige ou plafond 50 pages -> dict vide (fail-closed,
#   repli sur les surfaces CLI de `pr view`).
# - `threads` : exactement la forme de `review_threads` ; depuis la
#   relecture ai-01 du 2026-11-19, le repli est STRICT (structure invalide
#   -> KeyError propage, pagination interrompue -> ThreadsIncomplete
#   propage = PR illisible, refus explicite -- jamais un prefixe juge).
# - `author_of` : {databaseId: login} -- le join NUMERIQUE de
#   `improper_dismissals` (le node-id GraphQL `PRR_...` n'y est PAS
#   comparable, d'ou databaseId), qui remplace l'appel REST
#   `pulls/{n}/reviews` du chemin gate.
#
# Couplage des pannes, assume et documente : une SEULE requete sert les
# surfaces ; si elle leve, `review_threads` propageait deja (PR illisible,
# fail-closed) -- desormais la panne emporte AUSSI le repli CLI de typed
# (la PR est rendue absente par l'appelant au lieu d'etre analysee sur les
# surfaces non typees). La divergence ne va QUE vers plus de blocage
# (jamais un verdict permissif fabrique), et le cas anterieur -- le
# GraphQL typed seul en panne -- est un cas de reseau partiel.
#
# Relecture ai-01 (review 5967281532, 2026-11-19) -- pagination ASYMETRIQUE
# et surfaces partielles : les connexions terminees ne sont plus demandees
# (`@include(if:)` -- une surface finie ne peut ni se re-accumuler ni se
# faire re-servir sa premiere page), chaque surface possede son propre etat
# complet/partiel (la panne d'une surface n'interrompt plus la pagination
# des autres), et TOUTE surface incomplete est RELUE via son chemin
# existant -- jamais son prefixe n'est rendu comme un resultat complet :
#   typed   <- `_typed_author_surfaces` (fail-closed {} -> repli surfaces
#              CLI completes de `pr view`)
#   reviews <- `_reviews_author_of_rest` (REST pagine, jointure complete
#              par construction -- sinon un dismissal par un tiers de la
#              page suivante restait non attribue)
#   threads <- `review_threads` (tolerances historiques ; structure
#              invalide -> KeyError propage = PR illisible, refus explicite)
_BUNDLE_QUERY = """
query($owner:String!,$repo:String!,$n:Int!,$cAfter:String,$rAfter:String,$tAfter:String,
      $cInc:Boolean!,$rInc:Boolean!,$tInc:Boolean!){
  repository(owner:$owner,name:$repo){
    pullRequest(number:$n){
      author{__typename login}
      comments(first:100,after:$cAfter) @include(if:$cInc){
        pageInfo{hasNextPage endCursor}
        nodes{author{__typename login} body createdAt}}
      reviews(first:100,after:$rAfter) @include(if:$rInc){
        pageInfo{hasNextPage endCursor}
        nodes{author{__typename login} body submittedAt state databaseId}}
      reviewThreads(first:100,after:$tAfter) @include(if:$tInc){
        pageInfo{hasNextPage endCursor}
        nodes{
          isResolved isOutdated path line
          comments(first:1){nodes{author{login __typename} body createdAt}}
        }}
    }
  }
}"""


def _reviews_author_of_rest(pr: int) -> dict:
    """Join ``id numerique -> login`` des reviews, par le REST historique.

    Chemin existant du gate avant le bundle (#22757) : ``pulls/{n}/reviews``
    pagine sert le join de `improper_dismissals` quand le bundle ne peut pas
    le fournir (surface reviews incomplete). L'appelant garde ses propres
    tolerances -- la fonction laisse remonter ce que ``gh_json`` leve.
    """
    o = _O()
    reviews = o.gh_json(["api", f"repos/{o.REPO}/pulls/{pr}/reviews", "--paginate"])
    if not isinstance(reviews, list):
        reviews = []
    return {r.get("id"): o._author_login(r, "user")
            for r in reviews if isinstance(r, dict)}


def _pr_review_bundle(pr: int) -> dict:
    """Surfaces typees + threads + join des dismissals en UNE requete.

    Rend ``{"typed": dict, "threads": list, "author_of": dict}``. Les trois
    valeurs suivent les contrats documentes ci-dessus : chaque surface est
    rendue COMPLETE ou relue via son chemin existant -- un prefixe n'est
    jamais presente comme un resultat complet ; l'echec de l'APPEL propage,
    comme ``review_threads`` le faisait deja.
    """
    o = _O()
    owner, name = o.REPO.split("/")
    comments: list[dict] = []
    reviews: list[dict] = []
    threads: list[dict] = []
    pr_author: dict = {}
    author_of: dict[int, str] = {}
    c_after: str | None = None
    r_after: str | None = None
    t_after: str | None = None
    c_done = r_done = t_done = False   # connexion terminee : plus demandee
    c_bad = r_bad = t_bad = False       # incomplete : a relire via l'existant
    for _ in range(50):
        if c_done or c_bad:
            c_done = True  # une surface incomplete n'est pas re-demandee
        if r_done or r_bad:
            r_done = True
        if t_done or t_bad:
            t_done = True
        if c_done and r_done and t_done:
            break
        args = [
            "api", "graphql", "-f", f"query={_BUNDLE_QUERY}",
            "-F", f"owner={owner}", "-F", f"repo={name}", "-F", f"n={pr}",
            "-F", f"cInc={str(not c_done).lower()}",
            "-F", f"rInc={str(not r_done).lower()}",
            "-F", f"tInc={str(not t_done).lower()}",
        ]
        if c_after and not c_done:
            args += ["-F", f"cAfter={c_after}"]
        if r_after and not r_done:
            args += ["-F", f"rAfter={r_after}"]
        if t_after and not t_done:
            args += ["-F", f"tAfter={t_after}"]
        data = o.gh_json(args)
        try:
            node = data["data"]["repository"]["pullRequest"]
        except Exception:
            # Structure globale invalide : les trois surfaces sont incompletes.
            c_bad = r_bad = t_bad = True
            break
        if not pr_author and isinstance(node.get("author"), dict):
            pr_author = node["author"]
        if not c_done and "comments" in node:
            conn = node["comments"]
            nodes = conn.get("nodes") if isinstance(conn, dict) else None
            if not isinstance(nodes, list):
                c_bad = c_done = True
            else:
                comments.extend(n for n in nodes if isinstance(n, dict))
                info = (conn.get("pageInfo") or {}) if isinstance(conn, dict) else {}
                if info.get("hasNextPage") is False:
                    c_done = True
                elif info.get("hasNextPage") is True:
                    nxt = info.get("endCursor") or c_after
                    if nxt == c_after:
                        c_bad = c_done = True  # curseur fige
                    else:
                        c_after = nxt
                else:
                    # hasNextPage absent/non booléen : la connexion n'est PAS
                    # prouvée terminée (relecture ai-01 2026-11-19) — la
                    # surface est incomplète, relue via son chemin existant.
                    c_bad = c_done = True
        if not r_done and "reviews" in node:
            conn = node["reviews"]
            nodes = conn.get("nodes") if isinstance(conn, dict) else None
            if not isinstance(nodes, list):
                r_bad = r_done = True
            else:
                reviews.extend(n for n in nodes if isinstance(n, dict))
                for r in nodes:
                    if isinstance(r, dict) and isinstance(r.get("databaseId"), int):
                        login = o._author_login(r)
                        if login:
                            author_of[r["databaseId"]] = login
                info = (conn.get("pageInfo") or {}) if isinstance(conn, dict) else {}
                if info.get("hasNextPage") is False:
                    r_done = True
                elif info.get("hasNextPage") is True:
                    nxt = info.get("endCursor") or r_after
                    if nxt == r_after:
                        r_bad = r_done = True  # curseur fige
                    else:
                        r_after = nxt
                else:
                    # hasNextPage absent/non booléen : incomplète (cf comments).
                    r_bad = r_done = True
        if not t_done and "reviewThreads" in node:
            conn = node["reviewThreads"]
            nodes = conn.get("nodes") if isinstance(conn, dict) else None
            if not isinstance(nodes, list):
                t_bad = t_done = True
            else:
                threads.extend(n for n in nodes if isinstance(n, dict))
                info = (conn.get("pageInfo") or {}) if isinstance(conn, dict) else {}
                if info.get("hasNextPage") is False:
                    t_done = True
                elif info.get("hasNextPage") is True:
                    nxt = info.get("endCursor") or t_after
                    if nxt == t_after:
                        t_bad = t_done = True  # curseur fige
                    else:
                        t_after = nxt
                else:
                    # hasNextPage absent/non booléen : incomplète (cf comments).
                    t_bad = t_done = True
    else:
        # Plafond : toute surface non terminee est incomplete, pas un resultat.
        c_bad = c_bad or not c_done
        r_bad = r_bad or not r_done
        t_bad = t_bad or not t_done

    typed: dict[str, object] = {}
    if not (c_bad or r_bad):
        if pr_author:
            typed["author"] = pr_author
        if comments:
            typed["comments"] = [
                {"author": c.get("author") or {}, "body": c.get("body") or "",
                 "createdAt": c.get("createdAt")}
                for c in comments
            ]
        if reviews:
            typed["reviews"] = [
                {"author": r.get("author") or {}, "body": r.get("body") or "",
                 "submittedAt": r.get("submittedAt"),
                 "state": r.get("state")}
                for r in reviews
            ]
    else:
        # Surface incomplete -> chemin existant (fail-closed {} -> repli CLI).
        print(f"  [!] PR #{pr}: surface typee incomplete au bundle -- "
              "relecture via _typed_author_surfaces.", file=sys.stderr)
        typed = o._typed_author_surfaces(pr)

    if r_bad:
        # Jointure incomplete -> REST historique complet (un dismissal par un
        # tiers de la page suivante doit rester attribue, jamais silencieusement
        # absent du join).
        print(f"  [!] PR #{pr}: surface reviews incomplete au bundle -- "
              "relecture du join via pulls/{{n}}/reviews.", file=sys.stderr)
        try:
            author_of = _reviews_author_of_rest(pr)
        except subprocess.TimeoutExpired:
            raise
        except Exception:
            author_of = {}

    out_threads: list[dict]
    if t_bad:
        # Threads incomplets -> chemin existant. Relecture ai-01 du
        # 2026-11-19 : `review_threads` rend des enregistrements DEJA
        # normalises (resolved/outdated/author/body/createdAt) — les faire
        # repasser par le convertisseur des noeuds GraphQL bruts corrompait
        # le verdict (resolved->False, auteur->"?", corps perdu : un thread
        # RESOLU ressortait INLINE-UNRESOLVED). On rend le resultat du
        # repli TEL QUEL. strict=True : un repli encore incomplet
        # (hasNextPage absent, curseur fige, plafond) PROPAGE au lieu de
        # rendre un prefixe — refus de conclure, jamais un verdict B.0 sur
        # le prefixe.
        print(f"  [!] PR #{pr}: surface threads incomplete au bundle -- "
              "relecture via review_threads.", file=sys.stderr)
        out_threads = o.review_threads(pr, strict=True)
    else:
        out_threads = []
        for t in threads:
            first = (t.get("comments") or {}).get("nodes") or [{}]
            c = first[0]
            out_threads.append({
                "resolved": bool(t.get("isResolved")),
                "outdated": bool(t.get("isOutdated")),
                "path": t.get("path"),
                "line": t.get("line"),
                "author": o._author_login(c) or "?",
                "body": c.get("body", ""),
                "createdAt": c.get("createdAt"),
            })
    return {"typed": typed, "threads": out_threads, "author_of": author_of}


def improper_dismissals(pr: int, author_of: dict | None = None) -> set[str]:
    """Auteurs de review dont la reserve a ete dismissee par QUELQU'UN D'AUTRE.

    `gh pr view --json reviews` ne dit ni qui a dismissee ni quand : il ne rend
    que l'etat final `DISMISSED`. L'acteur vit dans la timeline REST
    (`review_dismissed`), l'auteur de la review dans les reviews — les deux
    se joignent par l'`id` NUMERIQUE (le champ `id` de `gh pr view` est un
    node-id GraphQL, `PRR_kwDO...`, non comparable au `review_id` entier).

    #22757 (tranche appels) : le join `id -> auteur` peut venir du bundle
    `_pr_review_bundle` (`databaseId` GraphQL) via le parametre `author_of`
    — le chemin gate economise alors l'appel REST `pulls/{n}/reviews`.
    Fourni ou non, la jointure reste NUMERIQUE et la timeline REST reste
    le seul Historique lu (les `dismissedReviews` GraphQL ne rendent que
    l'etat courant, pas l'historique des dismissals : les verdicts
    divergeraient sur une review dismissee puis resoumise).

    Retourne des LOGINS d'auteurs de review, pas des ids : la reserve est
    reappariee par auteur dans `analyse`. Sur-approximation assumee quand un
    meme auteur a deux reviews dismissees dont une legitimement — un gate se
    trompe du cote qui bloque, jamais du cote qui laisse passer.

    Non cable sur `audit()` : deux appels API par PR, pour un chemin retrospectif
    ou l'enforcement n'a plus lieu. Le gate pre-merge est le point de controle.
    """
    o = _O()
    try:
        if author_of is None:
            author_of = _reviews_author_of_rest(pr)
            if not author_of:
                # reviews illisibles : on retombe sur l'ancien comportement
                # (pas de join -> pas d'improper detecte), timeline non lue.
                return set()
        events = o.gh_json(["api", f"repos/{o.REPO}/issues/{pr}/timeline", "--paginate"])
    except subprocess.TimeoutExpired:
        # #19643 (residu) : un ensemble vide lirait la reserve d'un tiers comme
        # levee. Une expiration remonte jusqu'au verdict non-CLEAN de main().
        raise
    except Exception:
        return set()  # timeline illisible : on retombe sur l'ancien comportement
    if not isinstance(events, list):
        return set()
    improper: set[str] = set()
    for e in events:
        if not isinstance(e, dict) or e.get("event") != "review_dismissed":
            continue
        actor = o._author_login(e, "actor")
        rid = (e.get("dismissed_review") or {}).get("review_id")
        emitter = author_of.get(rid)
        if not emitter:
            continue
        if actor == emitter or actor in o.LIFT_OVERRIDE_LOGINS:
            continue
        improper.add(emitter)
    return improper
