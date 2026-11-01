#!/usr/bin/env python3
"""Plancher de temps entre le DERNIER commit de tete d'une PR et son merge.

Mandat user 2026-09-07 : « Je veux bien un delai de 2h oui stp, si certains
checks doivent durcir, n'hesite pas. »

Pourquoi ce module existe, et pourquoi il vit DANS le `PR gate`
--------------------------------------------------------------

Mesure du 2026-09-07 sur la protection de `main` :

    required_status_checks.contexts = ["PR gate"]
    required_pull_request_reviews  = null
    strict                          = false
    enforce_admins                  = false

Une seule surface peut refuser un merge sur ce depot : le check `PR gate`.
Aucune fenetre horaire n'existe nulle part -- une recherche des motifs
`datetime.now().hour`, `MERGE_HOURS`, `ALLOWED_HOURS` sur `scripts/` rend
zero -- et les deux seuls mecanismes temporels du depot ne gatent PAS un
merge :

  * `DWELL_HOURS_DEFAULT = 24.0` (`scripts/pick_idle_grain.py`) refuse de
    *proposer* une issue creee il y a moins de 24 h -- c'est un picker, pas
    un gate ;
  * l'attente bornee du `PR gate` (`--timeout-min 45`) attend que les
    constituants concluent -- elle ne differe rien une fois qu'ils sont verts.

D'ou l'attachement retenu : le plancher est evalue par le gate lui-meme,
**apres** que les constituants ont conclu verts, et **hors** de la boucle
d'attente. Aucun runner n'est tenu a dormir : un sommeil de 2 h tiendrait
2 h le slot que l'agregateur occupe deja.

Comment le rouge se leve tout seul
----------------------------------

Un check-run ne se re-evalue pas : rendu rouge a T+5 min parce que la tete est
jeune, il resterait rouge pour toujours si personne ne le rejouait. Deux
organes deja en place rejouent precisement ce cas de figure, sans qu'aucun ne
soit a ecrire :

  * `pr-gate-rerun.yml` -- `workflow_run` sur la fin d'un garde ;
  * `pr-gate-stale-sweep.yml` -- balayage periodique (`cron: '7 * * * *'`,
    mais cadence REELLE mesuree 2 h 33 - 5 h 18 entre tirs, #15197) qui
    selectionne exactement « une jambe `PR gate` rouge alors que tout le reste
    est vert », c'est-a-dire l'etat qu'une PR en attente de plancher presente,
    et **re-lance le run d'origine** (un POST d'un check-run homonyme atterrit
    dans une suite etrangere et GitHub ANDe les deux -- mesure #11519).

Consequence a assumer et a dire : le plancher est un PLANCHER, pas une
horloge. Une PR devient mergeable au premier balayage suivant l'ecoulement
des 2 h -- donc, a la cadence mesuree, entre 2 h 00 et ~7 h 20 apres son
dernier commit, pas a 2 h 00 pile et pas a 3 h 00 non plus.

Et la consequence qui compte pour une lane : cette fenetre est trop large
pour etre attendue. Le verdict le dit donc explicitement -- on enchaine un
autre grain, et on rejoue la jambe soi-meme apres l'ecoulement si on veut
la merger sans attendre le balayage. Le message NE DOIT PAS dire qu'aucun
geste n'est requis : c'etait faux (le balayage n'est pas horaire) et cela
transformait un minuteur en instruction d'attente. Voir #15726.

La date lue est celle du COMMITTER, pas de l'auteur
---------------------------------------------------

`--amend`, `rebase`, `gh pr update-branch` conservent la date d'auteur et
rafraichissent celle du committer. Le mandat parle du « dernier commit de
tete » : c'est la date de committer qui la porte. Une PR rebasee re-arme donc
son plancher, ce qui est le comportement voulu -- la tete qui va etre mergee
n'a jamais ete observee 2 h par la CI avant le rebase.

#16149 -- le rafraichissement de base ne re-arme plus le plancher qu'il franchit
--------------------------------------------------------------------------------

`gh pr update-branch` est le seul remede a un rouge perime (un `gh run rerun`
rejoue la base gelee d'origine), mais il cree un commit de fusion qui
rafraichit la date de committer : le remede re-armait les 120 min qu'il sert
a franchir -- une taxe de 2 h par reparation, sur un commit sans aucun
contenu d'auteur (son delta appartient a `main`, deja gate par ses propres
gardes). Le plancher se mesure desormais sur le DERNIER COMMIT QUI MODIFIE
LE COTE PR. Un rebase, lui, reecrit les commits d'auteur : single-parent, il
reste mesure -- le comportement voulu ci-dessus. Une fusion dont le second
parent n'est PAS sur la base (l'auteur incorpore sa propre sous-branche)
introduit du contenu d'auteur : elle reste mesuree aussi. Une filiation
illisible ne vaut pas reconnaissance de rafraichissement : la fusion se
mesure alors elle-meme (comportement d'avant #16149 -- plus strict, jamais
plus lache).

CR ai-01 2026-09-16 -- la forme des parents ne prouve pas l'absence de contenu
-----------------------------------------------------------------------------

Contre-exemple exact-tree (review CHANGES_REQUESTED sur la tete b722ae246f) :
un `git merge main` MANUEL avec resolution substantielle de conflit a
exactement la forme de parents d'un update-branch (second parent ancetre de
la base) tout en ecrivant du contenu d'auteur frais dans l'arbre. Remonter
sur la seule forme des parents exemptait a tort cette resolution : le
plancher etait mesure sur le vieux premier parent alors que la tete portait
du contenu jamais observe par la CI.

L'exemption exige desormais une PREUVE d'absence de contenu d'auteur :
l'arbre du commit de fusion doit etre IDENTIQUE a l'auto-merge de ses deux
parents, verifie par `git merge-tree --write-tree <P1> <P2>` (Git >= 2.38)
apres fetch borne des parents manquants. Un auto-merge impossible (conflits
-- sortie non nulle de merge-tree) prouve qu'un VRAI merge ne peut exister
qu'avec une resolution d'auteur : jamais exemptee. Une preuve indisponible
(git absent, fetch muet, sortie illisible) ne vaut PAS exemption : la fusion
se mesure elle-meme -- fail-closed, exactement comme une filiation
illisible. Le prix assume : un update-branch serveur dont la preuve echoue
pour raison d'infrastructure re-arme le plancher (2 h) ; c'est le trade-off
d'une frontiere de securite -- on ne franchit jamais sur une absence de
preuve.

CR ai-01 2026-09-16 19:10Z -- la preuve doit etre ATTEIGNABLE dans le gate
---------------------------------------------------------------------------

`pr-gate.yml` tourne sur un checkout `actions/checkout@v4` SANS fetch-depth
(shallow depth 1) et sparse. Dans cette topologie, chaque parent est ramene
en `--depth=1` : les deux parents n'ont aucun historique commun, `merge-base`
echoue, et `git merge-tree --write-tree` refuse de calculer ("unrelated
histories") -- la preuve d'equivalence etait INATTENABLE et meme un
update-branch serveur LEGITIME se re-armait 120 min. Le repair : avant
merge-tree, on approfondit le checkout par palliers bornes
(`git fetch --deepen=N`, cap `_DEEPEN_MAX_DEPTH`) jusqu'a rendre le
merge-base calculable. Au-dela du cap, ou dans un depot non shallow (des
historiques veritablement sans relation), la preuve reste indisponible ->
fail-closed : l'exemption ne franchit jamais sur une absence de preuve
(inchange).

Derogation
----------

Le label `merge-dwell-waived` leve le plancher pour la PR qui le porte. Il
existe pour un cas nomme : `main` est rouge et le correctif ne doit pas
attendre 2 h. Le module dit **dans le message** que la derogation a joue, pour
qu'elle reste lisible dans le log du gate et pas seulement dans la liste des
labels.

#18686 -- la derogation est VERIFIEE, pas crue
----------------------------------------------

Le login `jsboige` etant partage par toutes les lanes et par le user, aucun
controle par auteur de l'evenement ne distingue personne : le 01/10, une lane
a pose le label elle-meme sur deux PRs de contenu sans aucun rapport avec un
`main` rouge. Le gate verifie desormais lui-meme la condition que cette
section nommait deja : le label ne joue QUE si la tete de la branche par
defaut porte un check-run COMPLETE en conclusion `failure` (un rouge de `main`,
quelle que soit la suite qui le porte -- on ne re-resout pas « la suite que la
PR repare » : c'est une lecture de plus par PR labellisee, et un rouge est un
rouge). Le motif releve (nom du check en echec) est rendu dans le message.

Sinon le message dit « label present, condition non remplie » et le plancher
s'applique normalement. Une couleur de `main` ILLISIBLE ne vaut pas rouge :
la derogation ne franchise jamais sur une absence de preuve -- fail-closed,
comme l'exemption de rafraichissement plus haut. Le cas « issue de rouge main
citee dans le body » de l'organe n'est PAS implante : une citation d'issue
ouverte est porte par la moitie des PRs du depot, l'accepter rendrait la
derogation atteignable par n'importe quel body -- exactement le bypass que
l'organe vient de subir. Arbitrage documente dans la PR.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
from datetime import datetime, timedelta, timezone

#: Plancher par defaut, en minutes. 120 = le mandat user du 2026-09-07.
DEFAULT_DWELL_MIN = 120.0

#: Minute du cron de `pr-gate-stale-sweep.yml` (l.102, `cron: '7 * * * *'`).
#: `lift` est arrondi a l'instant `:07` strictement posterieur au plancher :
#: c'est l'heure GARANTIE a laquelle un sweep nominal peut franchir, pas la
#: seule (le `push` heartbeat sert en pratique 89 fois / 100 -- #15770,
#: mediane 11 min), mais une heure a laquelle la lane qui revient au cron est
#: sure de trouver la jambe relevee. Si le cron bouge, la constante doit
#: bouger -- un commentaire en ce sens garde le lien casse si on l'oublie.
SWEEP_MINUTE = 7

#: Label qui leve le plancher sur une PR donnee.
WAIVER_LABEL = "merge-dwell-waived"

#: Forme du message « plancher non ecoule », pour les consommateurs qui ne
#: peuvent pas reevaluer le plancher eux-memes. Le picker en est un : il ne voit
#: que le TEXTE du gate (ni date de committer ni labels sous la main), et il a
#: besoin de distinguer « ce rouge est un minuteur » de « ce rouge est un
#: defaut ». La forme vit ici, avec l'emetteur, parce qu'une copie chez le
#: lecteur deriverait en silence -- le lecteur cesserait de matcher et le rouge
#: DWELL redeviendrait un grain dit reparable sans qu'aucun test ne rougisse.
_DWELL_PENDING_RE = re.compile(
    r"tete du (\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z)[^\n]*?"
    r"plancher (\d+) min[^\n]*?"
    r"reste (\d+) min[^\n]*?"
    r"ecoule a (\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z)"
)


def _next_sweep_after(floor: datetime) -> datetime:
    """Le premier instant `SWEEP_MINUTE:00:00Z` strictement posterieur a `floor`.

    `floor` est la date-heure a laquelle le plancher est FRAICHEMENT ecoule.
    Le sweep `:07` qui suit peut et anterieur -- dans ce cas on prend le suivant.
    But : informer la lane de l'heure GARANTIE du balayage nominal, pas de
    l'heure du plancher brut (qui tait que le sweep est anterieur).
    """
    candidate = floor.replace(minute=SWEEP_MINUTE, second=0, microsecond=0)
    if candidate <= floor:
        candidate = candidate + timedelta(hours=1)
    return candidate


class DwellError(RuntimeError):
    """Etat de plancher illisible. Rule 1 du gate : on refuse, on ne passe pas."""


def parse_iso8601(value: str) -> datetime:
    """Parse une date ISO-8601 GitHub (`2026-09-07T09:48:43Z`) en aware-UTC.

    `datetime.fromisoformat` n'accepte le `Z` qu'a partir de Python 3.11 ; le
    remplacement explicite garde le module lisible sur 3.10, la version
    plancher annoncee par `CLAUDE.md` section E.
    """
    text = (value or "").strip()
    if not text:
        raise DwellError("date vide")
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    try:
        parsed = datetime.fromisoformat(text)
    except ValueError as exc:
        raise DwellError("date illisible: {!r}".format(value)) from exc
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return parsed.astimezone(timezone.utc)


def evaluate(
    committed_at: datetime,
    now: datetime,
    dwell_min: float,
    waived: bool = False,
    waiver_motif: str = "",
) -> tuple[bool, float, str]:
    """Decide si le plancher est ecoule. Fonction PURE (testable sans reseau).

    Renvoie `(ok, minutes_restantes, message)`.

    Une horloge qui recule -- tete datee dans le futur, par decalage de machine
    ou date de committer forgee -- rend l'age negatif : le plancher n'est alors
    PAS ecoule, et le message le dit. Traiter le futur comme « tres vieux »
    serait la seule facon de transformer ce garde en passe-plat.

    `waiver_motif` (#18686) : quand la derogation est VERIFIEE, le motif releve
    (le check de `main` en echec) est rendu dans le message pour rester lisible
    dans le log du gate -- une derogation sans motif publie serait une ligne de
    label que rien ne justifie au moment de la relire.
    """
    if dwell_min <= 0:
        return True, 0.0, "dwell desactive (--dwell-min <= 0)"
    if waived:
        suffix = " -- {}".format(waiver_motif) if waiver_motif else ""
        return True, 0.0, (
            "dwell leve par le label `{}`{} "
            "(plancher {:.0f} min non applique)".format(
                WAIVER_LABEL, suffix, dwell_min
            )
        )

    age_min = (now - committed_at).total_seconds() / 60.0
    remaining = dwell_min - age_min
    stamp = committed_at.strftime("%Y-%m-%dT%H:%M:%SZ")
    if remaining <= 0:
        return True, 0.0, (
            "dwell ecoule: tete du {}, {:.0f} min "
            "(plancher {:.0f} min)".format(stamp, age_min, dwell_min)
        )
    # #15693 : l'heure de LEVEE absolue, pas seulement les minutes restantes.
    # « 101 min » oblige la lane a refaire le calcul et l'incite a agir ; un
    # re-push reactionnaire remet le plancher a zero depuis la nouvelle tete
    # (le defaut multiplie le temps d'attente au lieu de le mesurer).
    # #16092 : l'heure du plancher brut (tete + dwell_min) **tait** que le
    # sweep `:07` est anterieur d'une fraction d'heure sur la majorite des PRs.
    # On arrondit au premier `:07` STRICTEMENT postérieur -- c'est l'heure
    # GARANTIE du balayage nominal, pas l'heure du plancher.
    lift = _next_sweep_after(committed_at + timedelta(minutes=dwell_min)).strftime(
        "%Y-%m-%dT%H:%M:%SZ"
    )
    return False, remaining, (
        "tete du {}, {:.0f} min -- plancher {:.0f} min, reste {:.0f} min ; "
        "ecoule a {}. "
        "Rien a corriger dans le code : cette jambe est un minuteur. "
        "NE PAS ATTENDRE -- enchainer un autre grain ; c'est la candidate "
        "qui attend, pas la lane. Passe cette heure, la jambe se re-agrege "
        "au balayage suivant (pr-gate-stale-sweep.yml ; cadence MESUREE "
        "2 h 33 - 5 h 18 entre tirs, pas horaire malgre son cron "
        "'7 * * * *' -- #15197), ou tout de suite en la rejouant soi-meme "
        "(`gh run rerun <run_id> --job <job_id>`). "
        "Urgence (main rouge) : poser le label `{}` sur "
        "la PR.".format(stamp, age_min, dwell_min, remaining, lift, WAIVER_LABEL)
    )


def parse_pending_message(message: str) -> "dict | None":
    """Champs du plancher NON ecoule dans un message de `evaluate`, ou None.

    Inverse de la branche « plancher en cours » de `evaluate` : c'est ce que lit
    un consommateur qui n'a pas de quoi recalculer le plancher lui-meme (#15910).

    ``None`` couvre les DEUX autres verdicts du gate -- plancher ecoule et
    derogation par label -- et tout texte etranger. Les distinguer importe : un
    plancher ecoule est un rouge qui va tomber seul au prochain balayage, une
    derogation dit que le plancher ne mord pas du tout, et aucun des deux n'est
    « un plancher de 0 minute ».
    """
    match = _DWELL_PENDING_RE.search(message or "")
    if not match:
        return None
    return {"head_at": match.group(1), "dwell_min": int(match.group(2)),
            "remaining_min": int(match.group(3)), "lift_at": match.group(4)}


def _gh_json(path: str) -> object:
    try:
        completed = subprocess.run(
            ["gh", "api", path],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            check=False,
        )
    except FileNotFoundError as exc:  # pragma: no cover - environnement
        raise DwellError("gh CLI absent: {}".format(exc)) from exc
    if completed.returncode != 0:
        raise DwellError(
            "gh api {} a echoue (exit {}): {}".format(
                path, completed.returncode, completed.stderr.strip()[:300]
            )
        )
    try:
        return json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise DwellError("reponse non-JSON de gh api {}".format(path)) from exc


def _commit_payload(repo: str, sha: str, fetch=_gh_json) -> dict:
    payload = fetch("repos/{}/commits/{}".format(repo, sha))
    if not isinstance(payload, dict):
        raise DwellError("payload commit inattendu pour {}".format(sha[:12]))
    return payload


def _committer_date(payload: dict, sha: str) -> datetime:
    committer = ((payload.get("commit") or {}).get("committer") or {})
    date = committer.get("date")
    if not date:
        raise DwellError("pas de commit.committer.date sur {}".format(sha[:12]))
    return parse_iso8601(date)


def head_committed_at(repo: str, sha: str, fetch=_gh_json) -> datetime:
    """Date de COMMITTER de `sha`. Leve `DwellError` si elle est illisible."""
    return _committer_date(_commit_payload(repo, sha, fetch), sha)


def _second_parent_is_base_ancestor(
    repo: str, parent_sha: str, base_sha: str, fetch=_gh_json
) -> bool:
    """#16149 : le second parent du commit de fusion est-il un ancetre de la
    base ? C'est la signature d'un rafraichissement de base (`gh pr
    update-branch` comme `git merge main` manuel). L'egalite directe evite
    l'appel compare ; sinon `compare/{base}...{parent}` rend "behind" quand
    parent est un ancetre de base. Une lecture illisible ne vaut PAS
    reconnaissance : False, la fusion se mesure alors elle-meme (comportement
    d'avant #16149 -- plus strict, jamais plus lache)."""
    if parent_sha == base_sha:
        return True
    try:
        cmp = fetch(
            "repos/{}/compare/{}...{}".format(repo, base_sha, parent_sha)
        )
    except DwellError:
        return False
    if not isinstance(cmp, dict):
        return False
    return cmp.get("status") in ("behind", "identical")


def _default_run_git(args):
    """Execute `git <args>` dans le depot courant (le gate tourne a la racine
    du checkout). Renvoie (returncode, stdout) ; les erreurs d'execution
    remontent a l'appelant, qui les traite en preuve indisponible."""
    completed = subprocess.run(
        ["git"] + list(args),
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        check=False,
    )
    return completed.returncode, completed.stdout


#: Refs candidates pour la base canonique, du plus canonique au plus large.
#: La porte de pile (cf. `check_adjoint_prevalidation.py`) mesure
#: ``main..tete`` ; le gate exige `baseRefName == main`, donc la base est
#: toujours `main`.
_BASE_REF_CANDIDATES = (
    "refs/remotes/origin/main",
    "origin/main",
    "main",
)


def _resolve_base_ref(run_git):
    """La ref de la base resolue localement, ou None.

    Aucun candidat resolu = base inconnue (checkout minimal) : les appelants
    traitent alors le depot comme potentiellement tronque, comme avant le
    correctif #23089.
    """
    for ref in _BASE_REF_CANDIDATES:
        try:
            rc, _ = run_git(["rev-parse", "--verify", "--quiet", ref + "^{commit}"])
        except (OSError, subprocess.SubprocessError):
            return None
        if rc == 0:
            return ref
    return None


def shallow_boundary_shas(run_git):
    """Les SHA declares comme racines shallow par le depot (`.git/shallow`).

    Chaque ligne est un commit dont l'ascendance est coupee. Le fichier peut
    etre absent (depot complet) : la liste est alors vide.
    """
    try:
        rc, out = run_git(["rev-parse", "--git-path", "shallow"])
    except (OSError, subprocess.SubprocessError):
        return []
    if rc != 0:
        return []
    path = (out or "").strip()
    if not path:
        return []
    try:
        with open(path, encoding="utf-8") as handle:
            return [line.strip() for line in handle if line.strip()]
    except OSError:
        return []


def base_history_truncated(run_git=None, base_ref=None):
    """L'historique de la base est-il REELLEMENT tronque ?

    `git rev-parse --is-shallow-repository` rend `true` des que `.git/shallow`
    porte UNE ligne -- y compris des racines mortes, sans rapport avec la base.
    Mesure (ai-01, 2026-10-28) : six bornes etrangeres a l'historique de
    `main`, booleen `true` en permanence, alors que `main` etait complet
    (18 788 commits visibles, le compte de l'API). Un predicat base sur ce
    booleen seul ne protege donc rien : la jambe locale resterait
    atteignable, et le clone complet serait rendu superficiel par le fetch.

    Seule une borne qui est un ANCETRE de la base tronque l'historique de la
    base -- c'est la seule question que pose un calcul `main..tete`. Base
    inconnue (aucun candidat resolu) : on repond conservativement `True`, le
    depot est traite comme tronque (comportement d'avant le correctif).
    """
    if run_git is None:
        run_git = _default_run_git
    try:
        rc, out = run_git(["rev-parse", "--is-shallow-repository"])
    except (OSError, subprocess.SubprocessError):
        return False
    if rc != 0 or (out or "").strip() != "true":
        return False
    boundaries = shallow_boundary_shas(run_git)
    if not boundaries:
        return False
    if base_ref is None:
        base_ref = _resolve_base_ref(run_git)
    if base_ref is None:
        return True
    for sha in boundaries:
        try:
            rc, _ = run_git(["merge-base", "--is-ancestor", sha, base_ref])
        except (OSError, subprocess.SubprocessError):
            return True
        if rc == 0:
            return True
    return False


def _shallow_path(run_git):
    """Le chemin du fichier `.git/shallow` du depot courant, ou None."""
    try:
        rc, out = run_git(["rev-parse", "--git-path", "shallow"])
    except (OSError, subprocess.SubprocessError):
        return None
    if rc != 0:
        return None
    return (out or "").strip() or None


def _raw_parents(sha, run_git):
    """TOUS les parents BRUTS d'un commit, ou None si l'objet est illisible.

    Les parents sont lus dans l'objet commit lui-meme (`git cat-file commit`)
    et non par `rev-list --parents` : sur une frontiere shallow, le graft
    MASQUE les parents a la traversee (mesure : `rev-list --parents` rend le
    seul sha, sans parent), alors que l'objet conserve ses lignes `parent`.
    Ce sont ces lignes qui disent si la frontiere tranche un historique reel
    ou si elle ne masque rien du tout.

    Tous les parents, et pas seulement le premier : le graft coupe la
    traversee de TOUS les parents d'un commit de fusion, donc un second
    parent absent est exactement aussi dangereux a exposer que le premier.
    Une liste vide signifie « racine d'histoire » ; `None` signifie
    « illisible », et les deux ne se confondent pas.
    """
    try:
        rc, out = run_git(["cat-file", "commit", sha])
    except (OSError, subprocess.SubprocessError):
        return None
    if rc != 0:
        return None
    return [
        line.split(" ", 1)[1].strip()
        for line in (out or "").splitlines()
        if line.startswith("parent ")
    ]


def _first_parent(sha, run_git):
    """Le premier parent BRUT d'un commit, ou None (racine d'histoire ou illisible)."""
    parents = _raw_parents(sha, run_git)
    return parents[0] if parents else None


#: Budget de `_ancestry_readable`, en greffes traversees. Un `.git/shallow`
#: reel en porte quelques-unes (6 sur ai-01, 14 au pire mesure) : au-dela de
#: ce budget on ne conclut pas, et l'appelant GARDE la frontiere (fail-safe).
_ANCESTRY_GRAFT_HOPS_MAX = 64


def _ancestry_readable(sha, run_git):
    """L'ascendance COMPLETE de `sha` est-elle presente dans la base d'objets ?

    C'est la condition qui rend sur a retirer une frontiere shallow dont le
    parent est present (#23089, option (a) demandee par le coordinateur) :
    tant que le parcours atteint une VRAIE racine d'histoire sans rencontrer
    d'objet absent, le graft ne masque rien, et le retirer ne coupe aucun
    `git log`.

    La lecture procede par bonds : `rev-list --max-parents=0` rend les
    racines atteignables, greffes COMPRISES (une frontiere declaree y
    apparait comme une racine) ; pour chaque racine on relit ses parents
    BRUTS dans l'objet, et on repart au-dessus de ceux qui en ont encore un.
    Une racine dont les parents bruts sont absents de la liste est une vraie
    racine ; celle qui en porte encore un est une frontiere de graft et se
    detend a son tour. Le parcours ne conclut que lorsque la pile est vide :
    une seule branche qui atteint une vraie racine ne suffit pas, car une
    frontiere de FUSION peut en avoir une complete et l'autre tronquee.

    Ce que la fonction mesure est le graphe de COMMITS, pas les arbres : un
    blob absent ne fait pas echouer un `rev-list` de commits, et le graft
    shallow ne coupe que les commits.

    Lecture impossible, objet absent, budget epuise -> `False`. Le doute ne
    retire jamais rien.
    """
    pending = [sha]
    seen = set()
    hops = 0
    while pending:
        current = pending.pop()
        if current in seen:
            continue  # deja detendu : ne depense pas le budget deux fois
        seen.add(current)
        if hops >= _ANCESTRY_GRAFT_HOPS_MAX:
            return False
        hops += 1
        try:
            rc, out = run_git(["rev-list", "--max-parents=0", current])
        except (OSError, subprocess.SubprocessError):
            return False
        if rc != 0:
            return False  # objet absent ou lecture refusee
        roots = (out or "").split()
        if not roots:
            return False
        for root in roots:
            parents = _raw_parents(root, run_git)
            if parents is None:
                return False
            # Une racine SANS parent brut est une vraie racine d'histoire :
            # rien a detendre. Une racine qui porte encore un parent brut est
            # une frontiere de graft, et son ascendance masquee doit etre
            # parcourue comme les autres. On empile dans les deux cas ; la
            # boucle s'arrete quand la pile est vide, c'est-a-dire quand
            # TOUTES les branches atteintes ont rendu une vraie racine.
            #
            # Ne JAMAIS rendre True des qu'une branche atteint une vraie
            # racine : sur une frontiere de FUSION dont un seul cote est
            # complet, l'autre cote resterait non parcouru et la frontiere
            # serait retiree alors que son ascendance est tronquee (#23089,
            # review du coordinateur, 2026-11-01).
            pending.extend(parents)
    return True


#: Borne de lecture des reflogs dans `_alive_tips`. Un reflog de depot actif
#: peut porter des dizaines de milliers d'entrees ; au-dela de cette borne on
#: garde les plus recentes (l'ordre de `git reflog` est du plus recent au plus
#: ancien), et `_reachable_from` reste fail-safe sur ce qui n'a pas ete lu.
_ALIVE_TIPS_RELOG_MAX = 500


def _alive_tips(run_git):
    """Les tetes depuis lesquelles une racine shallow peut etre ATTEINTE.

    `for-each-ref` ne voit que les refs. Trois temoins d'historique vive lui
    echappent : un `HEAD` detache, le `HEAD` de chaque worktree lie, et les
    entrees de reflog. Une racine atteinte depuis l'un d'eux n'est PAS morte :
    la retirer couperait un `git log` reel (#23110, reserve ai-01 du
    2026-10-28).

    Lecture impossible -> liste vide, et c'est `_reachable_from` qui protege :
    un doute ne retire jamais rien.
    """
    tips: list[str] = []
    seen: set[str] = set()

    def add(raw):
        sha = (raw or "").strip()
        if sha and sha not in seen:
            seen.add(sha)
            tips.append(sha)

    def read(argv):
        try:
            rc, out = run_git(argv)
        except (OSError, subprocess.SubprocessError):
            return ""
        return out or "" if rc == 0 else ""

    add(read(["rev-parse", "HEAD"]))
    # Worktrees lies : un worktree en HEAD detache n'apparait dans aucune ref,
    # et son HEAD est distinct de celui du depot courant. On demande son HEAD
    # par chemin (`-C <path>`) plutot que de lire la ligne `HEAD <sha>` du
    # porcelain (git >= 2.36 seulement) : la meme reponse sur toute version.
    for line in read(["worktree", "list", "--porcelain"]).splitlines():
        if line.startswith("worktree "):
            path = line.split(" ", 1)[1].strip()
            if path:
                add(read(["-C", path, "rev-parse", "HEAD"]))
        elif line.startswith("HEAD "):
            add(line.split(" ", 1)[1])
    # Les reflogs retiennent des tetes qu'aucune ref ne porte plus.
    for line in read(["reflog", "--format=%H", "--all"]).splitlines()[:_ALIVE_TIPS_RELOG_MAX]:
        add(line)
    return tips


def _reachable_from(sha, tip, run_git):
    """`sha` est-il un ancetre de `tip` (lui-meme inclus) ?

    Lecture impossible -> `True` : on ne retire pas une racine sur un doute.
    Retirer une racine VIVANTE casse le parcours qui la traversait, alors que
    laisser une racine morte ne coute qu'un booleen `is-shallow-repository`.
    """
    try:
        rc, _ = run_git(["merge-base", "--is-ancestor", sha, tip])
    except (OSError, subprocess.SubprocessError):
        return True
    return rc == 0


def prune_dead_shallow_roots(run_git=None):
    """Retire les racines shallow MORTES du depot courant.

    Une racine shallow declaree dans `.git/shallow` que plus aucune ref ne
    contient, et dont le parent est absent du depot, ne sert a rien : elle
    ne masque aucun historique (il n'existe pas ici) et elle rend le depot
    "shallow" en permanence -- `git rev-parse --is-shallow-repository` rend
    alors `true` pour toujours, et toute garde fondee sur ce booleen croit
    le depot tronque alors que son historique est complet.

    Mesure (ai-01, 2026-10-28) : six racines de cette sorte dans le clone du
    coordinateur, que `git fetch --unshallow` n'efface pas (il n'a rien a
    approfondir pour elles : leur parent n'existe pas dans ce depot).

    **Second cas, mesure sur le meme clone le 2026-11-01 (option (a) du
    coordinateur)** : les six racines ont en realite leur parent PRESENT, et
    l'ancien critere les gardait toutes -- `--prune-shallow` rendait 0 et
    `is-shallow-repository` restait `true` indefiniment. Une frontiere qu'on
    peut PROUVER sans effet est morte aussi : si tous ses parents bruts sont
    presents et que l'ascendance complete est lisible
    (`_ancestry_readable`), le graft ne masque rien, et le retirer ne coupe
    aucun parcours. Le retrait n'a lieu que sur cette preuve ; parent present
    mais ascendance illisible = frontiere GARDEE.

    Le retrait n'enleve rien : une racine qu'aucune ref ne contient n'est
    atteignable par aucun parcours de l'historique, et soit son parent etait
    deja absent -- le parcours s'arretait la de toute facon --, soit son
    ascendance entiere est presente, donc rien n'est plus masque. Seule la
    reponse "shallow" du depot change.

    **Commande EXPLICITE, jamais appelee par une garde (#23110).** La porte
    pile (`check_adjoint_prevalidation.build_stack_index`) appelait cette
    fonction a chaque passe : une lecture y ecrivait dans `.git/shallow` du
    clone de l'appelant, alors que la liste des racines shallow appartient au
    transport (`.git/shallow` est ce que `fetch` et `clone` ecrivent). Le
    geste se fait donc a la main, par `merge_dwell.py --prune-shallow`, quand
    l'operateur constate qu'un depot complet se declare shallow.

    Le critere d'une racine VIVANTE ne se limite pas aux refs : `HEAD`, le
    `HEAD` de chaque worktree lie et les reflogs comptent aussi, par
    atteignabilite (`merge-base --is-ancestor`) et non par identite.

    Renvoie les SHA retires (liste vide si rien a faire).
    """
    if run_git is None:
        run_git = _default_run_git
    boundaries = shallow_boundary_shas(run_git)
    if not boundaries:
        return []
    tips = _alive_tips(run_git)
    dead: list[str] = []
    for sha in boundaries:
        try:
            rc, out = run_git(
                ["for-each-ref", "--contains", sha, "--format=%(refname)"]
            )
        except (OSError, subprocess.SubprocessError):
            continue
        if rc == 0 and (out or "").strip():
            continue  # une ref contient cette racine : elle vit
        if any(_reachable_from(sha, tip, run_git) for tip in tips):
            continue  # HEAD, HEAD de worktree ou reflog l'atteint : elle vit
        parents = _raw_parents(sha, run_git)
        if not parents:
            # racine d'histoire (ou objet illisible) : rien a retirer
            continue
        try:
            rc, _ = run_git(["cat-file", "-e", parents[0] + "^{commit}"])
        except (OSError, subprocess.SubprocessError):
            continue
        if rc == 0 and not _ancestry_readable(sha, run_git):
            # Un parent est present, mais son ascendance ne l'est pas : la
            # frontiere masque encore un historique tronque, on la GARDE.
            # Mesure (ai-01, 2026-11-01) : les six frontieres du clone du
            # coordinateur ont toutes leur parent present -- c'est ce cas-ci
            # qui laissait `is-shallow-repository` a `true` pour toujours.
            continue
        dead.append(sha)
    if not dead:
        return []
    path = _shallow_path(run_git)
    if not path:
        return []
    keep = [sha for sha in boundaries if sha not in dead]
    if not keep:
        # Plus aucune frontiere : le FICHIER lui-meme doit disparaitre.
        # Mesure (2026-10-28) : `git rev-parse --is-shallow-repository`
        # reste `true` tant que `.git/shallow` EXISTE, meme vide -- le
        # booleen teste la presence du fichier, pas son contenu. Un fichier
        # laisse en place maintiendrait donc le depot "shallow" en
        # permanence, exactement comme les racines mortes qu'on vient de
        # retirer.
        try:
            os.unlink(path)
        except OSError:
            return []
        return dead
    temporary = path + ".prune-tmp"
    try:
        with open(temporary, "w", encoding="utf-8", newline="\n") as handle:
            for sha in keep:
                handle.write(sha + "\n")
        os.replace(temporary, path)
    except OSError:
        try:
            os.unlink(temporary)
        except OSError:
            pass
        return []
    return dead


def _ensure_commit_present(sha, run_git):
    """Best effort : ramener localement un parent absent avant merge-tree.
    Le checkout du gate porte le cote PR ; la base, elle, peut manquer. Un
    echec ici n'est PAS fatal : merge-tree echouera ensuite et la fusion se
    mesurera elle-meme (fail-closed, cf. CR 2026-09-16). L'approfondissement
    qui rendra le merge-base calculable est gere par `_deepen_until_merge_base`.

    #23089 : `--depth=1` sur un depot COMPLET y cree une borne superficielle
    -- le depot passe shallow alors que son historique etait complet, et les
    calculs `main..tete` se mettent a voir des commits deja merges comme
    « propres » (faux « stack top », #22244 et #22252 rendues BLOCKED sur des
    squash deja merges le 2026-10-28). La borne n'a de sens que dans un
    depot dont l'historique de la base est DEJA tronque : le checkout du gate,
    qui est shallow par construction. Ailleurs, le fetch se fait sans
    `--depth` et ne rend jamais le depot superficiel.
    """
    try:
        rc, _ = run_git(["cat-file", "-e", sha + "^{commit}"])
        if rc == 0:
            return
        if base_history_truncated(run_git):
            run_git(["fetch", "--depth=1", "--quiet", "origin", sha])
        else:
            run_git(["fetch", "--quiet", "origin", sha])
    except (OSError, subprocess.SubprocessError):
        pass  # best effort : merge-tree echouera, la fusion se mesurera


#: Bornes de l'approfondissement shallow (CR ai-01 2026-09-16 19:10Z). Le
#: checkout du gate est shallow (actions/checkout@v4 sans fetch-depth, depth
#: 1) : deux parents ramenes en --depth=1 n'ont aucun historique commun, et
#: merge-tree refuse alors de calculer -- le cas legitime update-branch se
#: re-armait. On approfondit par palliers croissants jusqu'au merge-base ;
#: au-dela de la borne, la preuve reste indisponible -> fail-closed.
_DEEPEN_START_DEPTH = 64
_DEEPEN_FACTOR = 2
_DEEPEN_MAX_DEPTH = 1024


def _merge_base_available(first, second, run_git):
    """Le merge-base des deux parents est-il calculable localement ?
    Une execution defaillante vaut indisponible (False), jamais acquise."""
    try:
        rc, _ = run_git(["merge-base", first, second])
        return rc == 0
    except (OSError, subprocess.SubprocessError):
        return False


def _is_shallow_repository(run_git):
    """Le checkout courant est-il shallow ? `git fetch --deepen` y est
    refuse : un merge-base introuvable dans un depot COMPLET est un
    veritable unrelated-histories, qui reste fail-closed sans aucun fetch."""
    try:
        rc, out = run_git(["rev-parse", "--is-shallow-repository"])
        return rc == 0 and (out or "").strip() == "true"
    except (OSError, subprocess.SubprocessError):
        return False


def _deepen_until_merge_base(first, second, run_git):
    """Best effort borne : rendre le merge-base de deux parents calculable.

    `git fetch --deepen=N` approfondit TOUTES les frontieres shallow du
    checkout (y compris les parents ramenes par sha en --depth=1) ; le
    merge-base est re-teste apres chaque pallier. Echec ou cap atteint :
    False -- merge-tree echouera ensuite et la fusion se mesurera elle-meme
    (fail-closed, cf. CR 2026-09-16). Ne leve jamais."""
    if not _is_shallow_repository(run_git):
        return False
    depth = _DEEPEN_START_DEPTH
    while depth <= _DEEPEN_MAX_DEPTH:
        try:
            rc, _ = run_git(
                ["fetch", "--deepen={}".format(depth), "--quiet", "origin"]
            )
            if rc == 0 and _merge_base_available(first, second, run_git):
                return True
        except (OSError, subprocess.SubprocessError):
            return False
        depth *= _DEEPEN_FACTOR
    return False


def _auto_merge_tree(first, second, run_git):
    """Tree OID de l'auto-merge de deux parents, ou None si non calculable.

    `git merge-tree --write-tree` (Git >= 2.38) ecrit l'arbre du merge
    automatique SANS toucher a l'index ni au worktree, et sort non nul en
    cas de conflits -- un merge reel n'existe alors qu'avec une resolution
    d'auteur : jamais content-free. Dans le checkout shallow du gate, les
    parents sont d'abord approfondis par palliers bornes jusqu'a rendre le
    merge-base calculable (CR ai-01 2026-09-16 19:10Z). Toute execution
    defaillante (git absent, OSError, sortie vide) vaut preuve indisponible :
    None, fail-closed."""
    try:
        if not _merge_base_available(first, second, run_git):
            _deepen_until_merge_base(first, second, run_git)
        rc, out = run_git(["merge-tree", "--write-tree", first, second])
    except (OSError, subprocess.SubprocessError):
        return None
    if rc != 0:
        return None
    for line in (out or "").splitlines():
        oid = line.strip()
        if oid:
            return oid
    return None


def _tree_sha(payload):
    commit = payload.get("commit") or {}
    tree = commit.get("tree") or {}
    return tree.get("sha") if isinstance(tree, dict) else None


#: Borne de la remontee first-parent : au-dela, l'etat est pathologique (une
#: PR accumule rarement 50 rafraichissements de base non rebases) et on
#: refuse plutot que de mesurer silencieusement un commit arbitraire.
_MAX_WALK = 50


def last_authoritative_committed_at(
    repo: str,
    sha: str,
    base_sha: str,
    fetch=_gh_json,
    run_git=None,
) -> datetime:
    """#16149 : date de COMMITTER du dernier commit qui modifie le cote PR.

    La remontee est celle de `last_authoritative_sha` ; seule la date du
    commit atteint est rendue ici."""
    current, payload = _walk_authoritative(repo, sha, base_sha, fetch, run_git)
    return _committer_date(payload, current)


def last_authoritative_sha(
    repo: str,
    sha: str,
    base_sha: str,
    fetch=_gh_json,
    run_git=None,
) -> str:
    """SHA du dernier commit qui modifie le cote PR (meme remontee que le
    plancher DWELL). Deux tetes qui rendent le meme SHA ne different que par
    des rafraichissements de base PROUVES content-free : c'est ce que lit
    `merge_ready` pour savoir si l'approbation du coordinateur, posee sur une
    tete anterieure, couvre encore le contenu de la tete courante."""
    current, _payload = _walk_authoritative(repo, sha, base_sha, fetch, run_git)
    return current


def _walk_authoritative(repo, sha, base_sha, fetch, run_git):
    """Remontee first-parent commune au plancher DWELL et a `merge_ready`.

    Remonte la chaine first-parent au-dela des fusions de rafraichissement
    de base PROUVEES content-free : deux parents, le SECOND ancetre de la
    base, ET l'arbre du commit identique a l'auto-merge des parents (CR
    ai-01 2026-09-16 : la forme des parents seule n'exempte pas une
    resolution manuelle de conflit). Le rebase, la fusion d'une sous-branche
    propre, une resolution d'auteur et toute fusion dont la preuve
    d'equivalence est indisponible restent mesurees -- fail-closed."""
    if run_git is None:
        run_git = _default_run_git
    current = sha
    for _ in range(_MAX_WALK):
        payload = _commit_payload(repo, current, fetch)
        parents = payload.get("parents") or []
        if len(parents) == 2:
            second = (parents[1] or {}).get("sha") or ""
            if second and _second_parent_is_base_ancestor(
                repo, second, base_sha, fetch
            ):
                first = (parents[0] or {}).get("sha")
                if not first:
                    raise DwellError(
                        "fusion sans premier parent sur {}".format(current[:12])
                    )
                # CR 2026-09-16 : preuve d'absence de contenu d'auteur.
                # L'arbre du merge doit etre exactement l'auto-merge ; sinon
                # (resolution substantif, conflits, preuve muette) la fusion
                # se mesure elle-meme.
                _ensure_commit_present(first, run_git)
                _ensure_commit_present(second, run_git)
                auto_tree = _auto_merge_tree(first, second, run_git)
                merge_tree = _tree_sha(payload)
                if auto_tree and merge_tree and auto_tree == merge_tree:
                    current = first
                    continue
                return current, payload
        return current, payload
    raise DwellError(
        "chaine first-parent de plus de {} fusions de base depuis {} "
        "-- etat pathologique, refus".format(_MAX_WALK, sha[:12])
    )


def _pr_payload(repo: str, pr_number: int, fetch=_gh_json) -> dict:
    payload = fetch("repos/{}/pulls/{}".format(repo, pr_number))
    if not isinstance(payload, dict):
        raise DwellError("payload PR inattendu pour #{}".format(pr_number))
    return payload


def _labels_carry_waiver(payload: dict) -> bool:
    names = {
        (label or {}).get("name", "")
        for label in (payload.get("labels") or [])
        if isinstance(label, dict)
    }
    return WAIVER_LABEL in names


def is_waived(repo: str, pr_number: int, fetch=_gh_json) -> bool:
    """La PR porte-t-elle `merge-dwell-waived` ?

    Un echec de lecture n'est PAS une derogation : il remonte en `DwellError`
    et le gate refuse (rule 1). Lire « pas de label » d'une API muette est
    exactement le zero propre que le harnais interdit de croire.

    #18686 : ceci ne dit PAS que la derogation JOUE -- seulement que le label
    est pose. La condition (main rouge) est verifiee par `_main_red_motif`,
    consommee par `check`.
    """
    return _labels_carry_waiver(_pr_payload(repo, pr_number, fetch))


def _default_branch(repo: str, fetch=_gh_json) -> str:
    payload = fetch("repos/{}".format(repo))
    branch = payload.get("default_branch") if isinstance(payload, dict) else None
    if not branch:
        raise DwellError("pas de default_branch sur {}".format(repo))
    return branch


#: Liste des workflows dont un rouge sur `main` peut legitimer la derogation
#: `merge-dwell-waived`. Chaque entree est le couple (yml_path, display_name) :
#: le `yml_path` est l'identifiant du fichier sous `.github/workflows/` (utilise
#: dans l'API `actions/workflows/{file}/runs`) ; le `display_name` est le nom
#: GitHub visible dans la liste des workflow-runs (celui qu'on retrouve dans
#: la reponse `workflow_runs[].name`). La liste reste explicite et documentee
#: pour qu'une derive silencieuse d'un nom GitHub ne fausse pas le verdict.
#:
#: Pourquoi cette liste : un workflow path-filtre `scripts/**` peut etre
#: rouge sur main sans rougir la PR candidate -- sauf a toucher les memes
#: paths, la PR ne declenche pas le workflow et ne voit donc jamais ce
#: rouge. C'est precisement le cas que la derogation vise : main est
#: reellement rouge, mais la PR n'a aucun moyen de le voir. A ce jour
#: (2026-10-04) le seul workflow repondant a ce critere est `Scripts &
#: Notebook-Tools Tests` (scripts-tests.yml : declencheurs push main ET
#: pull_request, tous deux filtres par la MEME liste de chemins -- les deux
#: incluent `tests/**`, `pytest.ini`, `.github/workflows/**` et une poignee
#: de sujets hors `scripts/` (registre d'attributions, `conway_lean/**`,
#: `prosody_lab/syllable_pitch.py`, `Track2-GoogleADK/**`, ...). Une PR qui
#: ne touche AUCUN de ces chemins ne le declenche sur aucun des deux. #19069
#: corrige ici deux mentions erronees successives : « pas de trigger
#: pull_request » (version initiale) puis « une PR hors `scripts/**` », qui
#: ignorait `tests/**` et `.github/workflows/**` (releve Hermes).
MAIN_RED_WORKFLOWS = (
    # (yml_path, display_name)
    ("scripts-tests.yml", "Scripts & Notebook-Tools Tests"),
)

#: #19180 : conclusions qui portent un verdict ROUGE sur main. `timed_out`
#: (le workflow a epuise son temps) et `startup_failure` (il n'a pas pu
#: demarrer) sont des rouges reels : main n'a pas rendu de vert. Seules les
#: conclusions SANS verdict -- `cancelled`, `skipped`, et toute autre valeur
#: hors des deux tuples -- se sautent (#19069).
MAIN_RED_CONCLUSIONS = ("failure", "timed_out", "startup_failure")
MAIN_VERDICT_CONCLUSIONS = ("success",) + MAIN_RED_CONCLUSIONS


def _main_red_motif(repo: str, fetch=_gh_json) -> "str | None":
    """#18686 + #18790 + #18796 : motif de rouge observable sur la branche
    par defaut, ou None si vert.

    Pour chaque workflow de `MAIN_RED_WORKFLOWS`, lit le DERNIER run
    REELLEMENT CONCLU sur `main` via l'API workflow-directe
    `repos/{repo}/actions/workflows/{yml_path}/runs?branch={branch}&event=push
    &status=completed&per_page=10`, puis saute cote client les runs sans
    verdict (`cancelled`, `skipped` : `status=completed` les inclut, et en
    passe de merge en rafale la concurrence du workflow annule les runs
    intermediaires -- le dernier run rendu masquait alors le rouge reel,
    #19069). Le premier run a verdict rendu -- `success`, ou un rouge de
    `MAIN_RED_CONCLUSIONS` (#19180 : `timed_out` et `startup_failure` en
    sont) -- est le verdict le plus frais de ce workflow sur main,
    **independamment de son anciennete**
    (limite de la fenetre globale du commit de tete : un merge non lie aux
    paths du workflow peut evict le run hors de la fenetre de 100 -- CR
    ai-01 2026-10-02 18:55Z sur #18796).

    Pli latest-wins par `created_at` parmi les workflows consideres : un seul
    verdict de rouge suffit, le plus frais gagne. La liste explicite reste
    documentee plus haut ; un nom GitHub derive rend `latest` vide, jamais
    un faux positif.

    Renvoie le motif releve (nom GitHub du workflow en echec + id du run)
    pour que le message de derogation reste justifiable a la relecture.

    Pourquoi PAS les check-runs du commit de tete (l'ancienne approche) :
    `.github/workflows/pr-gate.yml` ne tourne que sur `pull_request`, donc
    il n'y a aucun check-run `PR gate` sur la tete de main -- `latest`
    reste `None`, et la derogation ne s'ouvrait jamais, meme quand main
    etait reellement rouge (mesure du 2026-10-02 par myia-ai-01, tete
    `d8b7bb9628`, aucun check-run `PR gate`).

    Pourquoi PAS `actions/runs?branch=main&per_page=100` (l'approche
    fenetre globale, 32968cb51) : la fenetre de 100 runs sur main couvre
    typiquement 30-40 minutes, et chaque merge ajoute une vingtaine de
    runs d'autres workflows. Apres 35 a 40 minutes sans merge sous
    `scripts/**`, le dernier run de `Scripts & Notebook-Tools Tests` sort
    de la fenetre -- `latest` redevient `None`, et un main reellement
    rouge redevient invisible (mesure du 2026-10-02 18:55Z, tete
    `32968cb51` : 100 runs sur main couvraient 35 minutes seulement).

    Une couleur ILLISIBLE ne vaut PAS rouge : None, la derogation ne
    franchise jamais sur une absence de preuve -- fail-closed, comme
    l'exemption de rafraichissement de base. Pas de DwellError ici : un
    label dont la condition ne peut pas etre prouvee retombe sur le
    plancher NORMAL, le gate continue de mesurer sans refuser.
    """
    try:
        branch = _default_branch(repo, fetch)
    except DwellError:
        return None
    latest = None
    for _yml, display_name in MAIN_RED_WORKFLOWS:
        try:
            payload = fetch(
                "repos/{}/actions/workflows/{}/runs"
                "?branch={}&event=push&status=completed&per_page=10".format(
                    repo, _yml, branch
                )
            )
        except DwellError:
            return None
        entries = (
            payload.get("workflow_runs") if isinstance(payload, dict) else None
        )
        if not isinstance(entries, list) or not entries:
            continue
        # #19069 : `status=completed` inclut les runs `cancelled`/`skipped`.
        # En passe de merge en rafale, la concurrence du workflow annule les
        # runs intermediaires et le dernier run rendu n'a alors AUCUN
        # verdict : la derogation restait fermee alors que le dernier run
        # reellement conclu sur main etait rouge. On saute les runs sans
        # verdict et on prend le premier reellement conclu. #19180 : un
        # `timed_out` ou un `startup_failure` EST un verdict (rouge) ; le
        # sauter remontait jusqu'au vert precedent et declarait main vert.
        run = next(
            (
                r
                for r in entries
                if isinstance(r, dict)
                and r.get("conclusion") in MAIN_VERDICT_CONCLUSIONS
            ),
            None,
        )
        if run is None:
            continue
        # Garde-fou : le display_name GitHub doit matcher le display_name
        # canonique de l'entree. Un changement de nom cote GitHub ne fait
        # PAS evoluer silencieusement le verdict : on ignore le run.
        if run.get("name") != display_name:
            continue
        if run.get("conclusion") not in MAIN_RED_CONCLUSIONS:
            continue
        created = run.get("created_at") or ""
        if latest is None or created > (latest.get("created_at") or ""):
            latest = run
    if latest is None:
        return None
    conclusion = latest.get("conclusion")
    # Le motif nomme la conclusion quand ce n'est pas un `failure` ordinaire,
    # pour que la derogation reste justifiable a la relecture (#19180).
    qualifier = "" if conclusion == "failure" else " ({})".format(conclusion)
    return "main rouge: workflow `{}` en echec{} sur {} (run {})".format(
        latest.get("name") or "?",
        qualifier,
        branch,
        (latest.get("html_url") or "").rsplit("/", 1)[-1] or "?",
    )


def _latest_check_runs(repo: str, ref: str, fetch=_gh_json, max_pages: int = 5):
    """Dernier check-run par NOM sur `ref`, ou None si la couleur est illisible.

    Pli latest-wins par `started_at` : la liste rendue par l'API contient
    aussi les tentatives supersedees. Lire la premiere entree est le defaut
    que #16765 a mesure (six rouges tous supersedes sur un meme head) : un
    rouge perime rouvrirait la derogation sur un organe deja vert, et un
    vert perime l'ouvrirait sur un organe encore rouge.

    Pagination : une tete de PR de carnets porte 129 check-runs mesures
    (review 5622234166) -- au-dela de `per_page=100`, le nom-preuve peut
    vivre en page 2 et la voie se fermer a tort, precisement sur la
    population visee. On suit les pages tant qu'une page est pleine,
    bornees a `max_pages` (500 check-runs).

    Fail-closed : payload illisible -> None, jamais un dictionnaire vide qui
    se lirait « aucun organe rouge » (une couleur illisible ne vaut pas vert,
    cf #18686).
    """
    all_runs: "list[dict]" = []
    page = 1
    while page <= max_pages:
        url = "repos/{}/commits/{}/check-runs?per_page=100".format(repo, ref)
        if page > 1:
            url += "&page={}".format(page)
        try:
            payload = fetch(url)
        except DwellError:
            return None
        if not isinstance(payload, dict):
            return None
        runs = payload.get("check_runs")
        if not isinstance(runs, list):
            return None
        all_runs.extend(run for run in runs if isinstance(run, dict))
        if len(runs) < 100:
            break
        page += 1
    latest: "dict[str, dict]" = {}
    for run in all_runs:
        name = run.get("name")
        if not name:
            continue
        previous = latest.get(name)
        if previous is None or (
            (run.get("started_at") or "") >= (previous.get("started_at") or "")
        ):
            latest[name] = run
    return latest


def _pr_earlier_red_organs(repo: str, pr_number: int, head_sha: str,
                           fetch=_gh_json, max_commits: int = 10):
    """Organes rouges a des commits ANTERIEURS de la PR (#22085, review).

    Un organe qui ne tourne que sur `pull_request` n'a AUCUN check-run a la
    tete de la branche par defaut : sa couleur « de main » n'existe pas la
    ou une lecture des check-runs de main la cherchait (mesure review
    5622234166 : 12 check-runs push sur la tete de main -- Pages, Quarto,
    CodeQL -- aucun `Live-read freshness`). Le rouge se voit sur les PRs ;
    la mesure reelle de ce que CETTE PR a repare est donc son propre
    passe : chaque push re-poste les check-runs sur la nouvelle tete, les
    commits anterieurs gardent les leurs.

    Retourne {nom: check-run rouge} (premier rouge rencontre par commit,
    base -> tete). Une lecture impossible rend un dict vide : ce segment
    ne prouve rien, il ne deroge pas -- fail-closed.
    """
    try:
        payload = fetch("repos/{}/pulls/{}/commits?per_page={}".format(
            repo, pr_number, max_commits))
    except DwellError:
        return {}
    if not isinstance(payload, list):
        return {}
    shas: "list[str]" = []
    for entry in payload:
        if isinstance(entry, dict) and entry.get("sha"):
            shas.append(entry["sha"])
    red: "dict[str, dict]" = {}
    for sha in shas:
        if sha == head_sha:
            continue
        runs = _latest_check_runs(repo, sha, fetch)
        if not runs:
            continue
        for name, run in runs.items():
            if (run.get("conclusion") in MAIN_RED_CONCLUSIONS
                    and name not in red):
                red[name] = run
    return red


def _repair_motif(repo: str, head_sha: "str | None", pr_number: "int | None",
                  fetch=_gh_json):
    """#22085 : motif de derogation quand la PR REPARE un rouge.

    Le rouge de #22018 (`Live-read freshness`) n'est pas visible « depuis la
    PR » au sens de #18686 : l'organe tourne aussi sur `pull_request`, donc
    toutes les PRs le voient -- mais la PR qui le repare devait attendre son
    plancher de 120 min comme les autres, et `MAIN_RED_WORKFLOWS` ne le
    couvrait pas.

    Deux sources de rouge, toutes deux reelles et fail-closed :

    1. les organes ROUGES a la tete de la branche par defaut, pli
       latest-wins -- mesure reelle pour les organes `push` (Pages, Quarto,
       CodeQL...) ;
    2. les organes rouges a des commits ANTERIEURS de cette PR
       (`_pr_earlier_red_organs`) -- mesure reelle pour les organes qui ne
       tournent que sur `pull_request` : jamais presents sur main, leur
       rouge ne se lit que sur les PRs.

    La derogation s'ouvre sur le premier organe que la PR rend `success` a
    sa tete, A CONDITION que ce vert soit POSTERIEUR au rouge (review,
    point 2 : un vert anterieur au rouge ne prouve aucune reparation --
    une PR sans rapport garde son plancher). Le label seul ne suffit donc
    jamais, et la preuve porte sur l'organe precis -- pas sur une couleur
    globale.

    Limite assumee : l'API ne dit pas quels organes sont BLOQUANTS. Un
    organe advisory rouge peut donc ouvrir la voie -- mais seulement pour
    une PR qui le fait passer au vert, ce qui reste une reparation reelle.
    """
    if not head_sha or pr_number is None:
        return None
    try:
        branch = _default_branch(repo, fetch)
    except DwellError:
        return None
    main_latest = _latest_check_runs(repo, branch, fetch)
    if main_latest is None:
        return None
    reds: "dict[str, tuple[dict, str]]" = {}
    for name, run in main_latest.items():
        if run.get("conclusion") in MAIN_RED_CONCLUSIONS:
            reds[name] = (run, "tete de {}".format(branch))
    for name, run in _pr_earlier_red_organs(
            repo, pr_number, head_sha, fetch).items():
        if name not in reds:
            reds[name] = (run, "commit anterieur de la PR")
    if not reds:
        return None
    head_latest = _latest_check_runs(repo, head_sha, fetch)
    if not head_latest:
        return None
    for name in sorted(reds):
        head_run = head_latest.get(name)
        if not (isinstance(head_run, dict)
                and head_run.get("conclusion") == "success"):
            continue
        red_run, where = reds[name]
        if (head_run.get("started_at") or "") <= (red_run.get("started_at") or ""):
            # Vert ANTÉRIEUR au rouge : la PR a verdi avant que le rouge
            # n'arrive -- ce n'est pas elle qui l'a repare.
            continue
        return (
            "organe `{}` en echec ({}, check-run {}) -- repare a la tete "
            "de la PR (check-run {} poste apres le rouge)".format(
                name,
                where,
                red_run.get("id") or "?",
                head_run.get("id") or "?",
            )
        )
    return None


def check(
    repo: str,
    sha: str,
    pr_number: "int | None",
    dwell_min: float = DEFAULT_DWELL_MIN,
    now: "datetime | None" = None,
    fetch=_gh_json,
    run_git=None,
) -> tuple[bool, str]:
    """Verdict reseau complet. Renvoie `(ok, message)`.

    `pr_number is None` desactive le plancher : le gate tourne alors hors
    contexte de PR (`workflow_dispatch`), ou son check-run atterrit sur le
    commit de la branche par defaut et ne peut de toute facon pas bouger le
    `mergeState` d'une PR (documente en tete de `pr-gate.yml`). Y appliquer
    un plancher rougirait la branche par defaut sans rien gater.

    #18686 : le label `merge-dwell-waived` ne leve le plancher que si `main`
    est VERIFIE rouge (`_main_red_motif`). Sinon le message le dit
    (« label present, condition non remplie ») et le plancher s'applique.
    """
    if dwell_min <= 0 or pr_number is None:
        return True, "dwell non applicable (hors contexte de PR ou desactive)"
    pr = _pr_payload(repo, pr_number, fetch=fetch)
    waived = _labels_carry_waiver(pr)
    waiver_motif = ""
    unmet_note = ""
    if waived:
        motif = _main_red_motif(repo, fetch)
        if motif is None:
            # #22085 : seconde voie. Le rouge que toutes les PRs voient (un
            # organe qui tourne aussi sur `pull_request`) n'ouvre la
            # derogation que si CETTE PR prouve qu'elle le repare a sa tete.
            motif = _repair_motif(repo, sha, pr_number, fetch)
        if motif is None:
            waived = False
            unmet_note = (
                " -- label `{}` present mais condition non remplie "
                "(main vert, rouge non repare par cette PR, ou couleur "
                "illisible) : plancher applique".format(WAIVER_LABEL)
            )
        else:
            waiver_motif = motif
    base_sha = ((pr.get("base") or {}).get("sha") or "")
    if not base_sha:
        raise DwellError("pas de base.sha sur la PR #{}".format(pr_number))
    committed = last_authoritative_committed_at(
        repo, sha, base_sha, fetch=fetch, run_git=run_git
    )
    ok, _remaining, message = evaluate(
        committed, now or datetime.now(timezone.utc), dwell_min, waived,
        waiver_motif=waiver_motif,
    )
    return ok, message + unmet_note


if __name__ == "__main__":  # pragma: no cover - commande manuelle
    import argparse
    import sys

    parser = argparse.ArgumentParser(
        description=__doc__.splitlines()[0] if __doc__ else "merge_dwell"
    )
    parser.add_argument(
        "--prune-shallow",
        action="store_true",
        help="#23110 : retirer les racines shallow MORTES du depot courant "
        "(commande EXPLICITE, a lancer a la main -- aucune garde ne "
        "l'appelle, `git fetch --unshallow` ne les efface pas). Les SHA "
        "retires sortent sur stdout, un par ligne.",
    )
    args = parser.parse_args()
    if not args.prune_shallow:
        parser.error("exactly one of --prune-shallow is required")
    removed = prune_dead_shallow_roots()
    for sha in removed:
        print(sha)
    print(
        "racines shallow mortes retirees : {}".format(len(removed)),
        file=sys.stderr,
    )
    raise SystemExit(0)
