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
"""

from __future__ import annotations

import json
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
) -> tuple[bool, float, str]:
    """Decide si le plancher est ecoule. Fonction PURE (testable sans reseau).

    Renvoie `(ok, minutes_restantes, message)`.

    Une horloge qui recule -- tete datee dans le futur, par decalage de machine
    ou date de committer forgee -- rend l'age negatif : le plancher n'est alors
    PAS ecoule, et le message le dit. Traiter le futur comme « tres vieux »
    serait la seule facon de transformer ce garde en passe-plat.
    """
    if dwell_min <= 0:
        return True, 0.0, "dwell desactive (--dwell-min <= 0)"
    if waived:
        return True, 0.0, (
            "dwell leve par le label `{}` "
            "(plancher {:.0f} min non applique)".format(WAIVER_LABEL, dwell_min)
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


def _ensure_commit_present(sha, run_git):
    """Best effort : ramener localement un parent absent avant merge-tree.
    Le checkout du gate porte le cote PR ; la base, elle, peut manquer. Un
    echec ici n'est PAS fatal : merge-tree echouera ensuite et la fusion se
    mesurera elle-meme (fail-closed, cf. CR 2026-09-16). L'approfondissement
    qui rendra le merge-base calculable est gere par `_deepen_until_merge_base`."""
    try:
        rc, _ = run_git(["cat-file", "-e", sha + "^{commit}"])
        if rc == 0:
            return
        run_git(["fetch", "--depth=1", "--quiet", "origin", sha])
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
                return _committer_date(payload, current)
        return _committer_date(payload, current)
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
    """
    return _labels_carry_waiver(_pr_payload(repo, pr_number, fetch))


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
    """
    if dwell_min <= 0 or pr_number is None:
        return True, "dwell non applicable (hors contexte de PR ou desactive)"
    pr = _pr_payload(repo, pr_number, fetch=fetch)
    waived = _labels_carry_waiver(pr)
    base_sha = ((pr.get("base") or {}).get("sha") or "")
    if not base_sha:
        raise DwellError("pas de base.sha sur la PR #{}".format(pr_number))
    committed = last_authoritative_committed_at(
        repo, sha, base_sha, fetch=fetch, run_git=run_git
    )
    ok, _remaining, message = evaluate(
        committed, now or datetime.now(timezone.utc), dwell_min, waived
    )
    return ok, message
