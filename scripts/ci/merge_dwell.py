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
  * `pr-gate-stale-sweep.yml` -- balayage horaire (`cron: '7 * * * *'`) qui
    selectionne exactement « une jambe `PR gate` rouge alors que tout le reste
    est vert », c'est-a-dire l'etat qu'une PR en attente de plancher presente,
    et **re-lance le run d'origine** (un POST d'un check-run homonyme atterrit
    dans une suite etrangere et GitHub ANDe les deux -- mesure #11519).

Consequence a assumer et a dire : le plancher est un PLANCHER, pas une
horloge. Une PR devient mergeable au premier balayage horaire suivant
l'ecoulement des 2 h -- donc entre 2 h 00 et 3 h 00 apres son dernier commit,
pas a 2 h 00 pile.

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
LE COTE PR : la chaine first-parent est remontee au-dela des fusions dont le
SECOND parent est un ancetre de la base (la forme exacte d'un rafraichissement
de base). Un rebase, lui, reecrit les commits d'auteur : single-parent, il
reste mesure -- le comportement voulu ci-dessus. Une fusion dont le second
parent n'est PAS sur la base (l'auteur incorpore sa propre sous-branche)
introduit du contenu d'auteur : elle reste mesuree aussi. Une filiation
illisible ne vaut pas reconnaissance de rafraichissement : la fusion se
mesure alors elle-meme (comportement d'avant #16149 -- plus strict, jamais
plus lache).

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

#: Label qui leve le plancher sur une PR donnee.
WAIVER_LABEL = "merge-dwell-waived"


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
    lift = (committed_at + timedelta(minutes=dwell_min)).strftime(
        "%Y-%m-%dT%H:%M:%SZ"
    )
    return False, remaining, (
        "tete du {}, {:.0f} min -- plancher {:.0f} min, reste {:.0f} min, "
        "leve au premier balayage suivant {}. "
        "Le balayage horaire (pr-gate-stale-sweep.yml, cron '7 * * * *') "
        "re-agrege cette jambe des que le plancher est ecoule ; aucun geste "
        "manuel n'est requis. Urgence (main rouge) : poser le label `{}` sur "
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


#: Borne de la remontee first-parent : au-dela, l'etat est pathologique (une
#: PR accumule rarement 50 rafraichissements de base non rebases) et on
#: refuse plutot que de mesurer silencieusement un commit arbitraire.
_MAX_WALK = 50


def last_authoritative_committed_at(
    repo: str, sha: str, base_sha: str, fetch=_gh_json
) -> datetime:
    """#16149 : date de COMMITTER du dernier commit qui modifie le cote PR.

    Remonte la chaine first-parent au-dela des fusions de rafraichissement
    de base : un commit a deux parents dont le SECOND est un ancetre de la
    base n'introduit aucun contenu d'auteur (son delta appartient a la base,
    deja gatee). Le rebase et la fusion d'une sous-branche propre restent
    mesures -- voir la section #16149 du docstring de module."""
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
                current = first
                continue
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
        repo, sha, base_sha, fetch=fetch
    )
    ok, _remaining, message = evaluate(
        committed, now or datetime.now(timezone.utc), dwell_min, waived
    )
    return ok, message
