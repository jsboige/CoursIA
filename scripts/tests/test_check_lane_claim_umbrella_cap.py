#!/usr/bin/env python3
"""#22500 point 3 -- le plafond hebdomadaire des EPICs s'applique au claim.

Fichier NEUF, volontairement : #22457 et #22413 sont ouvertes sur
`scripts/tests/test_check_lane_claim.py`, et une collision de test coute un
cycle de rebase pour rien (le fichier source, lui, reste unique).

Ce que ces tests tiennent, dans l'ordre de la demande (commentaire 6409466826
de #22500) CORRIGEE par #26414 (decision ai-01 du 2026-11-13, option 1
« filles existantes hors plafond, pas du tout ») :

  - un claim pose directement sur l'EPIC obeit au plafond : la visite d'une
    AUTRE lane de moins de 7 jours le bloque, avec la cause
    `PLAFOND EPIC (#22500)` ;
  - une fille d'EPIC n'est PLUS plafonnee -- servir un sous-grain DEJA OUVERT
    est permis par #22500 point 2, la creation reste cappee cote picker ;
    criteres de sortie : EPIC visite et fille creee il y a moins de 7 jours,
    claim d'une autre lane sur la fille -> cause None ;
  - l'issue elle-meme ne compte pas comme sa propre visite (sinon le premier
    claim legitime de la semaine se bloquerait) ;
  - une classe `consolidation` est exemptee ;
  - ZERO appel reseau pour toute issue qui n'est pas elle-meme un umbrella
    (fille comprise) -- la borne de cout du coordinateur (274 s pour la
    commande des lanes) se mesure ici ;
  - une lecture qui echoue ne bloque pas et se NOMME (pas de faux
    « plafond respecte ») ;
  - la cause rendue est le litteral de l'organe, pas une seconde ecriture.

Run: python -m pytest scripts/tests/test_check_lane_claim_umbrella_cap.py
"""
import datetime as dt
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_lane_claim as clc
import pick_idle_grain as pig

# Horloge figee pour les tests qui injectent `now` : les horodatages des
# fixtures sont relatifs a cette date, donc les ages calcules sont exacts.
NOW = dt.datetime(2026, 10, 26, 12, 0, tzinfo=dt.UTC)
CAUSE_PREFIX = "PLAFOND EPIC (#22500)"
SERRE100 = 16334  # l'EPIC de la mesure fondatrice (11 PRs ouvertes en 10 j)
LANE = "myia-ai-01:CoursIA-2"        # la lane qui interroge
OTHER_LANE = "myia-po-2024:CoursIA"  # une autre lane du cluster


# --- helpers -----------------------------------------------------------------

def iso(**delta) -> str:
    """ISO 8601 UTC (forme `createdAt` serveur) decale de `delta` depuis NOW."""
    return (NOW - dt.timedelta(**delta)).strftime("%Y-%m-%dT%H:%M:%SZ")


def comment(body, created_at, author="jsboige"):
    return {"body": body, "createdAt": created_at,
            "author": {"login": author}, "url": None}


def issue(number, *, title="t", body="", labels=None, comments=(), **extra):
    d = {"number": number, "title": title, "body": body,
         "comments": list(comments)}
    if labels is not None:
        d["labels"] = [{"name": name} for name in labels]
    d.update(extra)
    return d


def pool_item(number, title, created_at, body=""):
    """Forme d'un element de `fetch_pool` (cle `created_at`, LABELS bruts)."""
    return {"number": number, "title": title, "body": body,
            "created_at": created_at, "labels": []}


def epic(number=SERRE100, *, labels=("EPIC",), comments=(), title=None):
    return issue(number, title=title or f"[EPIC #{number} - serre] umbrella",
                 labels=list(labels), comments=comments)


def daughter(number=22617, *, parent=SERRE100, created_at=None,
             claimed=True):
    """Une fille d'EPIC creee puis claimee dans la minute (forme #22609).

    ``claimed=False`` modelise le controle PRE-claim (le geste L898 qu'une
    lane lance AVANT de poster son marqueur) : depuis l'arbitrage #22687 du
    2026-11-08, la lane qui tient deja un claim actif sur N ne mesure plus le
    plafond -- les controles negatifs « une NOUVELLE visite est bloquee » se
    jouent donc sans claim preexistant.
    """
    comments = []
    if claimed:
        comments.append(comment("[CLAIMED] lane myia-ai-01:CoursIA-2 -- x",
                                created_at or iso(hours=1)))
    return issue(number, title=f"[#{parent} - tranche {number}] sous-grain",
                 body=f"Part of #{parent}\n\nGrain: DEEP/lean -- lane x:y",
                 comments=comments)


class Loaders:
    """Parents + pool injectes ; chaque appel est COMPTE (la borne se mesure)."""

    def __init__(self, parents=None, pool=None, pool_error=None):
        self.parents = parents or {}
        self.pool = pool if pool is not None else []
        self.pool_error = pool_error
        self.calls = []

    def parent(self, number):
        self.calls.append(("parent", number))
        if number not in self.parents:
            raise RuntimeError(f"parent #{number} absent de la fixture")
        return self.parents[number]

    def pool_(self):
        self.calls.append(("pool", None))
        return self.pool, self.pool_error

    @property
    def parent_calls(self):
        return [n for kind, n in self.calls if kind == "parent"]

    @property
    def pool_calls(self):
        return len([1 for kind, _ in self.calls if kind == "pool"])


def run(payload, loaders, **kwargs):
    """`_run_check` avec le plafond cable sur des lectures injectees.

    La lane qui interroge est passee a l'organe : #25443 exclut du plafond
    le propre marqueur de cette lane quand N est l'EPIC lui-meme.
    """
    return clc._run_check(
        payload, LANE,
        epic_cap=True,
        epic_cap_probe=lambda p: clc.epic_visit_cap(
            p, now=NOW, parent_loader=loaders.parent,
            pool_loader=loaders.pool_, my_lane=LANE),
        **kwargs,
    )


def report(capsys) -> dict:
    """Le rapport JSON imprime par `_run_check` (il precede la phrase verdict)."""
    out = capsys.readouterr().out
    data, _ = json.JSONDecoder().raw_decode(out[out.index("{"):])
    return data


# --- le scenario fondateur, corrige par #26414 --------------------------------

def test_daughter_of_epic_visited_this_week_is_not_capped(capsys):
    """#26414 (option 1, ai-01) : les filles existantes sont HORS plafond.

    Avant #26414, une soeur creee il y a 2 jours bloquait le claim de #22617
    avec la cause `PLAFOND EPIC (#22500)` -- c'etait le controle negatif exige
    par #22500 point 3. Servir un sous-grain DEJA OUVERT est permis par #22500
    point 2 : la cause est None et la mesure ne coute AUCUN appel (ni parent,
    ni pool).
    """
    payload = daughter(22617, claimed=False)
    loaders = Loaders(
        parents={SERRE100: epic()},
        pool=[
            pool_item(22609, f"[#{SERRE100} - tranche 22609] soeur", iso(days=2)),
            pool_item(22617, f"[#{SERRE100} - tranche 22617] moi", iso(hours=1)),
        ],
    )
    rc = run(payload, loaders)
    assert rc == 0
    data = report(capsys)
    assert data["blocked"] is False
    assert data["epic_visit_cap"] is None
    assert data["epic_visit_cap_error"] is None
    assert loaders.calls == []


def test_exit_criterion_daughter_created_by_the_visit_claimed_elsewhere(capsys):
    """Le critere de sortie de #26414 : meme le pire scenario ne plafonne plus.

    EPIC visite il y a moins de 7 jours, fille creee PAR cette visite, et un
    claim d'une AUTRE lane pose sur la fille : le controle de notre lane sur
    la fille rend cause None. Le claim etranger est age de 3 jours (perime au
    seuil de 48 h) pour que ce qui est verifie ici soit bien le plafond, pas
    le blocage de lane.
    """
    payload = daughter(22617, claimed=False)
    payload["comments"].append(comment(
        f"[CLAIMED] lane {OTHER_LANE} -- tranche 22617", iso(days=3)))
    loaders = Loaders(
        parents={SERRE100: epic(comments=[comment(
            f"[CLAIMED] lane {OTHER_LANE} -- visite de la semaine",
            iso(days=2, hours=12))])},
        pool=[pool_item(22609, f"[#{SERRE100} - tranche 22609] soeur",
                        iso(days=2, hours=12))],
    )
    rc = run(payload, loaders, stale_threshold=48)
    assert rc == 0
    data = report(capsys)
    assert data["epic_visit_cap"] is None
    assert data["blocked"] is False
    assert loaders.calls == []


def test_cause_is_the_organ_literal_not_a_copy(capsys):
    """La cause est rendue par `umbrella_visit_cause`, pas re-ecrite ici.

    On la recalcule a la main avec l'organe, sur la charge que le gate lui a
    passee (depuis #26414, le seul sujet est l'EPIC N lui-meme) : toute
    divergence (litteral change d'un cote seulement) rougit.
    """
    payload = epic(comments=[comment(
        f"[RELEASED] lane {OTHER_LANE} -- tranche rendue", iso(days=3))])
    assert run(payload, Loaders(pool=[])) == 1
    got = report(capsys)["epic_visit_cap"]
    expected = pig.umbrella_visit_cause(
        {"number": SERRE100, "title": None, "labels": [{"name": "EPIC"}],
         "klass": "umbrella", "last_claim_stamp": iso(days=3),
         "last_claim_marker": "RELEASED", "last_child_stamp": None},
        now=NOW,
    )
    assert got == expected


def test_the_claimed_issue_is_not_its_own_visit(capsys):
    """Sans cette exclusion, l'EPIC present dans son propre pool se bloquerait.

    Depuis #26414 le sujet est N lui-meme : l'exclusion se joue sur le pool,
    ou N apparait comme fille d'un EPIC plus grand creee il y a 1 minute.
    """
    payload = epic()
    loaders = Loaders(pool=[pool_item(SERRE100, f"[#99000 - moi] moi",
                                       iso(minutes=1))])
    rc = run(payload, loaders)
    assert rc == 0
    data = report(capsys)
    assert data["epic_visit_cap"] is None
    assert data["blocked"] is False
    assert loaders.pool_calls == 1 and loaders.parent_calls == []


def test_second_daughter_within_the_week_is_not_capped(capsys):
    """Miroir du fondateur corrige : la deuxieme fille de la semaine passe.

    Avant #26414 c'etait « la deuxieme fille voit la premiere : c'est tout le
    defaut » ; la creation reste cappee cote PICKER, pas au claim des filles.
    """
    loaders = Loaders(
        parents={SERRE100: epic()},
        pool=[
            pool_item(22619, f"[#{SERRE100} - a] a", iso(minutes=1)),
            pool_item(22620, f"[#{SERRE100} - b] b", iso(hours=2)),
        ],
    )
    assert run(daughter(22620, claimed=False), loaders) == 0
    data = report(capsys)
    assert data["epic_visit_cap"] is None and data["blocked"] is False
    assert loaders.calls == []


def test_resume_of_own_active_claim_skips_the_cap(capsys):
    """#22687 -- le cas mesure par ai-01 le 2026-11-08 sur #23499.

    La lane tient un `[CLAIMED]` actif sur la fille depuis AVANT la visite qui
    arme le plafond (claim 9 j, rendu de main sur l'EPIC 0,7 j) et repare sa
    PR ouverte : le plafond SAUTE, cause nommee dans `epic_visit_cap_skipped`
    -- la reprise d'un chantier ouvert n'est pas une NOUVELLE visite. Avant
    l'arbitrage, ce cas rendait `BLOCKED: PLAFOND EPIC (#22500)` alors que le
    rapport portait `my_active_claim: true`.
    """
    payload = daughter(23499, created_at=iso(days=9))
    loaders = Loaders(
        parents={SERRE100: epic(comments=[comment(
            f"[RELEASED] lane {OTHER_LANE} -- tranche", iso(days=0.7))])},
        pool=[],
    )
    rc = run(payload, loaders)
    assert rc == 0
    data = report(capsys)
    assert data["blocked"] is False
    assert data["my_active_claim"] is True
    assert data["epic_visit_cap"] is None
    assert "already holds an active claim" in data["epic_visit_cap_skipped"]
    assert "not a new umbrella visit" in data["epic_visit_cap_skipped"]


def test_picker_reducer_reads_the_cap_cause():
    """#22687 constat 2 -- `_summarize_claim` (voie solo du picker).

    Le producteur rend exit 1 avec la cause dans `epic_visit_cap` et RIEN
    dans `blocking_lanes` (discipline de visite, pas collision de lane) :
    sans lire la cle, le reducteur concluait FREE sur un rouge. La cause est
    le litteral de l'organe, transmis tel quel derriere le prefixe.
    """
    out = json.dumps({
        "issue": 22617, "blocking_lanes": [], "my_active_claim": False,
        "stale_claims": [], "implicit_occupation": [],
        "epic_visit_cap": "PLAFOND EPIC (#22500) : rendu de main sur "
                          "l'EPIC il y a 0.7 j",
    }) + "\nCLEAR-ish"
    code, human = pig._summarize_claim(out, 1)
    assert code == pig.CLAIM_CODE_BLOCKED
    assert human.startswith("PLAFOND : PLAFOND EPIC (#22500)")
    assert "0.7 j" in human


def test_picker_reducer_stays_free_without_cap_cause():
    """Miroir du precedent : sans cause de plafond, le verdict FREE tient.

    La voie batch du picker reste `epic_cap=False` (#22630 possede le
    tirage) : son resume ne porte jamais la cle, et ce cas doit rester FREE.
    """
    out = json.dumps({
        "issue": 22617, "blocking_lanes": [], "my_active_claim": False,
        "stale_claims": [], "implicit_occupation": [],
        "epic_visit_cap": None,
    }) + "\nCLEAR: no other lane claims #22617."
    code, _ = pig._summarize_claim(out, 0)
    assert code == pig.CLAIM_CODE_FREE


# --- claim pose directement sur l'EPIC (demande explicite) -------------------

def test_claim_on_the_epic_by_another_lane_is_capped(capsys):
    """Controle POSITIF : la visite d'une AUTRE lane arme encore le plafond.

    #25443 a retire du plafond le propre marqueur de la lane qui interroge ;
    il n'a pas retire la regle. Le claim d'une autre lane, pose il y a moins
    de 7 jours, arme toujours le plafond.

    La claim est agee de 3 jours : le filtrage de peremption (48 h) la sort
    des blockers -- sans quoi le verdict serait exit 1 pour une AUTRE
    raison (le blocage de l'autre lane) et le plafond ne serait jamais
    mesure. Ce qui reste a etre verifie ici est donc bien le plafond.
    """
    payload = epic(comments=[comment(
        f"[CLAIMED] lane {OTHER_LANE} -- tranche", iso(days=3))])
    loaders = Loaders(pool=[])
    rc = run(payload, loaders, stale_threshold=48)
    assert rc == 1
    data = report(capsys)
    assert data["epic_visit_cap"].startswith(CAUSE_PREFIX)
    # #22687 constat 1 : la cause NOMME le marqueur retenu au lieu du mot
    # generique « claim », qui affirmait une prise sur tout marqueur -- y
    # compris un `[RELEASED]` (cf le test dedie plus bas).
    assert "prise sur l'EPIC il y a 3.0 j" in data["epic_visit_cap"]
    assert data["epic_visit_cap_epic"] == SERRE100
    # L'EPIC est N lui-meme : sa charge est deja lue, aucun parent a chercher.
    assert loaders.parent_calls == []


def test_claim_on_the_epic_by_the_same_lane_is_clear(capsys):
    """#25443 -- le controle qui suit le claim ne se bloque pas sur lui.

    La sequence du protocole est : on pose son `[CLAIMED]`, puis on relance
    le controle AVANT d'editer. Instance mesuree : po-2027 sur #12051,
    claim de 06:42:59Z, verdict `PLAFOND EPIC (#22500) ... il y a 0.0 j`
    trois minutes plus tard -- sur son propre marqueur.
    """
    payload = epic(comments=[comment(
        f"[CLAIMED] lane {LANE} -- tranche", iso(minutes=3))])
    loaders = Loaders(pool=[])
    rc = run(payload, loaders)
    assert rc == 0
    data = report(capsys)
    assert data["epic_visit_cap"] is None
    assert data["blocked"] is False


def test_closed_visit_of_the_querying_lane_still_caps(capsys):
    """Controle POSITIF, version du COORDINATEUR (demande du 09/11) : une
    visite PASSEE ET CLOSE de la lane qui interroge arme encore le plafond.

    #25443 tranche 1 ecartait du plafond TOUS les marqueurs de la lane qui
    interroge, ses visites passees et closes comprise. Le plafond devenait
    « une visite par semaine et par AUTRE lane » au lieu de « un EPIC hors
    consolidation se visite au plus une fois par semaine » (#22500) : une
    lane seule sur un EPIC pouvait le reprendre chaque jour -- livrer une
    tranche le lundi, en claimer une autre le mardi, et lire `CLEAR`.

    Ici la visite est CLOSE (`[DELIVERED]` de la lane) : elle continue
    d'armer le plafond, datee par son marqueur de cloture.
    """
    payload = epic(comments=[
        comment(f"[CLAIMED] lane {LANE} -- tranche 1", iso(days=3)),
        comment(f"[DELIVERED] lane {LANE} -- PR #1234",
                iso(days=3, minutes=-5)),
    ])
    loaders = Loaders(pool=[])
    rc = run(payload, loaders)
    assert rc == 1
    cause = report(capsys)["epic_visit_cap"]
    assert cause.startswith(CAUSE_PREFIX)
    assert "livraison sur l'EPIC il y a 3.0 j" in cause
    # L'EPIC est N lui-meme : sa charge est deja lue, aucun parent a chercher.
    assert loaders.parent_calls == []


def test_in_progress_claim_does_not_erase_the_closed_visit(capsys):
    """Cas MIXTE : visite close de la lane il y a 3 jours, puis claim en
    cours de la MEME lane il y a 3 minutes.

    C'est le cas qui distingue « visite en cours » de « toutes les visites »
    (demande du coordinateur, point 3). Le claim de la minute ne s'auto-
    bloque pas -- mais la visite close continue d'armer le plafond, et c'est
    sa CLOTURE qui le date, pas le claim.
    """
    payload = epic(comments=[
        comment(f"[CLAIMED] lane {LANE} -- tranche 1", iso(days=3)),
        comment(f"[DELIVERED] lane {LANE} -- PR #1234",
                iso(days=3, minutes=-5)),
        comment(f"[CLAIMED] lane {LANE} -- tranche 2", iso(minutes=3)),
    ])
    loaders = Loaders(pool=[])
    rc = run(payload, loaders)
    assert rc == 1
    cause = report(capsys)["epic_visit_cap"]
    assert cause.startswith(CAUSE_PREFIX)
    assert "livraison sur l'EPIC il y a 3.0 j" in cause
    # La date retenue est celle de la CLOTURE : si le claim de la minute
    # armait le plafond, la cause porterait « il y a 0.0 j ».
    assert "il y a 0.0 j" not in cause


def test_coordinator_override_naming_the_lane_is_clear(capsys):
    """#25443 -- l'override qui rend le grain a la lane ne rearme pas le plafond.

    Instance mesuree : #12051, 07:52Z -- apres l'`[OVERRIDE]` du
    coordinateur qui rendait la tranche a po-2027, le meme controle rendait
    `override sur l'EPIC il y a 0.0 j` et seul `--force` passait.
    """
    payload = epic(comments=[comment(
        f"[OVERRIDE] lane {LANE} -- paths: CLAUDE.md, README.md -- "
        "arbitrage du coordinateur : la tranche est rendue a cette lane",
        iso(minutes=5), author="myia-ai-01")])
    loaders = Loaders(pool=[])
    rc = run(payload, loaders)
    assert rc == 0
    data = report(capsys)
    assert data["epic_visit_cap"] is None
    assert data["blocked"] is False


def test_released_marker_on_the_epic_is_named_not_called_a_claim(capsys):
    """#22687 constat 1 -- la cause nomme ce que la lane a FAIT.

    Mesure fondatrice : sur #16334 le marqueur retenu etait un `[RELEASED]`,
    et la cause annoncait « claim pose sur l'EPIC ». Une lane qui lit ca rend
    la main une seconde fois (ou croit qu'une autre lane tient l'EPIC) pour
    une visite qui est en realite un rendu. La date seule ne distingue pas
    une prise d'un rendu : le marqueur, si.
    """
    payload = epic(comments=[comment(
        f"[RELEASED] lane {OTHER_LANE} -- tranche rendue", iso(days=3))])
    rc = run(payload, Loaders(pool=[]))
    assert rc == 1
    cause = report(capsys)["epic_visit_cap"]
    assert cause.startswith(CAUSE_PREFIX)
    assert "rendu de main sur l'EPIC il y a 3.0 j" in cause
    assert "claim" not in cause


def test_every_marker_the_organ_reads_has_its_own_word(capsys):
    """Aucun marqueur de l'organe ne retombe sur le mot generique.

    `CANCELLED` est lu par `_KEYWORDS` : il doit donc avoir sa traduction,
    comme le `[RELEASED]` ci-dessus. Un code absent du dictionnaire est un
    trou, pas un repli acceptable -- cf `marker_label` pour les codes que
    l'organe ne produit pas.
    """
    payload = epic(comments=[comment(
        f"[CANCELLED] lane {OTHER_LANE} -- tranche abandonnee",
        iso(days=3))])
    rc = run(payload, Loaders(pool=[]))
    assert rc == 1
    cause = report(capsys)["epic_visit_cap"]
    assert "annulation sur l'EPIC il y a 3.0 j" in cause
    assert "claim" not in cause


def test_claim_older_than_the_window_does_not_block(capsys):
    payload = epic(comments=[comment(
        "[CLAIMED] lane myia-ai-01:CoursIA-2 -- tranche", iso(days=10))])
    rc = run(payload, Loaders(pool=[]))
    assert rc == 0
    assert report(capsys)["epic_visit_cap"] is None


# --- exemptions --------------------------------------------------------------

def test_consolidation_epic_is_exempt(capsys):
    """Une consolidation REVIENT souvent : c'est son travail (#22500).

    Depuis #26414 le sujet est N lui-meme : l'exemption se joue sur un claim
    pose directement sur l'EPIC de consolidation.
    """
    payload = epic(13504, labels=("EPIC", "consolidation"), comments=[comment(
        f"[CLAIMED] lane {OTHER_LANE} -- retour de consolidation", iso(days=3))])
    loaders = Loaders(pool=[])
    rc = run(payload, loaders, stale_threshold=48)
    assert rc == 0
    data = report(capsys)
    assert data["epic_visit_cap"] is None
    # Aucun EPIC retenu -> le pool n'est meme pas paye.
    assert loaders.pool_calls == 0


def test_a_daughter_never_loads_its_parent(capsys):
    """#26414 : plus AUCUN `gh issue view` de parent, meme pas pour verifier.

    Le loader parent de la fixture LEVE s'il etait appele : `calls == []` est
    la preuve que la fille ne paie rien du tout.
    """
    payload = daughter(22617, parent=22000, claimed=False)
    loaders = Loaders(parents={22000: issue(22000, title="une issue ordinaire")})
    rc = run(payload, loaders)
    assert rc == 0
    data = report(capsys)
    assert data["epic_visit_cap"] is None
    assert loaders.calls == []
    assert data["epic_visit_cap_calls"] == {"parent_payloads": 0, "pool": 0}


# --- cout ------------------------------------------------------------------

def test_issue_without_parent_costs_zero_call(capsys):
    """Le cas le plus frequent : aucune requete, aucune seconde (demande #22500)."""
    payload = issue(22001, title="un grain ordinaire", body="pas de parent ici")
    loaders = Loaders()
    rc = run(payload, loaders)
    assert rc == 0
    data = report(capsys)
    assert loaders.calls == []
    assert data["epic_visit_cap_calls"] == {"parent_payloads": 0, "pool": 0}


def test_cost_is_reported_for_the_capped_case(capsys):
    """La borne publiee : 1 pool, aucun parent (#26414), pas davantage."""
    loaders = Loaders(pool=[])
    assert run(epic(comments=[comment(
        f"[CLAIMED] lane {OTHER_LANE} -- tranche", iso(days=3))]), loaders,
        stale_threshold=48) == 1
    assert report(capsys)["epic_visit_cap_calls"] == {
        "parent_payloads": 0, "pool": 1}
    assert loaders.parent_calls == []
    assert loaders.pool_calls == 1


def test_another_lane_blocking_skips_the_cap_entirely(capsys):
    """Verdict deja exit 1 -> on ne paie pas 8,6 s de pool pour le redire."""
    payload = daughter(22617)
    payload["comments"].append(comment(
        "[CLAIMED] lane myia-po-2024:CoursIA -- paths: scripts/x.py",
        iso(hours=3)))
    loaders = Loaders(parents={SERRE100: epic()})
    # `--paths` pour que le verdict des blockers soit `exit 1` (PATH_SCOPED) et
    # non le `exit 2` NOT_SCOPED du call sans scope : ici on mesure le saut du
    # plafond, pas la regle de scope.
    rc = run(payload, loaders, my_paths=["scripts/x.py"])
    assert rc == 1
    data = report(capsys)
    assert data["blocking_lanes"] == ["myia-po-2024:CoursIA"]
    assert data["epic_visit_cap"] is None
    assert data["epic_visit_cap_skipped"]
    assert loaders.calls == []


# --- echec de lecture : nomme, jamais un faux « respecte » ------------------

def test_unreadable_pool_does_not_block_and_is_named(capsys):
    """L'EPIC n'a AUCUN marqueur : la seule visite possible viendrait du pool
    (sous-issues creees) -- c'est elle qui est illisible, et elle ne bloque pas."""
    loaders = Loaders(pool=[], pool_error=(
        "GraphQL indisponible (RuntimeError), REST egalement indisponible"))
    rc = run(epic(), loaders)
    assert rc == 0
    data = report(capsys)
    assert data["epic_visit_cap"] is None
    assert "pool:" in data["epic_visit_cap_error"]
    assert data["blocked"] is False


def test_parents_are_never_read_anymore(capsys):
    """#26414 -- le legs « parent illisible » ne se produit plus : aucun parent
    n'est charge, donc aucun echec de lecture parent n'existe."""
    class Broken(Loaders):
        def parent(self, number):
            raise RuntimeError("gh issue view 16334 exit 1")

    loaders = Broken()
    rc = run(daughter(22617, claimed=False), loaders)
    data = report(capsys)
    assert rc == 0
    assert data["epic_visit_cap"] is None
    assert data["epic_visit_cap_error"] is None
    assert loaders.calls == []  # le loader parent n'est jamais appele
    assert data["epic_visit_cap_calls"] == {"parent_payloads": 0, "pool": 0}


# --- le gate est OFF par defaut, et la CLI l'allume -------------------------

def test_cap_is_off_by_default_so_direct_calls_stay_offline(capsys):
    """Tout appel direct (et 100+ tests existants) reste byte-identique."""
    payload = daughter(22617)
    rc = clc._run_check(payload, "myia-ai-01:CoursIA-2")
    assert rc == 0
    data = report(capsys)
    assert data["epic_visit_cap"] is None
    assert data["epic_visit_cap_calls"] is None


def test_cli_check_mode_wires_the_cap(monkeypatch, capsys):
    """Le geste L898 (`check_lane_claim.py N --lane L`) porte vraiment le gate.

    Depuis #26414, le seul cas plafonne est un claim sur l'EPIC lui-meme : la
    CLI est donc eprouvee SUR l'EPIC (visite d'une autre lane il y a 2 jours,
    perimee au seuil de 48 h pour isoler le plafond).
    """
    now = dt.datetime.now(dt.UTC)
    def stamp(**delta):
        return (now - dt.timedelta(**delta)).strftime("%Y-%m-%dT%H:%M:%SZ")
    payload = epic(comments=[comment(
        f"[CLAIMED] lane {OTHER_LANE} -- tranche", stamp(days=2))])
    monkeypatch.setattr(clc, "_gh_issue_comments", lambda issue: payload)
    monkeypatch.setattr(clc, "_epic_cap_parent_payload", lambda n: epic())
    monkeypatch.setattr(clc, "_epic_cap_pool", lambda: ([], None))
    monkeypatch.setattr(clc, "_find_open_prs_referencing_issue",
                        lambda *a, **k: [])
    rc = clc.main([str(SERRE100), "--lane", "myia-ai-01:CoursIA-2"])
    assert rc == 1
    data = report(capsys)
    assert data["epic_visit_cap"].startswith(CAUSE_PREFIX)


def test_cli_from_json_stays_offline(monkeypatch, tmp_path, capsys):
    """`--from-json` est un contrat HORS RESEAU : ni parent, ni pool."""
    payload = issue(22617, title=f"[#{SERRE100} - tranche] sous-grain",
                    body=f"Part of #{SERRE100}")
    path = tmp_path / "payload.json"
    path.write_text(json.dumps(payload), encoding="utf-8")

    def boom(*a, **k):
        raise AssertionError("network leg must not run in --from-json mode")

    monkeypatch.setattr(clc, "_epic_cap_parent_payload", boom)
    monkeypatch.setattr(clc, "_epic_cap_pool", boom)
    monkeypatch.setattr(clc, "_find_open_prs_referencing_issue",
                        lambda *a, **k: [])
    rc = clc.main(["22617", "--lane", "myia-ai-01:CoursIA-2",
                   "--from-json", str(path)])
    assert rc == 0
    assert report(capsys)["epic_visit_cap"] is None


if __name__ == "__main__":  # pragma: no cover
    sys.exit(pytest.main([__file__, "-q"]))
