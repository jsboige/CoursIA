#!/usr/bin/env python3
"""#22500 point 3 -- le plafond hebdomadaire des EPICs s'applique au claim.

Fichier NEUF, volontairement : #22457 et #22413 sont ouvertes sur
`scripts/tests/test_check_lane_claim.py`, et une collision de test coute un
cycle de rebase pour rien (le fichier source, lui, reste unique).

Ce que ces tests tiennent, dans l'ordre de la demande (commentaire 6409466826
de #22500) :

  - une fille d'EPIC dont une AUTRE fille a ete creee il y a moins de 7 jours
    est BLOCKED, avec la cause `PLAFOND EPIC (#22500)` ;
  - l'issue elle-meme ne compte pas comme sa propre visite (sinon le premier
    claim legitime de la semaine se bloquerait) ;
  - un claim pose directement sur l'EPIC obeit a la meme regle ;
  - une classe `consolidation` est exemptee ;
  - ZERO appel reseau quand l'issue n'a pas de parent (le cas courant) et
    zero pool quand le parent n'est pas un EPIC -- la borne de cout du
    coordinateur (274 s pour la commande des lanes) se mesure ici ;
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


def daughter(number=22617, *, parent=SERRE100, created_at=None):
    """Une fille d'EPIC creee puis claimee dans la minute (forme #22609)."""
    return issue(number, title=f"[#{parent} - tranche {number}] sous-grain",
                 body=f"Part of #{parent}\n\nGrain: DEEP/lean -- lane x:y",
                 comments=[comment("[CLAIMED] lane myia-ai-01:CoursIA-2 -- x",
                                   created_at or iso(hours=1))])


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
    """`_run_check` avec le plafond cable sur des lectures injectees."""
    return clc._run_check(
        payload, "myia-ai-01:CoursIA-2",
        epic_cap=True,
        epic_cap_probe=lambda p: clc.epic_visit_cap(
            p, now=NOW, parent_loader=loaders.parent,
            pool_loader=loaders.pool_),
        **kwargs,
    )


def report(capsys) -> dict:
    """Le rapport JSON imprime par `_run_check` (il precede la phrase verdict)."""
    out = capsys.readouterr().out
    data, _ = json.JSONDecoder().raw_decode(out[out.index("{"):])
    return data


# --- le scenario fondateur ---------------------------------------------------

def test_daughter_of_epic_visited_this_week_is_blocked(capsys):
    """#22609 (creee 01:45Z) visite #16334 -> le claim de #22617 est BLOCKED.

    C'est le controle negatif exige par #22500 : cette assertion ECHOUE sur le
    `check_lane_claim.py` d'avant le point 3 (le kwarg `epic_cap` n'existe pas,
    et la fixture de fille n'a jamais ete plafonnee).
    """
    payload = daughter(22617)
    loaders = Loaders(
        parents={SERRE100: epic()},
        pool=[
            pool_item(22609, f"[#{SERRE100} - tranche 22609] soeur", iso(days=2)),
            pool_item(22617, f"[#{SERRE100} - tranche 22617] moi", iso(hours=1)),
        ],
    )
    rc = run(payload, loaders)
    assert rc == 1
    data = report(capsys)
    assert data["blocked"] is True
    assert data["epic_visit_cap"].startswith(CAUSE_PREFIX)
    assert "sous-issue creee il y a 2.0 j" in data["epic_visit_cap"]
    assert data["epic_visit_cap_epic"] == SERRE100
    assert data["epic_visit_cap_error"] is None


def test_cause_is_the_organ_literal_not_a_copy(capsys):
    """La cause est rendue par `umbrella_visit_cause`, pas re-ecrite ici.

    On la recalcule a la main avec l'organe, sur la charge que le gate lui a
    passee : toute divergence (litteral change d'un cote seulement) rougit.
    """
    loaders = Loaders(
        parents={SERRE100: epic()},
        pool=[pool_item(22609, f"[#{SERRE100} - a] a", iso(days=2))],
    )
    assert run(daughter(22617), loaders) == 1
    got = report(capsys)["epic_visit_cap"]
    expected = pig.umbrella_visit_cause(
        {"number": SERRE100, "title": None, "labels": [{"name": "EPIC"}],
         "klass": "umbrella", "last_claim_stamp": None,
         "last_child_stamp": iso(days=2)},
        now=NOW,
    )
    assert got == expected


def test_the_claimed_issue_is_not_its_own_visit(capsys):
    """Sans cette exclusion, la 1re fille de la semaine se bloquerait elle-meme."""
    payload = daughter(22617)
    loaders = Loaders(
        parents={SERRE100: epic()},
        pool=[pool_item(22617, f"[#{SERRE100} - moi] moi", iso(minutes=1))],
    )
    rc = run(payload, loaders)
    assert rc == 0
    data = report(capsys)
    assert data["epic_visit_cap"] is None
    assert data["blocked"] is False


def test_second_daughter_within_the_week_is_blocked_by_the_first(capsys):
    """La deuxieme fille de la semaine voit la premiere : c'est tout le defaut."""
    loaders = Loaders(
        parents={SERRE100: epic()},
        pool=[
            pool_item(22619, f"[#{SERRE100} - a] a", iso(minutes=1)),
            pool_item(22620, f"[#{SERRE100} - b] b", iso(hours=2)),
        ],
    )
    assert run(daughter(22620), loaders) == 1
    assert report(capsys)["epic_visit_cap_epic"] == SERRE100


# --- claim pose directement sur l'EPIC (demande explicite) -------------------

def test_claim_on_the_epic_itself_is_capped(capsys):
    # Claim sur l'EPIC par la lane elle-meme : `others` reste vide (sinon le
    # blocage d'une autre lane rendrait exit 1 pour une autre raison, et le
    # plafond serait saute -- cf le test dedie plus bas).
    payload = epic(comments=[comment(
        "[CLAIMED] lane myia-ai-01:CoursIA-2 -- tranche", iso(days=3))])
    loaders = Loaders(pool=[])
    rc = run(payload, loaders)
    assert rc == 1
    data = report(capsys)
    assert data["epic_visit_cap"].startswith(CAUSE_PREFIX)
    assert "claim pose sur l'EPIC il y a 3.0 j" in data["epic_visit_cap"]
    assert data["epic_visit_cap_epic"] == SERRE100
    # L'EPIC est N lui-meme : sa charge est deja lue, aucun parent a chercher.
    assert loaders.parent_calls == []


def test_claim_older_than_the_window_does_not_block(capsys):
    payload = epic(comments=[comment(
        "[CLAIMED] lane myia-ai-01:CoursIA-2 -- tranche", iso(days=10))])
    rc = run(payload, Loaders(pool=[]))
    assert rc == 0
    assert report(capsys)["epic_visit_cap"] is None


# --- exemptions --------------------------------------------------------------

def test_consolidation_epic_is_exempt(capsys):
    """Une consolidation REVIENT souvent : c'est son travail (#22500)."""
    payload = daughter(22617, parent=13504)
    loaders = Loaders(
        parents={13504: epic(13504, labels=("EPIC", "consolidation"))},
        pool=[pool_item(22609, "[#13504 - a] a", iso(hours=2))],
    )
    rc = run(payload, loaders)
    assert rc == 0
    data = report(capsys)
    assert data["epic_visit_cap"] is None
    # Aucun EPIC retenu -> le pool n'est meme pas paye.
    assert loaders.pool_calls == 0


def test_parent_that_is_not_an_epic_costs_no_pool(capsys):
    payload = daughter(22617, parent=22000)
    loaders = Loaders(parents={22000: issue(22000, title="une issue ordinaire")})
    rc = run(payload, loaders)
    assert rc == 0
    data = report(capsys)
    assert data["epic_visit_cap"] is None
    assert loaders.parent_calls == [22000]
    assert loaders.pool_calls == 0
    assert data["epic_visit_cap_calls"] == {"parent_payloads": 1, "pool": 0}


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
    """La borne publiee : 1 lecture de parent + 1 pool, pas davantage."""
    loaders = Loaders(parents={SERRE100: epic()},
                      pool=[pool_item(22609, f"[#{SERRE100} - a] a", iso(days=1))])
    assert run(daughter(22617), loaders) == 1
    assert report(capsys)["epic_visit_cap_calls"] == {
        "parent_payloads": 1, "pool": 1}
    assert loaders.parent_calls == [SERRE100]
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
    loaders = Loaders(parents={SERRE100: epic()}, pool=[], pool_error=(
        "GraphQL indisponible (RuntimeError), REST egalement indisponible"))
    rc = run(daughter(22617), loaders)
    assert rc == 0
    data = report(capsys)
    assert data["epic_visit_cap"] is None
    assert "pool:" in data["epic_visit_cap_error"]
    assert data["blocked"] is False


def test_unreadable_parent_does_not_block_and_is_named(capsys):
    class Broken(Loaders):
        def parent(self, number):
            raise RuntimeError("gh issue view 16334 exit 1")

    rc = run(daughter(22617), Broken())
    data = report(capsys)
    assert rc == 0
    assert data["epic_visit_cap"] is None
    assert "16334" in data["epic_visit_cap_error"]


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
    """Le geste L898 (`check_lane_claim.py N --lane L`) porte vraiment le gate."""
    now = dt.datetime.now(dt.UTC)
    def stamp(**delta):
        return (now - dt.timedelta(**delta)).strftime("%Y-%m-%dT%H:%M:%SZ")
    payload = issue(22617, title=f"[#{SERRE100} - tranche] sous-grain",
                    body=f"Part of #{SERRE100}")
    pool = [pool_item(22609, f"[#{SERRE100} - a] a", stamp(days=2))]
    monkeypatch.setattr(clc, "_gh_issue_comments", lambda issue: payload)
    monkeypatch.setattr(clc, "_epic_cap_parent_payload", lambda n: epic())
    monkeypatch.setattr(clc, "_epic_cap_pool", lambda: (pool, None))
    monkeypatch.setattr(clc, "_find_open_prs_referencing_issue",
                        lambda *a, **k: [])
    rc = clc.main(["22617", "--lane", "myia-ai-01:CoursIA-2"])
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
