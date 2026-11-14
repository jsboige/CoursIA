"""Tests pour le dossier de cloture comme signal de livraison TERMINAL.

Mesure fondatrice (2026-11-02, issue #19253, label `consolidation`) :

- le marqueur `[INFO] candidate-delivered` du 30/10 16:49Z a **expire** le
  01/11 16:49Z (regle des 48 h de #22500) ;
- le tapis a alors **resservi l'issue trois fois dans la journee**, en
  demandant un `[CLAIMED]` sur un travail deja livre ;
- le dossier `[CLOSURE PREFLIGHT]` de verdict CLOSE datait du **02/11
  08:29Z** : il etait dans le fil, et le tapis ne le voyait pas.

Le correctif : le dossier de cloture -- reuse tel quel de l'organe
canonique `scripts/check_closure_dossier.py` -- est un signal **TERMINAL**.
Il arme l'etat de livraison comme un marqueur, mais il ne porte **pas
d'heure** : la regle des 48 h ne peut donc pas l'expirer.

Aucun appel reseau : la boucle du tapis prend ses sondes inertes par
defaut (#19913), la lecture d'evenement est injectee, et les dates sont
relatives au NOW du module.
"""
import sys
import types
from datetime import timedelta
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pick_idle_grain as pig

NOW = pig.NOW


def _iso(hours_ago: float) -> str:
    return (NOW - timedelta(hours=hours_ago)).strftime("%Y-%m-%dT%H:%M:%SZ")


# --- le corps reel du dossier de #19253 (extrait, champs complets) --------

DOSSIER_CLOSE = """[CLOSURE PREFLIGHT]
schema: 1
lane: myia-po-2025:CoursIA
issue: 19253
verdict: CLOSE
acceptance:
  - "Applications/ ne joue plus le role d'une partie 3 muette -> ABSENT de l'arbre"
  - "la carte de reorganisation est en place -> Part1..Part5 presents"
residue: none
open-prs: 0
comments-reviewed: 14
[/CLOSURE PREFLIGHT]"""

DOSSIER_KEEP = DOSSIER_CLOSE.replace("verdict: CLOSE", "verdict: KEEP")

ANNONCE = ("Fermeture sur dossier `[CLOSURE PREFLIGHT]` (verdict CLOSE, "
           "gate `check_closure_dossier.py` rc=0, commentaire 6572592182 "
           "ci-dessus).")


def _item(number, *, klass="grain", visit_h=None, labels=None, **extra):
    it = {
        "number": number,
        "klass": klass,
        "title": f"issue #{number}",
        "labels": labels or [],
        "created_at": _iso(24 * 400),
    }
    if visit_h is not None:
        it["last_delivery_stamp"] = _iso(visit_h)
    it.update(extra)
    return it


def _consol(number, *, visit_h=None, **extra):
    return _item(number, labels=[{"name": "consolidation"}], visit_h=visit_h,
                 **extra)


def _belt_args(grains=2):
    return types.SimpleNamespace(grains=grains, include_delivered=False,
                                 lane="myia-ai-01:CoursIA-2")


def _free_claims(items):
    return {it["number"]: (pig.CLAIM_CODE_FREE, "libre") for it in items}


def _run(pool, *, event_probe=None, probe_budget=8, **kw):
    return pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(grains=len(pool) + 2),
        probe_budget=probe_budget, delivery_event_probe=event_probe, **kw)


# --- la grammaire du dossier : l'organe canonique est reutilise -----------

def test_le_dossier_close_est_reconnu():
    assert pig._closure_dossier_verdict(DOSSIER_CLOSE) == "CLOSE"


def test_le_dossier_keep_ecarte_le_tapis_mais_expire():
    """Decision #24461 (c), point 2 -- le tapis ecarte en plus, a la lecture
    de la liste et sans sonde, les issues qui portent un dossier
    `[CLOSURE PREFLIGHT]` VIVANT (verdict KEEP) : la cloture est EN COURS,
    l'issue n'est pas un grain de production.

    Ce test portait la semantique OPPOSEE (le KEEP n'ecarte rien) ; la
    decision l'inverse explicitement. Ce qui reste vrai, et qui est
    verifie ici, c'est la DIFFERENCE avec un dossier CLOSE : le KEEP porte
    une HEURE, donc il EXPIRE (48 h, #22500) ; le CLOSE est terminal et
    n'expire jamais. Et le LABEL reste etroit (borne 1 de la decision) : un
    dossier KEEP n'arme pas le label."""
    assert pig._closure_dossier_verdict(DOSSIER_KEEP) == "KEEP"
    # KEEP : la cloture est en cours -> l'issue sort du tapis.
    assert pig._delivered_state([DOSSIER_KEEP]) is True
    # ... mais le dossier KEEP est EXPIRABLE (il porte une heure).
    assert pig._delivery_event_from_comments(
        [{"body": DOSSIER_KEEP, "createdAt": _iso(1)}])[2] is not None
    # ... et il n'arme PAS le label (borne 1 : attestation dediee seule).
    assert pig.delivery_grammar.attestation_state([DOSSIER_KEEP],
                                                   dossier=False) == (
        pig.delivery_grammar.NONE)


def test_un_dossier_malforme_est_ignore():
    """Fail-OPEN : un dossier dont un champ obligatoire manque n'est PAS
    un signal de cloture -- il est ignore, pas devine."""
    casse = "\n".join(l for l in DOSSIER_CLOSE.splitlines()
                       if not l.startswith("residue:"))
    assert pig._closure_dossier_verdict(casse) is None
    assert pig._delivered_state([casse]) is False


def test_une_mention_en_prose_ne_signale_rien():
    """Controler NEGATIF : une prose qui MENTIONNE la marqueur d'ouverture
    n'est pas un dossier. Sans ce controle, la simple recherche de la
    sous-chaine suffirait a ecarter des issues vivantes."""
    prose = ("On notera que le format `[CLOSURE PREFLIGHT]` est reserve aux "
             "dossiers de cloture ; cette issue n'est pas concernee.")
    assert pig._closure_dossier_verdict(prose) is None
    assert pig._delivered_state([prose]) is False


# --- l'etat de livraison s'arme -------------------------------------------

def test_le_dossier_close_arme_l_etat_de_livraison():
    assert pig._delivered_state([DOSSIER_CLOSE]) is True


def test_le_dossier_arme_meme_sans_le_marqueur_de_livraison():
    """Le cas mesure : le marqueur `[INFO] candidate-delivered` du 30/10
    avait expire ; le dossier du 02/11 est le seul signal vivant."""
    assert pig._delivered_state([
        "[INFO] candidate-delivered -- lane myia-po-2028:CoursIA-2",
        DOSSIER_CLOSE,
    ]) is True


def test_une_retractation_posterieure_desarme_le_dossier():
    """La retractation garde sa valeur : une issue rouverte reste servable.
    Le dossier est terminal pour l'EXPIRATION, pas pour la retractation."""
    assert pig._delivered_state([
        DOSSIER_CLOSE,
        "[NOT-DELIVERED] lane myia-ai-01:CoursIA",
    ]) is False


# --- la terminalite : le dossier ne porte pas d'heure ---------------------

def test_le_dossier_close_ne_perime_jamais():
    """Le coeur du correctif : `stamp` reste `None`, donc la regle des 48 h
    (#22500) n'a aucune age a comparer -- le dossier ne peut pas expirer."""
    recent, state, stamp = pig._delivery_event_from_comments([
        {"body": DOSSIER_CLOSE, "createdAt": _iso(72)},
    ])
    assert recent is True
    assert state is True
    assert stamp is None
    assert pig._visit_age_hours(stamp, NOW) is None


def test_un_marqueur_ordinaire_perime_toujours():
    """Le CONTROLE du caractere cible : un marqueur normal garde son heure,
    et donc son expiration. Sans ce test, le correctif pourrait etre lu comme
    « plus rien n'expire »."""
    recent, state, stamp = pig._delivery_event_from_comments([
        {"body": "[INFO] candidate-delivered -- lane myia-po-2028:CoursIA-2",
         "createdAt": _iso(72)},
    ])
    assert state is True
    assert stamp == _iso(72)
    age_h = pig._visit_age_hours(stamp, NOW)
    assert age_h is not None and age_h >= pig.CONSOLIDATION_LAG_H


def test_le_dossier_prime_sur_un_marqueur_plus_recent():
    """Un marqueur pose APRES le dossier ne doit pas rendre au dossier son
    caractere expirable : la cloture reste la derniere decision."""
    _recent, state, stamp = pig._delivery_event_from_comments([
        {"body": DOSSIER_CLOSE, "createdAt": _iso(72)},
        {"body": "[INFO] candidate-delivered -- lane myia-ai-01:CoursIA-2",
         "createdAt": _iso(1)},
    ])
    assert state is True
    assert stamp is None


def test_l_annonce_de_cloture_est_reconnue():
    """L'annonce est la meme decision ecrite en prose par l'adjoint : sans
    elle, le DERNIER commentaire du fil redevenirait le seul point lu."""
    assert pig._closure_announced_close(ANNONCE) is True
    assert pig._closure_dossier_verdict(ANNONCE) is None
    recent, _state, _stamp = pig._delivery_event_from_comments([
        {"body": DOSSIER_CLOSE, "createdAt": _iso(1)},
        {"body": ANNONCE, "createdAt": _iso(0.1)},
    ])
    assert recent is True


# --- bout en bout sur la boucle du tapis ---------------------------------

def test_la_consolidation_cloturee_nest_plus_servie():
    """LE CONTROLE POSITIF demande par le dispatch : une consolidation dont
    le dossier de cloture est CLOSE n'est pas servie, meme quand son dernier
    marqueur est vieux de plus de 48 h.

    Le tuple injecte est celui que rend `_delivery_event_from_comments` sur un
    fil portant un dossier CLOSE : `(recent, state, stamp)` avec `stamp=None`.
    """
    item = _consol(19253, visit_h=72)
    picks, withheld, _state = _run([item], event_probe=lambda n: (True, True, None))
    assert picks == [], (
        f"une consolidation cloturee par dossier ne doit pas etre servie, "
        f"picks={[p['number'] for p in picks]}")
    assert withheld and "dossier de cloture CLOSE" in withheld[0][1]


def test_la_consolidation_non_cloturee_reste_servie():
    """Le CONTROLE NEGATIF de la boucle : sans dossier, une consolidation
    dont le marqueur a plus de 48 h est DUE et doit etre servie (#22500).
    Le correctif ne doit pas-etendre l'exclusion a tout le monde."""
    item = _consol(20381, visit_h=72)
    picks, withheld, _state = _run([item],
                                   event_probe=lambda n: (True, True, _iso(72)))
    assert [p["number"] for p in picks] == [20381]
    assert withheld == []
