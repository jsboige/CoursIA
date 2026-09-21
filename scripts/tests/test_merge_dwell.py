#!/usr/bin/env python3
"""Tests du plancher de merge (`scripts/ci/merge_dwell.py`, mandat user 2026-09-07).

Ce que ces tests epinglent, par ordre de degat s'ils cassent :

1. **Le plancher refuse vraiment une tete jeune.** Un garde temporel qui rend
   toujours vert est indiscernable d'un garde debranche -- c'est la premiere
   chose a mesurer, avant meme la mise en forme du message.
2. **Le futur n'est pas « tres vieux ».** Une date de committer dans le futur
   (decalage d'horloge, date forgee) rend l'age negatif ; la seule facon de
   transformer ce garde en passe-plat serait de la laisser passer.
3. **Une lecture d'API muette n'est pas une derogation.** `is_waived` sur une
   reponse illisible doit LEVER, jamais renvoyer False silencieusement -- le
   zero propre que le harnais interdit de croire.
4. **Hors contexte de PR, pas de plancher.** Le gate tourne aussi sur
   `workflow_dispatch`, ou son check-run atterrit sur la branche par defaut :
   y appliquer un plancher rougirait `main` sans rien gater.

Run: python -m pytest scripts/tests/test_merge_dwell.py
"""
import os
import shutil
import subprocess
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from ci import merge_dwell  # noqa: E402

NOW = datetime(2026, 9, 7, 12, 0, 0, tzinfo=timezone.utc)


# --- 1. le plancher refuse une tete jeune -----------------------------------

def test_tete_jeune_refusee():
    ok, remaining, msg = merge_dwell.evaluate(NOW - timedelta(minutes=5), NOW, 120.0)
    assert ok is False
    assert 114 < remaining <= 115
    assert "reste 115 min" in msg


def test_tete_agee_acceptee():
    ok, remaining, msg = merge_dwell.evaluate(NOW - timedelta(minutes=121), NOW, 120.0)
    assert ok is True
    assert remaining == 0.0
    assert "dwell ecoule" in msg


def test_bord_exact_accepte():
    """A 120 min pile le plancher est ecoule -- un plancher, pas un plafond."""
    ok, _, _ = merge_dwell.evaluate(NOW - timedelta(minutes=120), NOW, 120.0)
    assert ok is True


def test_message_de_refus_nomme_le_geste_de_levee():
    """Le rouge doit dire comment il se leve, sinon il se lit comme un blocage."""
    _, _, msg = merge_dwell.evaluate(NOW - timedelta(minutes=1), NOW, 120.0)
    assert "pr-gate-stale-sweep.yml" in msg
    assert merge_dwell.WAIVER_LABEL in msg


def test_message_de_refus_porte_lheure_de_levee_absolue():
    """#15693 : l'heure de tete ET l'heure de LEVEE. « 101 min » oblige la
    lane a refaire le calcul et l'incite a agir ; un re-push reactionnaire
    remet le plancher a zero depuis la nouvelle tete.

    #16092 : la levee est arrondie au premier `SWEEP_MINUTE:00:00Z`
    strictement posterieur au plancher brut. Tete 11:55 + plancher 120 min
    -> plancher brut 13:55 ; sweep `:07` qui suit = 14:07 (13:07 est
    anterieur a 13:55). C'est l'heure GARANTIE d'un sweep nominal, pas
    l'heure du plancher brut (qui tait que le sweep vient de passer)."""
    ok, _, msg = merge_dwell.evaluate(
        NOW.replace(hour=11, minute=55), NOW, 120.0
    )
    assert ok is False
    assert "tete du 2026-09-07T11:55:00Z" in msg
    assert "2026-09-07T14:07:00Z" in msg, (
        "l'heure de levee, arrondie au sweep :07 strictement postérieur "
        "au plancher brut (11:55+120=13:55 ; sweep suivant = 14:07)"
    )


def test_levee_arrondie_au_sweep_strictement_posterieur():
    """#16092 : quand le plancher brut est juste apres un `:07`, le calcul
    prend le `:07` suivant, pas l'anterieur (qui vient de passer et ne leve
    plus). Tete 11:55 + 10 min -> plancher 12:05 ; sweep anterieur 12:07
    inexistant (apres), 11:07 anterieur a 12:05, donc sweep suivant 12:07.
    """
    ok, _, msg = merge_dwell.evaluate(
        NOW.replace(hour=11, minute=55), NOW, 10.0
    )
    assert ok is False
    assert "2026-09-07T12:07:00Z" in msg


def test_levee_si_plancher_brut_pile_avant_un_sweep():
    """#16092 : tete 11:48 + 20 min -> plancher brut 12:08 ; sweep anterieur
    11:07 (avant), sweep suivant 12:07 STRICTEMENT anterieur ; le troisieme
    candidat suivant 13:07 est le strict-postérieur. Verifie qu'on ne
    selectionne jamais un sweep anterieur au plancher brut, même s'il est
    tres proche."""
    ok, _, msg = merge_dwell.evaluate(
        NOW.replace(hour=11, minute=48), NOW, 20.0
    )
    assert ok is False
    assert "2026-09-07T13:07:00Z" in msg


def test_sweep_minute_constant():
    """La constante `SWEEP_MINUTE` est rattachee au cron
    `pr-gate-stale-sweep.yml:102` (cron: '7 * * * *'). Si le cron bouge,
    elle doit bouger -- le commentaire dans merge_dwell.py porte ce lien."""
    assert merge_dwell.SWEEP_MINUTE == 7


# --- 2. le futur n'est pas « tres vieux » -----------------------------------

def test_tete_dans_le_futur_refusee():
    ok, remaining, _ = merge_dwell.evaluate(NOW + timedelta(minutes=30), NOW, 120.0)
    assert ok is False
    assert remaining > 120.0


# --- derogation et desactivation --------------------------------------------

def test_label_de_derogation_leve_le_plancher():
    ok, _, msg = merge_dwell.evaluate(
        NOW - timedelta(minutes=1), NOW, 120.0, waived=True
    )
    assert ok is True
    assert merge_dwell.WAIVER_LABEL in msg
    # Controle positif de la meme entree SANS derogation : sans lui, un test
    # vert ne distingue pas « le label a leve » de « le plancher ne mord pas ».
    assert merge_dwell.evaluate(NOW - timedelta(minutes=1), NOW, 120.0)[0] is False


def test_dwell_nul_desactive():
    ok, _, _ = merge_dwell.evaluate(NOW - timedelta(minutes=1), NOW, 0.0)
    assert ok is True


# --- 3. une API muette n'est pas une derogation -----------------------------

def test_is_waived_leve_sur_payload_inattendu():
    with pytest.raises(merge_dwell.DwellError):
        merge_dwell.is_waived("o/r", 1, fetch=lambda path: [])


def test_is_waived_lit_le_label():
    payload = {"labels": [{"name": "docs"}, {"name": merge_dwell.WAIVER_LABEL}]}
    assert merge_dwell.is_waived("o/r", 1, fetch=lambda path: payload) is True
    assert merge_dwell.is_waived(
        "o/r", 1, fetch=lambda path: {"labels": [{"name": "docs"}]}
    ) is False


def test_head_committed_at_leve_sans_date():
    with pytest.raises(merge_dwell.DwellError):
        merge_dwell.head_committed_at(
            "o/r", "deadbeef", fetch=lambda path: {"commit": {"committer": {}}}
        )


def test_head_committed_at_lit_la_date_du_committer():
    payload = {
        "commit": {
            "author": {"date": "2020-01-01T00:00:00Z"},
            "committer": {"date": "2026-09-07T09:48:43Z"},
        }
    }
    got = merge_dwell.head_committed_at("o/r", "abc", fetch=lambda path: payload)
    assert got == datetime(2026, 9, 7, 9, 48, 43, tzinfo=timezone.utc)


def test_parse_iso8601_refuse_une_date_vide():
    with pytest.raises(merge_dwell.DwellError):
        merge_dwell.parse_iso8601("")


# --- 4. hors contexte de PR, pas de plancher --------------------------------

def test_check_sans_numero_de_pr_ne_gate_rien():
    def boom(path):  # le reseau ne doit meme pas etre touche
        raise AssertionError("aucun appel gh attendu hors contexte de PR")

    ok, msg = merge_dwell.check("o/r", "abc", None, 120.0, fetch=boom)
    assert ok is True
    assert "non applicable" in msg


def test_check_bout_en_bout_refuse_une_tete_jeune():
    def fetch(path):
        if path.startswith("repos/o/r/pulls/"):
            return {"labels": [], "base": {"sha": "ba5e0000"}}
        return {"commit": {"committer": {"date": "2026-09-07T11:55:00Z"}}}

    ok, msg = merge_dwell.check("o/r", "abc", 42, 120.0, now=NOW, fetch=fetch)
    assert ok is False
    assert msg.startswith("tete du 2026-09-07T11:55:00Z")


def test_check_bout_en_bout_accepte_une_tete_agee():
    def fetch(path):
        if path.startswith("repos/o/r/pulls/"):
            return {"labels": [], "base": {"sha": "ba5e0000"}}
        return {"commit": {"committer": {"date": "2026-09-07T09:00:00Z"}}}

    ok, msg = merge_dwell.check("o/r", "abc", 42, 120.0, now=NOW, fetch=fetch)
    assert ok is True
    assert "dwell ecoule" in msg


# --- 5. le message est RELISIBLE par ses consommateurs (#15910) --------------

def test_le_plancher_est_relisible_par_ses_consommateurs():
    """Round-trip emetteur -> lecteur : la forme du message tient des deux cotes.

    Le picker ne peut pas recalculer le plancher (il ne voit que le texte du
    gate) : il lit ce message pour distinguer « ce rouge est un minuteur » de
    « ce rouge est un defaut ». Si la formulation derive d'un cote, le lecteur
    cesse de matcher EN SILENCE et le rouge DWELL redevient un grain dit
    reparable -- ce test echoue a la place, dans le module qui possede la forme.
    """
    ok, remaining, msg = merge_dwell.evaluate(NOW - timedelta(minutes=7), NOW, 120.0)
    assert ok is False
    parsed = merge_dwell.parse_pending_message(msg)
    # #16092 : lift_at est l'heure GARANTIE du balayage :07 posterieur au
    # plancher brut (11:53 + 120 min = 13:53 -> 14:07), pas le plancher brut.
    assert parsed == {"head_at": "2026-09-07T11:53:00Z", "dwell_min": 120,
                      "remaining_min": 113, "lift_at": "2026-09-07T14:07:00Z"}
    assert parsed["remaining_min"] == int(remaining)


def test_controle_negatif_les_autres_verdicts_ne_sont_pas_des_planchers():
    """Les DEUX autres verdicts du gate ne doivent PAS se lire comme un plancher.

    « plancher ecoule » est un rouge qui tombe seul au prochain balayage ;
    « derogation » dit que le plancher ne mord pas. Les confondre avec un
    plancher en cours ferait attendre une PR qui n'attend rien -- et, pire,
    ferait acquitter un rouge que personne ne levera.
    """
    _ok, _rem, ecoule = merge_dwell.evaluate(NOW - timedelta(minutes=200), NOW, 120.0)
    assert merge_dwell.parse_pending_message(ecoule) is None
    _ok, _rem, derogation = merge_dwell.evaluate(
        NOW - timedelta(minutes=5), NOW, 120.0, waived=True)
    assert merge_dwell.parse_pending_message(derogation) is None
    assert merge_dwell.parse_pending_message("") is None
    assert merge_dwell.parse_pending_message("texte etranger") is None


# --- 6. #16149 -- le rafraichissement de base ne re-arme pas le plancher ----

def _commit(sha, date, parents, tree=None):
    payload = {
        "commit": {"committer": {"date": date}},
        "parents": [{"sha": p} for p in parents],
    }
    if tree is not None:
        payload["commit"]["tree"] = {"sha": tree}
    return payload


def _git_proving(auto_tree):
    """Fake run_git dont merge-tree PROUVE l'equivalence : l'auto-merge des
    parents donne exactement `auto_tree` (les objets sont presents, donc le
    merge-base est calculable)."""
    def run_git(args):
        if args[:2] == ["cat-file", "-e"]:
            return 0, ""
        if args[0] == "fetch":
            return 0, ""
        if args[0] == "merge-base":
            return 0, "b0"
        if args[:2] == ["merge-tree", "--write-tree"]:
            return 0, auto_tree + "\n"
        raise AssertionError("git inattendu: " + " ".join(args))
    return run_git


def _git_conflicting():
    """Fake run_git dont merge-tree rend non nul : l'auto-merge CONFLIT -- un
    merge reel n'existe qu'avec une resolution d'auteur."""
    def run_git(args):
        if args[:2] == ["cat-file", "-e"]:
            return 0, ""
        if args[0] == "fetch":
            return 0, ""
        if args[0] == "merge-base":
            return 0, "b0"
        if args[:2] == ["merge-tree", "--write-tree"]:
            return 1, ""
        raise AssertionError("git inattendu: " + " ".join(args))
    return run_git


def _git_absent():
    """Fake run_git dont l'execution meme echoue (git introuvable) : preuve
    indisponible -> fail-closed, jamais d'exemption."""
    def run_git(args):
        raise OSError("git introuvable")
    return run_git


def test_16149_update_branch_ne_re_armed_pas_le_plancher():
    """Critere d'acceptation de l'issue : commit d'auteur T-180 min, puis
    fusion de rafraichissement de base T-1 min (second parent = la base
    elle-meme, arbre PROUVE identique a l'auto-merge) -- le plancher se
    mesure sur l'auteur, donc ecoule."""
    def fetch(path):
        if path == "repos/o/r/pulls/42":
            return {"labels": [], "base": {"sha": "ba5e"}}
        if path == "repos/o/r/commits/m3rg3":
            return _commit(
                "m3rg3", "2026-09-07T11:59:00Z", ["auc0", "ba5e"], tree="7ee0"
            )
        if path == "repos/o/r/commits/auc0":
            return _commit("auc0", "2026-09-07T09:00:00Z", ["r00t"])
        raise AssertionError("chemin inattendu: " + path)

    ok, msg = merge_dwell.check(
        "o/r", "m3rg3", 42, 120.0, now=NOW, fetch=fetch,
        run_git=_git_proving("7ee0"),
    )
    assert ok is True
    assert "2026-09-07T09:00:00Z" in msg, (
        "le plancher doit se mesurer sur le commit d'auteur, pas la fusion"
    )


def test_16149_second_parent_via_compare_behind():
    """Le second parent ancetre DE LOIN de la base (pas d'egalite directe) :
    l'appel compare rend "behind" et la fusion est franchie aussi."""
    def fetch(path):
        if path == "repos/o/r/pulls/42":
            return {"labels": [], "base": {"sha": "ba5e"}}
        if path == "repos/o/r/commits/m3rg3":
            return _commit(
                "m3rg3", "2026-09-07T11:59:00Z", ["auc0", "0ld"], tree="7ee0"
            )
        if path == "repos/o/r/commits/auc0":
            return _commit("auc0", "2026-09-07T08:00:00Z", ["r00t"])
        if path == "repos/o/r/compare/ba5e...0ld":
            return {"status": "behind", "behind_by": 3}
        raise AssertionError("chemin inattendu: " + path)

    ok, msg = merge_dwell.check(
        "o/r", "m3rg3", 42, 120.0, now=NOW, fetch=fetch,
        run_git=_git_proving("7ee0"),
    )
    assert ok is True
    assert "2026-09-07T08:00:00Z" in msg


def test_16149_fusion_de_sous_branche_auteur_re_arme():
    """Controle FN : une fusion dont le second parent n'est PAS un ancetre
    de la base (l'auteur incorpore sa propre sous-branche) introduit du
    contenu d'auteur -- le plancher se re-arme sur elle."""
    def fetch(path):
        if path == "repos/o/r/pulls/42":
            return {"labels": [], "base": {"sha": "ba5e"}}
        if path == "repos/o/r/commits/m3rg3":
            return _commit("m3rg3", "2026-09-07T11:59:00Z", ["auc0", "feat"])
        if path == "repos/o/r/compare/ba5e...feat":
            return {"status": "diverged"}
        raise AssertionError("chemin inattendu: " + path)

    ok, msg = merge_dwell.check("o/r", "m3rg3", 42, 120.0, now=NOW, fetch=fetch)
    assert ok is False
    assert msg.startswith("tete du 2026-09-07T11:59:00Z")


def test_16149_filiation_illisible_reste_stricte():
    """Controle FN : un compare muet ne vaut pas reconnaissance de
    rafraichissement -- la fusion se mesure elle-meme (comportement
    d'avant #16149, plus strict jamais plus lache)."""
    def fetch(path):
        if path == "repos/o/r/pulls/42":
            return {"labels": [], "base": {"sha": "ba5e"}}
        if path == "repos/o/r/commits/m3rg3":
            return _commit("m3rg3", "2026-09-07T11:59:00Z", ["auc0", "0ld"])
        if path.startswith("repos/o/r/compare/"):
            raise merge_dwell.DwellError("compare muet")
        raise AssertionError("chemin inattendu: " + path)

    ok, msg = merge_dwell.check("o/r", "m3rg3", 42, 120.0, now=NOW, fetch=fetch)
    assert ok is False


def test_16149_deux_fusions_empilees_sont_toutes_deux_franchies():
    """Deux update-branch successifs (chacun PROUVE content-free) : la
    remontee franchit les deux et mesure le commit d'auteur d'origine."""
    def fetch(path):
        if path == "repos/o/r/pulls/42":
            return {"labels": [], "base": {"sha": "ba5e"}}
        if path == "repos/o/r/commits/m3rg3":
            return _commit(
                "m3rg3", "2026-09-07T11:59:00Z", ["m3rg2", "ba5e"], tree="7ee0"
            )
        if path == "repos/o/r/commits/m3rg2":
            return _commit(
                "m3rg2", "2026-09-07T10:59:00Z", ["auc0", "0ld"], tree="7ee0"
            )
        if path == "repos/o/r/commits/auc0":
            return _commit("auc0", "2026-09-07T07:00:00Z", ["r00t"])
        if path == "repos/o/r/compare/ba5e...0ld":
            return {"status": "behind", "behind_by": 2}
        raise AssertionError("chemin inattendu: " + path)

    ok, msg = merge_dwell.check(
        "o/r", "m3rg3", 42, 120.0, now=NOW, fetch=fetch,
        run_git=_git_proving("7ee0"),
    )
    assert ok is True
    assert "2026-09-07T07:00:00Z" in msg


def test_16149_payload_pr_sans_base_leve():
    """Un payload PR sans base.sha est un etat illisible : DwellError (rule 1
    -- on refuse, on ne mesure pas sur une supposition)."""
    def fetch(path):
        if path == "repos/o/r/pulls/42":
            return {"labels": []}
        raise AssertionError("chemin inattendu: " + path)

    with pytest.raises(merge_dwell.DwellError):
        merge_dwell.check("o/r", "abc", 42, 120.0, now=NOW, fetch=fetch)


# --- CR ai-01 2026-09-16 : la forme des parents ne prouve pas l'absence de
# contenu d'auteur ; l'exemption exige une equivalence d'arbre PROUVEE ----


def _cr_payloads(tree):
    """Le contre-exemple exact de la review : head merge frais a 11:59,
    parents [author-old, base], auteur ancien a 08:00 -- NOW = 12:00, donc
    mesurer l'auteur rend le plancher ecoule (240 min), mesurer la fusion
    le re-arme (1 min)."""
    def fetch(path):
        if path == "repos/o/r/pulls/42":
            return {"labels": [], "base": {"sha": "ba5e"}}
        if path == "repos/o/r/commits/m3rg3":
            return _commit(
                "m3rg3", "2026-09-07T11:59:00Z", ["auc0", "ba5e"], tree=tree
            )
        if path == "repos/o/r/commits/auc0":
            return _commit("auc0", "2026-09-07T08:00:00Z", ["r00t"])
        raise AssertionError("chemin inattendu: " + path)
    return fetch


def test_cr_20260916_resolution_manuelle_substantive_re_arme():
    """LE faux negatif de la review : merge manuel de la base porteur d'une
    resolution de conflit substantielle -- l'arbre du commit DIFFERE de
    l'auto-merge (res0 != auto). La fusion reste authoritative : le plancher
    se re-arme sur 11:59, l'ok=True d'avant le repair est impossible."""
    ok, msg = merge_dwell.check(
        "o/r", "m3rg3", 42, 120.0, now=NOW,
        fetch=_cr_payloads(tree="res0"), run_git=_git_proving("a010"),
    )
    assert ok is False, (
        "une resolution d'auteur substantive dans un merge de base doit "
        "re-armer le plancher -- c'est le bypass exact de la review"
    )
    assert msg.startswith("tete du 2026-09-07T11:59:00Z")


def test_cr_20260916_auto_merge_conflitant_re_arme():
    """merge-tree rend non nul : l'auto-merge CONFLIT, donc tout merge reel
    de ces parents ne peut exister qu'avec une resolution d'auteur -- meme
    si l'arbre du commit etait par hasard celui d'un des parents, aucune
    equivalence n'est prouvable : la fusion se mesure."""
    ok, msg = merge_dwell.check(
        "o/r", "m3rg3", 42, 120.0, now=NOW,
        fetch=_cr_payloads(tree="a010"), run_git=_git_conflicting(),
    )
    assert ok is False
    assert msg.startswith("tete du 2026-09-07T11:59:00Z")


def test_cr_20260916_preuve_indisponible_fail_closed():
    """git introuvable : la preuve d'equivalence est indisponible, PAS
    acquise. Fail-closed -- la fusion se mesure elle-meme (le trade-off
    assume de la CR : jamais d'exemption sur une absence de preuve)."""
    ok, msg = merge_dwell.check(
        "o/r", "m3rg3", 42, 120.0, now=NOW,
        fetch=_cr_payloads(tree="a010"), run_git=_git_absent(),
    )
    assert ok is False
    assert msg.startswith("tete du 2026-09-07T11:59:00Z")


def test_cr_20260916_payload_sans_tree_fail_closed():
    """Le payload API ne porte pas commit.tree.sha : la comparaison
    d'equivalence est incomplete -- pas d'exemption sur une moitie de
    preuve."""
    ok, msg = merge_dwell.check(
        "o/r", "m3rg3", 42, 120.0, now=NOW,
        fetch=_cr_payloads(tree=None), run_git=_git_proving("a010"),
    )
    assert ok is False
    assert msg.startswith("tete du 2026-09-07T11:59:00Z")


def test_cr_20260916_vrai_update_branch_equivalent_passe_toujours():
    """Controle FP : un update-branch REEL (arbre du commit == auto-merge)
    franchit toujours la remontee -- le repair ne retablit pas la taxe de
    2 h pour le cas legitime #16149."""
    ok, msg = merge_dwell.check(
        "o/r", "m3rg3", 42, 120.0, now=NOW,
        fetch=_cr_payloads(tree="a010"), run_git=_git_proving("a010"),
    )
    assert ok is True
    assert "2026-09-07T08:00:00Z" in msg


def test_le_verdict_ne_dit_jamais_d_attendre():
    """#15726 : le message d'un plancher non ecoule ne doit pas fabriquer de l'attente.

    Ce test asserte des ABSENCES, et c'est voulu : la regression qu'il attrape
    n'est pas un calcul faux, c'est une PHRASE qui revient. Le verdict etait
    juste (`False`) tout en disant « aucun geste manuel n'est requis » -- une
    instruction d'attente, machine-emise sur chaque gate rouge, adossee a un
    balayage annonce horaire dont la cadence mesuree est de 2 h 33 a 5 h 18
    (#15197). Un organe qui dit au worker de ne rien faire est le frein que le
    mandat user du 2026-09-12 demande de retirer.
    """
    _, _, msg = merge_dwell.evaluate(
        datetime(2026, 9, 7, 11, 55, tzinfo=timezone.utc), NOW, 120.0, waived=False
    )
    assert "aucun geste" not in msg
    assert "geste manuel n'est requis" not in msg
    # Le mot « horaire » seul re-annonce la cadence fausse que #15197 mesure.
    assert "balayage horaire" not in msg
    # Et ce qui doit y etre : la lane continue, et peut rejouer elle-meme.
    assert "NE PAS ATTENDRE" in msg
    assert "rerun" in msg


# --- CR ai-01 2026-09-16 19:10Z : la preuve doit etre ATTEIGNABLE dans le
# checkout shallow du gate (integration depot reel, chemin de production
# `_default_run_git`) ------------------------------------------------------


def _git_version_supported():
    """`git merge-tree --write-tree` demande Git >= 2.38 (CR 2026-09-16)."""
    try:
        out = subprocess.run(
            ["git", "--version"], capture_output=True, text=True,
            encoding="utf-8", errors="replace"
        ).stdout
    except OSError:
        return False
    parts = out.strip().split()
    if len(parts) < 3 or parts[0] != "git":
        return False
    try:
        major, minor = (int(x) for x in parts[2].split(".")[:2])
    except ValueError:
        return False
    return (major, minor) >= (2, 38)


def _git(cwd, *args, env=None):
    e = {
        "GIT_AUTHOR_NAME": "test", "GIT_AUTHOR_EMAIL": "test@local",
        "GIT_COMMITTER_NAME": "test", "GIT_COMMITTER_EMAIL": "test@local",
    }
    if env:
        e.update(env)
    return subprocess.run(
        ["git", *args], cwd=str(cwd), env={**os.environ, **e},
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )


def _git_ok(result, what):
    assert result.returncode == 0, "{} a echoue:\n{}\n{}".format(
        what, result.stdout, result.stderr
    )


def _build_gate_topology(tmp_path, substantive=False):
    """Mini-depot REEL simulant la topologie du gate (`pr-gate.yml` :
    `actions/checkout@v4` sans fetch-depth -> checkout shallow depth 1). Le
    clone gate ne porte que la tete de PR ; les parents du merge de base en
    sont absents. Renvoie (chemin du clone, info) avec les sha/arbres REELS.

    `substantive=False` : update-branch legitime (arbre == auto-merge).
    `substantive=True`  : merge --no-commit + contenu d'auteur ajoute (arbre
    != auto-merge) -- la resolution manuelle substantive de la CR."""
    origin = tmp_path / "origin"
    uri = origin.as_uri()
    _git_ok(_git(tmp_path, "init", "--bare", "-b", "main", str(origin)),
            "init origin")
    work = tmp_path / "work"
    _git_ok(_git(tmp_path, "clone", uri, str(work)), "clone work")
    _git(work, "config", "user.name", "test")
    _git(work, "config", "user.email", "test@local")
    _git_ok(_git(work, "commit", "--allow-empty", "-m", "b0"), "b0")
    root_sha = _git(work, "rev-parse", "HEAD").stdout.strip()
    for i in range(40):
        (work / "g{:02d}".format(i)).write_text("g", encoding="utf-8")
        _git(work, "add", "-A")
        _git_ok(_git(work, "commit", "-m", "base{}".format(i)),
                "base{}".format(i))
    base_tip = _git(work, "rev-parse", "main").stdout.strip()

    author_env = {"GIT_AUTHOR_DATE": "2026-09-07T08:00:00Z",
                  "GIT_COMMITTER_DATE": "2026-09-07T08:00:00Z"}
    _git_ok(_git(work, "checkout", "-b", "pr", root_sha), "branch pr")
    (work / "a").write_text("a1", encoding="utf-8")
    _git(work, "add", "-A")
    _git_ok(_git(work, "commit", "-m", "a1", env=author_env), "a1")
    (work / "b").write_text("b1", encoding="utf-8")
    _git(work, "add", "-A")
    _git_ok(_git(work, "commit", "-m", "a2", env=author_env), "a2")
    author_tip = _git(work, "rev-parse", "HEAD").stdout.strip()

    merge_env = {"GIT_AUTHOR_DATE": "2026-09-07T11:59:00Z",
                 "GIT_COMMITTER_DATE": "2026-09-07T11:59:00Z"}
    if substantive:
        _git_ok(_git(work, "merge", "--no-commit", "main"), "merge no-commit")
        with (work / "a").open("a", encoding="utf-8") as fh:
            fh.write("\nresolution substantive d'auteur")
        _git(work, "add", "-A")
        _git_ok(_git(work, "commit", "-m", "merge resolution", env=merge_env),
                "commit resolution")
    else:
        _git_ok(_git(work, "merge", "-m", "update-branch merge", "main",
                     env=merge_env), "merge update-branch")
    merge_sha = _git(work, "rev-parse", "HEAD").stdout.strip()
    merge_tree = _git(work, "rev-parse", merge_sha + "^{tree}").stdout.strip()

    _git_ok(_git(work, "push", "origin", "main"), "push main")
    _git_ok(_git(work, "push", "origin", "pr"), "push pr")

    gate = tmp_path / "gate"
    _git_ok(_git(tmp_path, "clone", "--depth=1", "--branch", "pr",
                 uri, str(gate)), "clone gate shallow")
    return gate, {
        "merge_sha": merge_sha, "merge_tree": merge_tree,
        "merge_date": "2026-09-07T11:59:00Z", "author_tip": author_tip,
        "author_date": "2026-09-07T08:00:00Z", "base_tip": base_tip,
        "root_sha": root_sha,
    }


def _shallow_fetch_payloads(info):
    """Payloads API coherents avec le depot REEL construit : les sha et
    arbres cites sont ceux du repo ; seules les lectures gh api sont fakes."""
    def fetch(path):
        if path == "repos/o/r/pulls/42":
            return {"labels": [], "base": {"sha": info["base_tip"]}}
        if path == "repos/o/r/commits/" + info["merge_sha"]:
            return _commit(info["merge_sha"], info["merge_date"],
                           [info["author_tip"], info["base_tip"]],
                           tree=info["merge_tree"])
        if path == "repos/o/r/commits/" + info["author_tip"]:
            return _commit(info["author_tip"], info["author_date"],
                           [info["root_sha"]])
        raise AssertionError("chemin inattendu: " + path)
    return fetch


@pytest.mark.skipif(not _git_version_supported(),
                    reason="git >= 2.38 requis (merge-tree --write-tree)")
def test_cr_20260916_update_branch_legitime_franchit_le_checkout_shallow(
    tmp_path, monkeypatch
):
    """LE defaut de la CR 19:10Z : dans le checkout shallow du gate
    (actions/checkout depth 1), les parents ramenes en --depth=1 n'ont aucun
    historique commun -> merge-base indisponible, merge-tree refusait de
    calculer -> la preuve d'equivalence etait inatteignable et meme le
    update-branch LEGITIME se re-armait 120 min. Avec l'approfondissement
    borne, l'exemption est prouvable et la remontee mesure le commit
    d'auteur (T-240 min) -- plancher ecoule."""
    gate, info = _build_gate_topology(tmp_path, substantive=False)
    monkeypatch.chdir(gate)
    ok, msg = merge_dwell.check(
        "o/r", info["merge_sha"], 42, 120.0, now=NOW,
        fetch=_shallow_fetch_payloads(info),
        run_git=merge_dwell._default_run_git,
    )
    assert ok is True, msg
    assert info["author_date"] in msg, (
        "le plancher doit se mesurer sur le commit d'auteur, pas la fusion"
    )


@pytest.mark.skipif(not _git_version_supported(),
                    reason="git >= 2.38 requis (merge-tree --write-tree)")
def test_cr_20260916_resolution_substantive_re_arme_le_checkout_shallow(
    tmp_path, monkeypatch
):
    """Dans la MEME topologie shallow, un merge de base porteur de contenu
    d'auteur (arbre != auto-merge) reste autoritatif : le plancher se re-arme
    sur la fusion (T-1 min)."""
    gate, info = _build_gate_topology(tmp_path, substantive=True)
    monkeypatch.chdir(gate)
    ok, msg = merge_dwell.check(
        "o/r", info["merge_sha"], 42, 120.0, now=NOW,
        fetch=_shallow_fetch_payloads(info),
        run_git=merge_dwell._default_run_git,
    )
    assert ok is False, msg
    assert msg.startswith("tete du " + info["merge_date"])


def test_cr_20260916_approfondissement_indisponible_fail_closed():
    """Le deepen ne repond plus (reseau) : la preuve reste indisponible, la
    fusion se mesure elle-meme -- l'approfondissement ne transforme jamais
    un echec en exemption."""
    def run_git(args):
        if args[:2] == ["cat-file", "-e"]:
            return 0, ""
        if args[0] == "merge-base":
            return 1, ""
        if args[:2] == ["rev-parse", "--is-shallow-repository"]:
            return 0, "true\n"
        if args[0] == "fetch":  # deepen : plus rien ne repond
            return 128, ""
        if args[:2] == ["merge-tree", "--write-tree"]:
            return 128, "fatal: refusing to merge unrelated histories"
        raise AssertionError("git inattendu: " + " ".join(args))

    ok, msg = merge_dwell.check(
        "o/r", "m3rg3", 42, 120.0, now=NOW,
        fetch=_cr_payloads(tree="a010"), run_git=run_git,
    )
    assert ok is False
    assert msg.startswith("tete du 2026-09-07T11:59:00Z")


def test_cr_20260916_repo_complet_sans_merge_base_reste_fail_closed():
    """Depot COMPLET (non shallow) sans merge-base = historiques veritablement
    sans relation : --deepen y est refuse par git et on ne tente AUCUN fetch
    -- la fusion se mesure elle-meme."""
    calls = []

    def run_git(args):
        calls.append(args[0])
        if args[:2] == ["cat-file", "-e"]:
            return 0, ""
        if args[0] == "merge-base":
            return 1, ""
        if args[:2] == ["rev-parse", "--is-shallow-repository"]:
            return 0, "false\n"
        if args[:2] == ["merge-tree", "--write-tree"]:
            return 128, "fatal: refusing to merge unrelated histories"
        raise AssertionError("git inattendu: " + " ".join(args))

    ok, msg = merge_dwell.check(
        "o/r", "m3rg3", 42, 120.0, now=NOW,
        fetch=_cr_payloads(tree="a010"), run_git=run_git,
    )
    assert ok is False
    assert "fetch" not in calls, "un depot complet sans merge-base ne fetch pas"
