"""#15511 (P1) : le gate B.0 detecte la boucle de diagnostic sans action.

Motif fondateur : PR #14821 -- 31 commentaires / 68 101 caracteres
d'infra-diagnostic sur 5 jours, pour un livrable qui n'avait pas bouge
depuis le commit du premier jour (~90 % des commentaires sans action
attachee).

Remede P1 de l'issue : taxonomie d'emission en premiere ligne non vide
(`[ACTION]` / `[DIAG]` / `[ASK]`), et `check_unaddressed_nits.py` bloque
la PR a plus de 3 `[DIAG]` consecutifs sans `[ACTION]` intercale.

Le contrat est cote EMISSION (lecon #14682) : un commentaire non tague
est INVISIBLE pour ce detecteur. Les tests verifient les deux bordures
de ce contrat -- transparence du non-tague et de `[ASK]`, neutralite des
bots et du post-cutoff, seuil strictement superieur a 3.

Aucun reseau : `analyse` est pure, les donnees sont synthetiques.
"""
import importlib.util
import sys
from datetime import datetime, timezone
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_unaddressed_nits.py"
spec = importlib.util.spec_from_file_location("check_unaddressed_nits_15511", SCRIPT)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

CUTOFF = datetime(2026, 10, 1, 20, 0, tzinfo=timezone.utc)


def _c(login, minutes, body):
    at = datetime(2026, 10, 1, 10, minutes, tzinfo=timezone.utc).isoformat()
    return {"author": {"login": login}, "createdAt": at, "body": body}


def _pr(comments):
    return {"number": 1, "title": "t", "author": {"login": "jsboige"},
            "comments": comments, "reviews": [], "commits": []}


def _analyse(comments):
    return mod.analyse(_pr(comments), [], CUTOFF)


def test_quatre_diag_consecutifs_bloquent():
    res = _analyse([
        _c("jsboige", 0, "[DIAG] etat du pool : rien de neuf"),
        _c("jsboige", 5, "[DIAG] le check rouge date d'avant le garde"),
        _c("jsboige", 10, "[DIAG] re-mesure : toujours rouge"),
        _c("jsboige", 15, "[DIAG] troisieme passe : le rouge tient"),
    ])
    assert res["diag_loop"]["max_run"] == 4
    assert res["blocked"] is True
    entry = next(b for b in res["blocking"] if b["kind"] == "DIAG-LOOP")
    assert entry["src"] == "comment"
    assert entry["excerpt"]


def test_action_intercale_rompt_la_serie():
    res = _analyse([
        _c("jsboige", 0, "[DIAG] etat du pool"),
        _c("jsboige", 5, "[DIAG] toujours rien"),
        _c("jsboige", 10, "[ACTION] rerun du job rouge 41223549682, commit 093d935e09"),
        _c("jsboige", 15, "[DIAG] re-mesure apres rerun"),
        _c("jsboige", 20, "[DIAG] suite de la mesure"),
    ])
    assert res["diag_loop"]["max_run"] == 2
    assert res["diag_loop"]["action_count"] == 1
    assert res["blocked"] is False


def test_non_tague_et_ask_sont_transparents():
    # Seul [ACTION] interrompt (issue P1 : « sans [ACTION] intercale ») ;
    # un commentaire non tague, ni [ASK] ni [ASK USER], ne coupe rien.
    res = _analyse([
        _c("jsboige", 0, "[DIAG] premiere mesure"),
        _c("jsboige", 5, "commentaire de protocole ordinaire, non tague"),
        _c("jsboige", 10, "[ASK] decision tierce attendue sur le schema"),
        _c("jsboige", 15, "[ASK USER] arbitrage demande"),
        _c("jsboige", 20, "[DIAG] deuxieme mesure"),
        _c("jsboige", 25, "[DIAG] troisieme mesure"),
        _c("jsboige", 30, "[DIAG] quatrieme mesure"),
    ])
    assert res["diag_loop"]["max_run"] == 4
    assert res["blocked"] is True


def test_trois_diag_sont_un_signal_sans_blocage():
    res = _analyse([
        _c("jsboige", 0, "[DIAG] un"),
        _c("jsboige", 5, "[DIAG] deux"),
        _c("jsboige", 10, "[DIAG] trois"),
    ])
    assert res["diag_loop"]["max_run"] == 3
    assert res["blocked"] is False


def test_bots_et_post_cutoff_exclus():
    res = _analyse([
        _c("jsboige", 0, "[DIAG] un"),
        _c("jsboige", 5, "[DIAG] deux"),
        _c("jsboige", 10, "[DIAG] trois"),
        _c("github-actions", 15, "[DIAG] bot : compte pour rien"),
        {"author": {"login": "jsboige"},
         "createdAt": "2026-10-02T10:00:00+00:00",  # posterieur au cutoff
         "body": "[DIAG] quatre"},
    ])
    assert res["diag_loop"]["max_run"] == 3
    assert res["blocked"] is False


def test_tag_lu_sur_la_premiere_ligne_non_vide():
    # ligne vide d'ouverture : le tag reste lu ; un titre markdown "## [DIAG]"
    # n'est PAS un tag (ancre de debut de ligne).
    res = _analyse([
        _c("jsboige", 0, "\n[DIAG] apres une ligne vide"),
        _c("jsboige", 5, "## [DIAG] titre de section"),
        _c("jsboige", 10, "[DIAG] deux"),
    ])
    assert res["diag_loop"]["max_run"] == 2
    assert res["blocked"] is False


def test_marqueurs_de_protocole_ne_sont_ni_diag_ni_action():
    # Un commentaire de protocole dont le marqueur occupe deja la premiere
    # ligne -- dossier de prevalidation, claim, livraison, levee, verdict --
    # n'est pas un commentaire de diagnostic : il ne compte ni comme [DIAG]
    # ni comme [ACTION], et il ne rompt pas une serie en cours. Sans cette
    # borne, une lane qui taguerait son dossier `[ACTION]` le rendrait
    # invalide (check_adjoint_prevalidation.py exige le marqueur en tete).
    res = _analyse([
        _c("jsboige", 0, "[DIAG] premiere mesure"),
        _c("myia-po-2028", 5, "[ADJOINT PREFLIGHT] READY -- #23877 @ c209582157"),
        _c("myia-ai-01", 10, "[CLAIMED] lane myia-ai-01:CoursIA -- paths: scripts/**"),
        _c("myia-ai-01", 15, "[DELIVERED] lane myia-ai-01:CoursIA -- PR #23912"),
        _c("myia-ai-01", 20, "[OVERRIDE] lane myia-ai-01:CoursIA -- reserve levee"),
        _c("clusterManager-Myia", 25, "[Hermes] COMMENT_WITH_CONCERNS"),
        _c("jsboige", 30, "[DIAG] deuxieme mesure"),
        _c("jsboige", 35, "[DIAG] troisieme mesure"),
        _c("jsboige", 40, "[DIAG] quatrieme mesure"),
    ])
    assert res["diag_loop"]["diag_count"] == 4
    assert res["diag_loop"]["action_count"] == 0
    assert res["diag_loop"]["max_run"] == 4
    assert any(b["kind"] == "DIAG-LOOP" for b in res["blocking"])


def test_pr_sans_taxonomie_inchangee():
    # Contrat d'emission : sans aucun tag, le detecteur rend max_run=0 et
    # le verdict de l'organe ne change pas d'un iota.
    res = _analyse([
        _c("jsboige", 0, "reponse ecrite qui adresse la remarque"),
        _c("clusterManager-Myia", 5, "[Hermes] verdict de review"),
    ])
    assert res["diag_loop"]["max_run"] == 0
    assert res["diag_loop"]["diag_count"] == 0
    assert res["diag_loop"]["action_count"] == 0
    assert res["blocked"] is False


# --- Les deux tags P1 doivent sortir de la branche CRLF/HUMAN ------------
#
# Mesure fondatrice : po-2028:CoursIA, 2026-11-02 13:30Z. Un commentaire
# conforme a la regle (`[ACTION]` ou `[DIAG]` en premiere ligne) poste par
# un transport Windows (corps en CRLF) tombait dans la branche heuristique
# `"\r\n" in body` de `classify` et ressortait `HUMAN` -- le compte-rendu
# d'une action devenait un nit bloquant la PR qu'il documente. Les tags
# P1 manquaient a `AGENT_PREFIXES`, seul le vocabulaire dashboard y etait.

CORPS = "Le point est traite.\n\n- rebase fait\n- rerun lance\n- fix pousse\n"


def _crlf(txt):
    return txt.replace("\n", "\r\n")


def test_tags_p1_en_crlf_ne_sont_plus_des_nits():
    for pre in ("[ACTION]", "[DIAG]", "[ASK]", "[INFO]", "[ACTION][INFO]"):
        corps = _crlf(pre + "\n" + CORPS)
        assert mod.classify("jsboige", corps) is None, pre


def test_tags_p1_en_lf_inchange():
    # Non-regression : la correction ne doit rien changer au transport LF,
    # qui sortait deja par la branche `AGENT_PREFIXES`.
    for pre in ("[ACTION]", "[DIAG]", "[ASK]", "[INFO]", "[ACTION][INFO]"):
        assert mod.classify("jsboige", pre + "\n" + CORPS) is None, pre


def test_corps_non_tague_en_crlf_reste_un_nit():
    # La correction ajoute deux prefixes, elle n'elargit pas le filet :
    # un corps sans tag garde exactement le verdict d'avant (branche
    # CRLF + puces = heuristique UI web).
    assert mod.classify("jsboige", _crlf(CORPS)) == "HUMAN"


def test_action_portant_une_vraie_reserve_reste_un_nit():
    # Le point decisif : prefixer un commentaire `[ACTION]` ne blanchit
    # PAS son contenu. Une reserve vivante (glyphe de severite, ou prefixe
    # de verdict nomme) rend toujours `BOT-CONCERN`, dans les deux
    # transports. Sans ce test, le correctif minimal deviendrait un
    # contournement du gate.
    glyphe = "[ACTION] il reste un point\n\U0001F7E1 le seuil n'est pas atteint\n"
    assert mod.classify("jsboige", glyphe) == "BOT-CONCERN"
    assert mod.classify("jsboige", _crlf(glyphe)) == "BOT-CONCERN"

    verdict = "[ACTION] suite a ta reserve\nCHANGES_REQUESTED toujours en vigueur\n"
    assert mod.classify("jsboige", verdict) == "BOT-CONCERN"
    assert mod.classify("jsboige", _crlf(verdict)) == "BOT-CONCERN"


# --- Voie 3 preservee : le tag ne desactive pas le nommage de suivi ---------
#
# Reserve NanoClaw #24243 : AGENT_PREFIXES a un second consommateur, can_lift
# (gate de collect_followup_lifts, voie 3 de B.0). Un compte-rendu tague
# [ACTION] qui nomme une issue de suivi reste un nommeur valide -- les deux
# prefixes vivent dans CLASSIFY_AGENT_PREFIXES, consommee par classify seul.

def _comment(login, body):
    return {"author": {"login": login}, "createdAt": "2026-10-01T10:00:00+00:00",
            "body": body}


def test_action_tague_reste_un_nommeur_voie3():
    suivi = "[ACTION] point 2 reporte sciemment : suivi ouvert #24999\n"
    assert mod.can_lift(_comment("jsboige", suivi)) is True
    # [DIAG] : le tag decrit le genre du commentaire, pas un pouvoir de
    # nomination -- un diagnostic qui reporte nomme autant.
    assert mod.can_lift(_comment("jsboige", suivi.replace("[ACTION]", "[DIAG]"))) is True
    # Borne : les tags de protocole purs restent non-leveurs (can_lift lit
    # AGENT_PREFIXES, qui ne contient ni [ACTION ni [DIAG).
    assert mod.can_lift(_comment("jsboige", "[INFO] panorama du cycle\n")) is False
    assert mod.can_lift(_comment("jsboige", "[ACK] recu\n")) is False


def test_classify_lit_bien_les_deux_tags():
    # La classification, elle, lit l'extension : CRLF compris (couverture
    # croisee avec test_tags_p1_en_crlf_ne_sont_plus_des_nits, ici via la
    # constante nommee). AGENT_PREFIXES, elle, ne les contient plus.
    for pre in ("[ACTION", "[DIAG"):
        corps = pre + "]\n" + CORPS
        assert mod.classify("jsboige", corps) is None, pre
        assert mod.classify("jsboige", _crlf(corps)) is None, pre
    assert "[ACTION" not in mod.AGENT_PREFIXES
    assert "[DIAG" not in mod.AGENT_PREFIXES
