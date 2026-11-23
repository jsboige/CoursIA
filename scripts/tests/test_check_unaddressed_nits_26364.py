"""#26364 (tranche B.0) : le signalement de rouge herite de la base n'est pas un nit.

Motif fondateur : [ACTION] ai-01 du 2026-11-15, versement des frictions
mesurees par po-2028 (cycles 86-89). Un rouge herite de la base n'avait pas
de canal sur la PR : l'ecrire (comme l'exige la regle worker « ecrire en
commentaire, puis --ignore-red ») creait un nit B.0 qui bloquait la PR
qu'il documentait -- 7 occurrences mesurees.

Remede (spec ai-01) : marqueur `[BASE-INHERITED]` en premiere ligne non
vide, classe non-nit par l'organe -- contrat cote EMISSION, comme `[DIAG]`
(#15511 P1). Le commentaire reste un SIGNAL, pas une reserve : une reserve
vivante (glyphe de severite, prefixe de verdict) reste un nit, et le tag ne
desactive ni les levees ni les autres gardes.

Aucun reseau : `classify` et `analyse` sont pures, les donnees sont
synthetiques.
"""
import importlib.util
from datetime import datetime, timezone
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_unaddressed_nits.py"
spec = importlib.util.spec_from_file_location("check_unaddressed_nits_26364", SCRIPT)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

CUTOFF = datetime(2026, 11, 15, 20, 0, tzinfo=timezone.utc)

CORPS = (
    "Le check proof-integrity est rouge sur cette tete ; re-mesure sur "
    "origin/main au meme commit : rouge identique.\n\n"
    "- jambe fautive : proof-integrity\n"
    "- issue canonique ouverte : #26706\n"
)


def _crlf(txt):
    return txt.replace("\n", "\r\n")


def test_signalement_lf_et_crlf_ne_sont_plus_des_nits():
    # Le transport Windows (CRLF) etait la branche qui fabriquait le nit :
    # les deux transports doivent sortir par l'exemption de classification.
    corps = "[BASE-INHERITED] " + CORPS
    assert mod.classify("jsboige", corps) is None
    assert mod.classify("jsboige", _crlf(corps)) is None


def test_marqueur_lu_sur_premiere_ligne_non_vide():
    corps = "\n[BASE-INHERITED] apres une ligne vide d'ouverture\n" + CORPS
    assert mod.classify("jsboige", corps) is None


def test_reserve_vivante_reste_un_nit():
    # Le point decisif (parite avec test_action_portant_une_vraie_reserve_
    # reste_un_nit, #15511) : prefixer [BASE-INHERITED] ne blanchit PAS le
    # contenu. Une reserve vivante rend toujours BOT-CONCERN.
    glyphe = "[BASE-INHERITED] rouge herite\n\U0001F7E1 mais ce chemin doit etre fixe dans la PR\n"
    assert mod.classify("jsboige", glyphe) == "BOT-CONCERN"
    assert mod.classify("jsboige", _crlf(glyphe)) == "BOT-CONCERN"

    verdict = "[BASE-INHERITED] suite a ta reserve\nCHANGES_REQUESTED toujours en vigueur\n"
    assert mod.classify("jsboige", verdict) == "BOT-CONCERN"


def test_corps_non_tague_en_crlf_reste_un_nit():
    # L'ajout n'elargit pas le filet : sans le marqueur, le verdict d'avant
    # tient (branche CRLF + puces = heuristique UI web).
    assert mod.classify("jsboige", _crlf(CORPS)) == "HUMAN"


# --- Voie 3 preservee : le tag ne desactive pas le nommage de suivi ---------
#
# Reserve NanoClaw #24243 (parite #15511) : AGENT_PREFIXES a un second
# consommateur, can_lift. Un signalement [BASE-INHERITED] qui NOMME une issue
# canonique de suivi reste un nommeur valide -- le tag vit dans
# CLASSIFY_AGENT_PREFIXES, consommee par classify seul.

def _comment(login, body):
    return {"author": {"login": login},
            "createdAt": "2026-11-15T10:00:00+00:00", "body": body}


def test_signalement_tague_reste_un_nommeur_voie3():
    suivi = "[BASE-INHERITED] rouge herite de la base, suivi ouvert #26706\n"
    assert mod.can_lift(_comment("jsboige", suivi)) is True


def test_le_tag_ne_vit_que_dans_classify():
    assert "[BASE-INHERITED" in mod.CLASSIFY_AGENT_PREFIXES
    assert "[BASE-INHERITED" not in mod.AGENT_PREFIXES


# --- Neutre pour la boucle DIAG (#15511) ------------------------------------
#
# Spec ai-01 : classe non-nit, contrat cote emission « comme [DIAG] » -- le
# mecanisme, pas la boucle de pompage. [BASE-INHERITED] n'est ni un diagnostic
# ni une action : il ne compte dans aucune serie et ne rompt rien. Un signalement
# de rouge herite n'est pas de la ponpe de diagnostic -- il nomme une cause
# externe deja tranchee (l'issue canonique de suivi existe).

def _pr(comments):
    return {"number": 1, "title": "t", "author": {"login": "jsboige"},
            "comments": comments, "reviews": [], "commits": []}


def _c(minutes, body):
    at = datetime(2026, 11, 15, 10, minutes, tzinfo=timezone.utc).isoformat()
    return {"author": {"login": "jsboige"}, "createdAt": at, "body": body}


def test_neutre_pour_la_boucle_diag():
    # Transparent comme un commentaire non tague (cf test_non_tague_et_ask_
    # sont_transparents, #15511) : il ne compte ni comme [DIAG] ni comme
    # [ACTION], et il n'INTERROMPT pas une serie -- les 4 [DIAG] de part et
    # d'autre forment une seule serie de 4 (qui depasse le seuil : la garde
    # DIAG-LOOP n'est pas desarmee par un signalement de rouge herite).
    res = mod.analyse(_pr([
        _c(0, "[DIAG] premiere mesure"),
        _c(5, "[BASE-INHERITED] rouge herite, suivi ouvert #26706"),
        _c(10, "[DIAG] deuxieme mesure"),
        _c(15, "[DIAG] troisieme mesure"),
        _c(20, "[DIAG] quatrieme mesure"),
    ]), [], CUTOFF)
    assert res["diag_loop"]["max_run"] == 4
    assert res["diag_loop"]["diag_count"] == 4
    assert res["diag_loop"]["action_count"] == 0
    assert any(b["kind"] == "DIAG-LOOP" for b in res["blocking"])
