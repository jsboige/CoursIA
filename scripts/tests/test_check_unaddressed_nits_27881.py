"""#27881 : dans un commentaire de SIGNALEMENT, la PROSE seule n'est pas une reserve.

Motif fondateur : PR #27368 (lane `myia-ai-01:CoursIA-2`), commentaire
`[ACTION] lane myia-ai-01:CoursIA-2` du 2026-11-20T17:50:34Z. Le corps dit
« la PR merite un regard de taille avant merge, et je le dis dans le body
plutot que de le laisser decouvrir » ; l'organe classait ce commentaire
BOT-CONCERN sur le seul marqueur de PROSE `avant merge`, et la PR se
trouvait bloquee par SON PROPRE commentaire d'action (29 h).

Deux familles de marqueurs, a ne pas confondre : les marqueurs FORMELS sont
des verdicts (`CHANGES_REQUESTED`, glyphe 🟡/🔴, refus d'approbation), les
marqueurs de PROSE sont des locutions (`avant merge`, `a changer`). La PROSE
sur-accuse d'un facteur 5 — c'est le motif meme pour lequel #14682 a refuse
d'ajouter des mots de prose « bloquante » au filet.

Remede : dans un commentaire de signalement (`[ACTION]` / `[DIAG]` /
`[BASE-INHERITED]`), seule une reserve FORMELLE reste un nit. Un tag n'est
jamais un passe-droit : un verdict formel l'emporte toujours.

Aucun reseau : `classify` est pure, les donnees sont synthetiques (extrait
fidel du commentaire fondateur, phrases inchangees).
"""
import importlib.util
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_unaddressed_nits.py"
spec = importlib.util.spec_from_file_location("check_unaddressed_nits_27881", SCRIPT)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

# Extrait fidel du commentaire fondateur (#27368, 2026-11-20T17:50:34Z) :
# la phrase decisive est « la PR merite un regard de taille avant merge ».
FONDATEUR = (
    "[ACTION] lane myia-ai-01:CoursIA-2 — #27368 : le contenu de #27469 sort "
    "du perimetre, le perimetre reel est annonce, et le chemin de livraison de "
    "#27469 est trace (tete 6b4986ed39f5e)\n\n"
    "**2. La section Portee est recalee sur la realite.** Elle annoncait "
    "\"7 commits, 26 fichiers\" : c'est desormais **29 commits, 51 fichiers**, "
    "base `21e7399705b47`, et la liste des modules est remise a jour. J'y "
    "annonce aussi ce que tu peux mesurer toi-meme : le perimetre a grandi "
    "depuis ta revue — la PR merite un regard de taille avant merge, et je le "
    "dis dans le body plutot que de le laisser decouvrir.\n"
)


def _crlf(txt):
    return txt.replace("\n", "\r\n")


def test_le_commentaire_fondateur_n_est_plus_une_reserve():
    assert mod.classify("jsboige", FONDATEUR) is None


def test_le_transport_crlf_reste_muet():
    # Le transport Windows (CRLF) est la branche quilechturait le nit sur
    # d'autres commentaires (#19704) : les deux transports doivent sortir.
    assert mod.classify("jsboige", _crlf(FONDATEUR)) is None


def test_marqueur_lu_sur_premiere_ligne_non_vide():
    corps = "\n[ACTION] lane myia-ai-01:CoursIA-2\n\n" + FONDATEUR.split("\n", 1)[1]
    assert mod.classify("jsboige", corps) is None


def test_un_verdict_formel_reste_un_nit():
    # Le tag n'est pas un passe-droit : prefixer [ACTION] ne blanchit PAS un
    # verdict. Parite avec le test jumeau de #26364.
    for corps in (
        "[ACTION] lane x — CHANGES_REQUESTED : le point 2 casse.\n",
        "[ACTION] lane x — \U0001F7E1 le point 2 doit etre corrige.\n",
        "[ACTION] lane x — \U0001F534 bloquant : le point 2 doit etre corrige.\n",
        "[ACTION] lane x — pas de LGTM en l'etat : le point 2 casse.\n",
    ):
        assert mod.classify("jsboige", corps) == "BOT-CONCERN", corps


def test_la_demande_ask_reste_un_nit():
    # [ASK] = attente d'une decision tierce : c'est une demande, pas un
    # signalement. Elle reste bloquante.
    corps = "[ASK] lane x — il va falloir decider du perimetre avant merge.\n"
    assert mod.classify("jsboige", corps) == "BOT-CONCERN"


def test_un_commentaire_non_tague_garde_son_comportement():
    # Hors signalement, la PROSE continue de faire une reserve : le correctif
    # ne touche QUE les commentaires de signalement.
    corps = "Le point 2 est a changer avant merge.\n"
    assert mod.classify("jsboige", corps) == "BOT-CONCERN"


def test_un_prefixe_de_protocole_non_signalement_garde_son_comportement():
    # [INFO] et [CLAIMED] ne sont pas des commentaires de SIGNALEMENT : leur
    # comportement est inchange — la PROSE y fait toujours une reserve (le
    # correctif reste scope sur les trois tags ajoutes par #26364 et #15511).
    for prefixe in ("[INFO]", "[CLAIMED]", "[DELIVERED]"):
        corps = prefixe + " lane x — le point 2 est a changer avant merge.\n"
        assert mod.classify("jsboige", corps) == "BOT-CONCERN", prefixe


def test_une_reserve_formelle_sous_prefixe_de_protocole_reste_un_nit():
    corps = "[CLAIMED] lane x — CHANGES_REQUESTED : le point 2 casse.\n"
    assert mod.classify("jsboige", corps) == "BOT-CONCERN"
