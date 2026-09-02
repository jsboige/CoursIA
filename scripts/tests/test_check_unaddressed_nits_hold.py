"""Tests #13779 facette B — le gate B.0 et le verbe HOLD du coordinateur.

Defaut mesure : `.claude/rules/variation-protocol.md` §3 donne au coordinateur
UN verbe pour retenir une PR — **HOLD** (« HOLD sans remplacement = echec
coordinateur », « HOLD : citer la sortie de variation_light_cap.py »). Le gate,
lui, ne connaissait que BLOCAGE / BLOCK. Le post reel de myia-ai-01 sur #13712
(2026-08-30T22:19:57Z) — « **HOLD coordinateur — un point du preflight reste
ouvert, et le gate ne le voit pas.** » — rendait donc `classify -> None` : un
gate de merge aveugle au verbe de l'instrument qui le pilote.

Les tests sont ecrits par leurs FAUX NEGATIFS (un jeu de motifs se valide par
les formes qu'il doit attraper, jamais par ses hits, cf anti-regression.md) :
les cinq premiers ECHOUENT sur le code d'avant, les suivants sont des controles
qui passent des deux cotes et bornent l'elargissement.

La pose de HOLD est PLUS STRICTE que celle de BLOCAGE, sur deux axes, parce que
« hold » est un mot ordinaire la ou « blocage » est deja presque toujours un
verdict : tete de CORPS (pas n'importe ou dans les 60 premiers chars) et
MAJUSCULE (la forme du protocole). Les controles ci-dessous fixent ces deux
bornes — sans elles, « je ne mets pas de hold sur cette PR » bloquerait.
"""

import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_unaddressed_nits.py"

spec = importlib.util.spec_from_file_location("check_unaddressed_nits", CHECK_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits"] = mod
spec.loader.exec_module(mod)

# Corps EXACT du commentaire myia-ai-01 du 2026-08-30T22:19:57Z sur la PR #13712
# (tete seule : la suite est le detail du preflight, sans effet sur la pose).
FIXTURE_13712_HOLD = (
    "**HOLD coordinateur — un point du preflight reste ouvert, "
    "et le gate ne le voit pas.**"
)


# --- Les cinq formes que l'organe ratait (echouent sur le code d'avant) ---

def test_13779_hold_reel_de_13712_est_une_emission():
    assert mod._block_emitted(FIXTURE_13712_HOLD) is True


def test_13779_hold_reel_de_13712_est_classe_block():
    assert mod.classify("myia-ai-01", FIXTURE_13712_HOLD) == "BLOCK"


def test_13779_marqueur_hold_lane_en_tete_de_ligne():
    body = """Preflight en cours, deux points a verifier.

[HOLD] lane myia-po-2025:CoursIA — budget LIGHT epuise (3 pour 6 grains).
"""
    assert mod._block_emitted(body) is True


def test_13779_hold_en_titre_markdown():
    body = """## HOLD coordinateur

Le plancher G-VAR-1 n'est pas tenu : le genre est META.
"""
    assert mod._block_emitted(body) is True


def test_13779_hold_nu_sans_emphase():
    body = "HOLD — je tiens cette PR le temps que la lane nomme son remplacant."
    assert mod._block_emitted(body) is True


# --- Controles : les bornes de l'elargissement (passent des deux cotes) ---

def test_13779_hold_minuscule_en_prose_ne_pose_rien():
    # Sans la borne de CASSE, ce corps bloquerait la PR.
    body = "hold on, je regarde le rapport d'echec avant de me prononcer."
    assert mod._block_emitted(body) is False


def test_13779_hold_nomme_en_milieu_de_phrase_ne_pose_rien():
    # Sans la borne de POSITION, ce corps — qui dit l'exact contraire —
    # bloquerait la PR : le mot tombe dans les 60 premiers caracteres.
    body = "Je ne mets pas de HOLD sur cette PR, elle est saine. Je merge."
    assert mod._block_emitted(body) is False


def test_13779_hold_leve_est_une_levee_pas_une_emission():
    body = "**HOLD leve** — la lane a nomme son grain de contenu, je merge."
    assert mod._block_emitted(body) is False


def test_13779_hold_lifted_anglais_est_une_levee():
    body = "HOLD lifted — the coordinator named the replacement grain."
    assert mod._block_emitted(body) is False


def test_13779_override_en_tete_reste_exempte():
    # L'override est l'etage superieur du protocole (#11639) : un arbitrage qui
    # NOMME le hold qu'il leve ne doit pas se re-bloquer lui-meme.
    body = "[OVERRIDE] lane myia-po-2025:CoursIA — HOLD coordinateur leve, budget recompte."
    assert mod._block_emitted(body) is False


def test_13779_hold_cite_en_blockquote_ne_pose_rien():
    body = """> **HOLD coordinateur — budget LIGHT epuise.**

C'est traite : le grain est requalifie MED/notebook-python, cf commit 24799875f.
"""
    assert mod._block_emitted(body) is False


def test_13779_marqueur_hold_lane_en_backticks_ne_pose_rien():
    body = "Le protocole ecrit `[HOLD] lane <machine:workspace>` — je documente la forme."
    assert mod._block_emitted(body) is False


def test_13779_frontiere_de_mot_holder_ne_pose_rien():
    body = "HOLDER de la lane, je confirme que le grain est pris."
    assert mod._block_emitted(body) is False


# --- Regression : les deux formes historiques sont intactes ---

def test_13779_blocage_verdict_en_tete_emet_toujours():
    assert mod._block_emitted("**BLOCAGE — le preflight n'est pas passe.**") is True


def test_13779_blocage_lane_emet_toujours():
    assert mod._block_emitted("[BLOCAGE] lane myia-po-2023:CoursIA — scope non tenu.") is True


def test_13779_blocage_leve_ne_pose_toujours_rien():
    assert mod._block_emitted("**BLOCAGE leve** — le point est traite, je merge.") is False
