"""Tests for #15837 — narration retrospective FRANCAISE dans `CITERS`.

`CITERS` distingue une EMISSION de verdict (« je pose un CHANGES_REQUESTED »)
d'une CITATION (« mon CHANGES_REQUESTED precedent etait un faux positif »).
Sans elle, tout texte prononcant le mot bloquerait le merge. La liste
reconnaissait la narration en anglais ("previous", "stale", "earlier") et les
negations francaises ("pas de", "aucun"), mais AUCUN verbe de narration
retrospective en francais — alors que les lanes redigent en francais.

Defaut fondateur : le commentaire de #15762 (embarque ici VERBATIM) bloquait
le merge sur `dissipation CHANGES_REQUESTED c.589 leve`, une phrase qui declare
l'inverse d'une reserve. Mesure : `rc=1` avant, `rc=0` apres.

Deux exigences d'acceptation portent sur ce fichier :

  - le commentaire reel de #15762 devenu NEUTRALISE ;
  - un CONTROLE POSITIF ecrit exprès — un commentaire qui emet reellement
    `CHANGES_REQUESTED:` dans une phrase contenant le mot `dissipation`
    ailleurs — qui DOIT continuer a bloquer. Un assouplissement de filet qu'on
    n'a jamais vu refuser de s'appliquer n'est pas mesure, il est suppose ; et
    du cote permissif, une supposition se paie en reserve manquee (#10761).

Le controle `test_15837_candidat_refuse_levee_devant_le_marqueur` documente le
candidat ECARTE : « levee » mesurait lui aussi 5/5 narrations, mais un
participe peut qualifier un AUTRE nom que le marqueur, la ou un nom ne le peut
pas. Motif : mesure 2000 PRs mergees (2026-08-22..2026-09-12), 13113 corps,
2472 occurrences de marqueur — `dissipation` 7/7 narrations, `levee` 5/5, et
le controle ci-dessous fait refuser `levee` malgre son taux.

Aucun appel reseau : `classify` est pure, on lui passe le corps.
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


# Corps REEL du commentaire de myia-po-2024:CoursIA-2 sur #15762
# (2026-09-12T16:26Z), verbatim. Il porte DEUX occurrences de
# `CHANGES_REQUESTED` : celle a l'offset ~407 (« dissipation CHANGES_REQUESTED
# c.589 leve »), qui bloquait, et celle a ~530 (« 0 CHANGES_REQUESTED »), deja
# neutralisee par le citer « 0 » (#11916).
REAL_15762 = """\
Dissipation Tell c.589 + c.1079-L1 ★ NEW fondateur + c.1060-L1 ★ NEW fondateur (c.1102 sur head `a2bdc9789a42`, 2026-09-12 ~16:30Z)

**#15762** head actuel `a2bdc9789a42` (UNKNOWN → CLEAN c.1102). Branch `fix/<sujet>`. Statut `mergeable: true` + `mergeStateStatus: CLEAN` ✓ ripe merge ai-01 Tell c.R1.

**Reviews actives** : aucune. PR dans son état final.

**Tell c.1079-L1 ★ NEW fondateur** : dissipation CHANGES_REQUESTED c.589 levé N-1/N ET cross-base c.1063-L1 = ripe merge. PR dans son état final — tous checks SUCCESS ✓, 0 CHANGES_REQUESTED.

**Tell c.1060-L1 ★ NEW fondateur** : dissipation cumule multi-reviews + multi-merges main.

**Tell c.1059 ★ NEW fondateur** : dissipation nominative ≠ amend.

**Action attendue ai-01 Tell c.R1** : ripe merge séquentiel Tell c.R1.

— lane myia-po-2024:CoursIA-2, cycle c.1102 (431ᵉ) ~16:30Z
"""


# ---------------------------------------------------------------------------
# Le defaut fondateur : le commentaire reel ne bloque plus
# ---------------------------------------------------------------------------

def test_15837_commentaire_reel_15762_neutralise():
    """`rc=1` -> `rc=0` : le corps reel de #15762 ne porte plus de reserve."""
    assert mod.classify("myia-po-2024", REAL_15762) is None
    assert mod.has_live_marker(REAL_15762, mod.CONCERN_MARKERS) is False


def test_15837_commentaire_reel_porte_bien_le_marqueur():
    """Contre-epreuve : le corps contient bien `CHANGES_REQUESTED`. Sans cette
    assertion, le test precedent passerait aussi sur un corps vide — il
    mesurerait l'absence de marqueur, pas la neutralisation."""
    assert "CHANGES_REQUESTED" in REAL_15762
    assert REAL_15762.count("CHANGES_REQUESTED") == 2


# ---------------------------------------------------------------------------
# CONTROLE POSITIF (exige par l'acceptance) — une emission reelle bloque
# ---------------------------------------------------------------------------

def test_15837_controle_positif_emission_avec_dissipation_ailleurs():
    """Un commentaire qui EMET reellement `CHANGES_REQUESTED:` dans une phrase
    contenant `dissipation` AILLEURS doit continuer a bloquer. C'est le
    controle qui distingue « le mot narre » de « le mot neutralise tout le
    corps »."""
    body = ("La dissipation des reserves anciennes est acquise et documentee.\n"
            "\n"
            "CHANGES_REQUESTED: le split manque sur le head neuf.")
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_15837_controle_positif_dissipation_adjacente_a_une_emission():
    """Cas le plus dur : `dissipation` A MOINS DE 30 CARACTERES d'une emission
    reelle. La fenetre s'arrete au mot terminal — `dissipation du bruit` ne
    neutralise pas un `CHANGES_REQUESTED` qui suit, parce que le mot terminal
    de la fenetre est `bruit`, pas `dissipation`."""
    body = "dissipation du bruit amont OK.\n\nCHANGES_REQUESTED: il reste 2 points."
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


# ---------------------------------------------------------------------------
# Controles negatifs : les emissions nues restent vivantes
# ---------------------------------------------------------------------------

def test_15837_emissions_nues_restent_vivantes():
    """Aucune forme d'emission directe ne doit etre neutralisee par l'ajout."""
    emissions = (
        "Je pose un CHANGES_REQUESTED sur cette PR.",
        "Verdict : CHANGES_REQUESTED",
        "**CHANGES_REQUESTED: 2 points**\n- le split manque",
        "CONCERNS: le contrat n'est pas respecte",
    )
    for body in emissions:
        assert mod.classify("jsboige", body) == "BOT-CONCERN", body


# ---------------------------------------------------------------------------
# Les narrations mesurees sont neutralisees
# ---------------------------------------------------------------------------

def test_15837_narrations_dissipation_mesurees_neutralisees():
    """Les 7 occurrences mesurees de `dissipation` (nom terminal devant le
    marqueur) : toutes des narrations de levee."""
    narrations = (
        "**Tell c.1079-L1** : dissipation CHANGES_REQUESTED c.589 leve N-1/N = ripe merge.",
        "### dissipation CHANGES_REQUESTED c.1105 — head post-repair",
        "3 organes (c.1105 dissipation CHANGES_REQUESTED)",
        "+ c.1090 dissipation CHANGES_REQUESTED + c.1092 repair footer",
    )
    for body in narrations:
        assert mod.has_live_marker(body, mod.CONCERN_MARKERS) is False, body


# ---------------------------------------------------------------------------
# Le candidat ECARTE, et pourquoi (meme liste, meme fenetre, taux pourtant bon)
# ---------------------------------------------------------------------------

def test_15837_candidat_refuse_levee_devant_le_marqueur():
    """`levee` mesurait 5/5 narrations et a pourtant ete ECARTE de `CITERS`.

    Un NOM ne peut ici que signifier « dissipation DU verdict » — il est le
    dernier mot devant lui. Un PARTICIPE, lui, peut qualifier un AUTRE nom :
    « la reserve est levee. » est une clause COMPLETE, et la reserve qui suit
    est NEUVE. Ce test ECHOUE si on ajoute `levee` a `CITERS` (la premiere
    assertion tombe), et la simulation sous `finally` rend le cout visible
    plutot que suppose : la reserve vivante devient invisible au niveau
    `has_live_marker`, celui ou le candidat agirait."""
    body = ("Bonne nouvelle : la reserve est levee.\n\n"
            "CHANGES_REQUESTED: nouveau point sur le head.")
    assert mod.has_live_marker(body, mod.CONCERN_MARKERS) is True
    original = mod.CITERS
    mod.CITERS = original + ("levee",)
    try:
        assert mod.has_live_marker(body, mod.CONCERN_MARKERS) is False
    finally:
        mod.CITERS = original


def test_15837_residu_assume_narration_levee_avant_merge():
    """Residu ASSUME et documente : « La reserve est levee avant merge. » reste
    flagee. C'est un faux positif a trier, pas une reserve manquee — le cote
    bon marche de l'asymetrie. Ce test fige le residu pour qu'une PR future ne
    le « corrige » pas en rouvrant le faux negatif ci-dessus."""
    body = "La reserve est levee avant merge."
    assert mod.has_live_marker(mod._strip_quoted(body), mod.CONCERN_MARKERS) is True


if __name__ == "__main__":
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    failed = 0
    for fn in tests:
        try:
            fn()
            print(f"PASS {fn.__name__}")
        except Exception as exc:  # noqa: BLE001
            failed += 1
            print(f"FAIL {fn.__name__}: {type(exc).__name__}: {exc}")
    print(f"\n{len(tests) - failed}/{len(tests)} tests passes")
    sys.exit(1 if failed else 0)
