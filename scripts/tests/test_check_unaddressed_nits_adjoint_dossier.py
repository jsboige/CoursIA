"""Tests #16442/#16443 — un bloc [ADJOINT PREFLIGHT] est une ATTESTATION, pas une remarque.

Defaut mesure (2026-09-16, #16173) : l'organe B.0 attrapait le
`verdict: BLOCKED` d'un dossier adjoint SUPERSEDE comme un nit [HUMAN] non
leve -- le dossier devenait son propre bloquant, et le remede etait un
PATCH manuel du commentaire (pierre tombale + neutralisation des
marqueurs). La PR #16449 a reproduit le motif des 23:35Z (dossier interim
de lane a cheval sur la mutation de tete).

La separation des organes est le principe du fix : le VERDICT d'un dossier
appartient au gate `check_adjoint_prevalidation.py` (#16443), qui le
fail-close a l'empreinte pres ; l'organe nits lit des REMARQUES a lever.
Un bloc schema v1 entre ses delimiters `[ADJOINT PREFLIGHT]` /
`[/ADJOINT PREFLIGHT]` est une attestation machine-lisible : ni reserve,
ni levee.

Les tests sont ecrits par leurs FAUX POSITIFS (un jeu de motifs se valide
par les formes qu'il doit neutraliser, cf anti-regression.md) : les
premiers ECHOUENT sur le code d'avant, les controles suivants passent des
deux cotes et bornent le retrait (une phrase de reserve HORS du bloc reste
vie ; un bloc MALFORME sans delimiter fermant n'est pas retire --
fail-closed sur la malformation, comme le gate).
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


# Dossier BLOCKED reconstruit de la forme exacte du dossier #16173
# (issuecomment 5705104466 avant archivage) : schema v1, verdict BLOCKED,
# note portant la phrase de recommandation qui emettait ("avant merge").
DOSSIER_16173_BLOCKED = """[ADJOINT PREFLIGHT]
schema: 1
lane: myia-po-2025:CoursIA-2
pr: 16173
head: 3ebeea7b4bd4710e399f27d3dc699582bd38058
complete: true
body: read
comments-reviewed: 6
reviews-reviewed: 2
threads-reviewed: 3
threads-unresolved: 1
surfaces-sha256: 0000000000000000000000000000000000000000000000000000000000000000
diff-files: 2
diff-additions: 48
diff-deletions: 0
checks: latest-wins-green
b0: blocked
scope: pass
domain: pass
verdict: BLOCKED
note: thread inline #2 non leve au head -- re-review exact-head exigee avant merge
[/ADJOINT PREFLIGHT]"""

# Dossier interim d'une lane (forme reelle #16449, 2026-09-16T23:35:02Z) :
# laneattribue, verdict hors enum, honnete sur l'attente CI. Aucun marqueur
# de reserve ne doit en sortir non plus.
DOSSIER_16449_INTERIM = """[ADJOINT PREFLIGHT]
schema: 1
lane: myia-po-2026:CoursIA
pr: 16449
head: c02e81fa9e3476b8f35426032b357f53abd60fe2
complete: true
body: read
comments-reviewed: 7
reviews-reviewed: 1
threads-reviewed: 0
threads-unresolved: 0
surfaces-sha256: 48f9cbadde57ca4850f2094842822d26c51a95c41282ca8e1f4c7369356a1617
diff-files: 2
diff-additions: 72
diff-deletions: 0
checks: new-head-in-flight
b0: clear
scope: pass
domain: pass
verdict: REPAIR-APPLIED-AWAITING-CI
note: reagregation DWELL requise au nouveau head ; definition demandee au coordinateur par DM
[/ADJOINT PREFLIGHT]"""

# Pierre tombale (remede manuel #16173) : prose d'archive + bloc neutralise.
TOMBSTONE_16173 = """[ARCHIVE 2026-09-16] Dossier supersede par la mutation de tete -- cf dossier frais en fin de fil.

[ADJOINT PREFLIGHT]
schema: 1
verdict: (archive)
b0: (archive)
[/ADJOINT PREFLIGHT]"""


# --- Les faux positifs que l'organe comptait comme nits (echouent avant fix) ---

def test_dossier_bloque_nest_pas_un_nit():
    assert mod.classify("jsboige", DOSSIER_16173_BLOCKED) is None


def test_dossier_interim_nest_pas_un_nit():
    assert mod.classify("jsboige", DOSSIER_16449_INTERIM) is None


def test_tombstone_nest_pas_un_nit():
    assert mod.classify("jsboige", TOMBSTONE_16173) is None


def test_dossier_pur_nest_pas_une_levee():
    # Un dossier dont la note RACONTE une levee ("levee par Hermes") ne doit
    # pas compter comme evenement de levee : l'attestation ne leve rien.
    body = DOSSIER_16449_INTERIM.replace(
        "note: reagregation DWELL",
        "note: reserve Hermes levee par reponse ecrite a 22:10Z ; reagregation DWELL",
    )
    stripped = mod._strip_adjoint_dossier(body)
    assert mod.has_live_lift(stripped) is False


# --- Controles : ce que le retrait ne doit PAS neutraliser (passent des deux cotes) ---

def test_reserve_hors_du_bloc_reste_vivante():
    # Meme genre de remarque, HORS du bloc : c'est une remarque ordinaire.
    # (Prose sans mot de levee -- « merge. » en fin de phrase serait lu comme
    # une annonce de merge par l'etage LIFT, confondant le controle.)
    prose = "Le fil inline #2 reste a nuancer sur la formulation exacte."
    assert mod.classify("jsboige", prose) is not None  # vivante seule
    body = prose + "\n\n" + DOSSIER_16173_BLOCKED
    assert mod.classify("jsboige", body) is not None  # vivante aussi devant un bloc


def test_bloc_malforme_sans_fermant_nest_pas_retire():
    # Delimiter ouvrant sans fermant : le gate (check_adjoint_prevalidation)
    # refuse ce dossier ; l'organe ne doit pas non plus le blanchir.
    malformed = DOSSIER_16173_BLOCKED.replace("[/ADJOINT PREFLIGHT]", "")
    assert mod.classify("jsboige", malformed) is not None


def test_prose_de_tombstone_avec_reserve_reste_vivante():
    body = TOMBSTONE_16173.replace(
        "Dossier supersede",
        "Dossier supersede MAIS le thread inline #2 reste a nuancer avant merge",
    )
    assert mod.classify("jsboige", body) is not None


def test_strip_neutralise_le_span_et_garde_le_reste():
    body = "Avant le dossier.\n\n" + DOSSIER_16173_BLOCKED + "\n\nApres le dossier."
    stripped = mod._strip_adjoint_dossier(body)
    assert "verdict: BLOCKED" not in stripped
    assert "Avant le dossier." in stripped
    assert "Apres le dossier." in stripped
