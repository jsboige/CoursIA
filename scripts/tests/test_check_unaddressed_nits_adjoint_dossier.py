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


# --- #17065 : la QUEUE NARRATIVE du dossier n'est pas une reserve POSEE ---
#
# Defaut mesure (2026-09-19, #16862) : le strip #16442 ne retirait que le
# bloc delimite ; la queue narrative qui suit [/ADJOINT PREFLIGHT] -- que le
# gate ignore expressement (« Prose FOLLOWING the closing marker is ignored,
# not refused », check_adjoint_prevalidation.py) -- restait scannee par B.0.
# La phrase d'attestation OBLIGATOIRE « Aucun merge, APPROVED ou
# CHANGES_REQUESTED effectue ici » etait comptee comme une reserve posee :
# le dossier portant `b0: clear` devenait son propre bloquant, et via la
# delegation du picker (4e cause de repair -> cet organe), 8 lanes sur 8 en
# mode repair pendant que 313 issues sur 390 restaient admissibles.
#
# Forme reelle reconstruite du dossier #16862 (issuecomment 5745712744) :
# bloc schema v1 READY + queue de verifications firsthand + disposition.

DOSSIER_16862_AVEC_QUEUE = """[ADJOINT PREFLIGHT]
schema: 1
lane: myia-po-2027:CoursIA
pr: 16862
head: 0ee7c042750692c9015f6ae00fea30379fa665a1
complete: true
body: read
comments-reviewed: 4
reviews-reviewed: 0
threads-reviewed: 0
threads-unresolved: 0
surfaces-sha256: aadc60f68502db3e049fa3b46ab3d456836cab1bb9f2c1db0a4dff8359c9ff61
diff-files: 1
diff-additions: 140
diff-deletions: 140
checks: latest-wins-green
b0: clear
scope: pass
domain: pass
verdict: READY
[/ADJOINT PREFLIGHT]

Dossier de prevalidation tierce (gate #16907, Phase 4) — premier dossier sur cette PR.

### Verifications firsthand au head exact 0ee7c04275

- **B.0** : rc=0 ; 4 commentaires lus, 0 review, 0 thread inline.

**Disposition : READY pour lecture finale ai-01.** Aucun merge, APPROVED ou CHANGES_REQUESTED effectue ici.
"""


def test_dossier_ouvrant_queue_narrative_nest_pas_un_nit():
    # Echoue sur le code d'avant #17065 : la queue portait la phrase
    # d'attestation dont « CHANGES_REQUESTED » etait vivant.
    assert mod.classify("jsboige", DOSSIER_16862_AVEC_QUEUE) is None


def test_dossier_ouvrant_nest_pas_une_levee_queue_comprise():
    # La queue ne leve rien non plus (symetrie attestation, #16443) : un
    # dossier dont la queue RACONTE une disposition ne compte pas comme
    # evenement de levee.
    queue_levee = DOSSIER_16862_AVEC_QUEUE.replace(
        "**Disposition : READY pour lecture finale ai-01.**",
        "La reserve Hermes est levee par reponse ecrite a 22:10Z. **Disposition : READY.**",
    )
    stripped = mod._strip_adjoint_dossier(queue_levee)
    assert stripped == ""
    assert mod.has_live_lift(stripped) is False


def test_reserve_avant_le_dossier_ouvrant_reste_vivante():
    # Une vraie remarque PRECEDANT le bloc ouvrant reste lue normalement :
    # l'inertie ne s'etend qu'a la queue, jamais a la tete.
    prose = "Le fil inline #2 reste a nuancer sur la formulation exacte."
    assert mod.classify("jsboige", prose + "\n\n" + DOSSIER_16862_AVEC_QUEUE) is not None


def test_vraie_reserve_hors_dossier_reste_vivante():
    # Controle positif du contexte (pas de la liste) : une review qui POSE
    # un CHANGES_REQUESTED en dehors de tout dossier reste BOT-CONCERN.
    assert mod.classify("jsboige", "CHANGES_REQUESTED : decide casse en identifiant Lean, cellule 12.") is not None


# --- #18077 : 3e forme de #17065 -- dossier RETIRE par renommage des delimiteurs ---
#
# Mesure (ai-01, #16960, commentaire 5751421659, 2026-09-20) : un dossier
# retire en renommant ses delimiteurs `[ADJOINT-PREFLIGHT RETIRE]` gardait
# son bloc et sa queue narrative. Le span ne reconnaissait que la forme a
# espace : la phrase d'attestation de la queue redevenait une reserve POSEE
# que l'autrice de la PR ne pouvait pas lever -- ~8 h 30 de lane bloquee,
# levee seulement par DM coordinateur.

DOSSIER_RETIRE_TIRETS = (
    DOSSIER_16862_AVEC_QUEUE
    .replace("[ADJOINT PREFLIGHT]", "[ADJOINT-PREFLIGHT RETIRE]")
    .replace("[/ADJOINT PREFLIGHT]", "[/ADJOINT-PREFLIGHT RETIRE]")
)


def test_dossier_retire_par_tirets_nest_pas_un_nit():
    # Acceptance 1 -- echoue sur le code d'avant #18077 (BOT-CONCERN).
    assert mod.classify("jsboige", DOSSIER_RETIRE_TIRETS) is None


def test_variantes_de_delimiteurs_retires_sont_inertes():
    # Les formes derivees observees ou attendues : tiret sans suffixe,
    # espace avec suffixe. Chacune retire le bloc ET sa queue narrative.
    for ouvrant, fermant in (
        ("[ADJOINT-PREFLIGHT]", "[/ADJOINT-PREFLIGHT]"),
        ("[ADJOINT PREFLIGHT RETIRE]", "[/ADJOINT PREFLIGHT RETIRE]"),
        ("[ADJOINT-PREFLIGHT SUPERSEDE 2026-09-20]", "[/ADJOINT-PREFLIGHT SUPERSEDE]"),
    ):
        body = (
            DOSSIER_16862_AVEC_QUEUE
            .replace("[ADJOINT PREFLIGHT]", ouvrant)
            .replace("[/ADJOINT PREFLIGHT]", fermant)
        )
        assert mod.classify("jsboige", body) is None, ouvrant


def test_dossier_vivant_canonique_reste_une_attestation_entiere():
    # Acceptance 2 -- non-regression de #17070 : la forme canonique est
    # toujours retiree avec sa queue.
    assert mod._strip_adjoint_dossier(DOSSIER_16862_AVEC_QUEUE) == ""
    assert mod.classify("jsboige", DOSSIER_16862_AVEC_QUEUE) is None


def test_vraie_reserve_devant_un_bloc_retire_reste_bloquante():
    # Acceptance 3 -- une vraie reserve HUMAN adjacente au bloc retire
    # (en tete, hors du span) reste lue et bloquante.
    prose = "Le fil inline #2 reste a nuancer sur la formulation exacte."
    assert mod.classify("jsboige", prose + "\n\n" + DOSSIER_RETIRE_TIRETS) is not None


def test_bloc_retire_malforme_sans_fermant_nest_pas_retire():
    # Fail-closed inchange : un ouvrant renomme sans fermant ne blanchit rien.
    malforme = DOSSIER_RETIRE_TIRETS.replace("[/ADJOINT-PREFLIGHT RETIRE]", "")
    assert mod.classify("jsboige", malforme) is not None


def test_mention_en_ligne_du_delimiteur_nouvre_pas_de_span():
    # Le delimiteur cite dans une phrase (pas en debut de ligne) n'ouvre
    # aucun span : la reserve qui l'entoure reste lue.
    body = (
        "Le bloc [ADJOINT-PREFLIGHT RETIRE] ne leve pas le thread inline #2, "
        "qui reste a nuancer.\n\nCHANGES_REQUESTED : cellule 12."
    )
    assert mod.classify("jsboige", body) is not None
