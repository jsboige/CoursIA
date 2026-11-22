"""Temoins du correctif #27875 -- un lake INTRODUIT par une PR et non declare.

Defaut fondateur : PR #27587 (lake `busybeaver_lean`). La PR cree le lake
(dossier + `lakefile.lean` + `lean-toolchain` + sources) mais l'entree de
manifeste `scripts/lean/ci_lakes.json` arrive dans une PR EMPILEE (#27658).
Ni l'organe d'attestation (qui selectionne ses lakes dans le manifeste de la
TETE) ni la garde `merge_ready` ne pouvaient nommer le lake : le blocage rendu
etait muet, et l'empilement se refermait sur lui-meme.

Ce fichier porte les temoins UNITAIRES du module partage
`scripts/lean/lean_build_attestation.py` (la detection d'un lake touche par le
diff et non declare au manifeste). Les temoins de bout en bout de la garde
vivent dans `scripts/tests/test_merge_ready.py` (la qui a le harnais).

Acceptance :
  1. La racine d'un lake se deduit de son `lakefile.*` -- un `.lean` seul ne
     nomme pas de racine (on ne devine pas).
  2. Un lake touche par le diff et ABSENT du manifeste est signale.
  3. Un lake touche par le diff et DECLARE (par `project-path` ou par ses
     `paths`) n'est PAS signale.
  4. Un manifeste illisible ne signale rien (absence d'information).
"""

from __future__ import annotations

import base64
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lean"))

import lean_build_attestation as lba  # noqa: E402


#: Racine du lake introduit par la PR #27587 (cas fondateur).
BUSYBEAVER = "MyIA.AI.Notebooks/SymbolicAI/Lean/busybeaver_lean"
BUSYBEAVER_LAKEFILE = BUSYBEAVER + "/lakefile.lean"
#: Un lake deja declare au manifeste (entree `conway`).
CONWAY = "MyIA.AI.Notebooks/SymbolicAI/Lean/GOL/conway_lean"
CONWAY_LAKEFILE = CONWAY + "/lakefile.lean"

#: Manifeste minimal : un lake declare (`conway`), et rien pour busybeaver.
MANIFEST = {
    "version": 1,
    "lakes": [
        {
            "lake": "conway",
            "project-path": CONWAY,
            "paths": [
                CONWAY + "/**.lean",
                CONWAY + "/lakefile.lean",
                CONWAY + "/lean-toolchain",
            ],
        }
    ],
}


# ---------------------------------------------------------------------------
# Acceptance 1 -- la racine se deduit du `lakefile.*`
# ---------------------------------------------------------------------------

def test_racine_deduite_du_lakefile():
    """Le repertoire qui porte le `lakefile` est la racine du lake."""
    assert lba.lake_root_of_path(BUSYBEAVER_LAKEFILE) == BUSYBEAVER
    assert lba.lake_root_of_path(BUSYBEAVER + "/lakefile.toml") == BUSYBEAVER


def test_un_lean_seul_ne_nomme_pas_de_racine():
    """Un `.lean` seul ne permet pas de nommer la racine : on ne devine pas."""
    assert lba.lake_root_of_path(BUSYBEAVER + "/BusyBeaver.lean") == ""
    assert lba.lake_root_of_path("src/a.lean") == ""


def test_un_fichier_non_lean_ne_nomme_pas_de_racine():
    assert lba.lake_root_of_path(BUSYBEAVER + "/lean-toolchain") == ""
    assert lba.lake_root_of_path("docs/a.md") == ""


def test_chemins_windows_avec_antislash():
    """Un chemin Windows (`\\`) se normalise comme un chemin de depot."""
    assert lba.lake_root_of_path(
        BUSYBEAVER.replace("/", "\\") + "\\lakefile.lean") == BUSYBEAVER


# ---------------------------------------------------------------------------
# Acceptance 2 -- le lake introduit et non declare est signale
# ---------------------------------------------------------------------------

def test_lake_introduit_non_declare_est_signale():
    """#27875 -- cas fondateur : la PR introduit `busybeaver_lean`, le
    manifeste ne le declare pas -> la racine est signalee."""
    files = [
        BUSYBEAVER_LAKEFILE,
        BUSYBEAVER + "/lean-toolchain",
        BUSYBEAVER + "/BusyBeaver.lean",
        "MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-42-BusyBeaver-Lean.ipynb",
    ]
    assert lba.undeclared_lakes(files, MANIFEST) == [BUSYBEAVER]


def test_le_lake_declare_n_est_pas_signale():
    """Controle negatif : `conway` est declare -> rien a signaler."""
    files = [CONWAY_LAKEFILE, CONWAY + "/Conway.lean"]
    assert lba.undeclared_lakes(files, MANIFEST) == []


def test_declaration_par_project_path_suffit():
    """Controle negatif : une entree qui ne declare que `project-path`
    (sans `paths`) declare quand meme le lake."""
    manifest = {"lakes": [{"lake": "conway", "project-path": CONWAY}]}
    assert lba.undeclared_lakes([CONWAY_LAKEFILE], manifest) == []


def test_declaration_par_paths_suffit():
    """Controle negatif : une entree dont les `paths` couvrent le lakefile
    declare le lake, meme sans `project-path`."""
    manifest = {"lakes": [{"lake": "conway", "paths": [CONWAY + "/**"]}]}
    assert lba.undeclared_lakes([CONWAY_LAKEFILE], manifest) == []


def test_les_chemins_sans_lakefile_ne_signalent_rien():
    """Un diff sans `lakefile` ne peut pas introduire de lake."""
    files = [
        "MyIA.AI.Notebooks/SymbolicAI/Lean/Conway.lean",
        "scripts/lean/ci_lakes.json",
    ]
    assert lba.undeclared_lakes(files, MANIFEST) == []


def test_les_racines_sont_rendues_triees_sans_doublon():
    """Deux fichiers du meme lake ne produisent qu'une racine ; le rendu est
    trie (determinisme de l'organe)."""
    files = [
        BUSYBEAVER + "/lakefile.toml",
        BUSYBEAVER_LAKEFILE,
        CONWAY_LAKEFILE,
    ]
    assert lba.undeclared_lakes(files, MANIFEST) == [BUSYBEAVER]


# ---------------------------------------------------------------------------
# Acceptance 4 -- un manifeste illisible ne signale rien
# ---------------------------------------------------------------------------

def test_manifeste_absent_ne_signale_rien():
    """`None` = absence d'information : aucun lake signale (la garde retombe
    alors sur son motif generique, fail-closed conserve)."""
    assert lba.undeclared_lakes([BUSYBEAVER_LAKEFILE], None) == []


def test_manifeste_lu_vide_signale_le_lake_touche():
    """Un manifeste LU ( meme vide) est une preuve : le lake touche n'y est
    pas declare -> il est signale. La difference avec `None` est
    intentionnelle : illisible != vide."""
    assert lba.undeclared_lakes([BUSYBEAVER_LAKEFILE], {}) == [BUSYBEAVER]


def test_entree_non_dict_ignoree():
    """Une entree malformee ne fait pas planter la detection."""
    manifest = {"lakes": ["pas-un-dict", {"lake": "conway", "project-path": CONWAY}]}
    assert lba.undeclared_lakes([CONWAY_LAKEFILE], manifest) == []


# ---------------------------------------------------------------------------
# La lecture de la payload REST -- une seule definition du "illisible"
# ---------------------------------------------------------------------------

def _payload(manifest: dict) -> dict:
    raw = json.dumps(manifest).encode("utf-8")
    return {"content": base64.b64encode(raw).decode("ascii")}


def test_payload_manifeste_lue():
    """La payload REST `contents` porte le manifeste en base64."""
    manifest = lba.manifest_from_api_payload(_payload(MANIFEST))
    assert manifest == MANIFEST


def test_payload_illisible_rend_none():
    """Une payload sans `content`, au contenu non base64, ou non-JSON rend
    None (jamais un accord). Un JSON valide mais vide rend le MANIFESTE lu
    (`{}`) -- c'est une preuve, pas une absence d'information."""
    assert lba.manifest_from_api_payload({}) is None
    assert lba.manifest_from_api_payload({"content": "pas-du-base64!!"}) is None
    assert lba.manifest_from_api_payload("pas-un-dict") is None
    assert lba.manifest_from_api_payload({"content": "e30="}) == {}  # "{}"


def test_la_detection_tourne_sur_le_manifeste_lu():
    """Boucle complete : payload REST -> manifeste -> lake non declare."""
    manifest = lba.manifest_from_api_payload(_payload(MANIFEST))
    assert lba.undeclared_lakes([BUSYBEAVER_LAKEFILE], manifest) == [BUSYBEAVER]
