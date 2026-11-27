#!/usr/bin/env python3
"""Tests du RECUL du tapis (#27059) -- les ecarts qui ne refusent jamais.

Le tapis ne refuse jamais (continue.md P3) : une issue COUVERTE, RELACHEE
ou MERGEE est servie APRES les autres, dans un second palier. Ces tests
vivent dans leur propre fichier : la suite du tapis (`test_tapis_rapide.py`)
tient son plafond de lignes, et le recul a extrait son module
(`tapis_recul.py`) et ses tests pour la meme raison (#27059).

Les aides (`issue`, `com`, `lecture`, `_familles`, `_dossier`) viennent du
fichier de la suite : les construire ici les dupliquerait.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from coordination import tapis_rapide as tr
from test_tapis_rapide import (  # noqa: E402
    AUTRE,
    LANE,
    NOW,
    _dossier,
    _familles,
    _h,
    com,
    issue,
    lecture,
)

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")


def test_le_recul_sert_apres_et_ne_franchit_aucun_verrou():
    """Le tapis ne refuse jamais (continue.md P3) : COUVERTE, RELACHEE et MERGEE
    servent l'issue APRES les autres. Un ecart dur (PLAFOND) l'emporte sur un
    recul, et un claim vivant d'une autre lane verrouille une issue en recul."""
    rendue = f"[RELEASED] lane {AUTRE} -- barriere reelle, mesuree"
    prs = [{"number": 900, "title": "Fix(x,#2): y", "body": f"Grain: x -- lane {AUTRE}"},
           {"number": 901, "title": "Fix(x,#4): y", "body": f"Grain: x -- lane {AUTRE}"}]
    lec = lecture([
        issue(1),
        issue(2),                                         # COUVERTE : recul
        issue(3, comments=[com(24, rendue)]),             # RELACHEE : recul
        issue(4, comments=[com(2, f"[CLAIMED] lane {AUTRE} -- je prends")]),
        issue(5, labels=["EPIC"], comments=[             # PLAFOND (dur) + RELACHEE
            com(30, f"[CLAIMED] lane {AUTRE} -- paths: x/**"), com(24, rendue)]),
    ], prs=prs)
    tous = tr.etats(lec, LANE, NOW)
    par = {e.numero: e for e in tous}
    assert par[2].ecart == "COUVERTE" and tr.servable(par[2])
    assert par[2].notes[-1].startswith("servie en recul (COUVERTE)")
    assert par[3].ecart == "RELACHEE" and tr.servable(par[3])
    assert par[4].ecart == "RECLAMEE" and not tr.servable(par[4])  # verrou tenu
    assert par[5].ecart == "PLAFOND" and not tr.servable(par[5])   # le dur l'emporte
    file = [e.numero for e in tr.ordonner(tous, LANE, NOW, 8)]
    assert file[0] == 1 and sorted(file[1:]) == [2, 3]  # servies, apres l'issue libre


def test_un_grain_en_recul_passe_devant_un_conteneur_hors_quota():
    """#26926 : un conteneur ne passe jamais devant un grain, meme en recul.
    Quatre places, quota conteneurs de 1 : le grain libre, un conteneur dans
    son quota, puis les deux grains en recul -- les conteneurs hors quota ne
    comblent que ce qui reste."""
    rendue = f"[RELEASED] lane {AUTRE} -- barriere reelle, mesuree"
    prs = [{"number": 900, "title": "Fix(x,#2): y", "body": f"Grain: x -- lane {AUTRE}"}]
    lec = lecture([
        issue(1),
        issue(2),                                         # COUVERTE : recul
        issue(3, comments=[com(24, rendue)]),             # RELACHEE : recul
        issue(10, titre="[EPIC] a"), issue(11, titre="[EPIC] b"),
        issue(12, titre="[EPIC] c"),
    ], prs=prs)
    file = tr.ordonner(tr.etats(lec, LANE, NOW), LANE, NOW, 4)
    assert sorted(e.numero for e in file if not e.conteneur) == [1, 2, 3]
    assert sum(e.conteneur for e in file) == 1  # le seul conteneur du quota


def test_le_cli_sert_l_issue_en_recul_apres_les_grains_sans_ecart(tmp_path, capsysbinary):
    """Le CLI DIT le recul : l'issue COUVERTE sort des ecartees et revient
    dans `en_recul`, servie apres les grains sans ecart -- l'ordre le prouve."""
    prs = [{"number": 900, "title": "Ma PR", "body": f"Grain: x -- lane {LANE}\nSee #1",
            "created_at": _h(30)}]
    dossier = _dossier(tmp_path, _familles(3) + [issue(1)], prs)
    code = tr.main(["--lane", LANE, "--lecture", str(dossier), "--json"],
                   run=lambda argv, timeout: "")
    sortie = json.loads(capsysbinary.readouterr().out.decode("utf-8"))
    assert code == 0 and len(sortie["grains"]) == 7
    assert "COUVERTE" not in sortie["ecartees"]
    assert sortie["en_recul"]["COUVERTE"] == [{"numero": 1, "motif":
                                               "votre PR #900 la cite : portez-la au merge",
                                               "feuille": True}]
    # apres les six grains sans ecart (#28642 : le tour sert d'abord les jamais visitees)
    assert [g["numero"] for g in sortie["grains"]].index(1) == 6
    assert sortie["lecture"]["servables"] == 7 and sortie["lecture"]["en_recul"] == 1
