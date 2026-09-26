"""Tests de `check_twin_index_collisions.py` (organe de collision inter-revisions).

La regle testee est celle du module :

    union = tous les noms vus pour un (paire, index) sur les revisions
    si une revision contient deja toute l'union  ->  rien
    sinon, si |union| > 1                         ->  collision inter-revisions

Le cas « deja couvert par une revision » est le doublon intra-revision, celui
que `test_twin_registry_integrity.py` fait rougir sur `main`. Les deux verdicts
doivent rester DISTINCTS : un organe qui confondrait les deux accuserait une PR
d'un doublon que `main` porte deja.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_twin_index_collisions import (  # noqa: E402
    exit_code,
    find_conflicts,
    registry_of_ref,
    registry_of_worktree,
)
from check_twin_parity import audit_index  # noqa: E402

REPO = Path(__file__).resolve().parents[3]

A_0007 = "0007-2026-09-01-myia-po-2023-CoursIA.yaml"
B_0007 = "0007-2026-09-02-myia-po-2024-CoursIA.yaml"


def _reg(spec: dict) -> dict:
    """{paire: [(index, nom), ...]} -> {paire: {index: [noms]}}."""
    out = {}
    for pair, entries in spec.items():
        d: dict = {}
        for idx, name in entries:
            d.setdefault(idx, []).append(name)
        out[pair] = {k: sorted(v) for k, v in d.items()}
    return out


def test_meme_nom_des_deux_cotes_nest_pas_une_collision():
    """Le faux positif que la regle existe pour eviter : la branche HERITE le
    fichier de la base. Un nom identique n'est pas un doublon."""
    base = _reg({"app": [("0007", A_0007)]})
    head = _reg({"app": [("0007", A_0007)]})
    assert find_conflicts({"origin/main": base, "head": head}) == {
        "cross_ref": [], "intra_ref": []}


def test_collision_inter_revisions_detectee():
    """Le cas fondateur : deux lanes prennent `0007` depuis des checkouts
    differents -> deux NOMS differents, donc aucun conflit git."""
    base = _reg({"app": [("0007", A_0007)]})
    head = _reg({"app": [("0007", B_0007)]})
    got = find_conflicts({"origin/main": base, "head": head})
    assert got["intra_ref"] == []
    assert len(got["cross_ref"]) == 1
    c = got["cross_ref"][0]
    assert (c["pair"], c["index"]) == ("app", "0007")
    assert c["by_ref"]["origin/main"] == [A_0007]
    assert c["by_ref"]["head"] == [B_0007]


def test_sous_ensemble_nest_pas_une_collision():
    """La base porte deja les deux index ; la branche n'en reprend qu'un. Le
    merge ne cree rien."""
    base = _reg({"app": [("0007", A_0007), ("0008", "0008-b.yaml")]})
    head = _reg({"app": [("0007", A_0007)]})
    assert find_conflicts({"origin/main": base, "head": head}) == {
        "cross_ref": [], "intra_ref": []}


def test_branche_en_retard_sur_un_index_ajoute_par_une_autre():
    """La base a avance (une autre PR a pris `0008`) et la branche ne le sait
    pas : elle ne collisionne pas pour autant, elle doit juste se rafraichir."""
    base = _reg({"app": [("0007", A_0007), ("0008", "0008-other.yaml")]})
    head = _reg({"app": [("0007", A_0007), ("0009", "0009-mine.yaml")]})
    assert find_conflicts({"origin/main": base, "head": head}) == {
        "cross_ref": [], "intra_ref": []}


def test_doublon_intra_revision_classe_a_part():
    """Une seule revision porte deux noms au meme index : c'est le garde CI
    qui rougit, pas le merge. Ne doit JAMAIS sortir en cross_ref."""
    ref = _reg({"app": [("0007", A_0007), ("0007", B_0007)]})
    got = find_conflicts({"origin/main": ref})
    assert got["cross_ref"] == []
    assert len(got["intra_ref"]) == 1
    assert got["intra_ref"][0]["pair"] == "app"
    assert got["intra_ref"][0]["index"] == "0007"
    assert got["intra_ref"][0]["refs"] == ["origin/main"]
    assert got["intra_ref"][0]["names"] == sorted([A_0007, B_0007])


def test_index_disjoints_sont_propres():
    base = _reg({"app": [("0007", A_0007)], "ml": [("0003", "0003-c.yaml")]})
    head = _reg({"app": [("0008", "0008-d.yaml")], "ml": [("0004", "0004-e.yaml")]})
    assert find_conflicts({"origin/main": base, "head": head}) == {
        "cross_ref": [], "intra_ref": []}


def test_aucune_revision_rend_zero():
    assert find_conflicts({}) == {"cross_ref": [], "intra_ref": []}


def test_collision_portee_sur_plusieurs_paires():
    base = _reg({"app": [("0007", A_0007)], "ml": [("0003", "0003-c.yaml")]})
    head = _reg({"app": [("0007", B_0007)], "ml": [("0003", "0003-y.yaml")]})
    got = find_conflicts({"origin/main": base, "head": head})
    assert sorted((c["pair"], c["index"]) for c in got["cross_ref"]) == [
        ("app", "0007"), ("ml", "0003")]


def test_trois_revisions_collision_partielle():
    """Trois revisions, deux en collision : la troisieme ne doit ni masquer ni
    provoquer la collision."""
    r1 = _reg({"app": [("0007", A_0007)]})
    r2 = _reg({"app": [("0007", B_0007)]})
    r3 = _reg({"app": [("0009", "0009-c.yaml")]})
    got = find_conflicts({"origin/main": r1, "pr1": r2, "pr2": r3})
    assert len(got["cross_ref"]) == 1
    assert got["cross_ref"][0]["by_ref"] == {
        "origin/main": [A_0007], "pr1": [B_0007]}


def test_audit_index_est_le_predicat_du_garde_ci():
    """L'organe doit lire EXACTEMENT la grandeur que le garde CI teste
    (`name.split("-", 1)[0]`). Un instrument qui mesure une autre cle rendrait
    un vert faux."""
    for name in (A_0007, B_0007,
                 "0010-2026-09-23-myia-po-2027-CoursIA.yaml",
                 "0001-2026-08-04-myia-po-2023-CoursIA.yaml"):
        assert audit_index(name) == name.split("-", 1)[0]
    assert audit_index("0007-x.yaml") == "0007"
    assert len(audit_index("0007-x.yaml")) == 4


def test_contrat_de_sortie():
    """Une collision inter-revisions bloque toujours ; un doublon
    intra-revision ne bloque que sous `--in-tree`."""
    cross = [{"pair": "app", "index": "0007", "by_ref": {}}]
    intra = [{"pair": "app", "index": "0007", "refs": ["r"], "names": []}]
    assert exit_code([], [], in_tree=False) == 0
    assert exit_code([], [], in_tree=True) == 0
    assert exit_code([], intra, in_tree=False) == 0
    assert exit_code([], intra, in_tree=True) == 1
    assert exit_code(cross, [], in_tree=False) == 1
    assert exit_code(cross, intra, in_tree=False) == 1
    assert exit_code(cross, intra, in_tree=True) == 1


def _has_ref(ref: str) -> bool:
    return subprocess.run(
        ["git", "-C", str(REPO), "rev-parse", "--verify", "--quiet", ref],
        capture_output=True).returncode == 0


@pytest.mark.skipif(not _has_ref("origin/main"),
                    reason="origin/main absent (checkout detache en CI)")
def test_le_registre_de_main_ne_porte_aucun_doublon_intra_revision():
    """Controle positif : le predicat du garde CI, rejoue par cet organe sur le
    registre reel de `origin/main`. Si ce test rougit alors que le garde CI est
    vert, c'est que les deux instruments ont diverge -- le defaut que
    `audit_index` existe pour empecher."""
    reg = registry_of_ref("origin/main", REPO)
    assert reg, "registre vide : la lecture des revisions est cassee"
    got = find_conflicts({"origin/main": reg})
    assert got["intra_ref"] == [], (
        "doublon d'index intra-revision sur origin/main : %s" % got["intra_ref"])
    assert got["cross_ref"] == []


def test_registry_of_worktree_rend_la_meme_forme_que_registry_of_ref():
    """Les deux lecteurs doivent produire la meme structure -- un `--worktree`
    qui rendrait une forme differente ferait diverger le verdict en silence."""
    wt = registry_of_worktree(REPO)
    assert wt, "registre worktree vide"
    for pair, idxs in wt.items():
        assert isinstance(pair, str) and pair
        for idx, names in idxs.items():
            assert idx and names, (pair, idx)
            assert all(n.endswith(".yaml") for n in names)
