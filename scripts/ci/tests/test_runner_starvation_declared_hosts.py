"""Tests du predicat POOL ABSENT (#20697 point 4) de la sonde de starvation.

Le predicat par hote exige `offline > 0` : il ne voit que les hotes qui ont au
moins une entree dans l'inventaire. Un hote dont ZERO runner est inscrit cote
GitHub -- le cas fondateur de l'issue, dix conteneurs vivants et zero runner
enregistre pendant ~2 jours -- lui est structurellement invisible. L'inventaire
declare apporte ce qui manquait : la liste de ce qui DEVRAIT exister.

Module separe le 2026-11-25 : le module voisin
`test_runner_starvation_probe.py` depassait le plafond de 800 lignes des
scripts neufs (818), et ce predicat est un sujet distinct du cout d'un
passage de la sonde.
"""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_runner_starvation.py"
# Nom de module distinct de celui du module voisin : les deux fichiers
# executent le meme script source, et `@dataclass` resout ses annotations via
# sys.modules[nom]. Un nom partage ferait ecraser l'entree de l'autre fichier.
_spec = importlib.util.spec_from_file_location(
    "check_runner_starvation_pool_absent", SCRIPT)
mod = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = mod
_spec.loader.exec_module(mod)

_WAITER = "coursia-waiter"
_HOST = "myia-ai-01-wsl"


def _online(n: int) -> list[str]:
    return [f"{_HOST}-{i}" for i in range(1, n + 1)]


def _declared(path: str, hosts: list[dict]) -> mod.DeclaredHosts:
    with open(path, "w", encoding="utf-8") as fh:
        json.dump({"schema_version": 1, "hosts": hosts}, fh)
    return mod.load_declared_hosts(path, _WAITER)


def test_hote_declare_absent_de_l_inventaire_tire_pool_absent(tmp_path):
    """Le cas fondateur : l'hote n'a NI online NI offline -- invisible sinon."""
    declared = _declared(str(tmp_path / "d.json"), [
        {"host": _HOST, "labels": [_WAITER], "slots": 10},
        {"host": "myia-po-2099-linux-docker", "labels": [_WAITER], "slots": 4},
    ])
    inv = mod.RunnerInventory(online=_online(10), offline=[])
    warnings = mod.evaluate_host_loss(inv, declared)
    absent = [w for w in warnings if "POOL ABSENT" in w]
    assert len(absent) == 1, f"un seul hote manque : {warnings}"
    assert "myia-po-2099-linux-docker" in absent[0]
    assert "4 slot" in absent[0], "l'ampleur de la perte est chiffree"
    assert "d.json" in absent[0], "le message nomme le fichier a corriger"


def test_hote_declare_present_meme_offline_ne_double_pas_le_message(tmp_path):
    """Un hote qui apparait, meme entierement offline, garde POOL LOSS seul."""
    declared = _declared(str(tmp_path / "d.json"),
                         [{"host": _HOST, "labels": [_WAITER], "slots": 10}])
    inv = mod.RunnerInventory(online=[], offline=_online(10))
    warnings = mod.evaluate_host_loss(inv, declared)
    assert any("POOL LOSS" in w for w in warnings)
    assert not any("POOL ABSENT" in w for w in warnings), \
        f"un hote liste n'est pas absent : {warnings}"


def test_la_declaration_est_filtree_par_label(tmp_path):
    """Un hote declare pour un autre label ne crie pas sur celui-ci.

    Sans ce filtre, chaque passage de sonde alerterait sur les hotes des
    autres labels -- et l'organe deviendrait du bruit qu'on apprend a ignorer.
    """
    path = str(tmp_path / "d.json")
    with open(path, "w", encoding="utf-8") as fh:
        json.dump({"schema_version": 1, "hosts": [
            {"host": "myia-po-2028-linux-docker", "labels": ["coursia-linux"],
             "slots": 3},
        ]}, fh)
    declared = mod.load_declared_hosts(path, _WAITER)
    assert declared.available and declared.hosts == {}, \
        "le label mesure ne doit retenir que ses hotes"
    assert not mod.evaluate_host_loss(mod.RunnerInventory(online=_online(10)),
                                      declared)


def test_inventaire_declare_illisible_est_une_note_pas_un_rouge(tmp_path):
    """On ne peut pas prouver une disparition avec un fichier qu'on ne lit pas."""
    bad = tmp_path / "bad.json"
    bad.write_text("{ pas du json", encoding="utf-8")
    declared = mod.load_declared_hosts(str(bad), _WAITER)
    assert not declared.available and declared.error
    inv = mod.RunnerInventory(online=_online(10), offline=[])
    block = mod.evaluate(inv, mod.Starvation(), warn_floor=2, label=_WAITER,
                         declared=declared)
    assert block.status == "OK", f"pas de rouge : {block.errors}"
    assert any("inventaire declare non lu" in n for n in block.notes)


def test_sans_fichier_declare_le_predicat_est_desactive():
    """Chemin absent : l'organe reste utilisable, sans POOL ABSENT ni bruit."""
    declared = mod.load_declared_hosts("/chemin/inexistant.json", _WAITER)
    assert not declared.available
    inv = mod.RunnerInventory(online=_online(10), offline=[])
    assert not mod.evaluate_host_loss(inv, declared)
    assert not mod.evaluate_host_loss(inv, None)


def test_l_inventaire_declare_du_depot_couvre_les_hotes_du_label_waiter():
    """Le fichier livre avec l'organe n'est pas vide : il declare bien l'hote
    qui sert `coursia-waiter` (10 slots mesures le 2026-11-12). Un fichier
    vide rendrait le predicat inerte tout en donnant l'illusion du contraire."""
    shipped = mod.DEFAULT_DECLARED_HOSTS
    assert Path(shipped).is_file(), f"fichier livre absent : {shipped}"
    declared = mod.load_declared_hosts(shipped, "coursia-waiter")
    assert declared.available, declared.error
    assert declared.hosts, "au moins un hote declare pour ce label"
    assert "myia-ai-01-wsl-waiterb" in declared.hosts
