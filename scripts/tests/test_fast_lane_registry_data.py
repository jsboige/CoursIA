"""Le registre de la voie rapide vit en donnees (#28117) : identite temoin.

Contrat de l'extraction (#28117) : le registre charge depuis
``scripts/ci/fast_lane_registry.d/*.yaml`` est IDENTIQUE, entree pour entree,
champ pour champ, a l'ancien module monolithique (5098 lignes). Le temoin
gele est ``fixtures/fast_lane_registry_snapshot.json``, genere depuis le
dernier etat monolithique de ``main`` AVANT extraction -- le comparer a ce
que le chargeur produit aujourd'hui, c'est verifier qu'aucune porte, aucun
champ et aucun ordre n'a derive depuis.

Ajouter une porte a un groupe existant impose de regenerer le temoin
(``FAST_LANE_REGEN_SNAPSHOT=1 python -m pytest scripts/tests/
test_fast_lane_registry_data.py``) : le diff du JSON fait alors partie de la
review -- c'est voulu, une porte qui apparait doit se lire.

Fail-closed : le chargeur doit refuser un groupe inconnu, un marqueur body
inconnu et un champ requis manquant (une donnee incoherente ne peut PAS se
charger en silence, cf la lecon du registre muet #27233). Les erreurs
par-fichier claument AVANT le controle final des groupes manquants : un
repertoire minimal d'un seul fichier suffit a les provoquer.
"""
import json
import os
import shutil
import sys
import tempfile
import typing
from dataclasses import fields as dc_fields
from pathlib import Path

import pytest

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
DATA_DIR = CI_DIR / "fast_lane_registry.d"
SNAPSHOT = Path(__file__).resolve().parent / "fixtures" / \
    "fast_lane_registry_snapshot.json"

sys.path.insert(0, str(CI_DIR))
import fast_lane_registry as reg  # noqa: E402


def _ser_guard(g):
    out = {}
    for f in dc_fields(g):
        v = getattr(g, f.name)
        if f.name == "commenters":
            v = [_ser_commenter(c) for c in v]
        elif isinstance(v, tuple):
            v = list(v)
        out[f.name] = v
    return out


def _ser_commenter(c):
    out = {}
    for f in dc_fields(c):
        v = getattr(c, f.name)
        if f.name == "body":
            v = getattr(v, "__name__", repr(v))
        elif isinstance(v, tuple):
            v = list(v)
        out[f.name] = v
    return out


def _serialize():
    return {g: [_ser_guard(x) for x in getattr(reg, g)]
            for g in reg._REQUIRED_GROUPS}


def _sequences(obj):
    """(champ, type annonce, type servi) des champs de sequence d'un objet."""
    hints = typing.get_type_hints(type(obj), globalns=vars(reg),
                                  localns={"Callable": typing.Callable})
    for f in dc_fields(obj):
        annonce = typing.get_origin(hints[f.name])
        if annonce in (list, tuple):
            yield f.name, annonce, type(getattr(obj, f.name))


def test_les_sequences_ont_le_type_annonce():
    """Un tuple et une liste s'ecrivent pareil au temoin JSON.

    Le temoin ne peut donc pas voir une sequence servie dans le mauvais
    type. Ce test lit le type dans l'annotation du dataclass, qui est
    celle du monolithe. Mesure du 24/11 : le chargeur servait `paths` de
    cinq commenters en tuple, annonce en liste -- sans effet observe sur
    le runner (`commenter_paths` deploite la sequence), mais hors
    contrat d'identite.
    """
    ecarts = []
    for group in reg._REQUIRED_GROUPS:
        for guard in getattr(reg, group):
            ecarts += [f"{guard.name}.{champ}: servi {servi.__name__}, "
                       f"annonce {annonce.__name__}"
                       for champ, annonce, servi in _sequences(guard)
                       if servi is not annonce]
            for commenter in guard.commenters:
                ecarts += [f"{guard.name} / {commenter.header}.{champ}: servi "
                           f"{servi.__name__}, annonce {annonce.__name__}"
                           for champ, annonce, servi in _sequences(commenter)
                           if servi is not annonce]
    assert not ecarts, "\n".join(ecarts)


def test_identite_avec_le_temoir():
    """Entree pour entree, champ pour champ, ordre compris."""
    snapshot = json.loads(SNAPSHOT.read_text(encoding="utf-8"))
    charge = _serialize()
    assert set(charge) == set(snapshot), (
        f"groupes divergents: +{sorted(set(charge) - set(snapshot))} "
        f"-{sorted(set(snapshot) - set(charge))}")
    for group in snapshot:
        attendu, obtenu = snapshot[group], charge[group]
        assert len(attendu) == len(obtenu), (
            f"{group}: {len(attendu)} portes au temoin, {len(obtenu)} chargees")
        for i, (a, b) in enumerate(zip(attendu, obtenu)):
            assert a == b, (
                f"{group}[{i}] ({a.get('name')}) diverge sur "
                f"{[k for k in a if a[k] != b.get(k)]}")


def test_ajouter_une_porte_ne_touches_pas_le_module():
    """Acceptance 3 de #28117 : une porte factice charge depuis le YAML seul.

    On ajoute une entree au groupe TRANCHE1 dans une COPIE du repertoire de
    donnees : le chargeur la sert, sans qu'aucun fichier .py n'ait bouge
    (aucune constante, aucun schema -- le module importe reste le meme).
    """
    with tempfile.TemporaryDirectory() as tmp:
        data_copy = Path(tmp) / "d"
        shutil.copytree(DATA_DIR, data_copy)
        target = data_copy / "tranche1.yaml"
        text = target.read_text(encoding="utf-8")
        target.write_text(text.rstrip() + "\n"
                          "  - name: porte-factice-28117\n"
                          "    argv: [python, echo, porte-factice]\n"
                          '    source: "(garde factice du test #28117)"\n',
                          encoding="utf-8")
        loaded = reg._load_registry(data_dir=data_copy)
    assert len(loaded["TRANCHE1"]) == len(getattr(reg, "TRANCHE1")) + 1
    factice = loaded["TRANCHE1"][-1]
    assert factice.name == "porte-factice-28117"
    assert factice.argv == ["python", "echo", "porte-factice"]
    assert factice.source == "(garde factice du test #28117)"
    assert factice.blocking is True  # defaut du dataclass


def _fake_dir(files):
    tmp = tempfile.mkdtemp(prefix="flr_fake_")
    root = Path(tmp)
    for name, text in files.items():
        (root / name).write_text(text, encoding="utf-8")
    try:
        yield root
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_groupe_inconnu_refuse():
    for root in _fake_dir({"x.yaml": "group: TRANCHE99\nguards: []\n"}):
        with pytest.raises(reg.RegistryDataError, match="groupe inconnu"):
            reg._load_registry(data_dir=root)


def test_repertoire_de_donnees_absent_refuse():
    """Un deploiement incomplet (.py sans .d/) ne charge PAS 0 gardes.

    Le fail-closed est voulu (#28117) : un module qui s'importerait avec un
    repertoire de donnees absent servirait un registre vide -- une voie
    rapide muette, indiscernable d'une voie rapide absente (lecon #27233).
    La tolerance de panne qui reste est celle de #22041 : le registre
    LIVE-READ absent ne tue QUE les paths du garde concerne (mesure par
    scripts/tests/test_fast_lane.py::test_registre_absent_le_module_reste_importable).
    """
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        with pytest.raises(reg.RegistryDataError,
                            match="repertoire de donnees absent"):
            reg._load_registry(data_dir=Path(tmp) / "inexistant")


def test_marqueur_body_inconnu_refuse():
    yaml_text = (
        "group: TRANCHE1\n"
        "guards:\n"
        "  - name: x\n"
        "    argv: [python, x]\n"
        '    source: "(x)"\n'
        "    commenters:\n"
        "      - header: h\n"
        "        argv: [python, x]\n"
        "        body: fontion_inexistante\n"
        "        fatal_rc: [1]\n"
    )
    for root in _fake_dir({"x.yaml": yaml_text}):
        with pytest.raises(reg.RegistryDataError, match="body de commenter"):
            reg._load_registry(data_dir=root)


def test_champ_requis_manquant_refuse():
    yaml_text = (
        "group: TRANCHE1\n"
        "guards:\n"
        "  - argv: [python, x]\n"
        '    source: "(x)"\n'
    )
    for root in _fake_dir({"x.yaml": yaml_text}):
        with pytest.raises(reg.RegistryDataError, match="champ requis"):
            reg._load_registry(data_dir=root)


def test_regen_snapshot_explicite():
    """Regeneration du temoin : passive sauf FAST_LANE_REGEN_SNAPSHOT=1."""
    if os.environ.get("FAST_LANE_REGEN_SNAPSHOT") != "1":
        pytest.skip("passif sauf FAST_LANE_REGEN_SNAPSHOT=1")
    SNAPSHOT.parent.mkdir(parents=True, exist_ok=True)
    SNAPSHOT.write_text(
        json.dumps(_serialize(), ensure_ascii=False, indent=1) + "\n",
        encoding="utf-8")
