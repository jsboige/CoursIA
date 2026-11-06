"""Controles de `scripts/ci/check_harness_weight_delta.py` (#15204).

Le comparateur ne mesure rien : il compare deux instantanes produits par
l'organe canonique `scripts/audit/measure_autoloaded_harness.py`. Deux
fautes distinctes sont donc a.watch :

- **le comparateur ne detecte pas une croissance** -- verdict vert sur une PR
  qui ajoute du contexte a toutes les sessions. Le controle positif
  end-to-end (mesure reelle de l'organe sur un arbre, puis comparaison)
  verifie ce chemin de bout en bout, pas seulement l'arithmetique.
- **le comparateur accuse une dette pre-existante** -- verdict rouge sur une
  PR qui n'a rien ajoute. Le cliquet porte sur le DELTA ; la surface
  actuelle est deja au-dessus de la cible du mandat, un seuil absolu
  rendrait le garde rouge des sa naissance.

L'organe canonique a deja ses propres controles (`--self-check`) ; ce fichier
ne les recopie pas : il cable le couple (mesure -> comparaison) dans pytest.
"""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
_DELTA_PATH = _REPO / "scripts" / "ci" / "check_harness_weight_delta.py"
_ORGAN_PATH = _REPO / "scripts" / "audit" / "measure_autoloaded_harness.py"


def _load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec and spec.loader
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


delta = _load(_DELTA_PATH, "check_harness_weight_delta")
mah = _load(_ORGAN_PATH, "measure_autoloaded_harness")


def _instantane(total: int, rules=(), root_file=None, complete: bool = True) -> dict:
    """Un instantane au schema de l'organe canonique."""
    return {
        "autoloaded_total_bytes": total,
        "autoloaded_rules": [{"name": n, "bytes": b} for n, b in rules],
        "path_gated_rules": [],
        "root_file": root_file,
        "measurement_complete": complete,
        "ratio_bytes_per_token": 2.25,
    }


def _ecrire(root: Path, nom: str, texte: str) -> Path:
    (root / ".claude" / "rules").mkdir(parents=True, exist_ok=True)
    (root / ".claude" / "rules" / nom).write_text(texte, encoding="utf-8")
    return root


def _arbre(tmp_path: Path) -> Path:
    root = tmp_path / "depot"
    root.mkdir()
    (root / "CLAUDE.md").write_text("# projet\n", encoding="utf-8")
    _ecrire(root, "grande.md", "# grande\n\n" + "x" * 400)
    _ecrire(root, "gated.md", "---\npaths: a/**/*.ipynb\n---\n\n# gated\n")
    return root


# --- le verdict de base ------------------------------------------------------


def test_croissance_est_refusee(tmp_path):
    base = _instantane(100, rules=[("r.md", 60)])
    head = _instantane(160, rules=[("r.md", 120)])
    base_file = tmp_path / "base.json"
    head_file = tmp_path / "head.json"
    base_file.write_text(json.dumps(base), encoding="utf-8")
    head_file.write_text(json.dumps(head), encoding="utf-8")
    rc = delta.main([str(base_file), str(head_file)])
    assert rc == 1


def test_baisse_est_acceptee(tmp_path):
    base = _instantane(160, rules=[("r.md", 120)])
    head = _instantane(100, rules=[("r.md", 60)])
    base_file = tmp_path / "base.json"
    head_file = tmp_path / "head.json"
    base_file.write_text(json.dumps(base), encoding="utf-8")
    head_file.write_text(json.dumps(head), encoding="utf-8")
    assert delta.main([str(base_file), str(head_file)]) == 0


def test_egalite_est_acceptee(tmp_path):
    instantane = _instantane(100, rules=[("r.md", 60)])
    base_file = tmp_path / "base.json"
    head_file = tmp_path / "head.json"
    base_file.write_text(json.dumps(instantane), encoding="utf-8")
    head_file.write_text(json.dumps(instantane), encoding="utf-8")
    assert delta.main([str(base_file), str(head_file)]) == 0


def test_une_regle_qui_redevient_auto_chargee_compte_comme_croissance():
    """Une regle qui PERD son frontmatter `paths:` redevient auto-chargee.

    C'est le cas le plus discret de la classe : le fichier ne change pas de
    nom, sa taille ne bouge presque pas, et la surface que chaque session
    paie augmente de toute la regle.
    """
    base = {"autoloaded_total_bytes": 100, "autoloaded_rules": [],
            "path_gated_rules": [{"name": "r.md", "bytes": 900}],
            "root_file": {"name": "CLAUDE.md", "bytes": 100},
            "measurement_complete": True, "ratio_bytes_per_token": 2.25}
    head = {"autoloaded_total_bytes": 1000, "autoloaded_rules": [
                {"name": "r.md", "bytes": 900}],
            "path_gated_rules": [],
            "root_file": {"name": "CLAUDE.md", "bytes": 100},
            "measurement_complete": True, "ratio_bytes_per_token": 2.25}
    resultat = delta.compare(base, head)
    assert resultat["verdict"] == "GROWTH"
    assert resultat["delta_bytes"] == 900


def test_une_regle_path_gatee_qui_disparait_de_la_surface_reduit_le_total():
    base = {"autoloaded_total_bytes": 1000, "autoloaded_rules": [
                {"name": "r.md", "bytes": 900}],
            "path_gated_rules": [], "root_file": {"name": "CLAUDE.md", "bytes": 100},
            "measurement_complete": True, "ratio_bytes_per_token": 2.25}
    head = {"autoloaded_total_bytes": 100, "autoloaded_rules": [],
            "path_gated_rules": [{"name": "r.md", "bytes": 900}],
            "root_file": {"name": "CLAUDE.md", "bytes": 100},
            "measurement_complete": True, "ratio_bytes_per_token": 2.25}
    assert delta.compare(base, head)["verdict"] == "OK"


# --- les incidents : verdict inconnu, jamais un quitus -----------------------


def test_incident_json_illisible(tmp_path):
    base_file = tmp_path / "base.json"
    head_file = tmp_path / "head.json"
    base_file.write_text("{pas du json", encoding="utf-8")
    head_file.write_text("{}", encoding="utf-8")
    assert delta.main([str(base_file), str(head_file)]) == 2


def test_incident_fichier_absent(tmp_path):
    head_file = tmp_path / "head.json"
    head_file.write_text("{}", encoding="utf-8")
    assert delta.main([str(tmp_path / "absent.json"), str(head_file)]) == 2


def test_incident_cles_absentes(tmp_path):
    base_file = tmp_path / "base.json"
    head_file = tmp_path / "head.json"
    base_file.write_text(json.dumps({"autoloaded_total_bytes": 1}),
                         encoding="utf-8")
    head_file.write_text(json.dumps({"autoloaded_total_bytes": 1}),
                         encoding="utf-8")
    assert delta.main([str(base_file), str(head_file)]) == 2


def test_incident_mesure_incomplete(tmp_path):
    base_file = tmp_path / "base.json"
    head_file = tmp_path / "head.json"
    base_file.write_text(json.dumps(
        _instantane(10, complete=False)), encoding="utf-8")
    head_file.write_text(json.dumps(
        _instantane(10, complete=True)), encoding="utf-8")
    assert delta.main([str(base_file), str(head_file)]) == 2


# --- controle positif END-TO-END : la mesure reelle puis la comparaison ------


def test_controle_positif_mesure_reelle_detecte_la_croissance(tmp_path):
    """L'organe canonique mesure un arbre, le comparateur le refuse.

    Sans ce test, une arithmetique correcte sur des instantanes fabriquees
    pourrait masquer un chemin de detection mort (cle renommee, schema evolue).
    """
    root = _arbre(tmp_path)
    base = mah.measure(root)

    _ecrire(root, "grande.md", "# grande\n\n" + "x" * 900)
    head = mah.measure(root)

    resultat = delta.compare(base, head)
    assert resultat["verdict"] == "GROWTH"
    assert resultat["delta_bytes"] == 500
    surfaces = {d["surface"]: d for d in resultat["surfaces"]}
    assert surfaces["grande.md"]["kind"] == "modifie"
    assert surfaces["grande.md"]["delta_bytes"] == 500
    # La regle path-gatee reste absente de la surface auto-chargee : le
    # predicat de l'organe n'est pas contamine par la mesure.
    assert "gated.md" not in surfaces


def test_controle_positif_mesure_reelle_accepte_la_baisse(tmp_path):
    root = _arbre(tmp_path)
    base = mah.measure(root)
    _ecrire(root, "grande.md", "# grande\n\n" + "x" * 100)
    head = mah.measure(root)
    resultat = delta.compare(base, head)
    assert resultat["verdict"] == "OK"
    assert resultat["delta_bytes"] == -300


def test_une_regle_non_gatee_est_comptee_dans_la_surface(tmp_path):
    """Contrôle de la surface : la regle sans frontmatter est auto-chargee."""
    root = _arbre(tmp_path)
    mesure = mah.measure(root)
    noms = {r["name"] for r in mesure["autoloaded_rules"]}
    assert "grande.md" in noms
    assert "gated.md" not in noms
    assert mesure["root_file"]["name"] == "CLAUDE.md"


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__]))
