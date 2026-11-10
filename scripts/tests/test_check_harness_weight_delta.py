"""Controles de `scripts/ci/check_harness_weight_delta.py` (#15204).

Le comparateur ne mesure rien : il compare deux instantanes produits par
l'organe canonique `scripts/audit/measure_autoloaded_harness.py`. Deux
fautes distinctes sont donc a surveiller :

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


def _instantane(total: int, rules=(), root_file=None, complete: bool = True,
                gated=(), hashes=None) -> dict:
    """Un instantane au schema de l'organe canonique."""
    hashes = hashes or {}

    def _sha(nom):
        return hashes.get(nom, "sha-" + nom)

    return {
        "autoloaded_total_bytes": total,
        "autoloaded_rules": [{"name": n, "bytes": b, "sha256": _sha(n)}
                             for n, b in rules],
        "path_gated_rules": [{"name": n, "bytes": b, "sha256": _sha(n)}
                             for n, b in gated],
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


# --- la suppression : ni la croissance, ni la disparition muette ------------


def test_une_regle_supprimee_du_depot_est_refusee():
    """Le cliquet refuse aussi la DISPARITION, pas seulement la croissance.

    Une regle supprimee fait baisser le total : le delta seul la laisserait
    passer, en vert, sans que personne n'ait demande la suppression.
    """
    base = _instantane(1000, rules=[("r.md", 900)],
                       root_file={"name": "CLAUDE.md", "bytes": 100})
    head = _instantane(100, rules=[],
                       root_file={"name": "CLAUDE.md", "bytes": 100})
    resultat = delta.compare(base, head)
    assert resultat["verdict"] == "SUPPRESSION"
    assert resultat["surfaces_supprimees"] == ["r.md"]


def test_le_claude_md_racine_supprime_est_refuse():
    base = _instantane(1000, rules=[("r.md", 900)],
                       root_file={"name": "CLAUDE.md", "bytes": 100})
    head = _instantane(900, rules=[("r.md", 900)], root_file=None)
    resultat = delta.compare(base, head)
    assert resultat["verdict"] == "SUPPRESSION"
    assert "CLAUDE.md" in resultat["surfaces_supprimees"]


def test_un_renommage_nest_pas_une_suppression():
    """Une regle renommee garde son contenu, donc son empreinte.

    Sans l'appariment par `sha256`, le comparateur verrait une surface
    disparue et une surface apparue -- et accuserait a tort la PR.
    """
    base = _instantane(1000, rules=[("avant.md", 900)],
                       root_file={"name": "CLAUDE.md", "bytes": 100},
                       hashes={"avant.md": "sha-identique"})
    head = _instantane(1000, rules=[("apres.md", 900)],
                       root_file={"name": "CLAUDE.md", "bytes": 100},
                       hashes={"apres.md": "sha-identique"})
    resultat = delta.compare(base, head)
    assert resultat["verdict"] == "OK"
    assert resultat["surfaces_supprimees"] == []


def test_une_migration_vers_path_gated_nest_pas_une_suppression():
    """Le levier A du mandat : la regle sort du chemin auto-charge, sans
    disparaitre. Elle reste listee, donc elle n'est pas une suppression."""
    base = _instantane(1000, rules=[("r.md", 900)],
                       root_file={"name": "CLAUDE.md", "bytes": 100})
    head = _instantane(100, rules=[],
                       root_file={"name": "CLAUDE.md", "bytes": 100},
                       gated=[("r.md", 900)])
    resultat = delta.compare(base, head)
    assert resultat["verdict"] == "OK"
    assert resultat["surfaces_supprimees"] == []


def test_le_ratio_vient_de_linstantane_et_non_dune_constante():
    """Le ratio est emis par l'organe : le comparateur ne le redouble pas.

    Deux sources pour un meme nombre deriveient des que l'une change ; un
    instantane sans ratio est donc un instantane incomplet (rc=2).
    """
    base = _instantane(100, rules=[("r.md", 60)])
    head = _instantane(100, rules=[("r.md", 60)])
    base["ratio_bytes_per_token"] = 3.5
    head["ratio_bytes_per_token"] = 3.5
    resultat = delta.compare(base, head)
    assert resultat["bytes_per_token"] == 3.5
    assert resultat["base_tokens_derived"] == round(100 / 3.5)

    sans_ratio = _instantane(100, rules=[("r.md", 60)])
    del sans_ratio["ratio_bytes_per_token"]
    assert "ratio_bytes_per_token" in delta.REQUIRED_KEYS


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


def test_controle_positif_mesure_reelle_detecte_la_suppression(tmp_path):
    """Fin de bout en bout : une regle SUPPRIMEE du depot est refusee.

    Le cas que la seule arithmetique ne voit pas : le total baisse, le delta
    est negatif -- et la surface a disparu. C'est la mesure reelle qui
    apporte l'information (la surface disparue du catalogue), pas le calcul.
    """
    root = _arbre(tmp_path)
    base = mah.measure(root)
    (root / ".claude" / "rules" / "grande.md").unlink()
    head = mah.measure(root)

    resultat = delta.compare(base, head)
    assert resultat["verdict"] == "SUPPRESSION"
    assert "grande.md" in resultat["surfaces_supprimees"]


def test_controle_positif_mesure_reelle_accepte_le_renommage(tmp_path):
    """Fin de bout en bout : une regle RENOMMEE n'est pas une suppression."""
    root = _arbre(tmp_path)
    base = mah.measure(root)
    (root / ".claude" / "rules" / "grande.md").rename(
        root / ".claude" / "rules" / "grosse.md")
    head = mah.measure(root)

    resultat = delta.compare(base, head)
    assert resultat["verdict"] == "OK"
    assert resultat["surfaces_supprimees"] == []


def test_controle_positif_mesure_reelle_accepte_le_gating(tmp_path):
    """Fin de bout en bout : le levier A (gating) reste accepte.

    La regle passe de la surface auto-chargee a la surface path-gatee : le
    total baisse de sa taille exacte, la regle reste listee, et le cliquet
    passe.
    """
    root = _arbre(tmp_path)
    base = mah.measure(root)
    _ecrire(root, "grande.md",
            "---\npaths: a/**/*.ipynb\n---\n\n# grande\n\n" + "x" * 400)
    head = mah.measure(root)

    resultat = delta.compare(base, head)
    assert resultat["verdict"] == "OK"
    assert resultat["surfaces_supprimees"] == []
    assert resultat["delta_bytes"] < 0


def test_une_regle_non_gatee_est_comptee_dans_la_surface(tmp_path):
    """Contrôle de la surface : la regle sans frontmatter est auto-chargee."""
    root = _arbre(tmp_path)
    mesure = mah.measure(root)
    noms = {r["name"] for r in mesure["autoloaded_rules"]}
    assert "grande.md" in noms
    assert "gated.md" not in noms
    assert mesure["root_file"]["name"] == "CLAUDE.md"


# --- le cableage dans la voie rapide ----------------------------------------


def test_le_cliquet_est_cable_dans_la_voie_rapide():
    """Le comparateur ne sert a rien s'il n'est branche.

    Le numero de tranche n'est pas une convention : deux tranches peuvent
    porter le meme numero si deux PRs le reservent en meme temps (mesure du
    2026-11-07 : la tranche 39 du Cell-order gate et celle du cliquet de
    poids se sont quitteagees, et le merge a produit un conflit). Ce test
    epingle donc le *contenu* du garde -- son nom et sa semantique -- plutot
    qu'un simple compte de tranches.
    """
    import inspect
    import sys

    ci_dir = _REPO / "scripts" / "ci"
    if str(ci_dir) not in sys.path:
        sys.path.insert(0, str(ci_dir))
    import fast_lane
    from fast_lane_registry import TRANCHE40

    assert len(TRANCHE40) == 1, "la tranche du cliquet porte un seul garde"
    g = TRANCHE40[0]
    assert g.name == "Harness autoloaded weight ratchet (base vs PR, bloquant)"
    assert g.blocking, "le cliquet est bloquant : en advisory il n'arreterait rien"
    assert g.needs_base, "le cliquet compare la base a la tete"
    assert g.diff_bounded, "le garde est rejoue sur les seuls fichiers du diff"
    assert g.argv == ["python", "scripts/audit/measure_autoloaded_harness.py",
                      "--json"], (
        "la mesure doit venir de l'organe canonique, pas d'un recomptage")
    assert g.delta_argv == ["python", "scripts/ci/check_harness_weight_delta.py",
                            "{base_json}", "{head_json}"]
    assert g.swap_paths == ["CLAUDE.md", ".claude/rules"], (
        "la bascule base/tete ne porte que sur les surfaces mesurees")

    # Le moteur doit importer la tranche ET la lister dans la liste effective
    # des gardes : un registre qui la declare sans que le moteur la liste ne
    # la Selectionne jamais (defaut de cableage, invisible dans les tests
    # d'algorithme).
    assert getattr(fast_lane, "TRANCHE40", None) is TRANCHE40, (
        "le moteur doit importer la tranche du cliquet")
    source = inspect.getsource(fast_lane.main)
    assert "TRANCHE40" in source, (
        "la liste effective des gardes ne cite pas la tranche du cliquet : "
        "le garde ne sera jamais selectionne")
    assert fast_lane.guard_applies(g, ["CLAUDE.md"]), (
        "le cliquet doit etre selectionne par le chemin qu'il surveille")
    assert fast_lane.guard_applies(g, [".claude/rules/git-workflow.md"]), (
        "le cliquet doit etre selectionne par une regle auto-chargee")


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__]))
