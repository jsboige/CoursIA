"""Tests du garde zero-pad serie (#12586).

Les cas sont construits sur les formes REELLES de la serie GameTheory :
zero-pades valides (03a, 08d, 26), chiffre unique invalide (3a, 8d, 8-).
Le lookahead est la piece delicate -- chaque forme a son test.

Deuxieme volet (#15489, defaut 5) : la PORTEE du garde est une liste explicite
(`zero_pad_series.json`), lue quand le garde est lance sans argument -- c'est
l'invocation CI. Les tests de parite qui suivent verrouillent le fait que les
deux miroirs de cette liste (workflow `paths:` + garde de la voie rapide) ne
peuvent pas deriver du registre : sans eux, la duplication serait silencieuse,
et c'est precisement le silence que cette tranche supprime.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest
import yaml

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))

from check_series_zero_pad import (  # noqa: E402
    REGISTRY_PATH,
    REPO_ROOT,
    RegistryError,
    load_registry,
    main,
    violations,
)


@pytest.fixture
def series(tmp_path: Path) -> Path:
    d = tmp_path / "GameTheory"
    d.mkdir()
    return d


def test_serie_propre_passe(series: Path):
    for name in ["GameTheory-01-Setup.ipynb", "GameTheory-03a-X.ipynb",
                 "GameTheory-08d-Y.lean", "GameTheory-26-Z.ipynb"]:
        (series / name).write_text("x", encoding="utf-8")
    assert violations(series) == []


def test_chiffre_unique_avec_lettre_est_violation(series: Path):
    (series / "GameTheory-3a-Chemins.ipynb").write_text("x", encoding="utf-8")
    found = violations(series)
    assert len(found) == 1
    assert found[0]["name"] == "GameTheory-3a-Chemins.ipynb"


def test_chiffre_unique_avec_tiret_est_violation(series: Path):
    (series / "GameTheory-8-CombinatorialGames.ipynb").write_text("x",
                                                                  encoding="utf-8")
    assert len(violations(series)) == 1


def test_deux_chiffres_puis_lettre_passe(series: Path):
    # le 0 de 08d est suivi d'un chiffre -> pas une violation
    (series / "GameTheory-08d-Lean-CGT-Native.ipynb").write_text("x",
                                                                 encoding="utf-8")
    assert violations(series) == []


def test_sous_repertoire_scanne(series: Path):
    sub = series / "game_theory_lean"
    sub.mkdir()
    (sub / "GameTheory-3b-Fantom.ipynb").write_text("x", encoding="utf-8")
    found = violations(series)
    assert len(found) == 1
    assert found[0]["name"] == "GameTheory-3b-Fantom.ipynb"


def test_hors_prefix_ignore(series: Path):
    (series / "autre-3-nom.ipynb").write_text("x", encoding="utf-8")
    (series / "game_theory_lean").mkdir()
    (series / "game_theory_lean" / "Swaps.lean").write_text("x",
                                                            encoding="utf-8")
    assert violations(series) == []


def test_prefix_non_defaut(series: Path):
    (series / "Search-5-X.ipynb").write_text("x", encoding="utf-8")
    assert len(violations(series, prefix="Search")) == 1
    assert violations(series, prefix="GameTheory") == []


def test_main_sortie_zero_sur_serie_propre(series: Path, capsys):
    (series / "GameTheory-03b-Ok.ipynb").write_text("x", encoding="utf-8")
    assert main(["--series-dir", str(series), "--prefix", "GameTheory"]) == 0
    assert "OK" in capsys.readouterr().out


def test_main_sortie_un_sur_violation(series: Path, capsys):
    (series / "GameTheory-3e-Bad.ipynb").write_text("x", encoding="utf-8")
    assert main(["--series-dir", str(series), "--prefix", "GameTheory"]) == 1
    assert "3e-Bad" in capsys.readouterr().out


def test_main_json_shape(series: Path, capsys):
    import json
    (series / "GameTheory-3f-Bad.ipynb").write_text("x", encoding="utf-8")
    assert main(["--series-dir", str(series), "--json"]) == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["count"] == 1
    assert payload["violations"][0]["name"] == "GameTheory-3f-Bad.ipynb"


def test_main_repertoire_introuvable():
    assert main(["--series-dir", "Nulle/Part"]) == 2


# ---------------------------------------------------------------------------
# Portee explicite (#15489, defaut 5) -- le registre, ses modes d'echec, et ses
# deux miroirs.
# ---------------------------------------------------------------------------

def _registry(tmp_path: Path, entries: list[dict], name: str = "reg.json") -> Path:
    p = tmp_path / name
    p.write_text(json.dumps({"adopted": entries}), encoding="utf-8")
    return p


@pytest.fixture
def two_series(tmp_path: Path) -> tuple[Path, Path]:
    """Deux series sur disque : une propre (zero-padee), une en violation."""
    clean = tmp_path / "Clean"
    clean.mkdir()
    (clean / "Alpha-01-X.ipynb").write_text("x", encoding="utf-8")
    (clean / "Alpha-12-Y.ipynb").write_text("x", encoding="utf-8")
    dirty = tmp_path / "Dirty"
    dirty.mkdir()
    (dirty / "Beta-7-Bad.ipynb").write_text("x", encoding="utf-8")
    return clean, dirty


def test_registre_declare_des_series_qui_existent():
    """Le registre du depot ne doit nommer que des repertoires reels.

    Un registre qui pointe dans le vide n'est pas un detail cosmetique : le
    garde rendrait 2 en CI, et le rouge accuserait le depot au lieu du
    registre.
    """
    for entry in load_registry():
        assert (REPO_ROOT / entry["dir"]).is_dir(), entry["dir"]


def test_registre_aujourd_hui_vert_sur_l_arbre_reel(capsys):
    """L'invocation CI (sans argument) doit rendre 0 sur main.

    C'est la preuve d'admission des 8 series declarees : le critere du
    registre affirme "zero violation sur l'arbre entier", et ce test le
    verifie sur l'arbre reel plutot que de faire confiance a la note.
    """
    assert main([]) == 0
    out = capsys.readouterr().out
    assert "0 violation(s)" in out


def test_registre_scanne_toutes_les_series_declarees(two_series, tmp_path,
                                                     capsys):
    clean, _ = two_series
    reg = _registry(tmp_path, [{"series": "Alpha", "dir": str(clean)}])
    assert main(["--registry", str(reg), "--json"]) == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["mode"] == "registry"
    assert [s["series"] for s in payload["series"]] == ["Alpha"]


def test_famille_non_declaree_n_est_jamais_scannee(two_series, tmp_path,
                                                   capsys):
    """Non-regression du point d'acceptance : une famille NON adoptee ne doit
    pas rougir. `Dirty` porte Beta-7 (chiffre unique) et n'est pas declaree :
    le mode registre l'ignore completement."""
    clean, dirty = two_series
    reg = _registry(tmp_path, [{"series": "Alpha", "dir": str(clean)}])
    assert main(["--registry", str(reg)]) == 0
    out = capsys.readouterr().out
    assert "Dirty" not in out and "Beta" not in out


def test_serie_declaree_en_violation_rougit(two_series, tmp_path, capsys):
    """Le pendant du test precedent : declarer une serie non migree DOIT
    rougir. Sans ce test, le garde pourrait rendre 0 en ne scannant rien --
    c'est le mode de defaillance qu'un registre introduit."""
    _, dirty = two_series
    reg = _registry(tmp_path, [{"series": "Beta", "dir": str(dirty)}])
    assert main(["--registry", str(reg)]) == 1
    assert "Beta-7-Bad.ipynb" in capsys.readouterr().out


def test_serie_declaree_absente_rend_2(tmp_path, capsys):
    """Une serie declaree disparue est un defaut du REGISTRE, pas un vert."""
    reg = _registry(tmp_path, [{"series": "Fantome",
                                "dir": str(tmp_path / "nulle-part")}])
    assert main(["--registry", str(reg)]) == 2
    assert "introuvable" in capsys.readouterr().err


def test_registre_absent_rend_2_pas_vert(tmp_path, capsys):
    """Le mode de defaillance a interdire : un registre illisible qui rendrait
    0 en scannant zero serie."""
    assert main(["--registry", str(tmp_path / "absent.json")]) == 2
    assert "illisible" in capsys.readouterr().err


def test_registre_malforme_rend_2(tmp_path, capsys):
    bad = tmp_path / "bad.json"
    bad.write_text("{ pas du json", encoding="utf-8")
    assert main(["--registry", str(bad)]) == 2
    assert "malforme" in capsys.readouterr().err


def test_registre_sans_adopted_rend_2(tmp_path, capsys):
    empty = tmp_path / "empty.json"
    empty.write_text(json.dumps({"adopted": []}), encoding="utf-8")
    assert main(["--registry", str(empty)]) == 2
    assert "adopted" in capsys.readouterr().err


def test_surcharge_explicite_prime_sur_le_registre(two_series, capsys):
    """`--series-dir` reste la forme historique et doit continuer de marcher
    seule, registre du depot ou non : c'est ce qui garde les autres tests de
    ce fichier valides."""
    clean, _ = two_series
    assert main(["--series-dir", str(clean), "--prefix", "Alpha"]) == 0
    _, dirty = two_series
    assert main(["--series-dir", str(dirty), "--prefix", "Beta"]) == 1
    assert "Beta-7-Bad.ipynb" in capsys.readouterr().out


def test_json_registre_forme_stable(two_series, tmp_path, capsys):
    """Forme JSON stable pour consommation CI (acceptance de #15489)."""
    _, dirty = two_series
    reg = _registry(tmp_path, [{"series": "Beta", "dir": str(dirty)}])
    assert main(["--registry", str(reg), "--json"]) == 1
    payload = json.loads(capsys.readouterr().out)
    assert set(payload) >= {"schema", "mode", "series", "count", "violations",
                            "missing_dirs"}
    assert payload["schema"] == 2
    assert payload["count"] == 1
    assert payload["violations"][0]["series"] == "Beta"
    assert payload["series"][0]["count"] == 1


def test_json_serie_unique_porte_encore_les_cles_historiques(series: Path,
                                                             capsys):
    (series / "GameTheory-3f-Bad.ipynb").write_text("x", encoding="utf-8")
    assert main(["--series-dir", str(series), "--json"]) == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["mode"] == "series"
    assert payload["prefix"] == "GameTheory"
    assert payload["count"] == 1


def test_list_series(capsys):
    assert main(["--list-series"]) == 0
    lines = [l for l in capsys.readouterr().out.splitlines() if l.strip()]
    assert len(lines) == len(load_registry()) == 8
    assert any(l.startswith("GameTheory\t") for l in lines)


# --- Parite registre <-> miroirs -------------------------------------------
#
# Le registre est la source de verite ; le workflow et la voie rapide en
# portent une copie. Ces tests rendent la duplication VERIFIEE : sans eux,
# ajouter une serie au registre laisserait les deux miroirs muets, et le
# garde ne serait declenche par rien pour cette serie.

def _workflow_push_paths() -> list[str]:
    doc = yaml.safe_load(
        (REPO_ROOT / ".github/workflows/series-naming-gate.yml")
        .read_text(encoding="utf-8"))
    # PyYAML 1.1 lit la cle `on` comme le booleen True.
    on = doc.get("on", doc.get(True))
    return on["push"]["paths"]


def _fast_lane_paths() -> list[str]:
    sys.path.insert(0, str(REPO_ROOT / "scripts/ci"))
    import fast_lane_registry as flr

    guards = [g for lst in vars(flr).values()
              if isinstance(lst, list)
              for g in lst
              if getattr(g, "source", None) == "series-naming-gate.yml"]
    assert len(guards) == 1, "garde zero-pad introuvable ou duplique"
    return list(guards[0].paths)


@pytest.mark.parametrize("mirror", [_workflow_push_paths, _fast_lane_paths],
                         ids=["workflow-paths", "fast-lane-guard"])
def test_miroir_couvre_chaque_serie_declaree(mirror):
    """Chaque serie du registre doit apparaitre dans les deux miroirs, sinon le
    garde ne se declenche pas quand cette serie change."""
    paths = mirror()
    for entry in load_registry():
        assert f"{entry['dir']}/**" in paths, (
            f"{entry['series']} declaree mais absente du miroir : {entry['dir']}")
    assert "scripts/notebook_tools/zero_pad_series.json" in paths, (
        "le registre lui-meme doit declencher le garde")


@pytest.mark.parametrize("mirror", [_workflow_push_paths, _fast_lane_paths],
                         ids=["workflow-paths", "fast-lane-guard"])
def test_miroir_sans_serie_orpheline(mirror):
    """L'inverse : aucun miroir ne doit citer une serie non declaree. C'est ce
    qui empeche d'elargir la portee en editant le YAML sans passer par le
    critere d'admission mesure."""
    declared = {e["dir"] for e in load_registry()}
    for path in mirror():
        if path.startswith("MyIA.AI.Notebooks/") and path.endswith("/**"):
            assert path[:-3] in declared, (
                f"{path} n'est pas une serie declaree au registre")


def test_fast_lane_garde_nomme_la_portee_reelle():
    """Le nom du check-run ne doit pas mentir sur la portee (une portee
    'GameTheory serie' pour huit series serait un proxy faux)."""
    sys.path.insert(0, str(REPO_ROOT / "scripts/ci"))
    import fast_lane_registry as flr

    guard = next(g for lst in vars(flr).values() if isinstance(lst, list)
                 for g in lst
                 if getattr(g, "source", None) == "series-naming-gate.yml")
    assert "GameTheory" not in guard.name
    assert REGISTRY_PATH.name not in guard.argv  # lit le registre via son defaut
