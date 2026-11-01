#!/usr/bin/env python3
"""Tests de `scripts/lean/count_fr_import_hybrids.py` (#24019, EPIC #4980).

Le script existe pour rendre **reproductible** un chiffre qui ne l'etait pas :
deux mesures du meme defaut circulaient (29 fichiers / 41 aretes contre
70 / 118) sans que le predicat soit ecrit. Le critere d'acceptation porte donc
sur deux choses, et pas sur le compte du depot -- qui bougera a chaque tranche
de convergence :

1. le predicat est **exact** : un hybride construit remonte, et chacune des
   facons de ne pas etre un hybride (jumeau deja suffixe, aucune declaration
   propre, dependance sans jumeau, fichier vendore) ne remonte pas ;
2. un **perimetre vide rend 2**, jamais 0 : un repertoire mal designe ne doit
   pas passer pour un depot propre.

Cas couverts :

1. `in_scope` ecarte les trois fragments vendores et garde le reste ;
2. `find_lakes` trouve les racines de lac et **n'enumere pas** un lac vendore ;
3. `imports_of` separe les imports multiples et ignore les modules entre
   guillemets ou chevrons ;
4. `hybrid_edges` ne retient que le meme lac, le module non suffixe et le
   jumeau present sur le disque ;
5. `is_hybrid` exige les trois conditions (namespace suffixe, declaration,
   arete) -- chacune est testee par son absence ;
6. `census` sur un lac construit : controle positif, trois faux positifs
   ecartes, vendore ignore, comptes exacts ;
7. le namespace **non** suffixe ne compte pas, meme avec declaration et arete ;
8. l'**auto-import** compte comme une arete (sous-pattern nomme du census) ;
9. `main --self-test` rend 0 ;
10. `main` sur une racine absente rend 2 ;
11. `main` sur un repertoire sans lac rend 2 (perimetre vide = incident) ;
12. `--json` porte `files`, `edges`, `per_lake` et la liste des lacs ;
13. `--list` porte le detail par fichier dans la sortie texte.

Le module est charge **par chemin** : `scripts/lean/` n'est pas un paquet
importable depuis la racine du depot.

Usage : python scripts/tests/test_count_fr_import_hybrids.py
"""

import importlib.util
import json
import sys
import tempfile
from pathlib import Path

TOOL = Path(__file__).resolve().parents[1] / "lean" / "count_fr_import_hybrids.py"

spec = importlib.util.spec_from_file_location("count_fr_import_hybrids", TOOL)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


def _lake(tmp: str, name: str = "fixture_lean") -> Path:
    """Micro-lac : une dependance FR `Alpha/Base.lean` avec son jumeau `_en`."""
    lake = Path(tmp) / name
    (lake / "Alpha").mkdir(parents=True)
    (lake / "lakefile.toml").write_text('name = "fixture"\n', encoding="utf-8")
    (lake / "Alpha" / "Base.lean").write_text(
        "namespace Alpha.Base\n\ndef base := 1\n\nend Alpha.Base\n", encoding="utf-8"
    )
    (lake / "Alpha" / "Base_en.lean").write_text(
        "import Alpha.Base_en\n\nnamespace Alpha.Base_en\n\ndef base := 1\n\n"
        "end Alpha.Base_en\n",
        encoding="utf-8",
    )
    return lake


def _write(path: Path, text: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


def test_in_scope_excludes_vendored_fragments():
    assert not mod.in_scope(Path("x/.lake/packages/mathlib/Foo_en.lean"))
    assert not mod.in_scope(Path("x/_peters/Foo_en.lean"))
    assert not mod.in_scope(Path("x/reference_docs/Foo_en.lean"))
    assert mod.in_scope(Path("x/conway_lean/Conway/Nim_en.lean"))


def test_find_lakes_skips_vendored_lakefiles():
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "good_lean").mkdir()
        _write(root / "good_lean" / "lakefile.lean", "import Lake\n")
        _write(
            root / "good_lean" / ".lake" / "packages" / "vendor" / "lakefile.toml",
            'name = "v"\n',
        )
        names = [lake.name for lake in mod.find_lakes(root)]
    assert "good_lean" in names, names
    assert "vendor" not in names, names


def test_imports_of_splits_and_skips_quoted():
    text = "import Alpha.Base Beta.Core\nimport «weird.name»\nimport \"quoted\"\n"
    assert mod.imports_of(text) == ["Alpha.Base", "Beta.Core"]


def test_hybrid_edges_requires_same_lake_unsuffixed_and_twin():
    with tempfile.TemporaryDirectory() as tmp:
        lake = _lake(tmp)
        # Dependance sans jumeau : ne doit jamais produire d'arete.
        _write(lake / "Alpha" / "NoTwin.lean", "namespace Alpha.NoTwin\n")
        text = "import Alpha.Base Alpha.Base_en Alpha.NoTwin Mathlib.Data.Nat\n"
        edges = mod.hybrid_edges(lake, lake / "Alpha" / "Base_en.lean", text)
    assert edges == ["Alpha.Base"], edges


def test_is_hybrid_needs_the_three_conditions():
    ok = {"namespace_suffixed": True, "declarations": 1, "edges": ["Alpha.Base"]}
    assert mod.is_hybrid(ok)
    assert not mod.is_hybrid({**ok, "namespace_suffixed": False})
    assert not mod.is_hybrid({**ok, "declarations": 0})
    assert not mod.is_hybrid({**ok, "edges": []})


def test_census_positive_and_negative_controls():
    with tempfile.TemporaryDirectory() as tmp:
        lake = _lake(tmp)
        # POSITIF : hybride franc.
        _write(
            lake / "Alpha" / "Hybrid_en.lean",
            "import Alpha.Base\n\nnamespace Alpha.Hybrid_en\n\ndef h := 2\n\n"
            "end Alpha.Hybrid_en\n",
        )
        # FAUX POSITIF 1 : jumeau deja suffixe.
        _write(
            lake / "Alpha" / "Clean_en.lean",
            "import Alpha.Base_en\n\nnamespace Alpha.Clean_en\n\ndef c := 1\n\n"
            "end Alpha.Clean_en\n",
        )
        # FAUX POSITIF 2 : namespace suffixe sans declaration propre.
        _write(
            lake / "Alpha" / "Empty_en.lean",
            "import Alpha.Base\n\nnamespace Alpha.Empty_en\n\nend Alpha.Empty_en\n",
        )
        # FAUX POSITIF 3 : dependance sans jumeau `_en` sur le disque.
        _write(lake / "Alpha" / "NoTwin.lean", "namespace Alpha.NoTwin\n\ndef n := 1\n")
        _write(
            lake / "Alpha" / "Lonely_en.lean",
            "import Alpha.NoTwin\n\nnamespace Alpha.Lonely_en\n\ndef l := 1\n\n"
            "end Alpha.Lonely_en\n",
        )
        # Hors perimetre : un lac vendore portant un hybride evident.
        _write(
            lake / ".lake" / "packages" / "vendor" / "lakefile.toml", 'name = "v"\n'
        )
        _write(
            lake / ".lake" / "packages" / "vendor" / "Vendored_en.lean",
            "import Alpha.Base\n\nnamespace Vendored_en\n\ndef v := 1\n\n"
            "end Vendored_en\n",
        )

        report = mod.census(lake)

    found = {item["relative"] for item in report["hybrids"]}
    assert found == {"Alpha/Hybrid_en.lean"}, found
    assert report["files"] == 1, report
    assert report["edges"] == 1, report
    assert report["per_lake"]["fixture_lean"] == {"files": 1, "edges": 1}, report


def test_census_ignores_unsuffixed_namespace():
    with tempfile.TemporaryDirectory() as tmp:
        lake = _lake(tmp)
        _write(
            lake / "Alpha" / "Mirror_en.lean",
            "import Alpha.Base\n\nnamespace Alpha.Mirror\n\ndef m := 1\n\n"
            "end Alpha.Mirror\n",
        )
        report = mod.census(lake)
    assert report["files"] == 0, report["hybrids"]


def test_census_counts_auto_import_as_edge():
    with tempfile.TemporaryDirectory() as tmp:
        lake = _lake(tmp)
        _write(
            lake / "Alpha" / "Self_en.lean",
            "import Alpha.Self\n\nnamespace Alpha.Self_en\n\ndef s := 1\n\n"
            "end Alpha.Self_en\n",
        )
        _write(lake / "Alpha" / "Self.lean", "namespace Alpha.Self\n\ndef s := 1\n")
        report = mod.census(lake)
    relatives = {item["relative"] for item in report["hybrids"]}
    assert "Alpha/Self_en.lean" in relatives, report["hybrids"]
    assert report["edges"] >= 1, report


def test_main_self_test_is_green():
    assert mod.main(["--self-test"]) == 0


def test_main_missing_root_is_incident():
    missing = str(Path(tempfile.gettempdir()) / "coursia-absent-root-24019")
    assert mod.main(["--root", missing]) == 2


def test_main_empty_scope_is_incident():
    with tempfile.TemporaryDirectory() as tmp:
        assert mod.main(["--root", tmp]) == 2


def test_main_json_payload_shape():
    with tempfile.TemporaryDirectory() as tmp:
        lake = _lake(tmp)
        _write(
            lake / "Alpha" / "Hybrid_en.lean",
            "import Alpha.Base\n\nnamespace Alpha.Hybrid_en\n\ndef h := 2\n\n"
            "end Alpha.Hybrid_en\n",
        )
        report = mod.census(lake)
    assert report["files"] == 1 and report["edges"] == 1
    payload = json.loads(json.dumps(report))
    assert set(payload) >= {"root", "lakes", "n_lakes", "files", "edges", "per_lake"}
    assert payload["lakes"] == ["fixture_lean"], payload["lakes"]


def test_render_shows_total_and_list_detail():
    with tempfile.TemporaryDirectory() as tmp:
        lake = _lake(tmp)
        _write(
            lake / "Alpha" / "Hybrid_en.lean",
            "import Alpha.Base\n\nnamespace Alpha.Hybrid_en\n\ndef h := 2\n\n"
            "end Alpha.Hybrid_en\n",
        )
        report = mod.census(lake)
    text = mod.render(report, show_list=False)
    assert "TOTAL hybrides FR-import : 1 fichiers / 1 aretes" in text, text
    assert "Alpha/Hybrid_en.lean" not in text
    detailed = mod.render(report, show_list=True)
    assert "Alpha/Hybrid_en.lean" in detailed, detailed


def main() -> int:
    tests = [
        (name, obj)
        for name, obj in sorted(globals().items())
        if name.startswith("test_") and callable(obj)
    ]
    failures = 0
    for name, test in tests:
        try:
            test()
        except AssertionError as exc:
            failures += 1
            print(f"FAIL {name}: {exc}")
        except Exception as exc:  # noqa: BLE001 - un test qui explose est un echec
            failures += 1
            print(f"ERROR {name}: {type(exc).__name__}: {exc}")
        else:
            print(f"ok   {name}")
    total = len(tests)
    print(f"\n{total - failures}/{total} tests passes")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
