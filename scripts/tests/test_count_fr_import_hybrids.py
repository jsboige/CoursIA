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
12. `main` sur un lac **sans aucun** `_en.lean` rend 2 : un zero qui ne se
    distingue pas d'un chemin casse n'est pas une mesure ;
13. `--json` porte `files`, `edges`, `per_lake` et la liste des lacs ;
14. `--list` porte le detail par fichier dans la sortie texte ;
15. `strip_comments` retire bloc et ligne : un `import` ou un `def` commentes
    ne comptent pas ;
16. `census` compte les `_en.lean` **hors lac** au lieu de les taire ;
17. la sortie texte nomme le commit mesure (ou dit qu'il est hors depot git) ;
18. (#24666) un `_en.lean` hors `roots` est un **orphelin** non compte, le meme
    fichier sous un root declare remonte (probe de la sonde) ;
19. (#24666) un `_en.lean` importe par une racine est atteignable (fermeture des
    imports, comme Lake) ;
20. (#24666) un fichier sous un lac imbrique appartient au lac le plus proche,
    jamais au lac parent ;
21. (#24666) `lakefile.lean` : la forme `lean_lib X where roots := #[...]` est
    lue, un commentaire `-- lean_lib` ignore ;
22. (#24666) une clause `roots` de forme inconnue, ou un toml casse, est un
    **incident** (rc 2), jamais un retour silencieux au defaut `[name]` ;
23. (#24666) une racine declaree sans fichier est rapportee (`missing_roots`).

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
    # Lac declare (#24666) : sans `[[lean_lib]]`, Lake ne compile rien et tout
    # `_en.lean` serait un orphelin. Les globs couvrent le sous-arbre `Alpha`.
    (lake / "lakefile.toml").write_text(
        'name = "fixture"\n\n[[lean_lib]]\nname = "Fixture"\nglobs = ["Alpha.*"]\n',
        encoding="utf-8",
    )
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
    assert not mod.in_scope(Path("x/reference_docs/Foo_en.lean"))
    # Lake externe de la regle i18n : chemin reel sous GameTheory/SocialChoice/
    # (point 4 de la review Hermes de #24032 -- le fragment `/_peters/`
    # d'origine ne matchait AUCUN segment de ce chemin).
    assert not mod.in_scope(Path("MyIA.AI.Notebooks/GameTheory/SocialChoice/social_choice_lean_peters/Choice_en.lean"))
    # Un repertoire exclu **a la racine mesuree** : sans son `/` de tete, le
    # fragment ne matchait pas et le perimetre fuyait.
    assert not mod.in_scope(Path("social_choice_lean_peters/Foo_en.lean"))
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


def test_main_lake_without_en_twins_is_incident():
    """Un lac sans aucun `_en.lean` n'est pas un « zero propre » (#24032)."""
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        lake = root / "lonely_lean"
        lake.mkdir()
        _write(lake / "lakefile.toml", 'name = "lonely"\n')
        _write(lake / "Alpha" / "Base.lean", "namespace Alpha.Base\n\ndef b := 1\n")
        assert mod.main(["--root", str(root)]) == 2


def test_strip_comments_hides_commented_imports_and_declarations():
    text = (
        "/- import Alpha.Base\n   def commented := 1 -/\n"
        "import Alpha.Real\n"
        "-- import Alpha.Other\n"
        "-- def alsoCommented := 2\n"
        "namespace Alpha.Real_en\n"
    )
    stripped = mod.strip_comments(text)
    assert "Alpha.Base" not in stripped, stripped
    assert "Alpha.Other" not in stripped, stripped
    assert mod.imports_of(stripped) == ["Alpha.Real"], mod.imports_of(stripped)
    assert mod.DECL_RE.findall(stripped) == [], mod.DECL_RE.findall(stripped)


def test_census_counts_en_files_outside_lakes():
    with tempfile.TemporaryDirectory() as tmp:
        lake = _lake(tmp)
        _write(
            lake / "Alpha" / "Hybrid_en.lean",
            "import Alpha.Base\n\nnamespace Alpha.Hybrid_en\n\ndef h := 2\n\n"
            "end Alpha.Hybrid_en\n",
        )
        # `_en.lean` hors de tout lac : aucune arete possible, mais il ne doit
        # pas disparaitre de la mesure.
        _write(
            Path(tmp) / "loose" / "Orphan_en.lean",
            "import Alpha.Base\n\nnamespace Orphan_en\n\ndef o := 1\n",
        )
        report = mod.census(Path(tmp))
    assert report["n_lakes"] == 1, report
    assert report["n_en_outside_lakes"] == 1, report
    assert report["files"] == 1, report
    text = mod.render(report, show_list=False)
    assert "hors lac" in text, text


def test_render_names_the_measured_commit():
    with tempfile.TemporaryDirectory() as tmp:
        lake = _lake(tmp)
        _write(
            lake / "Alpha" / "Hybrid_en.lean",
            "import Alpha.Base\n\nnamespace Alpha.Hybrid_en\n\ndef h := 2\n\n"
            "end Alpha.Hybrid_en\n",
        )
        report = mod.census(lake)
    text = mod.render(report, show_list=False)
    # Hors depot git (repertoire temporaire) : la sortie le DIT au lieu de
    # taire la provenance du chiffre.
    assert report["measured_commit"] is None, report["measured_commit"]
    assert "Mesure hors depot git" in text, text


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


_HYBRID_HIDDEN = (
    "import Alpha.Base\n\nnamespace Alpha.Hidden_en\n\ndef h := 2\n\n"
    "end Alpha.Hidden_en\n"
)


def _set_toml(lake: Path, text: str) -> None:
    (lake / "lakefile.toml").write_text(text, encoding="utf-8")


def test_orphan_hybrid_counted_only_under_a_declared_root():
    """Probe (#24666) : le meme hybride, hors roots -> orphelin ; sous un root -> compte."""
    with tempfile.TemporaryDirectory() as tmp:
        outside = _lake(tmp, "outside_lean")
        _set_toml(
            outside,
            'name = "fixture"\n\n[[lean_lib]]\nname = "Fixture"\nroots = ["Alpha.Base"]\n',
        )
        _write(outside / "Alpha" / "Hidden_en.lean", _HYBRID_HIDDEN)
        report_out = mod.census(outside)

        inside = _lake(tmp, "inside_lean")
        _set_toml(
            inside,
            'name = "fixture"\n\n[[lean_lib]]\nname = "Fixture"\n'
            'roots = ["Alpha.Base", "Alpha.Hidden_en"]\n',
        )
        _write(inside / "Alpha" / "Hidden_en.lean", _HYBRID_HIDDEN)
        report_in = mod.census(inside)

    assert report_out["files"] == 0, report_out["hybrids"]
    assert {"lake": "outside_lean", "relative": "Alpha/Hidden_en.lean"} in report_out["orphans"], report_out["orphans"]
    assert report_out["n_en_orphans"] >= 1, report_out
    assert report_in["files"] == 1, report_in["hybrids"]
    # Base_en.lean n'est pas une racine ici : il reste orphelin, mais l'hybride, lui, est atteint.
    assert {"lake": "inside_lean", "relative": "Alpha/Hidden_en.lean"} not in report_in["orphans"], report_in["orphans"]
    text = mod.render(report_out, show_list=False)
    assert "orphelins non mesures" in text, text


def test_en_file_imported_by_a_root_is_reachable():
    """Lake compile la fermeture des imports d'une racine : un `_en` importe est atteignable."""
    with tempfile.TemporaryDirectory() as tmp:
        lake = _lake(tmp)
        _set_toml(
            lake,
            'name = "fixture"\n\n[[lean_lib]]\nname = "Fixture"\nroots = ["Alpha.Entry"]\n',
        )
        _write(lake / "Alpha" / "Entry.lean", "import Alpha.Hidden_en\n\nnamespace Alpha.Entry\n\nend Alpha.Entry\n")
        _write(lake / "Alpha" / "Hidden_en.lean", _HYBRID_HIDDEN)
        report = mod.census(lake)
    assert report["files"] == 1, report["hybrids"]
    # Alpha/Base_en.lean n'est importe par aucune racine : orphelin, lui. Le `_en`
    # importe (Hidden_en) ne doit pas figurer parmi les orphelins.
    orphan_names = {item["relative"] for item in report["orphans"]}
    assert "Alpha/Hidden_en.lean" not in orphan_names, orphan_names


def test_nested_lake_owns_its_files_not_the_parent():
    """Un `_en` sous un lac imbrique appartient au lac le plus proche (#24666)."""
    with tempfile.TemporaryDirectory() as tmp:
        outer = Path(tmp) / "outer_lean"
        outer.mkdir()
        _set_toml(
            outer,
            'name = "outer"\n\n[[lean_lib]]\nname = "Outer"\nglobs = ["inner_lean.*"]\n',
        )
        inner = outer / "inner_lean"
        inner.mkdir()
        _write(
            inner / "lakefile.toml",
            'name = "inner"\n\n[[lean_lib]]\nname = "Inner"\nglobs = ["Beta.*"]\n',
        )
        _write(inner / "Beta" / "Base.lean", "namespace Beta.Base\n\ndef b := 1\n\nend Beta.Base\n")
        _write(inner / "Beta" / "Base_en.lean", "namespace Beta.Base_en\n\ndef b := 1\n\nend Beta.Base_en\n")
        _write(
            inner / "Beta" / "Hyb_en.lean",
            "import Beta.Base\n\nnamespace Beta.Hyb_en\n\ndef h := 2\n\nend Beta.Hyb_en\n",
        )
        report = mod.census(outer)
    assert report["per_lake"] == {"inner_lean": {"files": 1, "edges": 1}}, report["per_lake"]
    # Deux `_en` appartiennent au lac interieur (Base_en, Hyb_en) ; le lac parent n'en possede aucun.
    assert report["n_en_files"] == 2, report["n_en_files"]


def test_lakefile_lean_roots_dsl_is_read():
    with tempfile.TemporaryDirectory() as tmp:
        lake = _lake(tmp, "dsl_lean")
        (lake / "lakefile.toml").unlink()
        _write(
            lake / "lakefile.lean",
            "import Lake\nopen Lake DSL\n\npackage dsl\n\n"
            "-- lean_lib Ignored where roots := #[`Ghost]\n"
            "@[default_target]\nlean_lib Fixture where\n"
            "  roots := #[`Alpha.Hidden_en]\n",
        )
        _write(lake / "Alpha" / "Hidden_en.lean", _HYBRID_HIDDEN)
        _write(lake / "Alpha" / "Other_en.lean", _HYBRID_HIDDEN.replace("Hidden", "Other"))
        selectors = mod.lake_selectors(lake)
        report = mod.census(lake)
    assert selectors == [("one", "Alpha.Hidden_en")], selectors
    assert report["files"] == 1, report["hybrids"]
    assert {"lake": "dsl_lean", "relative": "Alpha/Other_en.lean"} in report["orphans"], report["orphans"]


def test_unreadable_roots_is_incident_not_default():
    """Une clause `roots` de forme inconnue ne doit pas retomber sur le defaut `[name]`."""
    with tempfile.TemporaryDirectory() as tmp:
        lake = _lake(tmp, "weird_lean")
        (lake / "lakefile.toml").unlink()
        _write(
            lake / "lakefile.lean",
            "lean_lib Fixture where\n  roots := base ++ #[`Alpha.Base]\n",
        )
        try:
            mod.census(lake)
        except mod.LakefileError:
            pass
        else:
            raise AssertionError("LakefileError attendu pour une clause roots non reconnue")
        assert mod.main(["--root", str(Path(tmp))]) == 2


def test_broken_toml_is_incident():
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        lake = root / "broken_lean"
        lake.mkdir()
        _write(lake / "lakefile.toml", "[[lean_lib\nname = \n")
        _write(lake / "Alpha" / "Base_en.lean", "namespace Alpha.Base_en\n")
        assert mod.main(["--root", str(root)]) == 2


def test_missing_root_is_reported_not_silent():
    with tempfile.TemporaryDirectory() as tmp:
        lake = _lake(tmp)
        _set_toml(
            lake,
            'name = "fixture"\n\n[[lean_lib]]\nname = "Fixture"\nroots = ["Alpha.Ghost"]\n',
        )
        report = mod.census(lake)
    assert report["missing_roots"] == [{"lake": "fixture_lean", "module": "Alpha.Ghost"}], report["missing_roots"]
    assert "Alpha.Ghost" in mod.render(report, show_list=False)


# Formes reelles relevees sur le depot complet (#24666, point 1 de la reserve
# coordinateur) : copie verbatim des blocs `lean_lib` de trois lakefiles du depot
# (GameTheory/assignment_lean, SymbolicAI/Lean/differential_lean,
# Compression/Compression_lean), reunis dans un seul fichier de test.
_REAL_SHAPES_LAKEFILE = """import Lake
open Lake DSL

package «fixture» where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

@[default_target]
lean_lib Assignment where
  globs := #[`Assignment.*, `Assignment_en]

lean_lib «PrefixCodes» where
  -- Module plat (fichiers racine, aucune arborescence `PrefixCodes/`).
  globs := #[`PrefixCodes, `PrefixCodes_en, `Decode, `SymbolCodec_en]

lean_lib «Differential» where
  -- `Poincare` et `Poincare_en` suivent la meme regle.
  globs := #[
    `DifferentialTour, `DifferentialTour_en,
    `Poincare, `Poincare_en]
"""


def test_backtick_glob_forms_are_read_dsl():
    """`X`, `X.*`, `X.+` et les `.one/.submodules/.andSubmodules` (#24666)."""
    with tempfile.TemporaryDirectory() as tmp:
        lake = _lake(tmp, "forms_lean")
        (lake / "lakefile.toml").unlink()
        _write(
            lake / "lakefile.lean",
            "import Lake\nopen Lake DSL\n\npackage forms\n\n"
            "lean_lib «Forms» where\n  globs := #[`Alpha.*, `Alpha_en, `Beta.+]\n\n"
            "lean_lib «Kinds» where\n"
            "  globs := #[.submodules `Gamma, .andSubmodules `Delta, .one `Eps]\n",
        )
        _write(lake / "Beta" / "Hidden_en.lean", _HYBRID_HIDDEN)
        _write(lake / "Beta_en.lean", "namespace Beta_en\n\nend Beta_en\n")
        selectors = mod.lake_selectors(lake)
        _, reach, _ = mod.lake_reachable(lake, mod.find_lakes(lake))
    assert selectors == [
        ("all", "Alpha"),
        ("one", "Alpha_en"),
        ("sub", "Beta"),
        ("sub", "Gamma"),
        ("all", "Delta"),
        ("one", "Eps"),
    ], selectors
    reached = {p.relative_to(lake).as_posix() for p in reach}
    # `Beta.+` = sous-modules seuls : Beta/Hidden_en est atteint, Beta_en (la racine) non.
    assert "Beta/Hidden_en.lean" in reached, reached
    assert "Beta_en.lean" not in reached, reached


def test_toml_glob_suffixes_are_read():
    assert mod._glob_to_selector("Foo") == ("one", "Foo")
    assert mod._glob_to_selector("Foo.*") == ("all", "Foo")
    assert mod._glob_to_selector("Foo.+") == ("sub", "Foo")
    try:
        mod._glob_to_selector("Foo bar")
    except mod.LakefileError:
        pass
    else:
        raise AssertionError("forme inconnue doit lever LakefileError (fail-closed)")


def test_real_repo_shapes_are_read_not_incident():
    """Non-regression : les formes relevees dans le depot complet sont lues (aucun incident)."""
    with tempfile.TemporaryDirectory() as tmp:
        lake = Path(tmp) / "shapes_lean"
        lake.mkdir()
        _write(lake / "lakefile.lean", _REAL_SHAPES_LAKEFILE)
        selectors = mod.lake_selectors(lake)
    assert selectors == [
        ("all", "Assignment"),
        ("one", "Assignment_en"),
        ("one", "PrefixCodes"),
        ("one", "PrefixCodes_en"),
        ("one", "Decode"),
        ("one", "SymbolCodec_en"),
        ("one", "DifferentialTour"),
        ("one", "DifferentialTour_en"),
        ("one", "Poincare"),
        ("one", "Poincare_en"),
    ], selectors


def test_lib_with_globs_has_no_default_root():
    """Une lib qui declare `globs` n'ajoute pas la racine `[name]` (Planning, Kelly du depot)."""
    with tempfile.TemporaryDirectory() as tmp:
        lake = Path(tmp) / "planning_lean"
        lake.mkdir()
        _write(
            lake / "lakefile.lean",
            "lean_lib «Planning» where\n  globs := #[.submodules `Planning]\n",
        )
        selectors = mod.lake_selectors(lake)
        report = mod.census(lake)
    assert selectors == [("sub", "Planning")], selectors
    assert report["missing_roots"] == [], report["missing_roots"]


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
