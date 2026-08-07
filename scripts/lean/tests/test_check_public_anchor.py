#!/usr/bin/env python3
"""Tests de ``check_public_anchor`` (issue #8782, 2e etage du gate).

    pytest scripts/lean/tests/test_check_public_anchor.py
    python  scripts/lean/tests/test_check_public_anchor.py

Les cas sont construits en fixtures Lean minimales : ce qui est teste, c'est la
**logique d'ancrage**, pas la capacite de Lean a compiler les fixtures. Un seul
test touche le depot reel (``HashlifeCorrectness.lean``), et il est skippe si le
module a evolue -- c'est un temoin, pas un oracle fige.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_public_anchor import (  # noqa: E402
    ANCHORED_PUBLIC,
    ANCHORED_TRANSITIVE,
    ANONYMOUS,
    UNANCHORED,
    analyze_module,
    build_reference_graph,
    main,
    parse_declarations,
    public_closure_reaches,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
HASHLIFE = (
    REPO_ROOT
    / "MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/Conway/Life/HashlifeCorrectness.lean"
)


def _write(tmp_path: Path, body: str, name: str = "M.lean") -> Path:
    p = tmp_path / name
    p.write_text(body, encoding="utf-8")
    return p


def _verdicts(path: Path) -> list[str]:
    return [s["verdict"] for s in analyze_module(path)["sites"]]


# --------------------------------------------------------------------------
# Parsing : visibilite, namespaces, commentaires
# --------------------------------------------------------------------------


def test_parse_marks_private_and_public():
    decls = parse_declarations(
        "theorem pub : True := trivial\n"
        "private theorem priv : True := trivial\n"
        "private lemma with_attr : True := trivial\n"
    )
    assert [(d.name, d.private) for d in decls] == [
        ("pub", False),
        ("priv", True),
        ("with_attr", True),
    ]


def test_parse_qualifies_by_namespace_and_handles_root():
    decls = parse_declarations(
        "namespace Foo\n"
        "namespace Bar\n"
        "theorem inner : True := trivial\n"
        "end Bar\n"
        "theorem outer : True := trivial\n"
        "theorem _root_.escaped : True := trivial\n"
        "end Foo\n"
    )
    assert [d.name for d in decls] == ["Foo.Bar.inner", "Foo.outer", "escaped"]


def test_parse_ignores_end_of_section_when_popping_namespace():
    """``end`` d'une section ne doit pas desequilibrer la pile (cf #8722)."""
    decls = parse_declarations(
        "namespace Foo\nsection Helpers\ntheorem a : True := trivial\nend Helpers\n"
        "theorem b : True := trivial\nend Foo\n"
    )
    assert [d.name for d in decls] == ["Foo.a", "Foo.b"]


def test_sorry_in_prose_is_ignored(tmp_path):
    """Le mot ``sorry`` en docstring ou en commentaire ne produit aucun site."""
    p = _write(
        tmp_path,
        "/-- Ce lemme evite un `sorry` en reduisant au cas fini. -/\n"
        "theorem clean : True := trivial\n"
        "-- TODO: remplacer le sorry historique\n",
    )
    assert _verdicts(p) == []


def test_sorryax_and_sorry_prefixed_names_are_not_sorry(tmp_path):
    p = _write(
        tmp_path,
        "theorem a : True := by exact sorryAx _\ntheorem b : True := by sorry_like\n",
    )
    assert _verdicts(p) == []


# --------------------------------------------------------------------------
# Ancrage : les quatre verdicts
# --------------------------------------------------------------------------


def test_public_sorry_is_anchored(tmp_path):
    p = _write(tmp_path, "theorem visible : True := by sorry\n")
    assert _verdicts(p) == [ANCHORED_PUBLIC]


def test_private_cited_by_public_is_transitively_anchored(tmp_path):
    p = _write(
        tmp_path,
        "private theorem helper : True := by sorry\ntheorem exposed : True := by exact helper\n",
    )
    assert _verdicts(p) == [ANCHORED_TRANSITIVE]


def test_private_cited_by_nobody_is_unanchored(tmp_path):
    p = _write(tmp_path, "private theorem dead : True := by sorry\n")
    assert _verdicts(p) == [UNANCHORED]


def test_private_chain_private_all_the_way_is_unanchored(tmp_path):
    """Le coeur du defaut #8782 : chaine privee sur toute sa longueur."""
    p = _write(
        tmp_path,
        "private theorem leaf : True := by sorry\n"
        "private theorem mid : True := by exact leaf\n"
        "private theorem top : True := by exact mid\n",
    )
    assert _verdicts(p) == [UNANCHORED]


def test_private_chain_becomes_anchored_when_a_public_joins_it(tmp_path):
    """Meme chaine, plus un consommateur public : le gate la voit."""
    p = _write(
        tmp_path,
        "private theorem leaf : True := by sorry\n"
        "private theorem mid : True := by exact leaf\n"
        "theorem exposed : True := by exact mid\n",
    )
    assert _verdicts(p) == [ANCHORED_TRANSITIVE]


def test_example_sorry_is_anonymous(tmp_path):
    """``example`` n'a pas de nom : jamais enumerable, quelle que soit la chaine."""
    p = _write(tmp_path, "example : True := by sorry\n")
    assert _verdicts(p) == [ANONYMOUS]


def test_multiple_sorries_attributed_to_their_own_owner(tmp_path):
    p = _write(
        tmp_path,
        "private theorem hidden : True := by\n"
        "  have h : True := by sorry\n"
        "  sorry\n"
        "theorem shown : True := by sorry\n",
    )
    assert _verdicts(p) == [UNANCHORED, UNANCHORED, ANCHORED_PUBLIC]


def test_short_name_reference_across_namespace_counts(tmp_path):
    """Une reference intra-namespace en nom court doit creer l'arete."""
    p = _write(
        tmp_path,
        "namespace N\nprivate theorem helper : True := by sorry\n"
        "theorem exposed : True := by exact helper\nend N\n",
    )
    assert _verdicts(p) == [ANCHORED_TRANSITIVE]


def test_self_reference_does_not_anchor(tmp_path):
    """Une declaration recursive ne s'ancre pas elle-meme."""
    p = _write(tmp_path, "private def loop (n : Nat) : Nat := by sorry\n")
    assert _verdicts(p) == [UNANCHORED]


def test_public_closure_reaches_returns_the_anchors(tmp_path):
    decls = parse_declarations(
        "private theorem leaf : True := by sorry\n"
        "private theorem mid : True := by exact leaf\n"
        "theorem alpha : True := by exact mid\n"
        "theorem beta : True := by exact mid\n"
    )
    build_reference_graph(decls)
    reached, anchors = public_closure_reaches("leaf", decls)
    assert reached and anchors == ["alpha", "beta"]


# --------------------------------------------------------------------------
# Rapport et CLI
# --------------------------------------------------------------------------


def test_module_report_counts(tmp_path):
    p = _write(
        tmp_path,
        "private theorem dead : True := by sorry\ntheorem live : True := by sorry\n",
    )
    r = analyze_module(p)
    assert r["declarations"] == 2
    assert r["private_declarations"] == 1
    assert r["sorry_sites"] == 2
    assert r["unanchored"] == 1


def test_clean_module_is_silent(tmp_path):
    p = _write(tmp_path, "theorem ok : True := trivial\nprivate theorem h : True := trivial\n")
    r = analyze_module(p)
    assert r["sorry_sites"] == 0 and r["unanchored"] == 0


def test_cli_is_advisory_by_default(tmp_path, capsys):
    p = _write(tmp_path, "private theorem dead : True := by sorry\n")
    assert main([str(p)]) == 0
    assert "unanchored" in capsys.readouterr().out


def test_cli_fail_on_unanchored_is_opt_in(tmp_path):
    p = _write(tmp_path, "private theorem dead : True := by sorry\n")
    assert main([str(p), "--fail-on-unanchored"]) == 1


def test_cli_fail_flag_stays_green_when_all_anchored(tmp_path):
    p = _write(tmp_path, "theorem shown : True := by sorry\n")
    assert main([str(p), "--fail-on-unanchored"]) == 0


def test_cli_rejects_empty_lake(tmp_path):
    """Cible vide = erreur, jamais un rapport propre (classe EMPTY_* de #8940)."""
    (tmp_path / "empty_lake").mkdir()
    with pytest.raises(SystemExit) as e:
        main(["--lake", str(tmp_path / "empty_lake")])
    assert e.value.code == 2


def test_cli_rejects_missing_lake(tmp_path):
    with pytest.raises(SystemExit) as e:
        main(["--lake", str(tmp_path / "nope")])
    assert e.value.code == 2


def test_cli_rejects_missing_file(tmp_path):
    with pytest.raises(SystemExit) as e:
        main([str(tmp_path / "absent.lean")])
    assert e.value.code == 2


def test_cli_ignores_lake_dot_lake_subtree(tmp_path):
    """Les deps vendorees sous .lake/ ne doivent pas etre analysees."""
    lake = tmp_path / "lk"
    (lake / ".lake" / "packages" / "mathlib").mkdir(parents=True)
    (lake / ".lake" / "packages" / "mathlib" / "Dep.lean").write_text(
        "private theorem vendored : True := by sorry\n", encoding="utf-8"
    )
    (lake / "Own.lean").write_text("theorem mine : True := trivial\n", encoding="utf-8")
    assert [p.name for p in __import__("check_public_anchor").lean_sources(lake)] == ["Own.lean"]


def test_cli_json_is_parseable(tmp_path, capsys):
    import json

    p = _write(tmp_path, "private theorem dead : True := by sorry\n")
    assert main([str(p), "--json"]) == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload[0]["unanchored"] == 1


# --------------------------------------------------------------------------
# Temoin sur le depot reel
# --------------------------------------------------------------------------


def hashlife_modules() -> list[Path]:
    """L'agregateur **et** ses sous-modules.

    Le temoin ne peut pas viser un fichier : au split #9863 la substance a quitte
    ``HashlifeCorrectness.lean``, devenu un agregateur d'imports, pour descendre
    dans ``HashlifeCorrectness/{Foundation,Walls/*}.lean``. Viser le seul fichier
    d'origine faisait tomber le temoin a ``unanchored == 0`` -- soit precisement
    l'angle mort #8782 qu'il existe pour attraper, reproduit sur lui-meme.
    """
    mods = [HASHLIFE] if HASHLIFE.is_file() else []
    tree = HASHLIFE.with_suffix("")
    if tree.is_dir():
        mods += sorted(tree.rglob("*.lean"))
    return mods


@pytest.mark.skipif(not HASHLIFE.is_file(), reason="conway_lean absent de cet arbre")
def test_hashlife_blind_spot_stays_reabsorbed():
    """Garde-regression #8782 : l'angle mort Hashlife, reabsorbe par #9897, ne doit pas revenir.

    Ce test etait un *temoin* du defaut #8782 (chaines sorry privees non ancrees) :
    il assertait que la classe de defaut etait instanciee dans Hashlife pour exercer
    le gate ``check_public_anchor`` sur un cas reel. La fusion #9897 (-9 sorry) a
    reabsorbe cet angle mort : un scan de tous les modules own (198 fichiers, cf
    le corps de ce PR) ne trouve plus aucun site ``UNANCHORED`` dans tout le depot,
    pas seulement Hashlife.
    Sans cible, le temoin est converti en garde-regression, conformement a son propre
    docstring originel (<< mettre a jour le temoin >>).

    Porte sur l'**union** de l'agregateur et de ses sous-modules (cf
    ``hashlife_modules``) : c'est la meme union que ``target-modules`` cote CI.

    Deux proprietes gardees :

      - **regression** : aucun site ``UNANCHORED`` ne reaparait dans Hashlife (sinon
        le -9 sorry de #9897 est defait -> rouge, signalement d'une regression reelle).
      - **temoin d'integration** : le gate tourne toujours sur du vrai Lean et
        classifie le sorry residuel (au moins un site ``ANCHORED_PUBLIC`` visible),
        pour que l'outil reste exerce sur le depot reel, pas seulement sur des fixtures.

    Cf #8782, #9897, #9863 (split Hashlife).
    """
    sites = [s for p in hashlife_modules() for s in analyze_module(p)["sites"]]
    if not sites:
        pytest.skip("Hashlife totalement assaini : aucun sorry residuel a surveiller")
    unanchored = [s for s in sites if s["verdict"] == UNANCHORED]
    assert not unanchored, (
        "regression #8782 : un sorry prive non ancre a reaparu dans Hashlife -- "
        f"porteurs={sorted({s['owner'] for s in unanchored})}"
    )
    assert any(s["verdict"] == ANCHORED_PUBLIC for s in sites), (
        "aucun sorry public visible : le gate ne s'exerce plus sur un cas reel"
    )


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-v"]))
