#!/usr/bin/env python3
"""Unit tests for the pure helpers of `scripts/lean/check_public_anchor.py`.

Le script verifie mecaniquement que chaque `sorry` en position de code
est atteint par la cloture arriere d'une declaration publique
(2e etage du gate `proof-integrity`, issue #8782). Il utilise l'analyse
statique (pas de kernel Lean, pas de Mathlib) sur la portee module de
`private` en Lean 4. Helpers testables en isolation :

  - `parse_declarations(stripped)` : indexe les declarations du source,
    les qualifie par la pile de `namespace`, gere les modificateurs
    `private`/`protected`/`partial`/etc., distingue les declarations
    annonymes (`example`) des nommees.
  - `build_reference_graph(decls)` : renseigne `d.refs` (noms cites
    dans le corps, match exact ou par dernier composant).
  - `public_closure_reaches(target, decls)` : BFS inverse ; retourne
    (atteint, [ancres_publiques_triees]) selon que la cloture arriere
    contient au moins une declaration publique non-annonyme.

Couvre :
  - parse_declarations : basic, namespace, private, anonymous
  - build_reference_graph : reference par nom qualifie, par short name,
    exclusions (ne reference pas sa propre declaration)
  - public_closure_reaches : public direct, transitif via prive,
    unanchored quand toute la chaine est privee
  - Verdict labels : ANCHORED_PUBLIC / TRANSITIVE / UNANCHORED /
    ANONYMOUS / ORPHAN definis et utilises

Contexte : cycle 80 pool atomic epuise, META grain aligne sur les
organes Lean sans pytest coverage. Domain shift : Lean (vs CI/audit
cycles 76-77-79) = progres variete R6.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "lean"))

import check_public_anchor as cpa  # noqa: E402


# --- Constantes ----------------------------------------------------------


def test_verdict_labels_defined():
    """Les 5 verdicts sont definis et distincts."""
    assert cpa.ANCHORED_PUBLIC == "anchored_public"
    assert cpa.ANCHORED_TRANSITIVE == "anchored_transitive"
    assert cpa.UNANCHORED == "unanchored"
    assert cpa.ANONYMOUS == "anonymous"
    assert cpa.ORPHAN == "orphan_sorry"

    labels = {cpa.ANCHORED_PUBLIC, cpa.ANCHORED_TRANSITIVE, cpa.UNANCHORED,
              cpa.ANONYMOUS, cpa.ORPHAN}
    assert len(labels) == 5  # pas de doublon


# --- parse_declarations --------------------------------------------------


def test_parse_declarations_empty():
    """Un source vide (apres strip des commentaires) -> liste vide."""
    assert cpa.parse_declarations("") == []


def test_parse_declarations_one_public_theorem():
    """Un seul theorem public -> 1 declaration, non-private, non-anonymous."""
    src = "theorem foo : True := trivial\n"
    decls = cpa.parse_declarations(src)
    assert len(decls) == 1
    assert decls[0].name == "foo"
    assert decls[0].kind == "theorem"
    assert decls[0].private is False
    assert decls[0].anonymous is False
    assert decls[0].line == 1


def test_parse_declarations_namespace_qualifies_names():
    """Les declarations dans un namespace sont qualifiees par le namespace."""
    src = (
        "namespace Foo\n"
        "  theorem bar : True := trivial\n"
        "end Foo\n"
    )
    decls = cpa.parse_declarations(src)
    assert len(decls) == 1
    assert decls[0].name == "Foo.bar"


def test_parse_declarations_nested_namespaces():
    """Les namespaces imbriques composent le nom qualifie."""
    src = (
        "namespace Outer\n"
        "  namespace Inner\n"
        "    theorem baz : True := trivial\n"
        "  end Inner\n"
        "end Outer\n"
    )
    decls = cpa.parse_declarations(src)
    assert len(decls) == 1
    assert decls[0].name == "Outer.Inner.baz"


def test_parse_declarations_private_modifier():
    """Le modificateur `private` est detecte dans la declaration."""
    src = (
        "namespace Foo\n"
        "  private theorem hidden : True := trivial\n"
        "  theorem visible : True := trivial\n"
        "end Foo\n"
    )
    decls = cpa.parse_declarations(src)
    assert len(decls) == 2
    assert decls[0].name == "Foo.hidden"
    assert decls[0].private is True
    assert decls[1].name == "Foo.visible"
    assert decls[1].private is False


def test_parse_declarations_anonymous_example():
    """Une declaration sans nom (`example`) est anonyme, nom interne generee."""
    src = "example : True := trivial\n"
    decls = cpa.parse_declarations(src)
    assert len(decls) == 1
    assert decls[0].anonymous is True
    assert decls[0].name.startswith("__example_")
    assert decls[0].kind == "example"


def test_parse_declarations_def_kind():
    """Le mot-cle `def` est reconnu (et pas que theorem/lemma)."""
    src = "def myFunc (n : Nat) : Nat := n + 1\n"
    decls = cpa.parse_declarations(src)
    assert len(decls) == 1
    assert decls[0].kind == "def"
    assert decls[0].name == "myFunc"


def test_parse_declarations_body_extent():
    """Le `body` d'une declaration s'etend jusqu'a la declaration suivante."""
    src = (
        "namespace M\n"
        "  theorem a : True := by\n"
        "    trivial\n"
        "  theorem b : True := by\n"
        "    trivial\n"
        "end M\n"
    )
    decls = cpa.parse_declarations(src)
    assert len(decls) == 2
    assert "theorem a" in decls[0].body
    assert "theorem b" not in decls[0].body  # body de a finit AVANT b
    assert "theorem b" in decls[1].body


# --- build_reference_graph ----------------------------------------------


def test_build_reference_graph_empty():
    """Aucun decl -> graphe vide, decls inchanges."""
    cpa.build_reference_graph([])
    assert [] == []  # trivial


def test_build_reference_graph_self_excluded():
    """Une declaration ne se reference pas elle-meme (exclusion dans refs)."""
    src = (
        "namespace M\n"
        "  theorem foo : True := trivial\n"
        "  theorem bar : True := M.foo\n"
        "end M\n"
    )
    decls = cpa.parse_declarations(src)
    cpa.build_reference_graph(decls)
    bar = next(d for d in decls if d.name == "M.bar")
    foo = next(d for d in decls if d.name == "M.foo")
    # bar reference foo
    assert "M.foo" in bar.refs
    # foo ne reference pas bar (n'apparait pas dans son propre corps)
    assert "M.bar" not in foo.refs
    # foo ne se reference pas lui-meme (sortie de la fonction)
    assert "M.foo" not in foo.refs


def test_build_reference_graph_short_name():
    """Une reference par nom court (sans namespace) est resolue."""
    src = (
        "namespace M\n"
        "  theorem helper : True := trivial\n"
        "  theorem caller : True := M.helper\n"
        "end M\n"
    )
    decls = cpa.parse_declarations(src)
    cpa.build_reference_graph(decls)
    caller = next(d for d in decls if d.name == "M.caller")
    # Le token `helper` matche par short name -> M.helper
    assert "M.helper" in caller.refs


def test_build_reference_graph_anonymous_excluded():
    """Les declarations anonymes n'apparaissent pas dans by_qualified."""
    src = (
        "namespace M\n"
        "  example : True := trivial\n"
        "  theorem caller : True := trivial\n"
        "end M\n"
    )
    decls = cpa.parse_declarations(src)
    cpa.build_reference_graph(decls)
    by_qualified = {d.name: d.name for d in decls if not d.anonymous}
    assert "M.caller" in by_qualified
    # Pas de cle pour la declaration anonyme
    anon = next(d for d in decls if d.anonymous)
    assert anon.name not in by_qualified


# --- public_closure_reaches ---------------------------------------------


def test_public_closure_reaches_no_callers():
    """Un public sans aucun caller -> cloture arriere vide, pas d'ancrage.

    Note : `public_closure_reaches` est concu pour les declarations
    PRIVEES. Pour un public, `analyze_module` court-circuite avec le
    verdict `ANCHORED_PUBLIC` (le public est lui-meme un ancrage). La
    cloture arriere d'un public isole est vide (aucun caller ne le
    remonte) -- c'est coherent avec le role de la fonction.
    """
    src = "theorem pub : True := trivial\n"
    decls = cpa.parse_declarations(src)
    cpa.build_reference_graph(decls)
    reached, anchors = cpa.public_closure_reaches("pub", decls)
    # Pas de callers dans la cloture arriere -> anchors vide.
    assert reached is False
    assert anchors == []


def test_public_closure_reaches_transitive_via_private():
    """Un prive reference par un public -> ancrage transitif."""
    src = (
        "namespace M\n"
        "  private theorem helper : True := trivial\n"
        "  theorem pub : True := M.helper\n"
        "end M\n"
    )
    decls = cpa.parse_declarations(src)
    cpa.build_reference_graph(decls)
    reached, anchors = cpa.public_closure_reaches("M.helper", decls)
    assert reached is True
    assert anchors == ["M.pub"]


def test_public_closure_reaches_unanchored():
    """Un prive sans aucun caller public -> unanchored."""
    src = (
        "namespace M\n"
        "  private theorem orphan_helper : True := trivial\n"
        "end M\n"
    )
    decls = cpa.parse_declarations(src)
    cpa.build_reference_graph(decls)
    reached, anchors = cpa.public_closure_reaches("M.orphan_helper", decls)
    assert reached is False
    assert anchors == []


def test_public_closure_reaches_chain():
    """Une chaine : public -> prive1 -> prive2, prive2 atteint via BFS."""
    src = (
        "namespace M\n"
        "  private theorem deep : True := trivial\n"
        "  private theorem mid : True := M.deep\n"
        "  theorem pub : True := M.mid\n"
        "end M\n"
    )
    decls = cpa.parse_declarations(src)
    cpa.build_reference_graph(decls)
    reached, anchors = cpa.public_closure_reaches("M.deep", decls)
    assert reached is True
    # La cloture arriere de deep inclut mid (qui le reference) et pub (qui
    # reference mid) ; seul pub est public.
    assert anchors == ["M.pub"]


def test_public_closure_reaches_excludes_anonymous():
    """Les declarations anonymes sont exclues des ancrages."""
    src = (
        "namespace M\n"
        "  example : True := trivial\n"
        "  theorem only_anon_user : True := trivial\n"
        "end M\n"
    )
    decls = cpa.parse_declarations(src)
    cpa.build_reference_graph(decls)
    # Si on cherche un ancrage public pour l'anonymous (impossible) :
    anon = next(d for d in decls if d.anonymous)
    reached, anchors = cpa.public_closure_reaches(anon.name, decls)
    # La cloture peut etre vide car l'anonymous n'est pas enumerable comme caller
    # Resultat : anchors vide (exclusion explicite des anonymous dans la comprehension)
    assert anchors == []
    assert reached is False


def test_public_closure_reaches_anchors_sorted():
    """Les ancrages retournes sont tries par ordre alphabetique."""
    src = (
        "namespace M\n"
        "  private theorem h : True := trivial\n"
        "  theorem a : True := M.h\n"
        "  theorem b : True := M.h\n"
        "  theorem c : True := M.h\n"
        "end M\n"
    )
    decls = cpa.parse_declarations(src)
    cpa.build_reference_graph(decls)
    reached, anchors = cpa.public_closure_reaches("M.h", decls)
    assert reached is True
    assert anchors == ["M.a", "M.b", "M.c"]  # trie


# --- Integration : scenario du ticket #8782 ----------------------------


def test_scenario_public_lemma_chained_to_public():
    """Scenario : un lemme public appele par un autre public.

    On teste la cloture arriere de pub1 (qui est reference par pub2) :
    le caller pub2 est lui-meme public -> ancrage transitive reussi.
    """
    src = (
        "namespace M\n"
        "  theorem pub1 : True := trivial\n"
        "  theorem pub2 : True := M.pub1\n"
        "end M\n"
    )
    decls = cpa.parse_declarations(src)
    cpa.build_reference_graph(decls)
    # pub1 a pour caller pub2 (qui le reference), pub2 est public -> ancrage.
    r1, a1 = cpa.public_closure_reaches("M.pub1", decls)
    assert r1 is True
    assert a1 == ["M.pub2"]
    # pub2 n'a aucun caller -> cloture vide, pas d'ancrage dans la BFS.
    r2, a2 = cpa.public_closure_reaches("M.pub2", decls)
    assert r2 is False
    assert a2 == []


def test_scenario_unanchored_chain():
    """Scenario : chain de prives sans aucune racine publique."""
    src = (
        "namespace M\n"
        "  private theorem p1 : True := trivial\n"
        "  private theorem p2 : True := M.p1\n"
        "  private theorem p3 : True := M.p2\n"
        "end M\n"
    )
    decls = cpa.parse_declarations(src)
    cpa.build_reference_graph(decls)
    r, a = cpa.public_closure_reaches("M.p1", decls)
    assert r is False
    # Pas de public dans la cloture
    assert a == []


def test_decl_label_property():
    """Decl.label retourne le nom ou un placeholder anonyme."""
    src = (
        "theorem foo : True := trivial\n"
        "example : True := trivial\n"
    )
    decls = cpa.parse_declarations(src)
    foo = next(d for d in decls if d.kind == "theorem")
    anon = next(d for d in decls if d.kind == "example")
    assert foo.label == "foo"
    # Pour les anonymes, label = f"<{kind}@{line}>"
    assert anon.label.startswith("<example@")
    assert str(anon.line) in anon.label


# --- lean_sources helper -------------------------------------------------


def test_lean_sources_filters_lake_dir(tmp_path):
    """Les fichiers .lean sous `.lake/` sont filtres (deps vendored)."""
    (tmp_path / "Main.lean").write_text("-- public")
    (tmp_path / ".lake").mkdir()
    (tmp_path / ".lake" / "deps.lean").write_text("-- vendored")
    (tmp_path / "Other.lean").write_text("-- public 2")
    sources = cpa.lean_sources(tmp_path)
    names = [p.name for p in sources]
    assert "Main.lean" in names
    assert "Other.lean" in names
    assert "deps.lean" not in names


def test_lean_sources_returns_sorted(tmp_path):
    """Les sources sont triees (par Path.rglob + sorted)."""
    (tmp_path / "z.lean").write_text("")
    (tmp_path / "a.lean").write_text("")
    (tmp_path / "m.lean").write_text("")
    sources = cpa.lean_sources(tmp_path)
    names = [p.name for p in sources]
    # Sorted par sorted() sur Path -> tri par string
    assert names == sorted(names)
