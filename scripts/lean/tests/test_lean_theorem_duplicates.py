#!/usr/bin/env python3
"""Tests de l'organe de detection des theoremes en double (#24183, T0).

Le **controle positif** est la raison d'etre de ce fichier : l'organe doit
trouver les deux doublons que #23097 avait conclut absents en comparant les
noms de modules -- la paire **Arrow** et la paire **Sen**. Un organe qui ne
les voit pas ne mesure rien : il ne voit que le bruit.

Le **controle negatif** verifie l'inverse : les lemmes generiques qui
portent les memes noms dans des lacs sans rapport (`refl`, `trans`, `card`,
`step`) ne doivent pas apparaitre parmi les paires fortes.

Usage :
    python scripts/lean/tests/test_lean_theorem_duplicates.py
    python -m pytest scripts/lean/tests/test_lean_theorem_duplicates.py -q
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]


def _load_module():
    """Charge l'organe par son chemin (le script vit hors du paquet)."""
    path = REPO_ROOT / "scripts" / "lean" / "lean_theorem_duplicates.py"
    spec = importlib.util.spec_from_file_location("lean_theorem_duplicates", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules["lean_theorem_duplicates"] = module
    spec.loader.exec_module(module)
    return module


mod = _load_module()

# Les deux doublons attendus : (lac A, nom A) x (lac B, nom B).
ARROW = (
    "MyIA.AI.Notebooks/GameTheory/game_theory_lean",
    "arrow",
    "MyIA.AI.Notebooks/GameTheory/lean_game_defs",
    "arrow_impossibility",
)
SEN = (
    "MyIA.AI.Notebooks/GameTheory/game_theory_lean",
    "sen_impossibility",
    "MyIA.AI.Notebooks/GameTheory/lean_game_defs",
    "sen_impossibility",
)

# Les lemmes generiques qui ne doivent PAS etre signales comme doublons.
GENERIC = ("refl", "trans", "card", "step")


def _collect():
    decls = mod.collect()
    df = mod.document_frequency(decls)
    ndf = mod.name_frequency(decls)
    return decls, mod.find_duplicates(decls, mod.DEFAULT_DF_MAX, mod.DEFAULT_CONTAINMENT,
                                      df=df, ndf=ndf)


def _strong(pairs):
    return [p for p in pairs if p["strength"] == "forte"]


def test_population_mesuree():
    """La population exclut les freres `_en` et le Lean vendu."""
    decls = mod.collect()
    assert len(decls) > 1000, "population suspicieusement vide : %d" % len(decls)
    assert not [d for d in decls if d.path.endswith("_en.lean")], "freres _en exclus"
    assert not [d for d in decls if ".lake/" in d.path], "Lean vendu exclu"


def test_unite_tokens_de_nom():
    """Le namespace est retire, le camelCase est decoupe."""
    assert mod.raw_name_tokens("Arrow.arrow") == frozenset({"arrow"})
    assert mod.raw_name_tokens("arrow_impossibility") == frozenset(
        {"arrow", "impossibility"}
    )
    assert mod.raw_name_tokens("sen_impossibility") == frozenset(
        {"sen", "impossibility"}
    )
    assert mod.raw_name_tokens("Redraws.wf") == frozenset({"wf"})


def test_contenance_reconnait_le_prefixe():
    """La contenance rapproche `arrow` de `arrow_impossibility` (Jaccard non)."""
    a = mod.raw_name_tokens("arrow")
    b = mod.raw_name_tokens("arrow_impossibility")
    assert mod.containment(a, b) == 1.0
    assert mod.jaccard(a, b) < 0.6


def test_controle_positif_arrow_et_sen():
    """CONTROLE POSITIF OBLIGATOIRE : il doit trouver Arrow et Sen."""
    _decls, pairs = _collect()
    strong = _strong(pairs)
    for lake_a, name_a, lake_b, name_b in (ARROW, SEN):
        hit = [
            p
            for p in strong
            if {p["a"]["lake"], p["b"]["lake"]} == {lake_a, lake_b}
            and {p["name"], p["other_name"]} == {name_a, name_b}
        ]
        assert hit, (
            "controle positif rate : %s / %s absent des paires fortes"
            " (%d forte(s) trouvee(s))" % (name_a, name_b, len(strong))
        )


def test_controle_negatif_lemmes_generiques():
    """Les lemmes generiques ne doivent pas etre des paires fortes."""
    _decls, pairs = _collect()
    strong = _strong(pairs)
    for p in strong:
        for token in GENERIC:
            assert token not in p["shared_terms"], (
                "faux positif : terme generique %r dans une paire forte (%s / %s)"
                % (token, p["name"], p["other_name"])
            )


def test_le_monomere_ne_produit_pas_de_paire():
    """Une declaration isolee ne peut pas former de paire."""
    decls = [
        mod.Declaration(
            path="a.lean",
            lake="lake_a",
            name="arrow",
            kind="theorem",
            line=1,
            statement="x = x",
            doc="Une fleche de Theil.",
        )
    ]
    for d in decls:
        d.name_tokens = mod.raw_name_tokens(d.name)
        d.doc_tokens = mod.doc_tokens(d.doc)
        d.doc_words = mod.doc_words(d.doc)
        d.stmt_tokens = mod.stmt_tokens(d.statement)
        d.signature = frozenset(
            t for t in d.name_tokens if t in d.doc_words
        )
    pairs = mod.find_duplicates(decls)
    assert pairs == []


def test_page_generee_suivant_l_arbre():
    """`--check` passe sur la page commitee (pas de derive)."""
    assert mod.PAGE.is_file(), "page absente : %s" % mod.PAGE
    decls = mod.collect()
    df = mod.document_frequency(decls)
    ndf = mod.name_frequency(decls)
    pairs = mod.find_duplicates(decls, mod.DEFAULT_DF_MAX, mod.DEFAULT_CONTAINMENT,
                                df=df, ndf=ndf)
    expected = mod.render_page(pairs, mod.DEFAULT_DF_MAX, mod.DEFAULT_CONTAINMENT)
    current = mod.PAGE.read_text(encoding="utf-8")
    assert current == expected, "la page regeneree differe de l'arbre"


def main() -> int:
    failures = []
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for test in tests:
        try:
            test()
        except AssertionError as exc:
            failures.append((test.__name__, str(exc)))
            print("ECHEC %s : %s" % (test.__name__, exc))
        else:
            print("OK    %s" % test.__name__)
    print("")
    print("%d/%d tests passent." % (len(tests) - len(failures), len(tests)))
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
