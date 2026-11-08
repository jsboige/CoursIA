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

import contextlib
import importlib.util
import io
import pathlib
import re
import sys
import tempfile
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
# Le lac A suit la descente #24183 (#25262) : Arrow/Sen vivent dans le lac
# autonome social_choice_core_lean, plus dans game_theory_lean.
ARROW = (
    "MyIA.AI.Notebooks/GameTheory/SocialChoice/social_choice_core_lean",
    "arrow",
    "MyIA.AI.Notebooks/GameTheory/lean_game_defs",
    "arrow_impossibility",
)
SEN = (
    "MyIA.AI.Notebooks/GameTheory/SocialChoice/social_choice_core_lean",
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


def test_la_page_ne_cite_aucun_numero_de_ligne():
    """La page derivee est **independante des numeros de ligne**.

    C'est l'invariant qui rend la page stable : un `git mv` ou une insertion
    dans un `.lean` decale toutes les lignes qui suivent, et la page
    derivait alors pour une PR qui n'avait rien a voir avec elle. La page
    cite le **fichier** et le **nom de la declaration** -- les deux perdurent
    quand la ligne bouge.

    Le predicat de DERIVE (la page suit-elle l'arbre ?) n'est plus verifie
    ici : il est porte par le garde dedie
    `scripts/lean/check_lean_derived_pages.py`, cable sur les PRs qui
    touchent l'arbre Lean, les generateurs ou les pages. Le garder dans la
    suite globale rendait ROUGE toute PR de la flotte qui touche `scripts/`
    -- mesure du 2026-11-03 : 22 PRs de la lane `myia-ai-01:CoursIA-2`
    bloquees le meme jour, sans qu'aucune n'ait touche l'arbre Lean. Une
    porte qui accuse une PR d'un defaut qu'elle ne peut pas causer n'est pas
    une porte, c'est un bruit.
    """
    assert mod.PAGE.is_file(), "page absente : %s" % mod.PAGE
    current = mod.PAGE.read_text(encoding="utf-8")
    cites = re.findall(r"\.lean:\d+", current)
    assert not cites, (
        "la page cite des numeros de ligne, qui derivent a chaque commit "
        "Lean : %s" % sorted(set(cites))[:5])


def test_le_nom_du_script_nomme_est_le_fichier_lui_meme():
    """La docstring d'usage et l'en-tete de page nomment le script REEL.

    La reserve de NanoClaw (2026-11-02) portait sur sept occurrences d'un nom
    de script qui n'existait pas : la page commitee etait auto-contradictoire
    et `--check` ne pouvait pas voir sa propre faute (il regenere depuis le
    meme generateur). Le nom vient donc de `Path(__file__).name` ; ce test
    verifie que les deux surfaces nomment ce fichier -- et qu'il existe.
    """
    assert mod.SCRIPT_NAME == Path(mod.__file__).name
    cite = REPO_ROOT / "scripts" / "lean" / mod.SCRIPT_NAME
    assert cite.is_file(), "script absent : %s" % cite

    doc = mod.__doc__ or ""
    noms = set(re.findall(r"scripts/lean/([A-Za-z0-9_]+\.py)", doc))
    assert noms, "la docstring d'usage ne cite aucun script"
    for nom in noms:
        assert nom == mod.SCRIPT_NAME, (
            "la docstring d'usage cite %r, le script s'appelle %r"
            % (nom, mod.SCRIPT_NAME)
        )
        assert (REPO_ROOT / "scripts" / "lean" / nom).is_file()

    page = mod.render_page([], mod.DEFAULT_DF_MAX, mod.DEFAULT_CONTAINMENT)
    entete = page.splitlines()[2]
    assert mod.SCRIPT_NAME in entete, (
        "l'en-tete de page ne nomme pas le script : %r" % entete
    )


def test_write_check_evalue_le_controle():
    """`--write --check` ne peut pas sortir 0 sans avoir compare.

    Avant : le chemin `write` sortait en premier et `--check` n'etait jamais
    evalue -- un enchainement des deux rendait un faux feu vert. Le controle
    porte desormais sur le fichier reellement present sur le disque.
    """
    page_originale = mod.PAGE
    with tempfile.TemporaryDirectory() as tmp:
        page = Path(tmp) / "page.md"
        mod.PAGE = page
        try:
            sortie = io.StringIO()
            with contextlib.redirect_stdout(sortie):
                rc = mod.main(["--write", "--check"])
            assert rc == 0, "l'ecriture puis le controle doivent reussir"
            assert "OK :" in sortie.getvalue(), (
                "le verdict du controle n'a pas ete produit : %r"
                % sortie.getvalue()
            )

            # Ecriture qui n'atterrit pas (simulee) : la page reste perimee,
            # et le controle doit echouer plutot que de rendre un feu vert.
            page.write_text("contenu perime\n", encoding="utf-8")
            ecrire = pathlib.Path.write_text

            def ecriture_sans_effet(self, data, *args, **kwargs):
                return len(data)

            pathlib.Path.write_text = ecriture_sans_effet
            try:
                with contextlib.redirect_stdout(io.StringIO()):
                    rc = mod.main(["--write", "--check"])
            finally:
                pathlib.Path.write_text = ecrire
            assert rc == 1, (
                "une page non ecrite doit etre detectee par --check, "
                "y compris avec --write (rc=%s)" % rc
            )
        finally:
            mod.PAGE = page_originale


def test_docstring_attachee_derriere_un_attribut():
    """Un attribut sur SA ligne ne doit pas faire perdre la docstring.

    Mesure du 2026-11-02 sur le corpus : 16 declarations sur 4 640 perdaient
    leur docstring derriere un attribut, un commentaire ou un modificateur --
    et sortaient donc de toute paire possible, sans trace.
    """
    source = (
        "/-- Une fleche de Theil. -/\n"
        "@[simp]\n"
        "theorem arrow (f : SWF) : True := by trivial\n"
    )
    decls = mod.parse_file("a.lean", source, "lake_a")
    assert len(decls) == 1
    assert "Theil" in decls[0].doc, (
        "la docstring a ete perdue derriere l'attribut : %r" % decls[0].doc
    )


def test_docstring_non_attachee_a_travers_une_autre_declaration():
    """Une docstring ne traverse pas une declaration intermediaire.

    La regle tolérante ne doit pas rattacher a une declaration le texte
    d'une docstring qui appartient deja a une autre commande.
    """
    source = (
        "/-- Doc de foo. -/\n"
        "theorem foo : True := by trivial\n"
        "/-- Doc de bar. -/\n"
        "theorem bar : True := by trivial\n"
    )
    decls = mod.parse_file("a.lean", source, "lake_a")
    par_nom = {d.name: d for d in decls}
    assert "Doc de foo" in par_nom["foo"].doc
    assert "Doc de bar" in par_nom["bar"].doc
    assert "Doc de foo" not in par_nom["bar"].doc


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
