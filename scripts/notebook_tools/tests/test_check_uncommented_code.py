"""Tests de check_uncommented_code.py — « code non commente » (#26690).

Le defaut fondeur est une demande user, verbatim, en commentaire de PR le
2026-11-15 : « le code est non commente et tres difficile a lire. Le CI
devrait le rejeter sur ces deux bases » (#26607) et « il nous faut un organe
contre ca » (#26616).

Ce que ces tests protegent, dans l'ordre d'importance :

1. **le faux positif** — le user le nomme lui-meme : du code mathematique
   court et lisible n'a pas besoin de commentaires. Une cellule courte, un
   bloc d'imports ou un stub d'exercice (C.1) ne doivent JAMAIS sortir ;
2. **la langue** — le cens du corpus a mesure qu'un comptage `#` uniforme
   signalait 2703 cellules C# sur 4092, alors que le C# ne commente pas
   avec `#`. Le compteur suit le noyau, et les deux pieges symetriques sont
   testes : `#` dans une chaine Python, `//` dans une URL C# ;
3. **le bornage** — une cellule inchangee par la PR n'est pas re-jugee,
   sinon cabler l'organe rougit les ~950 carnets de `main` au lieu de tenir
   la ligne sur ce que la PR touche. Le bornage couvre le renommage
   (#26690) : un carnet renomme sans changement de contenu n'est pas neuf,
   sa base se lit a l'ancien chemin.

Les tests portent sur la logique pure (`analyse_cell`, `analyse_notebook`,
`changed_keys`, `_parse_rename_status`, `renamed_notebooks`, `compare`) :
git est simule par monkeypatch, aucun sous-processus reel, pas de noyau.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import check_uncommented_code as organ


def _cell(*lines: str) -> dict:
    return {
        "cell_type": "code",
        "source": [line + "\n" for line in lines],
        "metadata": {},
        "execution_count": 1,
        "outputs": [],
    }


def _markdown(*lines: str) -> dict:
    return {"cell_type": "markdown", "source": [line + "\n" for line in lines],
            "metadata": {}}


def _notebook(*cells: dict, language: str = "python") -> dict:
    return {
        "cells": list(cells),
        "metadata": {"kernelspec": {"language": language, "name": "x"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


#: 11 lignes de code (la ligne vide ne compte pas).
BODY_12 = (
    "def cout_total(commandes, prix, taxes):",
    "    total = 0.0",
    "    for commande in commandes:",
    "        ligne = commande['quantite'] * prix[commande['article']]",
    "        total = total + ligne",
    "    total = total * (1.0 + taxes)",
    "    return round(total, 2)",
    "",
    "resultat = cout_total(commandes, prix, 0.2)",
    "assert resultat > 0",
    "print(resultat)",
    "print(cout_total([], prix, 0.2))",
)

BODY_11_LINES = 11


# --------------------------------------------------------------------------
# 1. Le defaut, et le seuil qui l'attrape
# --------------------------------------------------------------------------

def test_cellule_longue_sans_commentaire_est_signalee():
    finding = organ.analyse_cell(_cell(*BODY_12))
    assert finding is not None
    assert finding["code_lines"] == BODY_11_LINES
    assert finding["comments"] == 0
    assert finding["counter"] == "python"


def test_un_seul_commentaire_suffit_a_taire_le_finding():
    assert organ.analyse_cell(
        _cell("# Cout total, taxes incluses.", *BODY_12)) is None


def test_cellule_courte_non_jugee():
    # Trois lignes de maths n'ont pas besoin d'un commentaire (verbatim user).
    assert organ.analyse_cell(_cell("a = 1", "b = 2", "print(a + b)")) is None


def test_seuil_de_longueur_est_inclusif():
    court = tuple("x%d = %d" % (i, i) for i in range(organ.MIN_CODE_LINES - 1))
    assert organ.analyse_cell(_cell(*court)) is None
    juste = tuple("x%d = %d" % (i, i) for i in range(organ.MIN_CODE_LINES))
    assert organ.analyse_cell(_cell(*juste)) is not None


# --------------------------------------------------------------------------
# 2. Les exemptions declarees
# --------------------------------------------------------------------------

def test_bloc_d_imports_non_juge():
    imports = tuple("import module_%d" % i for i in range(10))
    assert organ.analyse_cell(_cell(*imports)) is None


def test_docstring_exempte_une_cellule_courte():
    documented = ('"""Somme des recompenses actualisees."""',) + BODY_12[:7]
    assert organ.analyse_cell(_cell(*documented)) is None


def test_docstring_seule_ne_suffit_pas_sur_une_cellule_longue():
    long_cell = ('"""Une seule docstring."""',) + BODY_12
    while sum(1 for line in long_cell if organ._line_kind(line) == "code") \
            < organ.LONG_CELL_LINES:
        long_cell = long_cell + ("print(total)",)
    finding = organ.analyse_cell(_cell(*long_cell))
    assert finding is not None
    assert finding["has_docstring"] is True


def test_stub_d_exercice_exempte():
    stub = ("# TODO etudiant : completer le calcul", "resultat = None") + BODY_12
    assert organ.analyse_cell(_cell(*stub)) is None


def test_marqueur_de_stub_dans_une_chaine_n_exempte_pas():
    # Reserve #26694 : « voir # Etape 3 » dans une chaine n'est pas un stub.
    # Le substring sur la source entiere exemptait a tort la cellule ; le
    # marqueur ne compte plus que sur une ligne classee commentaire.
    cell = _cell('print("voir # Etape 3 du carnet compagnon")', *BODY_12)
    assert organ.analyse_cell(cell) is not None


def test_marqueur_indice_exempte():
    indice = ("# Indice : pensez a la formule de la somme",) + BODY_12
    assert organ.analyse_cell(_cell(*indice)) is None


# --------------------------------------------------------------------------
# 3. Le tokenizer : un '#' dans une chaine n'est pas un commentaire
# --------------------------------------------------------------------------

def test_diese_dans_une_chaine_ne_compte_pas_comme_commentaire():
    cell = _cell('COULEUR = "#ffffff"', "MOTIF = 'a#b'", *BODY_12)
    finding = organ.analyse_cell(cell)
    assert finding is not None, "un '#' de chaine ne doit pas blanchir la cellule"
    assert finding["comments"] == 0


def test_commentaire_reel_compte():
    cell = _cell("# Vraie explication", *BODY_12)
    assert organ.analyse_cell(cell) is None


def test_cellule_illisible_leve_le_drapeau_de_repli():
    # Parenthese non fermee : le tokenizer echoue. On ne rend pas zero en
    # silence, on rend un finding marque `fallback`.
    cell = _cell("a = 1", "b = 2", "c = a + b", "d = c * 2", "e = d - 1",
                 "f = e / 2", "g = f ** 2", "h = g + a", "total = h + (")
    finding = organ.analyse_cell(cell)
    assert finding is not None
    assert finding["counter"] == "fallback"


# --------------------------------------------------------------------------
# 4. La langue : le C# ne commente pas avec '#'
# --------------------------------------------------------------------------

CS_BODY = (
    "var total = 0.0;",
    "foreach (var c in commandes)",
    "{",
    "    total += c.Quantite * prix[c.Article];",
    "}",
    "total *= 1.0 + taxes;",
    "Console.WriteLine(Math.Round(total, 2));",
    "Console.WriteLine(total);",
    "Console.WriteLine(commandes.Count);",
)


def test_cellule_csharp_commentee_par_slash_slash_non_signalee():
    assert organ.analyse_cell(
        _cell("// Cout total, taxes incluses.", *CS_BODY), language="C#") is None


def test_cellule_csharp_sans_commentaire_signalee():
    finding = organ.analyse_cell(_cell(*CS_BODY), language="C#")
    assert finding is not None
    assert finding["counter"] == "csharp"


def test_url_dans_une_chaine_csharp_ne_compte_pas_comme_commentaire():
    # Piege miroir du '#' dans une chaine : sans masquage, cette cellule
    # serait blanchee par le '//' de l'URL.
    cell = _cell('var api = "https://api.exemple.fr/v1";', *CS_BODY)
    finding = organ.analyse_cell(cell, language="C#")
    assert finding is not None
    assert finding["comments"] == 0


def test_commentaire_bloc_csharp_compte():
    cell = _cell("/* Cout total taxes incluses */", *CS_BODY)
    assert organ.analyse_cell(cell, language="C#") is None


def test_langue_lue_dans_les_metadonnees_du_carnet():
    nb = _notebook(_cell(*CS_BODY), language="C#")
    findings = organ.analyse_notebook(nb)
    assert len(findings) == 1
    assert findings[0]["counter"] == "csharp"


# --------------------------------------------------------------------------
# 5. La langue : le Lean commente avec '--'
# --------------------------------------------------------------------------

LEAN_BODY = (
    "theorem deux_plus_deux : (2 : Nat) + 2 = 4 := by",
    "  norm_num",
    "  ring",
    "  omega",
    "  simp",
    "  rfl",
    "  decide",
    "  native_decide",
    "  trivial",
)


def test_cellule_lean_commentee_non_signalee():
    assert organ.analyse_cell(
        _cell("-- Une preuve tres simple.", *LEAN_BODY), language="lean4") is None


def test_cellule_lean_sans_commentaire_signalee():
    finding = organ.analyse_cell(_cell(*LEAN_BODY), language="lean4")
    assert finding is not None
    assert finding["counter"] == "lean"


# --------------------------------------------------------------------------
# 5 bis. La langue : le Rust (noyau evcxr) commente avec '//'
# --------------------------------------------------------------------------

RUST_BODY = (
    "fn somme<'a>(v: &'a [i64]) -> i64 {",
    "    let mut total = 0;",
    "    for x in v.iter() {",
    "        total += x;",
    "    }",
    "    total",
    "}",
    "let v = vec![1, 2, 3];",
    'println!("{}", somme(&v));',
)


def test_cellule_rust_commentee_par_slash_slash_non_signalee():
    # Avant la famille rust, le tokenizer Python lisait '//' comme un
    # operateur et comptait 0 commentaire sur cette cellule.
    assert organ.analyse_cell(
        _cell("// Somme des elements.", *RUST_BODY), language="rust") is None


def test_cellule_rust_sans_commentaire_signalee():
    finding = organ.analyse_cell(_cell(*RUST_BODY), language="rust")
    assert finding is not None
    assert finding["counter"] == "rust"


def test_url_dans_une_chaine_rust_ne_compte_pas_comme_commentaire():
    for line in ('let api = "https://api.exemple.fr/v1";',
                 'let api = r#"https://api.exemple.fr/"v1""#;',
                 "let barre = '/'; let api = \"http://x\";"):
        finding = organ.analyse_cell(_cell(line, *RUST_BODY), language="rust")
        assert finding is not None, line
        assert finding["comments"] == 0, line


def test_commentaire_bloc_rust_compte():
    cell = _cell("/* Somme des elements */", *RUST_BODY)
    assert organ.analyse_cell(cell, language="rust") is None


def test_duree_de_vie_ne_masque_pas_un_commentaire_rust():
    # Deux durees de vie sur une ligne ne forment pas un caractere : le
    # commentaire qui les suit reste visible.
    cell = _cell("fn f<'a, 'b>(x: &'a str) {} // deux durees de vie",
                 *RUST_BODY)
    assert organ.analyse_cell(cell, language="rust") is None


# --------------------------------------------------------------------------
# 6. Le bornage au diff
# --------------------------------------------------------------------------

def test_cellule_inchangee_hors_jugement():
    base = _notebook(_cell(*BODY_12))
    head = _notebook(_cell(*BODY_12), _cell("x = 1"))
    keys = organ.changed_keys(base, head)
    assert keys is not None
    assert organ.analyse_notebook(head, only_keys=keys) == []


def test_cellule_modifiee_jugee():
    base = _notebook(_cell(*BODY_12))
    head = _notebook(_cell(*(BODY_12 + ("print(1)",))))
    keys = organ.changed_keys(base, head)
    findings = organ.analyse_notebook(head, only_keys=keys)
    assert len(findings) == 1


def test_carnet_neuf_juge_entierement():
    head = _notebook(_cell(*BODY_12))
    assert organ.changed_keys(None, head) is None
    assert len(organ.analyse_notebook(head, only_keys=None)) == 1


def test_markdown_jamais_juge():
    head = _notebook(_markdown(*BODY_12))
    assert organ.analyse_notebook(head) == []


# --------------------------------------------------------------------------
# 7. Interface : self-test et code de sortie
# --------------------------------------------------------------------------

def test_self_test_integre():
    assert organ.self_test() == 0


def test_code_de_sortie_1_sur_un_carnet_fautif(tmp_path):
    path = tmp_path / "fautif.ipynb"
    path.write_text(json.dumps(_notebook(_cell(*BODY_12))), encoding="utf-8")
    assert organ.main(["--file", str(path)]) == 1


def test_code_de_sortie_0_sur_un_carnet_sain(tmp_path):
    path = tmp_path / "sain.ipynb"
    path.write_text(json.dumps(_notebook(_cell("# explique", *BODY_12))),
                    encoding="utf-8")
    assert organ.main(["--file", str(path)]) == 0


def test_sortie_json_est_lisible(tmp_path, capsys):
    path = tmp_path / "fautif.ipynb"
    path.write_text(json.dumps(_notebook(_cell(*BODY_12))), encoding="utf-8")
    organ.main(["--file", str(path), "--json"])
    payload = json.loads(capsys.readouterr().out)
    assert payload["flagged_cells"] == 1
    assert payload["rows"][0]["cells"][0]["code_lines"] == BODY_11_LINES


# --------------------------------------------------------------------------
# 8. Le renommage : la base se lit a l'ancien chemin (#26690, correctif
#    #26837 -- ces tests pytests doublent le self-test integre)
# --------------------------------------------------------------------------

def test_table_de_renommage_lit_toutes_les_lignes_R(monkeypatch):
    # R100 = renommage pur, R075 = renommage remanie (toujours un renommage
    # tant que la similarite passe le seuil -M). A/M/D sont ignores.
    out = "\n".join([
        "R100\tancien/Avant.ipynb\tnouveau/Apres.ipynb",
        "A\tnouveau/Neuf.ipynb",
        "M\tmodifie/Notebook.ipynb",
        "D\tdisparu/Vieux.ipynb",
        "R075\tsrc/Old.ipynb\tdst/New.ipynb",
        "",
    ])
    monkeypatch.setattr(organ.check_output_failure_text, "git",
                        lambda *args, **kwargs: out)
    monkeypatch.setattr(
        organ, "renamed_notebooks",
        lambda *args, **kwargs: organ.check_output_failure_text.renamed_notebooks(
            *args, **kwargs),
    )
    assert organ.renamed_notebooks("base") == {
        "nouveau/Apres.ipynb": "ancien/Avant.ipynb",
        "dst/New.ipynb": "src/Old.ipynb",
    }


def test_table_de_renommage_normalise_les_antislashs(monkeypatch):
    # git sous Windows rend des chemins a antislashs ; l'organe partage les
    # normalise avant de construire la table nouveau->ancien.
    out = ("R100\tancien" + organ.check_output_failure_text.BS + "Avant.ipynb\tnouveau"
           + organ.check_output_failure_text.BS + "Apres.ipynb")
    monkeypatch.setattr(organ.check_output_failure_text, "git",
                        lambda *args, **kwargs: out)
    monkeypatch.setattr(
        organ, "renamed_notebooks",
        lambda *args, **kwargs: organ.check_output_failure_text.renamed_notebooks(
            *args, **kwargs),
    )
    assert organ.renamed_notebooks("base") == {
        "nouveau/Apres.ipynb": "ancien/Avant.ipynb",
    }


def test_renommage_hors_seuil_absent_de_la_table(monkeypatch):
    # Un renommage lourdement remanie (similarite sous -M) apparait comme
    # une paire D+A, jamais comme R : il sera juge carnet neuf. C'est le
    # sur-signalement assume, jamais un blanchiment.
    out = "D\tancien/Avant.ipynb\nA\tnouveau/Apres.ipynb"
    monkeypatch.setattr(organ.check_output_failure_text, "git",
                        lambda *args, **kwargs: out)
    monkeypatch.setattr(
        organ, "renamed_notebooks",
        lambda *args, **kwargs: organ.check_output_failure_text.renamed_notebooks(
            *args, **kwargs),
    )
    assert organ.renamed_notebooks("base") == {}


def _fake_reader(heads: dict, bases: dict):
    """read_notebook_at simule : heads = contenu HEAD par chemin (ref None),
    bases = contenu de la base par chemin (toute autre ref)."""
    def read(ref, path, cwd=None):
        if ref is None:
            return heads.get(path)
        return bases.get(path)
    return read


def test_renommage_pur_sans_changement_pas_de_finding(monkeypatch):
    # Le defaut fondeur de #26690 : lire la base au NOUVEAU chemin rend
    # None, et le carnet renomme etait juge en entier comme neuf. La base
    # doit etre relue a l'ANCIEN chemin.
    content = _notebook(_cell(*BODY_12), _cell("x = 1"))
    monkeypatch.setattr(organ, "read_notebook_at", _fake_reader(
        heads={"nouveau/Apres.ipynb": content},
        bases={"ancien/Avant.ipynb": content},  # rien au nouveau chemin
    ))
    renames = {"nouveau/Apres.ipynb": "ancien/Avant.ipynb"}
    rows = organ.compare("BASE", ["nouveau/Apres.ipynb"], renames=renames)
    assert rows == []


def test_renommage_avec_cellule_modifiee_borne_au_changement(monkeypatch):
    head = _notebook(_cell(*BODY_12), _cell("x = 1"))
    base = _notebook(_cell("# explique, taxes incluses", *BODY_12), _cell("x = 1"))
    monkeypatch.setattr(organ, "read_notebook_at", _fake_reader(
        heads={"nouveau/Apres.ipynb": head},
        bases={"ancien/Avant.ipynb": base},
    ))
    rows = organ.compare("BASE", ["nouveau/Apres.ipynb"],
                         renames={"nouveau/Apres.ipynb": "ancien/Avant.ipynb"})
    assert len(rows) == 1
    assert rows[0]["new_notebook"] is False  # la base a ete trouvee
    assert len(rows[0]["cells"]) == 1         # seule la cellule modifiee


def test_renomme_vers_chemin_exclu_sort_du_perimetre(monkeypatch):
    # Un carnet renomme vers un chemin exclu (_output, archive...) n'est pas
    # juge : le filtre porte sur le chemin NOUVEAU (renamed_notebooks).
    out = "R100\tsrc/Ok.ipynb\tdst/_output/Ok.ipynb\nR100\tsrc/A.ipynb\tdst/A.ipynb"
    monkeypatch.setattr(organ.check_output_failure_text, "git",
                        lambda *a, **k: out)
    monkeypatch.setattr(
        organ, "renamed_notebooks",
        lambda *args, **kwargs: organ.check_output_failure_text.renamed_notebooks(
            *args, **kwargs),
    )
    assert organ.renamed_notebooks("BASE") == {
        "dst/A.ipynb": "src/A.ipynb",
    }


def test_vrai_carnet_neuf_reste_juge_en_entier(monkeypatch):
    # Sans renommage et sans base au chemin, le carnet reste neuf : la
    # correction ne doit jamais blanchir un vrai nouveau carnet.
    monkeypatch.setattr(organ, "read_notebook_at", _fake_reader(
        heads={"nouveau/Neuf.ipynb": _notebook(_cell(*BODY_12))},
        bases={},
    ))
    rows = organ.compare("BASE", ["nouveau/Neuf.ipynb"], renames={})
    assert len(rows) == 1
    assert rows[0]["new_notebook"] is True
    assert len(rows[0]["cells"]) == 1