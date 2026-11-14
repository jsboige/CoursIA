"""Tests pour scripts/notebook_tools/check_subseries_descent.py.

Couverture exigee : une sous-serie finie, un test par slug de ``manques``,
la resolution de liens (relatif, ./, fragment, %20, ../, http ignore, href),
source de cellule liste ou chaine, exclusions (_output, checkpoints, _archive,
dossier sans carnets), tete/accretions en comparaison entiere, chaine de
ledger, plafond des traductions, metadata papermill informative, tri naturel
du dernier carnet, carnets illisibles, codes de sortie de ``main``, capstone
(en racine, en sous-serie soeur, nom sans lien, lien sans nom, couverture en
carnets distincts) et option ``--exclude``.
"""
from __future__ import annotations

import importlib.util
import json
import os
from pathlib import Path

HERE = Path(__file__).resolve()
SCRIPT = HERE.parents[1] / "check_subseries_descent.py"
spec = importlib.util.spec_from_file_location("check_subseries_descent", SCRIPT)
check = importlib.util.module_from_spec(spec)
assert spec.loader
spec.loader.exec_module(check)

SUB_REL = "MyIA.AI.Notebooks/Test/S-01-Topic"
CAPSTONE = "S-02-Capstone-Sujet.ipynb"


# ---------------------------------------------------------------------------
# Aides de construction
# ---------------------------------------------------------------------------

def _write_nb(
    path: Path,
    md_blocks: list[str] | None = None,
    metadata: dict | None = None,
    as_list: bool = True,
) -> None:
    """Ecrit un notebook minimal ; source markdown en liste ou en chaine."""
    path.parent.mkdir(parents=True, exist_ok=True)
    cells = []
    if md_blocks:
        if as_list:
            source: list[str] | str = [b + "\n" for b in md_blocks]
        else:
            source = "\n".join(md_blocks)
        cells.append({"cell_type": "markdown", "metadata": {}, "source": source})
    cells.append(
        {
            "cell_type": "code",
            "metadata": {},
            "source": ["print('x')\n"],
            "outputs": [],
            "execution_count": 1,
        }
    )
    nb = {
        "cells": cells,
        "metadata": metadata if metadata is not None else {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb), encoding="utf-8")


def _write_md(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _build_finished(tmp_path: Path, sub_name: str = "S-01-Topic") -> tuple[Path, Path]:
    """Arbre complet : une sous-serie finie, aucune dimension manquante."""
    root = tmp_path / "MyIA.AI.Notebooks" / "Test"
    sub = root / sub_name
    sub.mkdir(parents=True)
    _write_md(root / "README.md", "[Sujet](%s/README.md)\n" % sub_name)
    _write_nb(
        root / "S-01-Alpha.ipynb",
        md_blocks=["[Descend](%s/S-01-a.ipynb)" % sub_name],
    )
    _write_nb(
        root / CAPSTONE,
        md_blocks=[
            "[a](%s/S-01-a.ipynb)" % sub_name,
            "[b](%s/S-01-b.ipynb)" % sub_name,
        ],
    )
    _write_md(sub / "README.md", "# Sujet\n")
    _write_nb(sub / "S-01-a.ipynb")
    _write_nb(sub / "S-01-b.ipynb")
    _write_nb(sub / "S-01-c.ipynb", md_blocks=["[Retour](../README.md)"])
    return root, sub


def _measure(root: Path, tmp_path: Path, ledger_rows=None, translation_lines=None):
    return check.measure_root(
        root,
        tmp_path,
        ledger_rows if ledger_rows is not None else [],
        translation_lines if translation_lines is not None else {},
    )


def _only_sub(data: dict) -> dict:
    assert len(data["sous_series"]) == 1
    return data["sous_series"][0]


def _sub_named(data: dict, name: str) -> dict:
    found = [ss for ss in data["sous_series"] if ss["nom"] == name]
    assert len(found) == 1
    return found[0]


# ---------------------------------------------------------------------------
# Resolution de liens
# ---------------------------------------------------------------------------

class TestExtractLinks:

    def test_relative_and_dotslash(self, tmp_path):
        base = tmp_path / "Root"
        base.mkdir()
        got = check.extract_links("[x](Sub/x.ipynb) [y](./Sub/x.ipynb)", base)
        want = [os.path.normpath(str(base / "Sub" / "x.ipynb"))] * 2
        assert got == want

    def test_fragment_and_query_stripped(self, tmp_path):
        base = tmp_path / "Root"
        base.mkdir()
        got = check.extract_links("[x](Sub/x.ipynb#ancre) [y](Sub/x.ipynb?q=1)", base)
        want = [os.path.normpath(str(base / "Sub" / "x.ipynb"))] * 2
        assert got == want

    def test_url_encoded_target(self, tmp_path):
        base = tmp_path / "Root"
        base.mkdir()
        got = check.extract_links("[x](Mon%20car.ipynb)", base)
        want = [os.path.normpath(str(base / "Mon car.ipynb"))]
        assert got == want

    def test_parent_relative(self, tmp_path):
        base = tmp_path / "A" / "B"
        base.mkdir(parents=True)
        got = check.extract_links("[x](../Root/Sub/x.ipynb)", base)
        want = [os.path.normpath(str(tmp_path / "A" / "Root" / "Sub" / "x.ipynb"))]
        assert got == want

    def test_remote_and_anchor_ignored(self, tmp_path):
        base = tmp_path / "Root"
        base.mkdir()
        got = check.extract_links(
            "[a](https://example.com/a.ipynb) [b](http://example.com/b.ipynb)"
            " [c](mailto:a@b.cd) [d](#ancre) [e](x.ipynb)",
            base,
        )
        assert got == [os.path.normpath(str(base / "x.ipynb"))]

    def test_href_form(self, tmp_path):
        base = tmp_path / "Root"
        base.mkdir()
        got = check.extract_links('<a href="Sub/README.md">y</a>', base)
        want = [os.path.normpath(str(base / "Sub" / "README.md"))]
        assert got == want

    def test_title_form(self, tmp_path):
        base = tmp_path / "Root"
        base.mkdir()
        got = check.extract_links('[x](Sub/x.ipynb "Titre")', base)
        want = [os.path.normpath(str(base / "Sub" / "x.ipynb"))]
        assert got == want

    def test_source_list_and_string_equivalent(self):
        nb_list = {
            "cells": [
                {"cell_type": "markdown", "source": ["[a](x.ipynb)", "\n"]},
                {"cell_type": "code", "source": ["print(1)"]},
                {"cell_type": "markdown", "source": "[b](y.ipynb)\n"},
            ]
        }
        nb_str = {
            "cells": [
                {"cell_type": "markdown", "source": "[a](x.ipynb)\n[b](y.ipynb)\n"},
            ]
        }
        base = Path("/base")
        links_from_list = check.extract_links(check.notebook_markdown(nb_list), base)
        links_from_str = check.extract_links(check.notebook_markdown(nb_str), base)
        assert links_from_list == links_from_str
        assert len(links_from_list) == 2


# ---------------------------------------------------------------------------
# Decouverte : exclusions
# ---------------------------------------------------------------------------

class TestListing:

    def test_output_suffix_and_checkpoints_ignored(self, tmp_path):
        root = tmp_path / "MyIA.AI.Notebooks" / "Test"
        sub = root / "S-01-Topic"
        sub.mkdir(parents=True)
        _write_md(root / "README.md", "[x](S-01-Topic/README.md)\n")
        _write_nb(root / "S-01-Alpha.ipynb", md_blocks=["[d](S-01-Topic/S-01-a.ipynb)"])
        _write_md(sub / "README.md", "#\n")
        _write_nb(sub / "S-01-a.ipynb", md_blocks=["[r](../README.md)"])
        _write_nb(sub / "S-01-b_output.ipynb", md_blocks=["[r](../README.md)"])
        _write_nb(sub / ".ipynb_checkpoints" / "S-01-c.ipynb")
        _write_nb(root / "S-01-Zzz_output.ipynb")
        data, _ = _measure(root, tmp_path)
        ss = _only_sub(data)
        assert ss["carnets"] == 1
        assert data["racine_carnets"] == 1

    def test_archive_and_empty_dirs_not_subseries(self, tmp_path):
        root = tmp_path / "MyIA.AI.Notebooks" / "Test"
        root.mkdir(parents=True)
        _write_md(root / "README.md", "#\n")
        _write_nb(root / "S-01-Alpha.ipynb")
        _write_nb(root / "_archive" / "S-01-vieux.ipynb")
        (root / "assets").mkdir()
        _write_md(root / "assets" / "img.png", "png")
        data, _ = _measure(root, tmp_path)
        assert data["sous_series"] == []
        assert data["total"] == 0


# ---------------------------------------------------------------------------
# Etat fini et slugs de manques
# ---------------------------------------------------------------------------

class TestFinie:

    def test_fully_finished(self, tmp_path):
        root, _sub = _build_finished(tmp_path)
        data, illisibles = _measure(root, tmp_path)
        ss = _only_sub(data)
        assert ss["manques"] == []
        assert ss["finie"] is True
        assert ss["carnets"] == 3
        assert ss["readme"] is True
        assert ss["marche"] == 1
        assert ss["descente"] == ["S-01-Alpha.ipynb", CAPSTONE]
        assert ss["remontee_dernier"] is True
        assert ss["remontee_total"] == 1
        assert ss["capstones"] == [{"carnet": CAPSTONE, "couverture": 2}]
        assert ss["consommateur_max"] == {"carnet": CAPSTONE, "couverture": 2}
        assert illisibles == []
        assert data["finies"] == 1
        assert data["total"] == 1
        assert data["readme_racine"] is True


class TestManqueSlugs:

    def test_manque_readme(self, tmp_path):
        root, sub = _build_finished(tmp_path)
        (sub / "README.md").unlink()
        ss = _only_sub(_measure(root, tmp_path)[0])
        assert ss["manques"] == ["readme"]
        assert ss["finie"] is False

    def test_manque_nom_nu(self, tmp_path):
        root, _sub = _build_finished(tmp_path, sub_name="S-01")
        ss = _only_sub(_measure(root, tmp_path)[0])
        assert ss["nom_nu"] is True
        assert ss["manques"] == ["nom-nu"]

    def test_manque_marche(self, tmp_path):
        root, _sub = _build_finished(tmp_path)
        _write_md(root / "README.md", "[Externe](https://example.com)\n")
        ss = _only_sub(_measure(root, tmp_path)[0])
        assert ss["marche"] == 0
        assert ss["manques"] == ["marche"]

    def test_manque_descente(self, tmp_path):
        # Aucun carnet de racine ne descend ; le capstone vit dans une
        # sous-serie soeur (modele #18857), donc seule la descente manque.
        root, _sub = _build_finished(tmp_path)
        _write_nb(root / "S-01-Alpha.ipynb")
        (root / CAPSTONE).unlink()
        other = root / "T-01-Autre"
        _write_md(root / "README.md", "[S](S-01-Topic/README.md) [T](T-01-Autre/README.md)\n")
        _write_md(other / "README.md", "#\n")
        _write_nb(
            other / "T-08-Sujet-Capstone.ipynb",
            md_blocks=[
                "[a](../S-01-Topic/S-01-a.ipynb)",
                "[b](../S-01-Topic/S-01-b.ipynb)",
                "[c](../S-01-Topic/S-01-c.ipynb)",
            ],
        )
        ss = _sub_named(_measure(root, tmp_path)[0], "S-01-Topic")
        assert ss["descente"] == []
        assert ss["capstones"] == [
            {"carnet": "T-01-Autre/T-08-Sujet-Capstone.ipynb", "couverture": 3}
        ]
        assert ss["manques"] == ["descente"]

    def test_manque_capstone_nom_sans_lien(self, tmp_path):
        # Un carnet nomme Capstone qui ne cite aucun carnet de la sous-serie
        # n'en est pas le capstone ; Alpha reste le plus large consommateur.
        root, _sub = _build_finished(tmp_path)
        _write_nb(root / CAPSTONE, md_blocks=["[Index](README.md)"])
        ss = _only_sub(_measure(root, tmp_path)[0])
        assert ss["capstones"] == []
        assert ss["consommateur_max"] == {"carnet": "S-01-Alpha.ipynb", "couverture": 1}
        assert ss["manques"] == ["capstone"]
        assert check._row_cells(ss)[6] == "non (max 1/3)"

    def test_manque_capstone_lien_sans_nom(self, tmp_path):
        # Une synthese qui cite toute la sous-serie sans s'appeler Capstone
        # est rendue comme consommateur_max, pas comme capstone.
        root, _sub = _build_finished(tmp_path)
        (root / CAPSTONE).unlink()
        _write_nb(
            root / "S-03-Synthese.ipynb",
            md_blocks=[
                "[a](S-01-Topic/S-01-a.ipynb)",
                "[b](S-01-Topic/S-01-b.ipynb)",
                "[c](S-01-Topic/S-01-c.ipynb)",
            ],
        )
        ss = _only_sub(_measure(root, tmp_path)[0])
        assert ss["capstones"] == []
        assert ss["consommateur_max"] == {"carnet": "S-03-Synthese.ipynb", "couverture": 3}
        assert ss["manques"] == ["capstone"]

    def test_capstone_interne_ne_compte_pas(self, tmp_path):
        # Un carnet nomme Capstone DANS la sous-serie ne la consomme pas
        # depuis la serie parente.
        root, sub = _build_finished(tmp_path)
        (root / CAPSTONE).unlink()
        _write_nb(
            sub / "S-01-bb-Capstone.ipynb",
            md_blocks=["[a](S-01-a.ipynb)", "[b](S-01-b.ipynb)"],
        )
        ss = _only_sub(_measure(root, tmp_path)[0])
        assert ss["capstones"] == []
        assert "capstone" in ss["manques"]

    def test_couverture_compte_les_carnets_distincts(self, tmp_path):
        root, _sub = _build_finished(tmp_path)
        _write_nb(
            root / CAPSTONE,
            md_blocks=[
                "[a](S-01-Topic/S-01-a.ipynb)",
                "[encore a](./S-01-Topic/S-01-a.ipynb#section)",
                "[readme](S-01-Topic/README.md)",
            ],
        )
        ss = _only_sub(_measure(root, tmp_path)[0])
        assert ss["capstones"] == [{"carnet": CAPSTONE, "couverture": 1}]
        assert ss["manques"] == []

    def test_descente_sans_objet_sans_carnet_de_racine(self, tmp_path):
        # Racine sans numerotation principale : deux familles soeurs, le
        # capstone de l'une vit dans l'autre. La descente n'est pas un manque.
        root = tmp_path / "MyIA.AI.Notebooks" / "Test"
        a, b = root / "Alpha", root / "Beta"
        _write_md(root / "README.md", "[A](Alpha/README.md) [B](Beta/README.md)\n")
        _write_md(a / "README.md", "#\n")
        _write_md(b / "README.md", "#\n")
        _write_nb(a / "Alpha-01-x.ipynb", md_blocks=["[Retour](../README.md)"])
        _write_nb(
            b / "Beta-08-Alpha-Capstone.ipynb",
            md_blocks=["[x](../Alpha/Alpha-01-x.ipynb)", "[Retour](../README.md)"],
        )
        data, _ = _measure(root, tmp_path)
        assert data["racine_carnets"] == 0
        ss = _sub_named(data, "Alpha")
        assert ss["descente"] is None
        assert ss["manques"] == []
        assert check._row_cells(ss)[4] == "n/a"
        # Des qu'un carnet de racine existe sans descendre, le manque revient.
        _write_nb(root / "Test-01-Intro.ipynb")
        ss = _sub_named(_measure(root, tmp_path)[0], "Alpha")
        assert ss["descente"] == []
        assert ss["manques"] == ["descente"]

    def test_manque_remontee(self, tmp_path):
        root, _sub = _build_finished(tmp_path)
        _write_nb(root / "S-01-Topic" / "S-01-c.ipynb")
        ss = _only_sub(_measure(root, tmp_path)[0])
        assert ss["remontee_dernier"] is False
        assert ss["remontee_total"] == 0
        assert ss["manques"] == ["remontee"]

    def test_manque_ledger(self, tmp_path):
        root, sub = _build_finished(tmp_path)
        rows = [
            {
                "ancien": SUB_REL + "/S-01-vieux.ipynb",
                "nouveau": SUB_REL + "/S-01-disparu.ipynb",
            }
        ]
        data, _ = _measure(root, tmp_path, ledger_rows=rows)
        ss = _only_sub(data)
        assert not (sub / "S-01-disparu.ipynb").exists()
        assert ss["ledger_lignes"] == 1
        assert ss["ledger_cibles_disparues"] == [SUB_REL + "/S-01-disparu.ipynb"]
        assert ss["manques"] == ["ledger"]

    def test_manque_traductions(self, tmp_path):
        root, sub = _build_finished(tmp_path)
        # "S-01-bb" tri naturellement avant "S-01-c" : le dernier carnet
        # (celui qui porte la remontee) reste S-01-c.ipynb.
        _write_nb(sub / "S-01-bb.ipynb")
        rows = [
            {
                "ancien": SUB_REL + "/S-01-vieux.ipynb",
                "nouveau": SUB_REL + "/S-01-bb.ipynb",
            }
        ]
        translations = tmp_path / "translations"
        _write_md(translations / "test" / "memoire.csv", "a\nb\nvoir S-01-vieux.ipynb\n")
        lines = check.load_translation_lines(translations)
        data, _ = _measure(root, tmp_path, ledger_rows=rows, translation_lines=lines)
        ss = _only_sub(data)
        assert ss["traductions_perimees"] == ["test/memoire.csv:3"]
        assert ss["traductions_perimees_total"] == 1
        assert ss["manques"] == ["traductions"]


# ---------------------------------------------------------------------------
# Tete et accretions en racine
# ---------------------------------------------------------------------------

class TestTeteAccretions:

    def _build_ict(self, tmp_path: Path) -> Path:
        root = tmp_path / "MyIA.AI.Notebooks" / "ICT-Series"
        sub = root / "ICT-05-Topic"
        sub.mkdir(parents=True)
        _write_md(root / "README.md", "#\n")
        _write_nb(root / "ICT-5-a.ipynb")
        _write_nb(root / "ICT-5b-b.ipynb")
        _write_nb(root / "ICT-50-c.ipynb")
        _write_nb(sub / "ICT-5-x.ipynb")
        return root

    def test_integer_comparison(self, tmp_path):
        root = self._build_ict(tmp_path)
        ss = _only_sub(_measure(root, tmp_path)[0])
        assert ss["tete_racine"] == ["ICT-5-a.ipynb"]
        assert ss["accretions_racine"] == ["ICT-5b-b.ipynb"]
        # ICT-50-c.ipynb n'apparait nulle part (50 != 5)
        assert "ICT-50-c.ipynb" not in (ss["tete_racine"] + ss["accretions_racine"])

    def test_na_for_plain_name(self, tmp_path):
        root = tmp_path / "MyIA.AI.Notebooks" / "GameTheory"
        sub = root / "Dynamics"
        sub.mkdir(parents=True)
        _write_md(root / "README.md", "#\n")
        _write_nb(root / "GameTheory-01-Setup.ipynb")
        _write_nb(sub / "Dynamics-01-x.ipynb")
        ss = _only_sub(_measure(root, tmp_path)[0])
        assert ss["tete_racine"] is None
        assert ss["accretions_racine"] is None
        cells = check._row_cells(ss)
        assert cells[7] == "n/a"


# ---------------------------------------------------------------------------
# Ledger : chaines de renommage
# ---------------------------------------------------------------------------

class TestLedgerChain:

    def test_chained_target_not_reported(self, tmp_path):
        root, sub = _build_finished(tmp_path)
        rows = [
            # Renommage en deux etapes : la cible intermediaire a disparu
            # mais est l'ancien de la ligne suivante -> pas une disparue.
            {
                "ancien": SUB_REL + "/S-01-old1.ipynb",
                "nouveau": SUB_REL + "/S-01-chained.ipynb",
            },
            {
                "ancien": SUB_REL + "/S-01-chained.ipynb",
                "nouveau": SUB_REL + "/S-01-c.ipynb",
            },
            # Vraie disparue : n'est l'ancien d'aucune ligne.
            {
                "ancien": SUB_REL + "/S-01-old2.ipynb",
                "nouveau": SUB_REL + "/S-01-gone.ipynb",
            },
        ]
        ss = _only_sub(_measure(root, tmp_path, ledger_rows=rows)[0])
        assert ss["ledger_lignes"] == 3
        assert ss["ledger_cibles_disparues"] == [SUB_REL + "/S-01-gone.ipynb"]
        assert ss["manques"] == ["ledger"]


# ---------------------------------------------------------------------------
# Traductions : plafond
# ---------------------------------------------------------------------------

class TestTraductionsCap:

    def test_cap_twenty_and_uncapped_total(self, tmp_path):
        root, sub = _build_finished(tmp_path)
        # S-01-bb tri avant S-01-c : la remontee du dernier carnet est intacte.
        _write_nb(sub / "S-01-bb.ipynb")
        rows = [
            {
                "ancien": SUB_REL + "/S-01-vieux.ipynb",
                "nouveau": SUB_REL + "/S-01-bb.ipynb",
            }
        ]
        translations = tmp_path / "translations"
        body = "".join("ligne %d cite S-01-vieux.ipynb\n" % i for i in range(1, 26))
        _write_md(translations / "gros.csv", body)
        lines = check.load_translation_lines(translations)
        ss = _only_sub(_measure(root, tmp_path, ledger_rows=rows, translation_lines=lines)[0])
        assert ss["traductions_perimees_total"] == 25
        assert len(ss["traductions_perimees"]) == 20
        assert ss["traductions_perimees"][0] == "gros.csv:1"
        assert ss["traductions_perimees"][-1] == "gros.csv:20"


# ---------------------------------------------------------------------------
# Metadata papermill : informative seulement
# ---------------------------------------------------------------------------

class TestMetadataAncienNom:

    def test_reported_but_not_in_manques(self, tmp_path):
        root, sub = _build_finished(tmp_path)
        # b cite un ancien nom -> signale ; a cite son propre nom via
        # _output.ipynb (suffixe retire) -> non signale.
        _write_nb(
            sub / "S-01-b.ipynb",
            metadata={
                "papermill": {
                    "input_path": "MyIA.AI.Notebooks/Test/S-01-Topic/S-01-ancien.ipynb"
                }
            },
        )
        _write_nb(
            sub / "S-01-a.ipynb",
            metadata={
                "papermill": {
                    "input_path": "MyIA.AI.Notebooks/Test/S-01-Topic/S-01-a_output.ipynb"
                }
            },
        )
        ss = _only_sub(_measure(root, tmp_path)[0])
        assert ss["metadata_ancien_nom"] == ["S-01-b.ipynb"]
        assert "S-01-a.ipynb" not in ss["metadata_ancien_nom"]
        assert ss["manques"] == []
        assert ss["finie"] is True


# ---------------------------------------------------------------------------
# Tri naturel du dernier carnet
# ---------------------------------------------------------------------------

class TestNaturalLast:

    def test_string_sort_would_disagree(self, tmp_path):
        root = tmp_path / "MyIA.AI.Notebooks" / "Test"
        sub = root / "S-01-Topic"
        sub.mkdir(parents=True)
        _write_md(root / "README.md", "#\n")
        _write_nb(root / "S-01-Alpha.ipynb")
        _write_md(sub / "README.md", "#\n")
        # Seul S-2 remonte ; par tri de chaines S-10-x < S-2-x, le "dernier"
        # serait S-2-x ; par tri naturel le dernier est S-10-x (sans remontee).
        _write_nb(sub / "S-10-x.ipynb")
        _write_nb(sub / "S-2-x.ipynb", md_blocks=["[Retour](../README.md)"])
        ss = _only_sub(_measure(root, tmp_path)[0])
        assert ss["remontee_total"] == 1
        assert ss["remontee_dernier"] is False
        # En inversant (S-10 remonte, S-2 non), le dernier remonte.
        _write_nb(sub / "S-2-x.ipynb")
        _write_nb(sub / "S-10-x.ipynb", md_blocks=["[Retour](../README.md)"])
        ss = _only_sub(_measure(root, tmp_path)[0])
        assert ss["remontee_dernier"] is True


# ---------------------------------------------------------------------------
# Carnets illisibles
# ---------------------------------------------------------------------------

class TestIllisibles:

    def test_invalid_json_lands_in_illisibles(self, tmp_path):
        root = tmp_path / "MyIA.AI.Notebooks" / "Test"
        sub = root / "S-01-Topic"
        sub.mkdir(parents=True)
        _write_md(root / "README.md", "#\n")
        _write_nb(root / "S-01-Alpha.ipynb")
        _write_nb(sub / "S-01-a.ipynb")
        broken_sub = sub / "S-01-broken.ipynb"
        broken_sub.write_text("{ceci n'est pas du json", encoding="utf-8")
        broken_root = root / "S-01-broken-root.ipynb"
        broken_root.write_text("pas du tout", encoding="utf-8")
        data, illisibles = _measure(root, tmp_path)
        assert "MyIA.AI.Notebooks/Test/S-01-Topic/S-01-broken.ipynb" in illisibles
        assert "MyIA.AI.Notebooks/Test/S-01-broken-root.ipynb" in illisibles
        assert _only_sub(data)["carnets"] == 2


# ---------------------------------------------------------------------------
# CLI : codes de sortie et formats
# ---------------------------------------------------------------------------

class TestMain:

    def test_exit_zero_by_default(self, tmp_path):
        root, _sub = _build_finished(tmp_path)
        rc = check.main(["--root", "MyIA.AI.Notebooks/Test", "--repo-root", str(tmp_path)])
        assert rc == 0

    def test_exit_zero_strict_when_finished(self, tmp_path):
        root, _sub = _build_finished(tmp_path)
        rc = check.main(
            ["--root", "MyIA.AI.Notebooks/Test", "--repo-root", str(tmp_path), "--strict"]
        )
        assert rc == 0

    def test_strict_exit_one_when_missing(self, tmp_path):
        root, _sub = _build_finished(tmp_path)
        (root / "S-01-Topic" / "README.md").unlink()
        rc = check.main(
            ["--root", "MyIA.AI.Notebooks/Test", "--repo-root", str(tmp_path), "--strict"]
        )
        assert rc == 1

    def test_bad_root_exit_two(self, tmp_path, capsys):
        rc = check.main(["--root", "Nope/Inexistant", "--repo-root", str(tmp_path)])
        assert rc == 2
        err = capsys.readouterr().err
        assert "n'est pas un repertoire" in err

    def test_json_output_keys(self, tmp_path, capsys):
        root, _sub = _build_finished(tmp_path)
        rc = check.main(
            ["--root", "MyIA.AI.Notebooks/Test", "--repo-root", str(tmp_path), "--json"]
        )
        assert rc == 0
        payload = json.loads(capsys.readouterr().out)
        assert set(payload) == {"roots", "illisibles"}
        rd = payload["roots"][0]
        assert rd["root"] == "MyIA.AI.Notebooks/Test"
        assert set(rd) == {
            "root",
            "racine_carnets",
            "readme_racine",
            "sous_series",
            "finies",
            "total",
        }
        ss = rd["sous_series"][0]
        assert set(ss) == {
            "nom",
            "chemin",
            "carnets",
            "readme",
            "nom_nu",
            "marche",
            "descente",
            "remontee_dernier",
            "remontee_total",
            "capstones",
            "consommateur_max",
            "tete_racine",
            "accretions_racine",
            "ledger_lignes",
            "ledger_cibles_disparues",
            "traductions_perimees",
            "traductions_perimees_total",
            "metadata_ancien_nom",
            "manques",
            "finie",
        }
        assert ss["chemin"] == "MyIA.AI.Notebooks/Test/S-01-Topic"
        assert ss["finie"] is True

    def test_markdown_header_and_text_header(self, tmp_path, capsys):
        root, _sub = _build_finished(tmp_path)
        rc = check.main(
            ["--root", "MyIA.AI.Notebooks/Test", "--repo-root", str(tmp_path), "--markdown"]
        )
        assert rc == 0
        md = capsys.readouterr().out
        assert "**MyIA.AI.Notebooks/Test** — 1/1 sous-series finies" in md
        assert "| Sous-serie | Carnets | README | Marche | Descente | Remontee | Capstone |" in md
        assert "| S-01-Topic | 3 | oui | 1 | 2 | oui | oui (2/3) |" in md
        rc = check.main(["--root", "MyIA.AI.Notebooks/Test", "--repo-root", str(tmp_path)])
        assert rc == 0
        text = capsys.readouterr().out
        assert "Sous-serie" in text
        assert "1/1 sous-series finies" in text
        assert "S-01-Topic" in text

    def test_exclude_retire_un_dossier_du_recensement(self, tmp_path, capsys):
        root, _sub = _build_finished(tmp_path)
        _write_nb(root / "service" / "outil.ipynb")
        base = ["--root", "MyIA.AI.Notebooks/Test", "--repo-root", str(tmp_path), "--json"]
        assert check.main(base) == 0
        roots = json.loads(capsys.readouterr().out)["roots"]
        assert [ss["nom"] for ss in roots[0]["sous_series"]] == ["S-01-Topic", "service"]
        assert check.main(base + ["--exclude", "service", "--strict"]) == 0
        rd = json.loads(capsys.readouterr().out)["roots"][0]
        assert [ss["nom"] for ss in rd["sous_series"]] == ["S-01-Topic"]
        assert rd["finies"] == rd["total"] == 1
