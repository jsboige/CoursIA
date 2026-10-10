#!/usr/bin/env python3
"""Tests for scripts/notebook_tools/check_activity_leak.py.

Epic #20250 phase 0 acceptance:

  - 3 controls POSITIFS must be flagged DENSLY:
      - un Corrigendum de cycle (titre + paragraphe de journal) ;
      - un « Dossier de domaine » de lane avec verdict de review ;
      - un paragraphe de coordination (DM + lane + horodatage ISO).
  - 3 controls NEGATIFS must PASS (aucune densite) :
      - le texte du cours (prose pedagogique sans marqueur) ;
      - les faux positifs MESURES de l'Epic : « DM » pour Diebold-Mariano,
        « adjoint » au sens mathematique, « dispatch dynamique » ;
      - les faux positifs mesures au premier audit plein : « cellule N »
        comme renvoi intra-carnet, « Tranche N » comme etiquette de
        structure (series CSP/Search).
  - Heritage de section : un paragraphe propre sous un titre porteur d'un
    identifiant de cycle est compte dense ; le titre H1 ne propage PAS.
  - Le mode diff ne juge que les passages AJOUTES : une mention isolee
    ajoutee ne declenche pas, un passage dense ajoute declenche.

The organ is loaded by path (importlib spec) : `scripts/notebook_tools/`
hosts both a module and standalone scripts, and namespace-package resolution
differs between local pytest and CI's combined collect (same reason as
test_check_cell_source_parses.py).
"""

import importlib.util
import sys
import unittest
from pathlib import Path


def _load_organ():
    scripts_dir = Path(__file__).resolve().parent.parent
    tool = scripts_dir / "notebook_tools" / "check_activity_leak.py"
    spec = importlib.util.spec_from_file_location("check_activity_leak", str(tool))
    module = importlib.util.module_from_spec(spec)
    # Python 3.14 : le decorateur @dataclass resout cls.__module__ dans
    # sys.modules avant l'exec -- un module charge par spec sans enregistrement
    # prealable rend 'NoneType' has no attribute '__dict__'.
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


_mod = _load_organ()
judge_passage = _mod.judge_passage
judge_cell = _mod.judge_cell
markers_in_text = _mod.markers_in_text
scan_notebook = _mod.scan_notebook
scan_diff = _mod.scan_diff
emit_diff = _mod.emit_diff
_markdown_paragraphs_of_blob = _mod._markdown_paragraphs_of_blob


# ---------------------------------------------------------------------------
# Controles POSITIFS : le recit d'activite, forme fondatrice SC-09
# ---------------------------------------------------------------------------

class TestPositiveControls(unittest.TestCase):
    def test_corrigendum_heading_is_dense(self):
        heading = "## Corrigendum c.1144 (reserve Monroe, DM HIGH adjoint po-2025 2026-10-09T18:52)"
        v = judge_passage(0, heading)
        self.assertTrue(v.dense, f"titre Corrigendum non dense: {v.markers}")

    def test_dossier_de_domaine_paragraph_is_dense(self):
        para = (
            "Dossier de domaine de la lane `myia-po-2024:CoursIA-2` sur cette PR "
            "(tete `27d7e0541d`), verdict `domain: fail`. Defaut reproduit "
            "firsthand, puis corrige."
        )
        v = judge_passage(0, para)
        self.assertTrue(v.dense)
        names = {n for n, _, _ in v.markers}
        self.assertIn("coord_noun", names)
        self.assertIn("machine", names)
        self.assertIn("verdict", names)
        self.assertIn("lane", names)

    def test_coordination_paragraph_is_dense(self):
        para = (
            "Le coordinateur myia-ai-01 a envoye un DM le 2026-10-07T18:52Z ; "
            "la reponse est arrivee dans commit 4e1d7ebf3."
        )
        v = judge_passage(0, para)
        self.assertTrue(v.dense)
        names = {n for n, _, _ in v.markers}
        self.assertIn("machine", names)
        self.assertIn("dm", names)
        self.assertIn("iso_ts", names)
        self.assertIn("commit_ref", names)

    def test_section_inheritance_under_cycle_heading(self):
        cell = (
            "## Corrigendum c.1209 (depouillement STV)\n\n"
            "Le depouillement initialement publie presentait une erreur dans la "
            "branche d'elimination, que la reproduction pas a pas a isolee."
        )
        verdicts = judge_cell(0, cell)
        body = [v for v in verdicts if not v.text.startswith("##")]
        self.assertEqual(len(body), 1)
        self.assertTrue(body[0].dense, "paragraphe corps non herite du titre")
        self.assertTrue(body[0].inherited)

    def test_h1_title_does_not_propagate(self):
        cell = (
            "# Percolation 03b - extensions L=128, L=256 (c.1105)\n\n"
            "Cette section mesure la transition de phase sur deux tailles de "
            "reseau et compare les corrections d'echelle finie aux predictions "
            "theoriques de Kesten pour la percolation par sites."
        )
        verdicts = judge_cell(0, cell)
        title = verdicts[0]
        body = verdicts[1]
        self.assertTrue(title.dense, "le titre porteur de cycle doit etre signale")
        self.assertFalse(body.dense, "le H1 ne doit pas propager a tout le carnet")
        self.assertFalse(body.inherited)


# ---------------------------------------------------------------------------
# Controles NEGATIFS : prose pedagogique et faux positifs mesures
# ---------------------------------------------------------------------------

class TestNegativeControls(unittest.TestCase):
    def test_course_prose_clean(self):
        para = (
            "Monroe propose une regle proportionnelle stricte ou chaque elu "
            "represente un nombre equilibre de votants. La formulation de 1995 "
            "minimise la somme des rangs, un probleme NP-dur resolu en pratique "
            "par programmation lineaire sur de petits profils."
        )
        v = judge_passage(0, para)
        self.assertFalse(v.dense)
        self.assertEqual(v.markers, [])

    def test_dm_diebold_mariano_not_flagged(self):
        for text in (
            "Le test de Diebold-Mariano rend DM p = 0.032 sur 4 seeds, sous le seuil.",
            "La statistique DM compare les pertes MSE des deux modeles.",
            "Le dual momentum (DM) combine momentum absolu et relatif.",
        ):
            with self.subTest(text=text):
                self.assertFalse(
                    any(n == "dm" for n, _, _ in markers_in_text(text)),
                    f"DM Diebold-Mariano/momentum signale a tort: {text}",
                )

    def test_dm_coordination_still_flagged(self):
        text = "Le coordinateur a envoye un DM HIGH a la lane po-2025."
        self.assertTrue(any(n == "dm" for n, _, _ in markers_in_text(text)))

    def test_adjoint_mathematical_not_flagged(self):
        for text in (
            "L'operateur adjoint verifie <Ax, y> = <x, A*y> pour tout couple.",
            "La matrice adjointe est la transposee conjuguee de la matrice.",
        ):
            with self.subTest(text=text):
                self.assertFalse(
                    any(n == "adjoint" for n, _, _ in markers_in_text(text)),
                    f"adjoint mathematique signale a tort: {text}",
                )

    def test_adjoint_lane_still_flagged(self):
        text = "L'adjoint a verifie le dossier avant de rendre la main."
        self.assertTrue(any(n == "adjoint" for n, _, _ in markers_in_text(text)))

    def test_dispatch_dynamic_not_flagged(self):
        for text in (
            "Le dispatch dynamique choisit la methode a l'execution selon le type.",
            "Le dispatch economique repartit la production entre les centrales.",
        ):
            with self.subTest(text=text):
                self.assertFalse(
                    any(n == "dispatch" for n, _, _ in markers_in_text(text)),
                    f"dispatch CS/EE signale a tort: {text}",
                )

    def test_dispatch_coordination_still_flagged(self):
        text = "Le dispatch a ete envoye au worker avec ses deux grains."
        self.assertTrue(any(n == "dispatch" for n, _, _ in markers_in_text(text)))

    def test_cellule_intra_notebook_not_flagged(self):
        # FP mesure au premier audit : renvoi aux cellules du carnet lui-meme.
        para = (
            "| Metrique | Meilleure config |\n"
            "| Periode EMA | EMA12/58 (Sharpe 0.335, cellule 14) |\n"
            "| Seuil Vol | insensible (cellule 16) |"
        )
        v = judge_passage(0, para)
        self.assertFalse(v.dense, f"renvoi intra-carnet signale: {v.markers}")

    def test_cellule_correction_context_still_flagged(self):
        # Le marqueur compte quand il voisine un marqueur de correction.
        para = (
            "La cellule 62 a ete corrigee dans le commit 8f0013edcf44 par la "
            "lane myia-po-2024:CoursIA-2."
        )
        v = judge_passage(0, para)
        self.assertTrue(v.dense)

    def test_tranche_structural_label_not_flagged(self):
        # « Tranche N » = etiquette pedagogique intra-carnet (CSP/Search).
        para = (
            "La **Tranche 1** (sections 1-4 ci-dessus) reimplemente from-scratch "
            "le solveur de N-Reines puis compare sa performance a celle du "
            "moteur CP-SAT sur la meme famille d'instances."
        )
        v = judge_passage(0, para)
        self.assertFalse(v.dense, f"etiquette Tranche N signalee: {v.markers}")

    def test_tranche_announcement_flagged(self):
        para = (
            "Les phases suivantes arriveront dans des PR suivantes de la lane "
            "myia-po-2024:CoursIA-2, avec la prochaine tranche dediee a l'audit."
        )
        v = judge_passage(0, para)
        self.assertTrue(v.dense)

    def test_issue_number_alone_not_dense(self):
        # Les numeros d'issue sont « a trier » par l'Epic : une mention isolee
        # en pied de carnet ne doit pas denser.
        para = (
            "Pour aller plus loin, voir l'issue #12100 sur les suppressions "
            "CodeQL inertes et le suivi editorial de la serie."
        )
        self.assertFalse(judge_passage(0, para).dense)


# ---------------------------------------------------------------------------
# Mode diff : seuls les passages AJOUTES sont juges
# ---------------------------------------------------------------------------

class TestDiffParity(unittest.TestCase):
    def test_added_dense_passage_detected_by_key(self):
        head = (
            '{"cells": [{"cell_type": "markdown", "source": '
            '["## Corrigendum c.1209 (depouillement STV)"]}]}'
        )
        keys = _markdown_paragraphs_of_blob(head)
        self.assertIn("## Corrigendum c.1209 (depouillement STV)", keys)
        # Le meme paragraphe present en base n'est PAS un ajout.
        base_keys = _markdown_paragraphs_of_blob(head)
        self.assertEqual(keys, base_keys)

    def test_new_file_paragraphs_are_added(self):
        """Statut A : tous les paragraphes sont legitimement neufs."""
        added, files, incidents = scan_diff("7a0521584^...7a0521584")
        self.assertEqual(incidents, [], "un ajout franc ne doit pas etre un incident")
        self.assertTrue(added, "le commit fondateur ajoute un corrigendum dense")
        self.assertIn(
            "MyIA.AI.Notebooks/GameTheory/SocialChoice/"
            "09-Committees-STV-Monroe-ChamberlinCourant.ipynb",
            files,
        )

    def test_broken_base_is_incident_not_refusal(self):
        """Base illisible : INCONNU (rc=2), jamais un refus fantome.

        Un `git show <base>:<rel>` en echec posait autrefois un blob de base
        vide : chaque paragraphe du carnet devenait un « ajout » et la garde
        refusait une PR pour du contenu preexistant. Le rc=2 est declare
        `warn_rc` au registre : neutre au check-run, jamais vert muet.
        """
        added, _files, incidents = scan_diff("deadbeef...HEAD")
        self.assertEqual(added, [], "une base illisible ne fabrique aucun finding")
        self.assertTrue(incidents, "une base illisible doit etre un incident")
        rc = emit_diff(added, [], True, incidents)
        self.assertEqual(rc, 2, "un incident sort en INCONNU, pas en OK ni en REFUS")


class TestNotebookScan(unittest.TestCase):
    def test_scan_notebook_part_on_fixture(self, tmp_path=None):
        import json
        import tempfile

        nb = {
            "cells": [
                {"cell_type": "markdown",
                 "source": ["# Mon carnet\n\n",
                            "Un paragraphe de cours tout a fait ordinaire sur la "
                            "theorie des jeux et les equilibres de Nash purs."]},
                {"cell_type": "markdown",
                 "source": ["## Corrigendum c.1209\n\n",
                            "Dossier de domaine de la lane `myia-po-2024:CoursIA-2` "
                            "avec verdict `domain: fail` et tete `27d7e0541d`."]},
                {"cell_type": "code", "source": ["print('x')"]},
            ]
        }
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "fixture.ipynb"
            path.write_text(json.dumps(nb), encoding="utf-8")
            report = scan_notebook(path)
        self.assertIsNotNone(report)
        self.assertGreater(report.part, 0.4)
        self.assertEqual(len(report.dense_passages), 2)


if __name__ == "__main__":
    unittest.main()
