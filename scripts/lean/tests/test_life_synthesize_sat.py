"""Tests de `life_synthesize_sat` (Loi II, EPIC #12205, variante -b).

Ce que ces tests etablissent, dans l'ordre de ce qui pourrait faire mentir le
livrable :

  1. **L'encodage est exact, pas approche.** `universe_bounds` doit contenir
     strictement l'evolution : si une cellule vivante atteignait le bord de la
     fenetre, traiter l'exterieur comme mort serait une approximation
     silencieuse, et toute UNSAT deviendrait ininterpretable.
  2. **Le solveur est valide contre l'oracle B1.** Chaque motif rendu est
     rejoue par `evolve`/`shift_v` du moteur d'enumeration — le modele SAT est
     l'hypothese, le moteur d'origine est la reference.
  3. **Les deux moteurs sont d'accord la ou les deux savent tourner.** Sur la
     boite du glider, l'ensemble des formes normalisees doit etre le **meme**.
     C'est le seul point ou l'enumeration exhaustive peut arbitrer.
  4. **La minimalite est une refutation.** Les tailles inferieures ne sont pas
     « non trouvees » : chacune est UNSAT, et le moteur de reference le
     confirme independamment sur la boite ou il peut encore enumerer.
  5. **L'impossibilite rend un temoin.** Le critere 4 de #12205 exige de
     savoir dire « aucune solution », pas de se taire.
"""

from __future__ import annotations

import re
import sys
from math import comb
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from life_synthesize import evolve, normalize, synthesize
from life_synthesize_sat import (
    CANONICAL_GLIDER,
    emit_lean,
    render,
    search_minimal,
    solve_exact_size,
    universe_bounds,
    verify_solution,
)

pytest.importorskip("z3", reason="z3-solver requis pour la synthese SAT")

GLIDER_SPEC = dict(n=4, v=(1, -1), box_w=4, box_h=4)
LWSS_SPEC = dict(n=4, v=(2, 0), box_w=5, box_h=5)


@pytest.fixture(scope="module")
def glider() -> dict:
    return search_minimal(**GLIDER_SPEC, max_cells=8)


@pytest.fixture(scope="module")
def lwss() -> dict:
    return search_minimal(**LWSS_SPEC, max_cells=10)


class TestEncodageExact:
    """Sans ce bloc, une UNSAT ne voudrait rien dire."""

    def test_la_fenetre_contient_strictement_l_evolution(self):
        """Aucune cellule vivante ne doit atteindre le bord de la fenetre.

        Si l'evolution touchait le bord, « exterieur = mort » serait une
        approximation : le modele SAT decrirait un autre univers que Life, et
        `IMPOSSIBLE` cesserait d'etre une refutation.
        """
        n, v = 4, (1, -1)
        xs, ys = universe_bounds(4, 4, n, v)
        window = {(x, y) for x in xs for y in ys}
        border = {(x, y) for (x, y) in window
                  if x in (xs[0], xs[-1]) or y in (ys[0], ys[-1])}
        # Le pire cas est le motif qui remplit toute la boite.
        cells = {(x, y) for x in range(4) for y in range(4)}
        for _ in range(n + 1):
            assert not (cells & border), "l'evolution atteint le bord"
            assert cells <= window
            cells = evolve(1, cells)

    def test_marge_croit_avec_n_et_v(self):
        xs_small, _ = universe_bounds(4, 4, 2, (1, 0))
        xs_large, _ = universe_bounds(4, 4, 6, (3, 0))
        assert len(xs_large) > len(xs_small)


class TestOracleB1:
    """Le solveur ne se valide pas lui-meme."""

    def test_chaque_motif_est_rejoue_par_le_moteur_de_reference(self, glider, lwss):
        for result, spec in ((glider, GLIDER_SPEC), (lwss, LWSS_SPEC)):
            assert result["patterns"], "aucun motif a verifier"
            for pattern in result["patterns"]:
                cells = {tuple(c) for c in pattern}
                assert verify_solution(cells, spec["n"], spec["v"]), (
                    f"motif refute par le moteur B1 : {sorted(cells)}"
                )

    def test_verify_solution_rejette_un_motif_faux(self):
        """Controle negatif : la verification doit savoir dire non."""
        assert not verify_solution({(0, 0), (1, 0), (2, 0)}, 4, (1, -1))
        assert not verify_solution(set(), 4, (1, -1))


class TestAccordDesDeuxMoteurs:
    """Le seul endroit ou l'enumeration exhaustive peut arbitrer."""

    def test_memes_formes_normalisees_sur_la_boite_du_glider(self, glider):
        brute = {normalize(set(p)) for p in synthesize(4, (1, -1), 4, 6)}
        sat = {tuple(map(tuple, p)) for p in glider["patterns"]}
        assert sat == brute, (
            f"desaccord SAT/enumeration\n  SAT seul : {sat - brute}\n"
            f"  enumeration seule : {brute - sat}"
        )

    def test_le_glider_canonique_est_retrouve(self, glider):
        assert glider["canonical_glider_present"]
        assert CANONICAL_GLIDER in {tuple(map(tuple, p)) for p in glider["patterns"]}

    def test_quatre_phases(self, glider):
        assert glider["count_normalized"] == 4


class TestMinimaliteEstUneRefutation:
    def test_glider_minimal_a_cinq_cellules(self, glider):
        assert glider["verdict"] == "FOUND"
        assert glider["min_cells"] == 5
        assert glider["sizes_refuted"] == [1, 2, 3, 4]

    def test_les_tailles_refutees_le_sont_vraiment(self):
        """Confirme la refutation SAT par enumeration exhaustive independante.

        Le solveur dit « aucun motif de taille <= 4 ». L'enumeration, qui peut
        encore tourner a cette taille, doit dire la meme chose — sinon la
        refutation serait un bug d'encodage deguise en resultat.
        """
        assert synthesize(4, (1, -1), 4, 4) == []

    def test_lwss_minimal_a_neuf_cellules(self, lwss):
        assert lwss["verdict"] == "FOUND"
        assert lwss["min_cells"] == 9
        assert lwss["sizes_refuted"] == [1, 2, 3, 4, 5, 6, 7, 8]

    def test_lwss_est_hors_de_portee_de_l_enumeration(self):
        """Justifie l'existence de ce moteur, chiffres a l'appui.

        Ce n'est pas « l'enumeration est lente » : c'est le nombre de
        sous-ensembles qu'elle devrait parcourir pour la seule taille 9.
        """
        assert comb(25, 9) == 2_042_975
        assert sum(comb(25, k) for k in range(1, 10)) > 3_800_000


class TestTemoinDImpossibilite:
    """Critere 4 de #12205 — savoir dire « aucune solution »."""

    def test_au_dela_de_la_vitesse_de_la_lumiere(self):
        """Deplacement 3 en 2 generations : impossible pour TOUT motif.

        L'information ne se propage que d'une cellule par generation dans Life.
        Ce cas est donc refutable par un argument independant du solveur : il
        sert de calibration au verdict IMPOSSIBLE.
        """
        result = search_minimal(n=2, v=(3, 0), box_w=3, box_h=3, max_cells=4)
        assert result["verdict"] == "IMPOSSIBLE"
        assert result["min_cells"] is None
        assert result["patterns"] == []

    def test_le_temoin_enumere_ce_qui_a_ete_refute(self):
        """Un silence n'est pas un temoin : la borne doit etre explicite."""
        result = search_minimal(n=2, v=(3, 0), box_w=3, box_h=3, max_cells=4)
        assert result["sizes_refuted"] == [1, 2, 3, 4]


class TestSanity:
    def test_determinisme(self):
        a = search_minimal(n=4, v=(1, -1), box_w=4, box_h=4, max_cells=5)
        b = search_minimal(n=4, v=(1, -1), box_w=4, box_h=4, max_cells=5)
        assert a["patterns"] == b["patterns"]
        assert a["min_cells"] == b["min_cells"]

    def test_first_only_rend_une_seule_forme(self):
        shapes = solve_exact_size(4, (1, -1), 4, 4, 5, enumerate_all=False)
        assert len(shapes) == 1
        assert verify_solution(set(shapes[0]), 4, (1, -1))

    def test_les_formes_sont_normalisees(self, glider, lwss):
        for result in (glider, lwss):
            for pattern in result["patterns"]:
                cells = [tuple(c) for c in pattern]
                assert min(x for x, _ in cells) == 0
                assert min(y for _, y in cells) == 0

    def test_le_glider_canonique_en_est_vraiment_un(self):
        """Pin de la constante elle-meme, pas seulement de sa forme.

        `CANONICAL_GLIDER` sert de temoin de recoupement avec le moteur
        B1 : si la constante cessait d'etre un glider, le recoupement
        continuerait de passer en comparant deux erreurs.
        """
        assert verify_solution(set(CANONICAL_GLIDER), 4, (1, -1))

    def test_render_dessine_le_glider(self):
        """Convention du module : x = colonne, y = ligne."""
        assert render(CANONICAL_GLIDER) == ["###", "..#", ".#."]

    def test_render_motif_vide(self):
        assert render(()) == []


class TestCertificatLean:
    """Le generateur produit le certificat ; il n'ecrit dans aucun lake.

    Le lake `conway_lean` appartient a une autre lane (claim
    `conway_lean/**` sur #12205). Ces tests le **lisent** comme reference
    externe — ils ne le modifient pas.
    """

    LAKE = (Path(__file__).resolve().parents[3]
            / "MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean"
            / "Conway/Life/Spaceships.lean")

    @staticmethod
    def _def_body(source: str, name: str) -> str:
        m = re.search(rf"def {name} : Grid :=\n(.*?)\n\n", source, re.S)
        assert m, f"def {name} introuvable"
        return m.group(1).strip()

    def test_le_moteur_reproduit_le_lwss_ecrit_a_la_main(self, lwss):
        """Recoupement inter-substrats le plus fort de ce livrable.

        Le moteur ne recoit que la **specification** (periode 4,
        deplacement (0, 2), boite 5x5, taille minimale). Il doit en
        ressortir le texte Lean que l'auteur de `Spaceships.lean` avait
        ecrit a la main — meme motif, meme mise en forme, meme enonce de
        theoreme. Si un jour les deux divergent, l'un des deux a tort et
        ce test le dit.
        """
        lake = self.LAKE.read_text(encoding="utf-8")
        ref = self._def_body(lake, "lwss")

        emitted = [
            emit_lean("lwss", [tuple(c) for c in p], 4, (2, 0))
            for p in lwss["patterns"]
        ]
        bodies = [self._def_body(text + "\n\n", "lwss") for text in emitted]
        assert ref in bodies, (
            "aucune forme synthetisee ne reproduit le `lwss` du lake\n"
            f"  lake  : {ref}\n  moteur: {bodies}"
        )

    def test_l_enonce_de_theoreme_emis_est_celui_du_lake(self, lwss):
        lake = self.LAKE.read_text(encoding="utf-8")
        assert (
            "theorem lwss_spaceship : isSpaceship lwss 4 (0, 2) = true := by decide"
            in lake
        )
        emitted = emit_lean("lwss", [tuple(c) for c in lwss["patterns"][0]],
                            4, (2, 0))
        assert (
            "theorem lwss_spaceship : isSpaceship lwss 4 (0, 2) = true := by decide"
            in emitted
        )

    def test_la_seconde_forme_est_absente_du_lake(self, lwss):
        """Honnetete : ce n'est PAS un vaisseau inedit.

        Les deux formes minimales sont le LWSS et son **miroir** (lignes
        renversees) : `normalize` quotiente par translation, pas par
        reflexion. Le miroir ne figure pas dans `Spaceships.lean`, mais le
        presenter comme une decouverte serait faux.
        """
        lake = self.LAKE.read_text(encoding="utf-8")
        ref = self._def_body(lake, "lwss")
        bodies = [
            self._def_body(
                emit_lean("lwss", [tuple(c) for c in p], 4, (2, 0)) + "\n\n",
                "lwss")
            for p in lwss["patterns"]
        ]
        autres = [b for b in bodies if b != ref]
        assert len(autres) == 1, autres

        def grille(body: str) -> list[tuple[int, int]]:
            return sorted(
                (int(a), int(b))
                for a, b in re.findall(r"\((-?\d+), (-?\d+)\)", body)
            )

        h = max(r for r, _ in grille(ref))
        miroir = sorted((h - r, c) for r, c in grille(ref))
        assert grille(autres[0]) == miroir, (
            "la seconde forme n'est pas le miroir du LWSS : la revendiquer "
            "comme un vaisseau inedit demanderait une verification neuve"
        )
