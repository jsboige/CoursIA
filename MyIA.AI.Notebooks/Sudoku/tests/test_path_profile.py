"""Tests pour Sudoku/scripts/path_profile.py (#27214).

Instrument du protocole scelle
``docs/research/sudoku-frontiere-inference-pre-enregistrement.md``. Les tests
portent sur des **invariants de definition**, jamais sur des valeurs attendues
du pilote : le protocole interdit d'ajuster une regle apres avoir vu une
mesure.

  1. Le rejou reproduit exactement le chemin de ``InferenceSolver.solve`` ;
     une divergence leve, elle ne rend pas un profil faux.
  2. ``tangle`` (protocole §4.3, revision v2) : nombre cyclomatique du graphe
     d'exclusion, ou le chiffre compte -- deux candidats d'unites communes
     mais de chiffres differents ne sont pas lies, et le graphe est simple.
  3. ``support`` (protocole §4.1) : une regle inconnue rend ``None``.
  4. Les variables se recalculent independamment depuis la trace officielle.
  5. Les comptes d'exclusion du protocole §7.5 se separent : lignes ignorees,
     doublons, grilles sans solution unique, traces refusees.

Pas d'erreur volontaire (regle C.1) : le cas de divergence utilise un solveur
dont ``solve`` est tronque, pas un code qui leve pour l'exemple.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

_SUDOKU = Path(__file__).resolve().parents[1]
for _p in (str(_SUDOKU), str(_SUDOKU / "scripts")):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import path_profile  # noqa: E402
from inference_trace import InferenceSolver  # noqa: E402
from path_profile import (  # noqa: E402
    CorpusReport,
    ReplayDivergence,
    exclusion_graph,
    fingerprint,
    format_report,
    main,
    profile_corpus,
    profile_grid,
    replay,
    support,
    tangle,
)

PUZZLES = _SUDOKU / "Puzzles"
RANK = {rule: i + 1 for i, rule in enumerate(InferenceSolver.RULE_ORDER)}

# Les six corpus du pilote (protocole §10.1), du plus facile au plus dur.
CORPUS_PILOTE = (
    "Sudoku_gen_facile.txt", "Sudoku_gen_moyen.txt", "Sudoku_gen_difficile.txt",
    "Sudoku_Easy51.txt", "Sudoku_hardest.txt", "Sudoku_top95.txt",
)


def _load(name: str, n: int | None = None) -> list[str]:
    out = []
    for line in (PUZZLES / name).read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if len(line) >= 81:
            out.append(line[:81])
            if n and len(out) >= n:
                break
    return out


def _state(cells: dict[tuple[int, int], set[int]]) -> tuple[frozenset[int], ...]:
    """Etat construit : ``{(row, col): {candidats}}`` ; les autres cases vides."""
    return tuple(frozenset(cells.get((idx // 9, idx % 9), ())) for idx in range(81))


def _solved_with_gesture(candidates: list[str]) -> str:
    """Premiere grille resolue par ``R`` dont la trace contient un geste."""
    for puzzle in candidates:
        trace = InferenceSolver(puzzle).solve()
        if trace.solved and any(RANK[s.rule] >= 3 for s in trace.steps):
            return puzzle
    raise AssertionError("aucune grille resolue avec geste parmi les candidates")


def _stalled(candidates: list[str]) -> str:
    """Premiere grille sur laquelle ``R`` s'arrete."""
    for puzzle in candidates:
        if InferenceSolver(puzzle).solve().stalled:
            return puzzle
    raise AssertionError("aucune grille en arret parmi les candidates")


# ---------------------------------------------------------------------------
# 1. Rejou = solve()
# ---------------------------------------------------------------------------


def test_replay_reproduit_solve_sur_un_echantillon_de_chaque_corpus() -> None:
    total = 0
    for name in ("Sudoku_gen_facile.txt", "Sudoku_gen_moyen.txt",
                 "Sudoku_gen_difficile.txt", "Sudoku_Easy51.txt",
                 "Sudoku_hardest.txt", "Sudoku_top95.txt"):
        for puzzle in _load(name, 5):
            ref = InferenceSolver(puzzle).solve()
            got = replay(InferenceSolver(puzzle)).trace
            assert got.solved == ref.solved
            assert got.stalled == ref.stalled
            assert [s.rule for s in got.steps] == [s.rule for s in ref.steps]
            assert ([s.placements for s in got.steps]
                    == [s.placements for s in ref.steps])
            assert ([s.eliminations for s in got.steps]
                    == [s.eliminations for s in ref.steps])
            assert [s.grid_after for s in got.steps] == [s.grid_after for s in ref.steps]
            total += 1
    assert total == 30


def test_une_divergence_du_rejou_leve(monkeypatch: pytest.MonkeyPatch) -> None:
    class SolveTronque(InferenceSolver):
        """Meme politique au rejou, mais ``solve`` ne rend qu'un pas."""

        def solve(self, max_steps: int = 10000):
            trace = super().solve(max_steps)
            trace.steps = trace.steps[:1]
            return trace

    monkeypatch.setattr(path_profile, "InferenceSolver", SolveTronque)
    with pytest.raises(ReplayDivergence):
        profile_grid(_load("Sudoku_Easy51.txt", 1)[0])


# ---------------------------------------------------------------------------
# 2. tangle (protocole §4.3, revision v2 : nombre cyclomatique normalise)
# ---------------------------------------------------------------------------


def test_tangle_d_un_etat_sans_candidat_n_est_pas_defini() -> None:
    assert tangle(_state({})) is None
    assert exclusion_graph(_state({})) is None


@pytest.mark.parametrize("cells", [
    {(0, 0): {1}},                                  # un seul candidat
    {(0, 0): {1, 2}},                               # deux chiffres d'une case
    {(0, 0): {1}, (0, 1): {1}},                     # meme chiffre, meme ligne
    {(0, 0): {1}, (8, 0): {1}},                     # meme chiffre, meme colonne
    {(0, 0): {1}, (1, 1): {1}},                     # meme chiffre, meme bloc
    {(0, 0): {1}, (8, 8): {2}},                     # deux candidats isoles
    {(0, 0): {1}, (0, 1): {2}},                     # meme ligne, chiffres differents
])
def test_tangle_vaut_0_sans_cycle(cells: dict[tuple[int, int], set[int]]) -> None:
    # Aucun lien, ou des liens qui ne ferment aucune boucle.
    assert tangle(_state(cells)) == 0.0


def test_tangle_d_une_case_de_trois_candidats() -> None:
    # Trois noeuds, trois liens : un cycle, soit 1 / 3.
    cells = {(0, 0): {1, 2, 3}}
    assert exclusion_graph(_state(cells)) == (3, 3, 1)
    assert tangle(_state(cells)) == pytest.approx(1 / 3)


def test_tangle_d_un_cycle_de_deux_cases() -> None:
    # Deux cases d'une ligne, chacune {1, 2} : 4 noeuds, 4 liens, 1 cycle.
    cells = {(0, 0): {1, 2}, (0, 1): {1, 2}}
    assert exclusion_graph(_state(cells)) == (4, 4, 1)
    assert tangle(_state(cells)) == pytest.approx(0.25)


def test_deux_unites_partagees_ne_font_qu_un_lien() -> None:
    # (0,0) et (0,1) partagent la ligne 0 et le bloc (0,0) ; (0,0) et (0,5),
    # la ligne 0 seule. Le graphe est simple : 4 liens dans les deux cas.
    deux_unites = {(0, 0): {1, 2}, (0, 1): {1, 2}}
    une_unite = {(0, 0): {1, 2}, (0, 5): {1, 2}}
    assert exclusion_graph(_state(deux_unites)) == (4, 4, 1)
    assert exclusion_graph(_state(une_unite)) == (4, 4, 1)


def test_tangle_depend_du_chiffre_et_pas_seulement_des_cases() -> None:
    # Memes cases, meme nombre de candidats : seuls les chiffres changent.
    memes_chiffres = {(0, 0): {1, 2}, (0, 1): {1, 2}}
    chiffres_disjoints = {(0, 0): {1, 2}, (0, 1): {3, 4}}
    assert tangle(_state(memes_chiffres)) == pytest.approx(0.25)
    assert tangle(_state(chiffres_disjoints)) == 0.0


def test_tangle_est_ramene_au_nombre_de_candidats() -> None:
    # Deux cases isolees de trois candidats : 2 cycles pour 6 noeuds, soit la
    # meme valeur qu'une seule case de trois candidats.
    cells = {(0, 0): {1, 2, 3}, (8, 8): {4, 5, 6}}
    assert exclusion_graph(_state(cells)) == (6, 6, 2)
    assert tangle(_state(cells)) == pytest.approx(1 / 3)


# ---------------------------------------------------------------------------
# 3. support (protocole §4.1)
# ---------------------------------------------------------------------------


def test_support_des_regles_dont_les_premises_citent_les_cases() -> None:
    st = _state({})
    assert support("naked_single", "case (3,4) n'a qu'un candidat : 7", st) == 1
    assert support("hidden_single", "valeur 9 n'apparait qu'en (2,7) dans son unite",
                   st) == 1
    assert support("naked_pair",
                   "(1,2) et (1,5) partagent exactement [3, 8] (row)", st) == 2
    assert support("naked_triple",
                   "(0,1), (0,4), (0,7) ne portent que [2, 5, 9] "
                   "(ligne, tuple nu d'ordre 3)", st) == 3
    assert support("naked_quad",
                   "(0,1), (0,4), (0,7), (1,1) ne portent que [2, 5, 9, 4] "
                   "(colonne, tuple nu d'ordre 4)", st) == 4
    assert support("hidden_pair",
                   "valeurs [1, 3] confinees a (2,2), (2,5) "
                   "(bloc, tuple cache d'ordre 2)", st) == 2
    assert support("hidden_quad",
                   "valeurs [1, 3, 6, 8] confinees a (2,2), (2,5), (5,2), (5,5) "
                   "(bloc, tuple cache d'ordre 4)", st) == 4


def test_support_pointing_pair_compte_la_valeur_dans_le_bloc() -> None:
    # Bloc (1,2) = lignes 3 a 5, colonnes 6 a 8.
    cells = {(3, 6): {5}, (4, 6): {5, 1}, (5, 6): {5}, (3, 5): {5}, (0, 0): {5}}
    assert support("pointing_pair", "valeur 5 alignee dans le bloc (1,2)",
                   _state(cells)) == 3


def test_support_locked_claiming_compte_la_valeur_dans_la_ligne() -> None:
    cells = {(4, 3): {3}, (4, 4): {3, 8}, (5, 3): {3}}
    assert support("locked_claiming",
                   "valeur 3 de la ligne 4 confinee au bloc (1,1)",
                   _state(cells)) == 2
    assert support("locked_claiming",
                   "valeur 3 de la colonne 3 confinee au bloc (1,1)",
                   _state(cells)) == 2


def test_support_xy_wing_compte_le_pivot_et_les_deux_pinces() -> None:
    # Lot 4 (#27533) : les premisses citent trois cases, au format du lot 3.
    st = _state({(5, 8): {1, 9}, (0, 8): {1, 6}, (5, 3): {6, 9}})
    assert support("xy_wing",
                   "pivot (5,8) [1, 9], pinces (0,8) [1, 6] et (5,3) [6, 9] : "
                   "6 elimine des cases visibles des deux pinces",
                   st) == 3


def test_support_xyz_wing_compte_le_pivot_et_les_deux_pinces() -> None:
    st = _state({(4, 4): {1, 4, 7}, (4, 0): {1, 4}, (0, 4): {4, 7}})
    assert support("xyz_wing",
                   "pivot (4,4) [1, 4, 7], pinces (4,0) [1, 4] et (0,4) [4, 7] : "
                   "7 elimine des cases visibles des trois cases",
                   st) == 3


def test_support_x_wing_compte_la_valeur_sur_les_deux_lignes() -> None:
    cells = {(2, 1): {7}, (2, 4): {7}, (6, 1): {7}, (6, 4): {7}, (2, 8): {2}}
    assert support("x_wing", "valeur 7 : lignes 2,6 partagent colonnes [1, 4]",
                   _state(cells)) == 4


def test_support_swordfish_compte_la_valeur_sur_les_lignes_de_base() -> None:
    cells = {(0, 1): {5}, (0, 4): {5}, (4, 4): {5}, (4, 8): {5}, (6, 1): {5},
             (6, 8): {5}, (2, 1): {5}}
    assert support("swordfish",
                   "valeur 5 : lignes (0, 4, 6) couvrent les colonnes [1, 4, 8]",
                   _state(cells)) == 6


def test_support_jellyfish_compte_la_valeur_sur_les_colonnes_de_base() -> None:
    cells = {(1, 0): {3}, (5, 0): {3}, (1, 2): {3}, (7, 2): {3}, (5, 6): {3},
             (8, 6): {3}, (7, 7): {3}, (8, 7): {3}, (1, 4): {3}}
    assert support("jellyfish",
                   "valeur 3 : colonnes (0, 2, 6, 7) couvrent les lignes [1, 5, 7, 8]",
                   _state(cells)) == 8


def test_support_d_une_regle_inconnue_vaut_none() -> None:
    st = _state({(2, 1): {7}})
    assert support("finned_swordfish",
                   "valeur 7 : lignes (2, 6, 8) couvrent les colonnes [1, 4, 8]",
                   st) is None
    # Les ailes sont des regles connues depuis le lot 4 : le temoin est un nom
    # qui ne designera jamais une technique, pour ne plus devoir bouger.
    assert support("regle_hors_catalogue", "(0,0), (0,1), (1,1)", st) is None


def test_support_d_un_format_de_premises_inattendu_vaut_none() -> None:
    # Un format qui n'est plus celui attendu ne rend pas un compte faux.
    st = _state({(3, 6): {5}, (4, 3): {3}})
    assert support("pointing_pair", "valeur 5 alignee dans le bloc 1,2", st) is None
    assert support("locked_claiming",
                   "valeur 3 de la ligne 4 dans le bloc (1,1)", st) is None
    assert support("x_wing", "valeur 7 : lignes 2 et 6 partagent colonnes 1 et 4",
                   st) is None
    # Base et couverture de meme orientation : ce n'est pas un poisson.
    assert support("swordfish",
                   "valeur 5 : lignes (3, 4, 6) couvrent les lignes [3, 4, 6]", st) is None


def test_support_d_un_recomptage_nul_vaut_none() -> None:
    # Zero case trouvee : l'etat contredit les premisses, ce n'est pas une mesure.
    st = _state({(3, 6): {5}})
    assert support("pointing_pair", "valeur 5 alignee dans le bloc (0,0)", st) is None
    assert support("locked_claiming",
                   "valeur 3 de la ligne 4 confinee au bloc (1,1)", st) is None
    assert support("x_wing", "valeur 7 : lignes 2,6 partagent colonnes [1, 4]",
                   st) is None


def test_support_est_reconnu_pour_tout_pas_des_traces_reelles() -> None:
    """Aucun pas d'une regle connue ne rend ``support`` non defini.

    Sur les six corpus du pilote : ``hidden_triple`` et ``hidden_quad``
    n'apparaissent que dans ``Sudoku_top95``. Le jeu des regles rencontrees
    est asserte egal a ``RULE_ORDER``, pour qu'une regression qui ne toucherait
    qu'une regle rare ne passe plus entre deux corpus.
    """
    rules_seen = set()
    for name in CORPUS_PILOTE:
        for puzzle in _load(name):
            for pas in replay(InferenceSolver(puzzle)).steps:
                rules_seen.add(pas.rule)
                assert support(pas.rule, pas.step.premises, pas.before) is not None
                assert support(pas.rule, pas.step.premises, pas.before) >= 1
    assert rules_seen == set(InferenceSolver.RULE_ORDER)


# ---------------------------------------------------------------------------
# 4. Variables recalculees depuis la trace officielle
# ---------------------------------------------------------------------------


def test_profil_d_une_grille_resolue_avec_geste() -> None:
    puzzle = _solved_with_gesture(_load("Sudoku_Easy51.txt"))
    trace = InferenceSolver(puzzle).solve()
    ranks = [RANK[s.rule] for s in trace.steps]
    idx_last = max(i for i, rk in enumerate(ranks) if rk >= 3)
    prof = profile_grid(puzzle)

    assert prof.solved and prof.trace_accepted
    assert prof.puzzle == trace.puzzle
    assert prof.n_steps == len(trace.steps)
    assert prof.r_max == max(ranks)
    assert prof.pos_r_max == pytest.approx(ranks.index(max(ranks)) / (len(ranks) - 1))
    assert prof.rank_last == ranks[idx_last]
    assert prof.elim_last == len(trace.steps[idx_last].eliminations)
    assert prof.collapse == len(ranks) - 1 - idx_last
    assert all(rk <= 2 for rk in ranks[idx_last + 1:])
    assert prof.support_last is not None and prof.support_last >= 1
    assert prof.tangle_last is not None and prof.tangle_last >= 0
    # Les variables d'arret ne sont pas definies pour une grille resolue.
    assert prof.steps_stall is None and prof.rank_hist is None
    assert prof.empty_stall is None and prof.cands_stall is None
    assert prof.tangle_stall is None


def test_tangle_last_est_mesure_sur_l_etat_qui_precede_le_geste_final() -> None:
    puzzle = _solved_with_gesture(_load("Sudoku_Easy51.txt"))
    played = replay(InferenceSolver(puzzle))
    last = max(i for i, pas in enumerate(played.steps) if RANK[pas.rule] >= 3)
    prof = profile_grid(puzzle)
    assert prof.tangle_last == tangle(played.steps[last].before)
    # Ce n'est ni l'etat initial, ni celui qui suit le geste.
    assert played.steps[last].before != played.steps[0].before or last == 0
    if last + 1 < len(played.steps):
        assert played.steps[last].before != played.steps[last + 1].before


def test_profil_d_une_grille_resolue_par_singletons_seuls() -> None:
    # Le geste final n'est pas defini quand la trace n'a que des singletons.
    singles_only = None
    for puzzle in _load("Sudoku_gen_facile.txt") + _load("Sudoku_Easy51.txt"):
        trace = InferenceSolver(puzzle).solve()
        if trace.solved and all(RANK[s.rule] <= 2 for s in trace.steps):
            singles_only = puzzle
            break
    assert singles_only is not None, "aucune grille resolue par singletons seuls"
    prof = profile_grid(singles_only)
    assert prof.solved
    assert prof.rank_last is None and prof.support_last is None
    assert prof.elim_last is None and prof.collapse is None
    assert prof.tangle_last is None
    assert prof.r_max <= 2


def test_profil_d_un_arret() -> None:
    puzzle = _stalled(_load("Sudoku_gen_difficile.txt") + _load("Sudoku_top95.txt"))
    trace = InferenceSolver(puzzle).solve()
    ranks = [RANK[s.rule] for s in trace.steps]
    prof = profile_grid(puzzle)

    assert not prof.solved and not trace.solved and trace.stalled
    assert prof.steps_stall == len(trace.steps)
    assert prof.rank_hist == {rk: ranks.count(rk) for rk in sorted(set(ranks))}
    assert sum(prof.rank_hist.values()) == prof.steps_stall
    assert prof.empty_stall == trace.steps[-1].grid_after.count("0")
    assert prof.cands_stall >= prof.empty_stall > 0
    assert prof.tangle_stall is not None and prof.tangle_stall >= 0
    # Les variables d'une grille resolue ne sont pas definies.
    for name in ("r_max", "pos_r_max", "rank_last", "support_last", "elim_last",
                 "collapse", "tangle_last"):
        assert getattr(prof, name) is None
    json.dumps(prof.to_dict())  # les cles d'un histogramme sont des chaines


# ---------------------------------------------------------------------------
# 5. Comptes d'exclusion du protocole §7.5
# ---------------------------------------------------------------------------


def test_comptes_d_exclusion(tmp_path: Path) -> None:
    easy = _load("Sudoku_gen_facile.txt", 1)[0]
    assert InferenceSolver(easy).solve().solved
    insatisfiable = "11" + "0" * 79      # deux 1 dans la premiere ligne
    non_unique = "1" + "0" * 80          # un seul indice : plusieurs solutions
    path = tmp_path / "corpus.txt"
    path.write_text("\n".join([
        easy,
        easy.replace("0", "."),          # doublon exact, ecrit avec des points
        "",                              # ligne vide
        "# un commentaire",
        insatisfiable,
        non_unique,
        "123",                           # ni vide ni grille
    ]) + "\n", encoding="utf-8")

    report = profile_corpus(path)
    assert report.n_grilles == 1
    assert report.n_lignes_ignorees == 3
    assert report.n_doublons == 1
    assert report.n_sans_solution_unique == 2
    assert report.n_resolues == 1 and report.n_arrets == 0
    assert report.coverage == 1.0
    assert report.n_traces_refusees == 0
    assert len(report.sha256) == 64
    assert report.profiles[0].puzzle == easy


def test_empreinte_d_un_corpus_ne_depend_pas_des_fins_de_ligne(
        tmp_path: Path) -> None:
    """LF et CRLF donnent la meme empreinte.

    Un checkout Windows livre en CRLF un fichier commite en LF : sur les
    octets lus tels quels, le meme corpus avait deux ``sha256`` selon la
    plateforme (#28619).
    """
    premiere, seconde = _load("Sudoku_gen_facile.txt", 2)
    texte = premiere + "\n" + seconde + "\n"
    en_lf = tmp_path / "en_lf.txt"
    en_crlf = tmp_path / "en_crlf.txt"
    en_lf.write_bytes(texte.encode("utf-8"))
    en_crlf.write_bytes(texte.replace("\n", "\r\n").encode("utf-8"))

    assert fingerprint(en_lf.read_bytes()) == fingerprint(en_crlf.read_bytes())
    assert fingerprint(en_crlf.read_bytes()) == fingerprint(texte.encode("utf-8"))
    rapport_lf, rapport_crlf = profile_corpus(en_lf), profile_corpus(en_crlf)
    assert rapport_lf.sha256 == rapport_crlf.sha256
    assert rapport_lf.n_grilles == rapport_crlf.n_grilles == 2
    # Un retour chariot isole n'est pas une fin de ligne : il reste dans l'empreinte.
    assert fingerprint(b"a\rb\n") != fingerprint(b"ab\n")


def test_une_trace_refusee_est_comptee_et_publiee(
        monkeypatch: pytest.MonkeyPatch) -> None:
    """``verify_trace`` refuse : la grille reste dans le corpus, marquee."""
    easy = _load("Sudoku_gen_facile.txt", 1)[0]

    class VerdictRefuse:
        accepted = False
        n_steps = 0

    monkeypatch.setattr(path_profile, "verify_trace", lambda trace: VerdictRefuse())
    prof = profile_grid(easy)
    assert prof.solved and not prof.trace_accepted


def test_mediane_sans_valeur_definie_vaut_none() -> None:
    report = CorpusReport(path="vide.txt", sha256="0" * 64)
    assert report.coverage == 0.0
    assert format_report(report).isascii()


# ---------------------------------------------------------------------------
# Ligne de commande
# ---------------------------------------------------------------------------


def test_ligne_de_commande_ecrit_un_rapport_json(tmp_path: Path,
                                                 capsys: pytest.CaptureFixture) -> None:
    source = PUZZLES / "Sudoku_gen_facile.txt"
    out = tmp_path / "profils.json"
    assert main([str(source), "--json", str(out)]) == 0
    payload = json.loads(out.read_text(encoding="utf-8"))
    (corpus,) = payload["corpora"]
    assert corpus["path"] == source.name
    assert corpus["n_grilles"] == 10 and len(corpus["profiles"]) == 10
    assert set(corpus["profiles"][0]) >= {
        "puzzle", "solved", "trace_accepted", "rank_last", "support_last",
        "collapse", "tangle_last", "steps_stall", "rank_hist", "tangle_stall"}
    assert corpus["sha256"] == profile_corpus(source).sha256
    text = capsys.readouterr().out
    assert text.isascii() and "couverture=" in text


def test_ligne_de_commande_sur_un_fichier_absent() -> None:
    assert main([str(PUZZLES / "absent.txt")]) == 2
