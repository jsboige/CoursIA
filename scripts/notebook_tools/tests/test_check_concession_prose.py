"""Tests du detecteur de prose de concession ajoutee (T5, #21433).

Couvre les controles exiges par l'attendu 2 de #21433 :
  - positif : une ligne d'aveu ajoutee est detectee ;
  - negatif : la prose ordinaire ne declenche pas ;
  - une ligne d'aveu DEJA PRESENTE au parent ne compte pas (correction F1) ;
plus les controles de robustesse : accent-blind, cellules code hors champ,
ligne deplacee entre cellules, commits de merge ecartes, reprise --since.
"""

import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_concession_prose import (  # noqa: E402
    CONCESSION_RE,
    added_concession_lines,
    iter_commits,
    main,
    markdown_cells,
)

NB_PLAIN = {
    "cells": [
        {"cell_type": "markdown", "source": ["# Titre\n", "Prose ordinaire."]},
    ],
}


def _nb(*lines):
    # nbformat : chaque element de la liste source se termine par \n.
    return {"cells": [{"cell_type": "markdown",
                       "source": [ln + "\n" for ln in lines]}]}


def _nb_code(*lines):
    return {"cells": [{"cell_type": "code", "source": list(lines)}]}


class TestAddedConcessionLines:
    def test_positive_added_line(self):
        head = _nb("# Titre\n", "Prose ordinaire.\n", "Resultat illustratif.")
        hits = added_concession_lines(NB_PLAIN, head)
        assert len(hits) == 1
        assert hits[0]["motif"] == "illustrati"
        assert hits[0]["cell"] == "pos-0"

    def test_negative_ordinary_prose(self):
        head = _nb("# Titre\n", "Prose ordinaire.\n",
                   "Le modele converge en 12 epoques, perte 0.03.")
        assert added_concession_lines(NB_PLAIN, head) == []

    def test_negative_empty_parent_unrelated_line(self):
        # Un parent VIDE suivi d'un head sans aveu : 0 hit.
        assert added_concession_lines({"cells": []}, NB_PLAIN) == []

    def test_already_in_parent_does_not_count(self):
        # Correction F1 : ligne d'aveu deja presente au parent -> pas un ajout.
        parent = _nb("Resultat illustratif.")
        head = _nb("Resultat illustratif.\n", "Suite du texte.")
        assert added_concession_lines(parent, head) == []

    def test_moved_between_cells_does_not_count(self):
        # Une ligne deplacee d'une cellule a l'autre n'est pas un ajout.
        parent = {"cells": [
            {"cell_type": "markdown", "source": ["Resultat illustratif."]},
            {"cell_type": "markdown", "source": ["Autre cellule."]},
        ]}
        head = {"cells": [
            {"cell_type": "markdown", "source": ["Autre cellule."]},
            {"cell_type": "markdown", "source": ["Resultat illustratif."]},
        ]}
        assert added_concession_lines(parent, head) == []

    def test_accent_blind(self):
        # « Exécution sautée » doit hit « sautee » apres normalisation.
        head = _nb("Executions sautee (locale)",
                   "Exécution sautée (distante)")
        hits = added_concession_lines({"cells": []}, head)
        assert len(hits) == 2
        assert {h["motif"] for h in hits} == {"sautee"}

    def test_code_cell_out_of_scope(self):
        head = _nb_code("x = placeholder")
        assert added_concession_lines({"cells": []}, head) == []

    def test_source_as_string_not_list(self):
        # nbformat permet source en str : aplatir les deux formes.
        head = {"cells": [
            {"cell_type": "markdown", "source": "Resultat illustratif."}]}
        hits = added_concession_lines({"cells": []}, head)
        assert len(hits) == 1

    def test_list_and_count_agree(self):
        # Lecon count-vs-list : la liste et son compte restent coherents.
        # Le motif se matche sur la forme NORMALISEE (la ligne brute garde
        # accents et casse, apport #21443).
        from check_concession_prose import _normalize
        head = _nb("Resultat illustratif.", "Mode degrade assume.")
        hits = added_concession_lines({"cells": []}, head)
        assert len(hits) == 2
        assert all(CONCESSION_RE.search(_normalize(h["line"])) for h in hits)

    def test_markdown_lines_normalizes(self):
        # markdown_cells rend les lignes BRUTES ; la normalisation est
        # interne a added_concession_lines (match + comparaison parent).
        cells = markdown_cells(_nb("Limites du modèle"))
        assert cells == {"pos-0": ["Limites du modèle"]}

    def test_raw_line_preserved_in_hit(self):
        # Apport 1 (#21443) : le hit garde la ligne BRUTE, accents et casse
        # d'origine -- le match seul porte sur la forme normalisee.
        head = _nb("Le résultat est purement illustratif ici.")
        hits = added_concession_lines({"cells": []}, head)
        assert len(hits) == 1
        assert hits[0]["line"] == "Le résultat est purement illustratif ici."
        assert hits[0]["motif"] == "illustrati"

    def test_cell_address_id_then_position_fallback(self):
        # Apport 2 (#21443) : adresse stable par id nbformat quand present,
        # position "pos-N" en repli pour les carnets sans id.
        head = {"cells": [
            {"cell_type": "markdown", "id": "cell-conclusion",
             "source": ["Résultat illustratif.\n"]},
            {"cell_type": "markdown", "source": ["Mode dégradé assumé.\n"]},
        ]}
        hits = added_concession_lines({"cells": []}, head)
        assert {h["cell"] for h in hits} == {"cell-conclusion", "pos-1"}


def _run_git(repo, *args):
    subprocess.run(["git", "-C", str(repo), *args], check=True,
                   capture_output=True, text=True,
                   encoding="utf-8", errors="replace")


def _commit_nb(repo, name, cells, msg):
    path = repo / name
    path.write_text(json.dumps({"cells": cells}), encoding="utf-8")
    _run_git(repo, "add", name)
    _run_git(repo, "commit", "-m", msg, "-q")


class TestCommitHitsAndHistory:
    def _repo(self, tmp_path):
        _run_git(tmp_path, "init", "-q")
        _run_git(tmp_path, "config", "user.email", "t@t.t")
        _run_git(tmp_path, "config", "user.name", "t")
        return tmp_path

    def _nb_file(self, *lines):
        return [{"cell_type": "markdown", "source": list(lines)}]

    def test_commit_detects_added_concession(self, tmp_path, capsys):
        repo = self._repo(tmp_path)
        _commit_nb(repo, "a.ipynb", self._nb_file("Prose ordinaire."), "c1")
        _commit_nb(repo, "a.ipynb",
                   self._nb_file("Prose ordinaire.", "Resultat illustratif."),
                   "c2")
        rc = main(["--commit", "HEAD", "--cwd", str(repo)])
        out = capsys.readouterr().out
        assert rc == 0
        rows = [json.loads(l) for l in out.splitlines() if l.startswith("{")]
        assert len(rows) == 1
        assert rows[0]["notebook"] == "a.ipynb"
        assert rows[0]["motif"] == "illustrati"

    def test_commit_no_concession_zero_hit(self, tmp_path, capsys):
        repo = self._repo(tmp_path)
        _commit_nb(repo, "a.ipynb", self._nb_file("Prose ordinaire."), "c1")
        _commit_nb(repo, "a.ipynb",
                   self._nb_file("Prose ordinaire.", "Encore du texte."),
                   "c2")
        rc = main(["--commit", "HEAD", "--cwd", str(repo)])
        out = capsys.readouterr().out
        assert rc == 0
        assert not [l for l in out.splitlines() if l.startswith("{")]

    def test_notebook_created_is_separate_kind(self, tmp_path, capsys):
        # Apport 3 (#21443) : un carnet CREE par le commit n'a pas de
        # baseline -- espece "notebook-added", comptee separement.
        from check_concession_prose import commit_hits
        repo = self._repo(tmp_path)
        _commit_nb(repo, "a.ipynb", self._nb_file("Prose ordinaire."), "c1")
        _commit_nb(repo, "nouveau.ipynb",
                   self._nb_file("Résultat illustratif."), "c2")
        hits, seen, skipped = commit_hits("HEAD", cwd=str(repo))
        assert skipped is None and seen == ["nouveau.ipynb"]
        assert len(hits) == 1
        assert hits[0]["kind"] == "notebook-added"
        assert hits[0]["line"] == "Résultat illustratif."
        # Via main : le resume separe bien les deux especes.
        rc = main(["--commit", "HEAD", "--cwd", str(repo)])
        out = capsys.readouterr().out
        assert rc == 0
        assert "0 hit(s) ajoute(s), 1 notebook-added" in out

    def test_broken_parent_json_skips_notebook(self, tmp_path):
        # Regression : un parent present mais JSON casse (historique ancien)
        # doit ecarter le carnet, pas crasher ni fabriquer une baseline
        # vide qui attribuerait tout le stock du head a ce commit.
        from check_concession_prose import commit_hits
        repo = self._repo(tmp_path)
        (repo / "a.ipynb").write_text("{pas du json", encoding="utf-8")
        _run_git(repo, "add", "a.ipynb")
        _run_git(repo, "commit", "-m", "c1", "-q")
        _commit_nb(repo, "a.ipynb",
                   self._nb_file("Résultat illustratif."), "c2")
        hits, seen, skipped = commit_hits("HEAD", cwd=str(repo))
        assert (hits, seen, skipped) == ([], [], None)

    def test_history_and_since_resume(self, tmp_path, capsys):
        repo = self._repo(tmp_path)
        _commit_nb(repo, "a.ipynb", self._nb_file("Prose ordinaire."), "c1")
        _commit_nb(repo, "a.ipynb",
                   self._nb_file("Prose ordinaire.", "Resultat illustratif."),
                   "c2")
        first = subprocess.run(
            ["git", "-C", str(repo), "rev-parse", "HEAD~1"],
            capture_output=True, text=True,
                   encoding="utf-8", errors="replace").stdout.strip()
        rows = iter_commits(cwd=str(repo))
        assert len(rows) == 2
        rows_after = iter_commits(cwd=str(repo), after=first)
        assert len(rows_after) == 1
        rc = main(["--history", "--since", first, "--cwd", str(repo)])
        out = capsys.readouterr().out
        assert rc == 0
        hits = [l for l in out.splitlines() if l.startswith("{")]
        assert len(hits) == 1
        assert "repris apres" in out

    def test_merge_commit_skipped(self, tmp_path, capsys):
        from check_concession_prose import commit_hits
        repo = self._repo(tmp_path)
        _commit_nb(repo, "a.ipynb", self._nb_file("Prose ordinaire."), "base")
        _run_git(repo, "checkout", "-q", "-b", "side")
        _commit_nb(repo, "b.ipynb", self._nb_file("Texte normal."), "side")
        _run_git(repo, "checkout", "-q", "-")  # retour a la branche de base
        _commit_nb(repo, "a.ipynb", self._nb_file("Prose ordinaire. Suite."),
                   "main2")
        _run_git(repo, "merge", "-q", "--no-ff", "side", "-m", "merge")
        merge_sha = subprocess.run(
            ["git", "-C", str(repo), "rev-parse", "HEAD"],
            capture_output=True, text=True,
                   encoding="utf-8", errors="replace").stdout.strip()
        # Le garde-fou commit_hits ecarte explicitement les merges.
        hits, seen, skipped = commit_hits(merge_sha, cwd=str(repo))
        assert (hits, seen, skipped) == ([], [], "merge")
        # L'historique reste propre : 0 hit, aucun faux ajout du merge.
        rc = main(["--history", "--cwd", str(repo)])
        out = capsys.readouterr().out
        assert rc == 0
        assert "0 hit(s) ajoute(s) + 0 notebook-added" in out

    def test_state_file_written(self, tmp_path, capsys):
        repo = self._repo(tmp_path)
        _commit_nb(repo, "a.ipynb", self._nb_file("Prose ordinaire."), "c1")
        _commit_nb(repo, "a.ipynb",
                   self._nb_file("Prose ordinaire.",
                                 "Sorties non execute ici."),
                   "c2")
        state = tmp_path / "state.txt"
        rc = main(["--history", "--cwd", str(repo), "--state", str(state)])
        out = capsys.readouterr().out
        assert rc == 0
        last = subprocess.run(["git", "-C", str(repo), "rev-parse", "HEAD"],
                              capture_output=True, text=True,
                   encoding="utf-8", errors="replace").stdout.strip()
        assert state.read_text(encoding="utf-8").strip() == last
        hits = [json.loads(l) for l in out.splitlines() if l.startswith("{")]
        assert len(hits) == 1 and hits[0]["motif"] == "non execute"

    def test_self_test_passes_without_repo(self, tmp_path, capsys):
        # Self-test synthetique : les controles (a)-(e) passent sans sha reel.
        rc = main(["--self-test", "--cwd", str(tmp_path)])
        out = capsys.readouterr().out
        assert rc == 0
        assert "self-test: PASS" in out
        assert "SKIP" in out  # replay reel absent d'un depot vierge
