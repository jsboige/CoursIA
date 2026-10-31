#!/usr/bin/env python3
r"""Tests de `list_scope_swallowed_issues.py` (#23348).

Le sujet de l'organe est un piege de forme : `Fix(ci,#22937)` et `Fix #22937`
se ressemblent a l'oeil et n'ont pas du tout le meme effet. Ces tests fixent la
frontiere la ou elle compte reellement :

- le numero retenu est celui qui suit la **derniere** virgule du scope, jamais
  un chiffre du scope (`Fix(ANALYSE-04,#21027)` doit rendre 21027, pas 04) ;
- un mot-cle de fermeture **explicite** dans le corps exclut le couple (le
  commit a bien ferme son issue) ;
- `See #N` et `Fix(ci,#N)` ne sont **pas** des fermetures ;
- le sous-ensemble discriminant est celui des verbes de correction, pas le
  total des formes.

Un motif de detection se valide par ses faux negatifs : chaque test negatif
ci-dessous nomme une forme que l'organe doit **laisser passer**.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import list_scope_swallowed_issues as organ  # noqa: E402


# --- parse_subject : ce que la forme avaleuse attrape ------------------------


def test_parse_subject_scope_simple():
    assert organ.parse_subject("Fix(ci,#22937): vague 2") == ("Fix", 22937)


def test_parse_subject_verbe_minuscule():
    assert organ.parse_subject("fix(lean,#11508): preuve restauree") == ("fix", 11508)


def test_parse_subject_numero_vient_apres_la_derniere_virgule():
    # Les chiffres du scope ne doivent pas etre pris pour le numero d'issue.
    assert organ.parse_subject("Fix(ANALYSE-04,#21027): calcul") == ("Fix", 21027)


def test_parse_subject_scope_a_plusieurs_virgules():
    assert organ.parse_subject("Fix(ci,tooling,#21488): gate") == ("Fix", 21488)


def test_parse_subject_verbe_compose():
    assert organ.parse_subject("Re-exec(notebook,#22804): basenames") == ("Re-exec", 22804)


def test_parse_subject_sans_scope_ne_matche_pas():
    assert organ.parse_subject("Fix: correction diverse") is None


def test_parse_subject_forme_fermante_ne_matche_pas():
    # `Fix #22937:` est justement la forme qui FERME : elle ne doit jamais
    # entrer dans la liste, sinon l'organe inventerait des faux positifs.
    assert organ.parse_subject("Fix #22937: vague 2") is None


def test_parse_subject_merge_ne_matche_pas():
    assert organ.parse_subject("Merge pull request #22937 from jsboige/x") is None


def test_parse_subject_reference_en_fin_de_sujet_ne_matche_pas():
    # `Feat(genai): ... (#22960)` : la reference est hors de la parenthese de
    # scope, c'est la forme correcte et GitHub la voit.
    assert organ.parse_subject("Feat(genai): poster HTML verifiable (#22960)") is None


# --- has_explicit_closing : ce qui a vraiment ferme -------------------------


def test_has_explicit_closing_closes():
    assert organ.has_explicit_closing("body\n\nCloses #22937", 22937) is True


def test_has_explicit_closing_fixes_avec_deux_points():
    assert organ.has_explicit_closing("Fixes: #22937", 22937) is True


def test_has_explicit_closing_sur_une_autre_issue_ne_compte_pas():
    assert organ.has_explicit_closing("Closes #11111", 22937) is False


def test_has_explicit_closing_see_ne_ferme_pas():
    assert organ.has_explicit_closing("See #22937", 22937) is False


def test_has_explicit_closing_forme_avaleuse_ne_ferme_pas():
    # Le mot-cle est suivi d'une parenthese, pas d'une reference : c'est le
    # defaut meme que l'organe mesure, il ne doit pas s'auto-exclure.
    assert organ.has_explicit_closing("Fix(ci,#22937): vague 2", 22937) is False


def test_has_explicit_closing_prefixe_ne_matche_pas():
    # `Hotfix #22937` ne doit pas etre lu comme le mot-cle `fix`.
    assert organ.has_explicit_closing("Hotfix #22937", 22937) is False


def test_has_explicit_closing_numero_plus_long_ne_matche_pas():
    assert organ.has_explicit_closing("Closes #229371", 22937) is False


# --- collect_swallowed : le croisement --------------------------------------


def _commits(*rows: tuple[str, str, str]) -> list[tuple[str, str, str]]:
    return list(rows)


def test_collect_retient_un_couple_issue_ouverte_plus_correction():
    commits = _commits(("a" * 40, "Fix(ci,#11044): correctif", ""))
    out = organ.collect_swallowed(commits, {11044})
    assert len(out) == 1
    assert out[0].number == 11044
    assert out[0].commit == "a" * 10
    assert out[0].verb == "Fix"
    assert out[0].is_correction is True


def test_collect_ignore_une_issue_fermee():
    commits = _commits(("a" * 40, "Fix(ci,#11044): correctif", ""))
    assert organ.collect_swallowed(commits, set()) == []


def test_collect_ignore_un_couple_deja_ferme_par_le_corps():
    commits = _commits(("a" * 40, "Fix(ci,#11044): correctif", "Closes #11044"))
    assert organ.collect_swallowed(commits, {11044}) == []


def test_collect_ignore_une_forme_non_corrective_par_defaut():
    commits = _commits(("a" * 40, "Add(guard,#22291): organe", ""))
    assert organ.collect_swallowed(commits, {22291}) == []


def test_collect_all_forms_inclut_les_verbes_non_correctifs():
    commits = _commits(("a" * 40, "Add(guard,#22291): organe", ""))
    out = organ.collect_swallowed(commits, {22291}, correction_only=False)
    assert [i.number for i in out] == [22291]
    assert out[0].is_correction is False


def test_collect_deduplique_par_issue_en_gardant_le_commit_le_plus_recent():
    commits = _commits(
        ("b" * 40, "Fix(ci,#11044): second correctif", ""),
        ("a" * 40, "Fix(ci,#11044): premier correctif", ""),
    )
    out = organ.collect_swallowed(commits, {11044})
    assert len(out) == 1
    assert out[0].commit == "b" * 10


def test_collect_rend_la_liste_vide_sur_un_corpus_sans_forme_avaleuse():
    commits = _commits(
        ("a" * 40, "Fix: correctif sans scope", ""),
        ("b" * 40, "Fix #11044: forme fermante", ""),
        ("c" * 40, "Feat(genai): poster (#22960)", ""),
    )
    assert organ.collect_swallowed(commits, {11044, 22960}) == []


# --- count_all_forms : la ligne discriminante -------------------------------


def test_count_all_forms_separe_total_et_corrections():
    commits = _commits(
        ("a" * 40, "Fix(ci,#1): x", ""),
        ("b" * 40, "Add(guard,#2): y", ""),
        ("c" * 40, "Fix(ci,#1): doublon", ""),
    )
    every, corrections = organ.count_all_forms(commits)
    assert (every, corrections) == (2, 1)


# --- read_commits : le format de sortie de git log --------------------------


def test_read_commits_parse_le_format_avec_corps_multiligne(monkeypatch):
    raw = (
        "a" * 40 + organ.FIELD_SEP + "Fix(ci,#1): sujet" + organ.FIELD_SEP + "ligne 1\nligne 2" + organ.RECORD_SEP
        + "b" * 40 + organ.FIELD_SEP + "Add(x,#2): autre" + organ.FIELD_SEP + organ.RECORD_SEP
    )
    monkeypatch.setattr(organ, "_run", lambda cmd: raw)
    commits = organ.read_commits("origin/main", 10)
    assert len(commits) == 2
    assert commits[0][1] == "Fix(ci,#1): sujet"
    assert "ligne 2" in commits[0][2]
    assert commits[1][2] == ""


# --- main : lister n'est pas rougir -----------------------------------------


def _stub_inputs(monkeypatch, commits, open_numbers):
    monkeypatch.setattr(organ, "read_commits", lambda ref, limit: commits)
    monkeypatch.setattr(organ, "read_open_issues", lambda repo, limit: open_numbers)


def test_main_rend_zero_meme_avec_des_trouvailles(monkeypatch, capsys):
    _stub_inputs(monkeypatch, [("a" * 40, "Fix(ci,#1): x", "")], {1})
    assert organ.main([]) == 0
    assert "total=1" in capsys.readouterr().out


def test_main_fail_on_findings_rend_un(monkeypatch):
    _stub_inputs(monkeypatch, [("a" * 40, "Fix(ci,#1): x", "")], {1})
    assert organ.main(["--fail-on-findings"]) == 1


def test_main_fail_on_findings_rend_zero_sur_liste_vide(monkeypatch):
    _stub_inputs(monkeypatch, [], set())
    assert organ.main(["--fail-on-findings"]) == 0


def test_main_json_est_du_json_valide(monkeypatch, capsys):
    import json

    _stub_inputs(monkeypatch, [("a" * 40, "Fix(ci,#11044): x", "")], {11044})
    organ.main(["--json"])
    payload = json.loads(capsys.readouterr().out)
    assert payload["total"] == 1
    assert payload["issues"][0]["number"] == 11044
    assert payload["correction_only"] is True


def test_main_rend_deux_si_l_organe_est_injoignable(monkeypatch, capsys):
    def boom(ref, limit):
        raise RuntimeError("gh absent")

    monkeypatch.setattr(organ, "read_commits", boom)
    monkeypatch.setattr(organ, "read_open_issues", lambda repo, limit: set())
    assert organ.main([]) == 2
    assert "[ERREUR]" in capsys.readouterr().err


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
