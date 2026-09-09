"""Tests for scripts/notebook_tools/detect_notebook_plan_loss.py (#14532).

Couvre les 4 scenarios d'acceptation + le comportement de la recherche de
substance en 3 passes :
  - section absente ET substance introuvable -> LOST_SECTION (signal)
  - retrogradation titre -> bold inline -> SUBSTANCE_FOUND_INLINE_BOLD (PAS de signal)
  - section renommee / absorbee -> SUBSTANCE_FOUND_TOKEN_MATCH (PAS de signal)
  - titre re-accentue / re-numerote -> INVISIBLE apres normalisation (PAS de signal)
  - STRUCTURE_DRIFT : nombre de cellules markdown different (PAS de comparaison
    elementaire, design #1 #8655 transpose)
  - NEW_FILE exempt (rc=0)
  - justification par-section via body PR (--pr-body-file) : leve le finding
    LOST_SECTION correspondant
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import detect_notebook_plan_loss as dpl  # noqa: E402


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
def _md(src, cell_id=None):
    """Cellule markdown avec source (str ou list) et id nbformat optionnel."""
    cell = {"cell_type": "markdown", "source": src, "metadata": {}}
    if cell_id is not None:
        cell["id"] = cell_id
    return cell


def _nb(*cells):
    return {"cells": list(cells), "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _write_nb(path: Path, nb: dict) -> None:
    path.write_text(json.dumps(nb, ensure_ascii=False, indent=2), encoding="utf-8")


# ---------------------------------------------------------------------------
# 1. Normalisation des titres
# ---------------------------------------------------------------------------
class TestNormalize:
    def test_accent_stripping(self):
        # `Prerequis` et `Prérequis` normalisent identiquement
        # (sinon 10/15 sur-accusations sur #14117).
        assert dpl._normalize_heading("Prérequis") == dpl._normalize_heading("Prerequis")
        assert dpl._normalize_heading("Données") == dpl._normalize_heading("Donnees")

    def test_numeral_prefix_stripped(self):
        # Une renumerotation `1.` -> `2.` ne doit pas fausser le diff de plan.
        # NB : la fonction prend le TEXTE du titre (sans `##`), c'est-a-dire
        # exactement ce qu'extract_headings() lui passe en pratique.
        assert dpl._normalize_heading("1. Installation et imports") == \
            dpl._normalize_heading("2. Installation et imports")
        assert dpl._normalize_heading("3.1. Sub section") == \
            dpl._normalize_heading("5.2. Sub section")

    def test_case_insensitive(self):
        assert dpl._normalize_heading("Objectifs") == dpl._normalize_heading("OBJECTIFS")
        assert dpl._normalize_heading("Objectifs") == dpl._normalize_heading("objectifs")

    def test_trailing_punctuation_stripped(self):
        assert dpl._normalize_heading("Quand utiliser X ?") == \
            dpl._normalize_heading("Quand utiliser X")
        assert dpl._normalize_heading("Section A.") == \
            dpl._normalize_heading("Section A")

    def test_whitespace_collapsed(self):
        assert dpl._normalize_heading("Foo  bar") == dpl._normalize_heading("foo bar")
        assert dpl._normalize_heading("  Foo  ") == dpl._normalize_heading("Foo")

    def test_invalid_empty_input(self):
        assert dpl._normalize_heading("") == ""
        assert dpl._normalize_heading("   ") == ""


# ---------------------------------------------------------------------------
# 2. Tokens significatifs
# ---------------------------------------------------------------------------
class TestTokens:
    def test_short_tokens_excluded(self):
        # Tokens < 4 caracteres ne comptent pas (sinon `de` / `la` / `les`
        # provoqueraient des faux positifs partout dans le head).
        toks = dpl._significant_tokens("Objectifs de la seance")
        # "objectifs", "seance" -- pas "de" ni "la"
        assert "objectifs" in toks
        assert "seance" in toks
        assert "de" not in toks
        assert "la" not in toks

    def test_empty_norm_yields_no_tokens(self):
        assert dpl._significant_tokens("") == set()
        assert dpl._significant_tokens("a") == set()
        assert dpl._significant_tokens("ab") == set()

    def test_unicode_tokens_stable(self):
        # Les accents sont strippes AVANT le tokenize (NFKD puis strip
        # combining) -- un titre avec caracteres composes produit le meme
        # ensemble de tokens que sa version ASCII-isee.
        toks_uni = dpl._significant_tokens("Prérequis opérationnels")
        toks_ascii = dpl._significant_tokens("Prerequis operationnels")
        assert toks_uni == toks_ascii


# ---------------------------------------------------------------------------
# 3. Extraction des headings et bold inline
# ---------------------------------------------------------------------------
class TestExtract:
    def test_headings_picks_h1_to_h6(self):
        nb = _nb(
            _md("# H1 titre\n\nSuite\n"),
            _md("## H2 titre\n\nSuite\n"),
            _md("### H3 titre\n"),
            _md("#### H4 titre\n"),
            _md("Pas un titre\n"),
        )
        h = dpl.extract_headings(nb)
        assert len(h) == 4
        assert [t[0] for t in h] == [0, 1, 2, 3]  # cell_idx
        assert [t[1] for t in h] == [1, 2, 3, 4]  # level
        assert h[0][2] == "H1 titre"

    def test_bold_inline_extraction(self):
        nb = _nb(_md(
            "Texte introductif.\n\n"
            "**Prerequis** : SW-3 Graph Operations.\n\n"
            "**Objectifs d'apprentissage** :\n\n"
            "- Item 1\n"
        ))
        bold = dpl._extract_bold_inline(nb)
        # Doit contenir les 2 formes normalisees (lowercase, NFKD accents
        # retires, whitespace collapse, ponctuation terminale strippee).
        assert "prerequis : sw-3 graph operations" in bold
        # La ponctuation terminale (les 2-points) est strippee par
        # ``_normalize_for_search`` -- on accepte le titre bold nu OU la
        # version prefixee par `:`.
        assert "objectifs d'apprentissage" in bold


# ---------------------------------------------------------------------------
# 4. Substance found in 3 passes (le coeur du predicat anti-FP)
# ---------------------------------------------------------------------------
class TestSubstance:
    def test_title_exact_match(self):
        # Passe 1 : titre normalise present dans l'ensemble head.
        found, mode = dpl._substance_present_heuristic(
            "objectifs d'apprentissage",
            head_headings_norm={"objectifs d'apprentissage", "introduction"},
            head_bold_norm=set(),
            head_text_norm="quelque part",
        )
        assert found is True
        assert mode == "SUBSTANCE_FOUND_RENAMED_SECTION"

    def test_bold_inline_match(self):
        # Passe 2 : titre retrograde en bold inline (`**Prerequis** : ...`).
        found, mode = dpl._substance_present_heuristic(
            "prerequis",
            head_headings_norm={"preambule"},
            head_bold_norm={"prerequis : sw-3 graph operations"},
            head_text_norm="",
        )
        assert found is True
        assert mode == "SUBSTANCE_FOUND_INLINE_BOLD"

    def test_token_match_absorption(self):
        # Passe 3 : un token significatif survit dans le head apres absorption.
        # C'est le cas de `### Quand utiliser quel endpoint ?` qui disparait
        # dans #14117 mais dont `endpoint` survit dans le tableau de comparaison.
        found, mode = dpl._substance_present_heuristic(
            "quand utiliser quel endpoint",
            head_headings_norm={"interpretation : dbpedia vs wikidata"},
            head_bold_norm=set(),
            head_text_norm="endpoint et service sont les deux termes comparés",
        )
        assert found is True
        assert mode == "SUBSTANCE_FOUND_TOKEN_MATCH"

    def test_no_substance_found(self):
        # Aucun match dans les 3 passes -> finding LOST_SECTION en aval.
        found, mode = dpl._substance_present_heuristic(
            "duree estimee 50 minutes",
            head_headings_norm={"introduction", "conclusion"},
            head_bold_norm={"navigation", "prerequis"},
            head_text_norm="le notebook fait 50 lignes de code",
        )
        # "50" et "minutes" sont < 4 chars -> aucun token significatif.
        # "duree" est 5 chars mais absent du head text.
        assert found is False
        assert mode is None

    def test_single_significant_token_survives(self):
        # Un SEUL token significatif suffit (le predicat ne demande pas tous).
        found, mode = dpl._substance_present_heuristic(
            "complexite algorithmique",
            head_headings_norm=set(),
            head_bold_norm=set(),
            head_text_norm="la complexite reste lineaire en pratique",
        )
        # `complexite` (11 chars) survit, `algorithmique` aussi.
        assert found is True
        assert mode == "SUBSTANCE_FOUND_TOKEN_MATCH"


# ---------------------------------------------------------------------------
# 5. scan_notebook : scenarios d'acceptation bout-en-bout
# ---------------------------------------------------------------------------
class TestScan:
    def test_no_change_no_finding(self, tmp_path: Path):
        # Plan identite entre base et head -> 0 finding. On utilise deux refs
        # git identiques pour court-circuiter le check structure -- le but
        # est uniquement de verifier que le pipeline n'invente pas de findings
        # quand rien ne change. NB : scan_notebook prend par defaut head_ref=None
        # (= working tree), ce qui teste le chemin de lecture disque ; ici on
        # donne HEAD explicite pour eviter un check working-tree vs git.
        nb_dict = _nb(
            _md("# H1 titre\n\nSuite.\n"),
            _md("## H2 sous-titre\n\nSuite.\n"),
        )
        p = tmp_path / "stable.ipynb"
        _write_nb(p, nb_dict)
        import subprocess
        subprocess.run(["git", "-C", str(tmp_path), "init", "-q"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.email", "t@t.t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.name", "t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "add", "stable.ipynb"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "commit", "-m", "b", "-q"], check=True)

        result = dpl.scan_notebook(p, base_ref="HEAD", head_ref="HEAD")
        assert "error" not in result
        assert result["findings"] == []

    def test_section_lost_raises_finding(self, tmp_path: Path):
        # Cas du ticket : `### Duree estimee : 50 minutes` a la base,
        # absent du head sans substance ailleurs -> LOST_SECTION.
        # Note : on garde le MEME nombre de cellules markdown entre base et
        # head sinon STRUCTURE_DRIFT bloque la passe substance (par design --
        # une difference de cellules = impossible de garantir une
        # comparaison ENSEMBLE).
        # On choisit un head dont AUCUN token significatif de `duree estimee
        # 50 minutes` ne survit (les seuls tokens >=4 chars du titre sont
        # `duree` et `estimee` -- le head ne contient ni l'un ni l'autre).
        nb_base = _nb(
            _md("# Plan\n\n"),
            _md("## Introduction\n\nCorps.\n\n### Duree estimee : 50 minutes\n\nSuite.\n"),
        )
        nb_head = _nb(
            _md("# Plan\n\n"),
            _md("## Introduction\n\nCorps.\n\n### Conclusion rapide\n\n"),
        )
        import subprocess
        p = tmp_path / "lost.ipynb"
        _write_nb(p, nb_base)
        subprocess.run(["git", "-C", str(tmp_path), "init", "-q"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.email", "t@t.t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.name", "t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "add", "lost.ipynb"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "commit", "-m", "base", "-q"], check=True)
        # HEAD pointe maintenant sur la version base ; on ecrit la version
        # head SUR DISQUE pour tester working_tree vs HEAD.
        _write_nb(p, nb_head)

        result = dpl.scan_notebook(p, base_ref="HEAD", head_ref=None)
        assert "error" not in result, result.get("error")
        assert result["stats"]["cell_count_stable"] is True
        kinds = [f["kind"] for f in result["findings"]]
        assert "LOST_SECTION" in kinds
        lost = next(f for f in result["findings"] if f["kind"] == "LOST_SECTION")
        # Le titre normalise doit etre celui du titre de base.
        assert "duree" in lost["base_heading_normalized"]
        assert "estimee" in lost["base_heading_normalized"]
        # NB : le `_normalize_heading` ne strip PAS les numerals internes
        # (`50`) ni les tokens >= 4 chars (`minutes`), on accepte leur
        # presence dans le titre normalise -- l'important est que la passe
        # 3 (token significatif) ne retrouve AUCUN de ces tokens dans le
        # head (cf. design du test ci-dessus).

    def test_retrogradation_to_inline_bold_no_finding(self, tmp_path: Path):
        # `### Prerequis` a la base, absent du head mais conserve en inline bold
        # `**Prerequis** : SW-3 Graph Operations.` -> SUBSTANCE_FOUND_INLINE_BOLD,
        # PAS de LOST_SECTION. Meme nombre de cellules markdown des deux cotes.
        nb_base = _nb(
            _md("# Plan\n\n"),
            _md("### Prerequis\n\nSW-3 Graph Operations.\n"),
        )
        nb_head = _nb(
            _md("# Plan\n\n"),
            _md("**Prerequis** : SW-3 Graph Operations.\n\n"),
        )
        import subprocess
        p = tmp_path / "retro.ipynb"
        _write_nb(p, nb_base)
        subprocess.run(["git", "-C", str(tmp_path), "init", "-q"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.email", "t@t.t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.name", "t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "add", "retro.ipynb"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "commit", "-m", "b", "-q"], check=True)
        _write_nb(p, nb_head)

        result = dpl.scan_notebook(p, base_ref="HEAD", head_ref=None)
        assert "error" not in result
        kinds = [f["kind"] for f in result["findings"]]
        assert "LOST_SECTION" not in kinds
        # Au moins un SUBSTANCE_FOUND via bold inline.
        found = [f for f in result["findings"] if f["kind"] == "SUBSTANCE_FOUND"]
        assert len(found) >= 1
        assert any(f["mode"] == "SUBSTANCE_FOUND_INLINE_BOLD" for f in found)

    def test_accent_normalization_no_finding(self, tmp_path: Path):
        # Une re-accentuation honnete `Prerequis` -> `Prérequis` ne doit PAS
        # lever de LOST_SECTION (la normalisation NFKD absorbe).
        nb_base = _nb(_md("# Plan\n\n## Prerequis\n\nTexte.\n"))
        nb_head = _nb(_md("# Plan\n\n## Prérequis\n\nTexte.\n"))
        import subprocess
        p = tmp_path / "acc.ipynb"
        _write_nb(p, nb_base)
        subprocess.run(["git", "-C", str(tmp_path), "init", "-q"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.email", "t@t.t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.name", "t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "add", "acc.ipynb"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "commit", "-m", "b", "-q"], check=True)
        _write_nb(p, nb_head)

        result = dpl.scan_notebook(p, base_ref="HEAD", head_ref=None)
        assert "error" not in result
        kinds = [f["kind"] for f in result["findings"]]
        # `Prérequis` re-accentue normalise -> identite -> 0 finding.
        assert kinds == []

    def test_structure_drift(self, tmp_path: Path):
        # Nombre de cellules markdown different entre base et head ->
        # STRUCTURE_DRIFT (PAS de comparaison elementaire).
        nb_base = _nb(_md("# Plan\n\n"), _md("## Section A\n\n"), _md("## Section B\n\n"))
        nb_head = _nb(_md("# Plan\n\n"), _md("## Section A\n\n"))
        import subprocess
        p = tmp_path / "sd.ipynb"
        _write_nb(p, nb_base)
        subprocess.run(["git", "-C", str(tmp_path), "init", "-q"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.email", "t@t.t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.name", "t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "add", "sd.ipynb"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "commit", "-m", "b", "-q"], check=True)
        _write_nb(p, nb_head)

        result = dpl.scan_notebook(p, base_ref="HEAD", head_ref=None)
        assert "error" not in result
        kinds = [f["kind"] for f in result["findings"]]
        assert "STRUCTURE_DRIFT" in kinds

    def test_new_file_exempt(self, tmp_path: Path):
        # Notebook NOUVEAU (absent de la base) -> exempt (rien a perdre, tout
        # est ajout) : 0 finding et stats COMPLETES. C'est le chemin qui
        # crashe en KeyError 'base_md_cells' avant #15147 -- les renommages
        # (MGS-7 -> MGS-07) sont vus comme des fichiers nouveaux par le gate.
        import subprocess
        other = tmp_path / "autre.ipynb"
        _write_nb(other, _nb(_md("# Autre\n\n")))
        subprocess.run(["git", "-C", str(tmp_path), "init", "-q"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.email", "t@t.t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.name", "t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "add", "autre.ipynb"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "commit", "-m", "b", "-q"], check=True)

        p = tmp_path / "nouveau.ipynb"
        _write_nb(p, _nb(_md("# Plan nouveau\n\n### Duree estimee : 50 minutes\n\n")))
        result = dpl.scan_notebook(p, base_ref="HEAD", head_ref=None)
        assert "error" not in result, result.get("error")
        assert result["new_file"] is True
        assert result["findings"] == []
        st = result["stats"]
        assert st["base_md_cells"] == 0
        assert st["head_md_cells"] == 1
        assert st["cell_count_stable"] is False
        assert st["base_headings"] == 0
        assert st["head_headings"] == 2


# ---------------------------------------------------------------------------
# 6. Justification par-section depuis le body PR
# ---------------------------------------------------------------------------
class TestBodyJustification:
    def test_marker_normalizes(self):
        # Le marker est compare a la forme NORMALISEE du titre de plan.
        justified = dpl._parse_pr_body_markers(
            "plan-loss: section assumee -- perdu.ipynb section: Duree estimee 50 minutes : "
            "synchronisee avec le code cell runtime",
            Path("perdu.ipynb"),
        )
        # On normalise cote garde (`duree estimee 50 minutes`), et le titre
        # dans le marker subit la meme normalisation.
        assert "duree estimee 50 minutes" in justified

    def test_em_dash_accepted(self):
        # Un editeur intelligent transpose `--` en em-dash -- la regex accepte les deux.
        justified = dpl._parse_pr_body_markers(
            "plan-loss: section assumée — perdu.ipynb section: Duree estimee 50 minutes : OK",
            Path("perdu.ipynb"),
        )
        assert "duree estimee 50 minutes" in justified

    def test_marker_different_notebook_inert(self):
        # Un marker visant un AUTRE notebook n'affecte pas le verdict du notre.
        justified = dpl._parse_pr_body_markers(
            "plan-loss: section assumee -- autre.ipynb section: Titre : raison",
            Path("perdu.ipynb"),
        )
        assert justified == set()

    def test_apply_body_justifications_substitutes(self):
        # Un finding LOST_SECTION sur un titre normalise couvert par le body
        # est converti en LOST_SECTION_JUSTIFIED_BY_BODY (meme politique que
        # detect_md_content_loss.py #13491).
        findings = [
            {"kind": "LOST_SECTION", "base_heading": "Duree", "base_heading_normalized": "duree"},
            {"kind": "LOST_SECTION", "base_heading": "Autre", "base_heading_normalized": "autre"},
        ]
        out = dpl._apply_body_justifications(findings, {"duree"})
        kinds = [f["kind"] for f in out]
        assert "LOST_SECTION_JUSTIFIED_BY_BODY" in kinds
        assert "LOST_SECTION" in kinds  # l'autre reste non justifiee


# ---------------------------------------------------------------------------
# 7. Main -- rc=0/1/2 sur pipeline complet
# ---------------------------------------------------------------------------
class TestMain:
    def test_clean_exits_zero(self, tmp_path: Path, monkeypatch, capsys):
        # Plan identique -> rc=0.
        import subprocess
        nb_dict = _nb(_md("# Plan\n\n## Section\n\n"))
        p = tmp_path / "clean.ipynb"
        _write_nb(p, nb_dict)
        subprocess.run(["git", "-C", str(tmp_path), "init", "-q"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.email", "t@t.t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.name", "t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "add", "clean.ipynb"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "commit", "-m", "b", "-q"], check=True)
        rc = dpl.main([str(p), "--base", "HEAD", "--check"])
        captured = capsys.readouterr()
        assert rc == 0, f"expected rc=0, got stdout={captured.out!r}, stderr={captured.err!r}"

    def test_justified_by_body_exits_zero(self, tmp_path: Path):
        # LOST_SECTION + body marker couvrant -> rc=0 (le marker leve).
        import subprocess
        p = tmp_path / "j.ipynb"
        nb_base = _nb(_md("# Plan\n\n### Duree est longue\n\n"))
        nb_head = _nb(_md("# Plan\n\n"))
        _write_nb(p, nb_base)
        subprocess.run(["git", "-C", str(tmp_path), "init", "-q"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.email", "t@t.t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.name", "t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "add", "j.ipynb"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "commit", "-m", "b", "-q"], check=True)
        _write_nb(p, nb_head)

        body_path = tmp_path / "pr_body.md"
        body_path.write_text(
            "plan-loss: section assumee -- j.ipynb section: Duree est longue : assumee\n",
            encoding="utf-8",
        )
        # On lance main, on capture stdout/stderr.
        rc = dpl.main([str(p), "--base", "HEAD", "--check", "--pr-body-file", str(body_path)])
        # Le marker couvre `duree est longue` (normalise) ; le finding
        # correspondant est JUSTIFIED -> pas bloquant -> rc=0.
        assert rc == 0, f"rc={rc}, expected 0 (justified)"

    def test_unjustified_lost_exits_one(self, tmp_path: Path):
        # LOST_SECTION SANS body marker -> rc=1.
        import subprocess
        p = tmp_path / "u.ipynb"
        nb_base = _nb(_md("# Plan\n\n### Duree est longue\n\n"))
        nb_head = _nb(_md("# Plan\n\n"))
        _write_nb(p, nb_base)
        subprocess.run(["git", "-C", str(tmp_path), "init", "-q"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.email", "t@t.t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.name", "t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "add", "u.ipynb"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "commit", "-m", "b", "-q"], check=True)
        _write_nb(p, nb_head)
        rc = dpl.main([str(p), "--base", "HEAD", "--check"])
        assert rc == 1

    def test_new_file_text_mode_exits_zero(self, tmp_path: Path, capsys):
        # new_file en mode TEXTE : la ligne [STATS] indexe
        # st['base_md_cells'] -- c'etait le KeyError de #15147 (le gate
        # lit rc=1 comme une perte de plan). Fichier PRESENT au disque,
        # ABSENT a la base -> rc=0, banniere [NEW FILE], [STATS] rendu.
        import subprocess
        other = tmp_path / "autre.ipynb"
        _write_nb(other, _nb(_md("# Autre\n\n")))
        subprocess.run(["git", "-C", str(tmp_path), "init", "-q"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.email", "t@t.t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.name", "t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "add", "autre.ipynb"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "commit", "-m", "b", "-q"], check=True)

        p = tmp_path / "nouveau.ipynb"
        _write_nb(p, _nb(_md("# Plan nouveau\n\n### Duree estimee : 50 minutes\n\n")))
        rc = dpl.main([str(p), "--base", "HEAD", "--check"])
        captured = capsys.readouterr()
        assert rc == 0, f"rc={rc}, stderr={captured.err!r}"
        assert "[NEW FILE]" in captured.out
        assert "md_cells base=0 head=1 stable=False" in captured.out

    def test_new_file_json_mode_exits_zero(self, tmp_path: Path, capsys):
        # new_file en mode JSON : sortie machine parseable, new_file=True,
        # stats avec les memes cles que les branches comparees (celles que
        # les consommateurs indexent, ex. le render texte ligne ci-dessus).
        import json
        import subprocess
        other = tmp_path / "autre.ipynb"
        _write_nb(other, _nb(_md("# Autre\n\n")))
        subprocess.run(["git", "-C", str(tmp_path), "init", "-q"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.email", "t@t.t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "config", "user.name", "t"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "add", "autre.ipynb"], check=True)
        subprocess.run(["git", "-C", str(tmp_path), "commit", "-m", "b", "-q"], check=True)

        p = tmp_path / "nouveau.ipynb"
        _write_nb(p, _nb(_md("# Plan nouveau\n\n### Duree estimee : 50 minutes\n\n")))
        rc = dpl.main([str(p), "--base", "HEAD", "--json"])
        captured = capsys.readouterr()
        assert rc == 0, f"rc={rc}, stderr={captured.err!r}"
        result = json.loads(captured.out)
        assert result["new_file"] is True
        assert result["findings"] == []
        assert result["stats"]["base_md_cells"] == 0
        assert result["stats"]["head_md_cells"] == 1
        assert result["stats"]["cell_count_stable"] is False
