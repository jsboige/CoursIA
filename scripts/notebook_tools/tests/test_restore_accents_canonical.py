"""Tests for scripts/notebook_tools/restore_accents_canonical.py — cure canonique #2876.

Verifie les 4 bright-lines defense-by-construction du registre #2876 (markdown-only
STRICT, adjudication ai-01 17/07 + raffinement link-target 18/07) :
  1. markdown-cell-source ONLY (code cells intouches)
  2. skip link targets ]( ... ) (defect #7135/#7145 : lien casse)
  3. skip code (consequence de 1)
  4. skip outputs / execution_count (seule la cle source est re-ecrite)
+ preservation casse + dictionnaire conservateur (non-ambigu) + structure nbformat.
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import restore_accents_canonical as rac  # noqa: E402


def _nb(cells):
    """Notebook synthetique : cells = liste de (cell_type, source_str)."""
    return {"cells": [{"cell_type": t, "source": s, "metadata": {}} for (t, s) in cells],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


# ---------------------------------------------------------------------------
# 1. markdown-cell-source ONLY : les cellules code sont intouches
# ---------------------------------------------------------------------------
class TestMarkdownOnly:
    def test_code_cell_never_touched(self, tmp_path):
        # un identifiant accentuable 'parametre' dans une cellule CODE ne doit
        # JAMAIS etre cure (defect #7094/#7143/#7154 : over-reach code).
        nb = _nb([("code", "parametre = 1\nprint(parametre)"),
                  ("markdown", "Le parametre est important.")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        res = rac.cure_notebook(p, write=True)
        cured = json.loads(p.read_text(encoding="utf-8"))
        # la cellule code reste byte-identique
        assert cured["cells"][0]["source"] == "parametre = 1\nprint(parametre)"
        # la cellule markdown est curee
        assert "paramètre" in cured["cells"][1]["source"]
        assert res["cures"] == 1

    def test_outputs_and_execution_count_preserved(self, tmp_path):
        # seule la cle 'source' d'une cellule markdown est re-ecrite ; une cellule
        # code avoisinante garde ses outputs + execution_count intacts (defect
        # #7105/#7124/#7132 : re-exec / regen outputs).
        nb = {"cells": [
            {"cell_type": "code", "source": "x = 1", "outputs": [{"data": "KEEP"}],
             "execution_count": 42, "metadata": {}},
            {"cell_type": "markdown", "source": "Le resultat est pret."},
        ], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rac.cure_notebook(p, write=True)
        cured = json.loads(p.read_text(encoding="utf-8"))
        assert cured["cells"][0]["outputs"] == [{"data": "KEEP"}]
        assert cured["cells"][0]["execution_count"] == 42
        assert cured["cells"][0]["source"] == "x = 1"  # code intact


# ---------------------------------------------------------------------------
# 2. skip link targets : defect #7135/#7145 (lien casse)
# ---------------------------------------------------------------------------
class TestLinkTargetProtection:
    def test_link_target_not_accented(self):
        # la cible du lien doit matcher le fichier reel sur disque (sans accent).
        line = "Voir [le modele de selection](Infer-10-Model-Selection.ipynb)."
        cured, n = rac._cure_line(line)
        assert "](Infer-10-Model-Selection.ipynb)" in cured  # cible intacte
        assert "sélection.ipynb" not in cured  # cible NON accentuee
        assert "modèle" in cured  # prose accented

    def test_multiple_links_protected(self):
        line = ("| [Model-Selection](Model-Selection.ipynb) | "
                "[Modeles-Hierarchiques](Modeles-Hierarchiques.ipynb) |")
        cured, n = rac._cure_line(line)
        assert "](Model-Selection.ipynb)" in cured
        assert "](Modeles-Hierarchiques.ipynb)" in cured
        assert "sélection.ipynb" not in cured and "modèles-Hierarchiques.ipynb" not in cured

    def test_image_src_protected(self):
        # ![alt](src.png) : la source image aussi
        line = "![schema du modele de parametres](assets/parametres.png)"
        cured, n = rac._cure_line(line)
        assert "](assets/parametres.png)" in cured  # src intact
        assert "parametres.png" in cured  # NON accente

    def test_link_with_title_protected(self):
        line = '[modele](Model-Selection.ipynb "titre du modele")'
        cured, n = rac._cure_line(line)
        # le ](...) "title" ) entier est un span ; la cible reste intacte
        assert "Model-Selection.ipynb" in cured


# ---------------------------------------------------------------------------
# 3. preservation casse + dictionnaire conservateur
# ---------------------------------------------------------------------------
class TestCaseAndDictionary:
    def test_capitalized_preserved(self):
        cured, n = rac._cure_line("Le Parametre general.")
        assert "Paramètre" in cured  # majuscule preservee

    def test_all_caps_preserved(self):
        cured, n = rac._cure_line("Les PARAMETRES sont la.")
        # tout-majuscule preserve
        assert "PARAMÈTRES" in cured

    def test_ambiguous_words_not_cured(self):
        # 'a', 'ou', 'la', 'complete' sont des mots FR valides sans accent
        # (a/ou/la) ou des mots EN (complete) -> le dictionnaire conservateur ne
        # les inclu PAS (restauration ambigue). On verifie qu'ils ne sont pas
        # dans le dictionnaire. (NB: 'tres' EST inclus car le mot FR reel = très,
        # la forme 'tres' n'est pas un mot FR valide.)
        for w in ("a", "ou", "la", "complete", "valeur", "the"):
            assert w not in rac.ACCENT_PAIRS, "{} should not be in dictionary".format(w)

    def test_word_boundary_not_partial(self):
        # 'parametrez' (verbe, pas dans le dict) ne doit pas matcher 'parametre'
        cured, n = rac._cure_line("parametrez la valeur")
        assert n == 0  # pas de cure partielle


# ---------------------------------------------------------------------------
# 4. structure nbformat preservee (list source + str source)
# ---------------------------------------------------------------------------
class TestNbformatStructure:
    def test_list_source_preserved_as_list(self, tmp_path):
        nb = {"cells": [
            {"cell_type": "markdown", "source": ["Le parametre\n", "est utile."], "metadata": {}}
        ], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        res = rac.cure_notebook(p, write=True)
        cured = json.loads(p.read_text(encoding="utf-8"))
        src = cured["cells"][0]["source"]
        assert isinstance(src, list)  # type preserve
        assert len(src) == 2  # nombre de chunks preserve
        assert "paramètre" in "".join(src)

    def test_paragraph_break_preserved_list_source(self, tmp_path):
        # Regression : bug blank-line collapse firsthand sur Infer-14 (28/33 cellules,
        # po-2024 c.634). Un chunk standalone "\n" (separateur de paragraphe) ne doit
        # JAMAIS etre absorbe par un join->split->re-chunk. La cure per-chunk preserve
        # byte-pour-byte le paragraph break markdown ("\n\n").
        nb = {"cells": [
            {"cell_type": "markdown",
             "source": ["# Infer : Systeme de Classement\n", "\n", "**Serie** : Parametres\n"],
             "metadata": {}}
        ], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rac.cure_notebook(p, write=True)
        cured = json.loads(p.read_text(encoding="utf-8"))
        src = cured["cells"][0]["source"]
        joined = "".join(src) if isinstance(src, list) else src
        # le paragraphe break \n\n entre le titre H1 et le bloc Serie doit survivre
        assert "\n\n" in joined, "paragraph break collapsed by cure"
        # le chunk count doit etre preserve (3 chunks : titre, blank, serie)
        assert isinstance(src, list) and len(src) == 3, f"chunk count drift: {src}"
        # les accents sont quand meme appliques + casse preservee
        assert "Système" in joined and "Paramètres" in joined

    def test_str_source_preserved_as_str(self, tmp_path):
        nb = {"cells": [
            {"cell_type": "markdown", "source": "Le parametre est utile.", "metadata": {}}
        ], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rac.cure_notebook(p, write=True)
        cured = json.loads(p.read_text(encoding="utf-8"))
        assert isinstance(cured["cells"][0]["source"], str)
        assert "paramètre" in cured["cells"][0]["source"]

    def test_idempotent(self, tmp_path):
        # curer 2x = meme resultat que 1x (pas de double-cure)
        nb = _nb([("markdown", "Le parametre et le resultat.")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rac.cure_notebook(p, write=True)
        once = p.read_text(encoding="utf-8")
        rac.cure_notebook(p, write=True)
        twice = p.read_text(encoding="utf-8")
        assert once == twice


# ---------------------------------------------------------------------------
# 5. main() exit codes (--check, --apply, --scope)
# ---------------------------------------------------------------------------
class TestMainExitCodes:
    def test_check_exit_1_when_cures_available(self, tmp_path):
        nb = _nb([("markdown", "Le parametre est pret.")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rc = rac.main([str(p), "--check"])
        assert rc == 1

    def test_check_exit_0_when_clean(self, tmp_path):
        nb = _nb([("markdown", "Le paramètre est prêt.")])  # deja accente
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rc = rac.main([str(p), "--check"])
        assert rc == 0

    def test_apply_and_check_mutually_exclusive(self, tmp_path):
        nb = _nb([("markdown", "parametre")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rc = rac.main([str(p), "--apply", "--check"])
        assert rc == 2

    def test_scope_flags_code_residue(self, tmp_path):
        # mode --scope : une cellule code avec 'parametre' = residue de script ad-hoc
        nb = _nb([("code", "parametre = 1"), ("markdown", "deja accente prêt")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rc = rac.main([str(p), "--check", "--scope"])
        assert rc == 1  # flagge le code residue

    def test_dry_run_does_not_write(self, tmp_path):
        nb = _nb([("markdown", "Le parametre.")])
        p = tmp_path / "nb.ipynb"
        original = json.dumps(nb)
        p.write_text(original, encoding="utf-8")
        rac.main([str(p), "--dry-run"])
        assert p.read_text(encoding="utf-8") == original  # inchange

    def test_apply_writes_and_cures(self, tmp_path):
        nb = _nb([("markdown", "Le parametre.")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rac.main([str(p), "--apply"])
        cured = json.loads(p.read_text(encoding="utf-8"))
        assert "paramètre" in cured["cells"][0]["source"]


# ---------------------------------------------------------------------------
# Adaptateur markdown pur (.md) — decks Slidev, Epic #11508 lot L1.
#
# Chaque test de protection est adosse a un faux positif MESURE en lecture seule
# sur les 18 decks de `slides/` (2026-08-17, detail sur #11508) : la cure notebook
# appliquee telle quelle proposait 979 cures dont 113 structurellement fausses.
# Un test ecrit sans faux positif mesure derriere lui n'est pas dans cette liste.
# ---------------------------------------------------------------------------
def _md(tmp_path, text, name="slides.md"):
    p = tmp_path / name
    p.write_text(text, encoding="utf-8")
    return p


class TestMarkdownFrontmatterProtected:
    """Le faux positif le plus grave : present dans 18 decks sur 18."""

    def test_document_frontmatter_theme_key_untouched(self, tmp_path):
        # `theme:` est la cle de configuration Slidev. L'accentuer casse le deck.
        p = _md(tmp_path, "---\ntheme: ../theme-ia101\n---\n\nUn parametre.\n")
        rac.main([str(p), "--apply"])
        out = p.read_text(encoding="utf-8")
        assert "theme: ../theme-ia101" in out       # cle ET valeur intactes
        assert "thème" not in out
        assert "paramètre" in out                    # la prose, elle, est curee

    def test_per_slide_frontmatter_untouched(self, tmp_path):
        # Slidev : `---` / cles / `---` entre deux slides.
        p = _md(tmp_path, "# Un\n\n---\nlayout: two-cols\nclass: probleme-dense\n---\n\nUn probleme.\n")
        rac.main([str(p), "--apply"])
        out = p.read_text(encoding="utf-8")
        assert "class: probleme-dense" in out        # valeur de config intacte
        assert "Un problème." in out                 # prose curee

    def test_content_segment_after_separator_is_still_cured(self, tmp_path):
        # Contre-epreuve : un `---` suivi de PROSE est un separateur de slide,
        # pas un frontmatter — la prose doit rester curable.
        p = _md(tmp_path, "# Un\n\n---\n\nUn probleme de methode.\n")
        rac.main([str(p), "--apply"])
        assert "problème" in p.read_text(encoding="utf-8")


class TestMarkdownFrontmatterProseKeys:
    """`title` et `info` portent du texte AFFICHE, pas de la configuration.

    Mesure du 2026-08-18 sur les 18 decks : 8 lignes concernees, dont
    `title: "Web Semantique - dotNetRDF & Python"`. Slidev alimente l'onglet du
    navigateur et les metadonnees du PDF exporte avec `title` — le deck
    exportait donc « Semantique » dans ses propres metadonnees. Les proteger
    avec le reste du frontmatter etait un masquage trop large.
    """

    def test_title_value_is_cured(self, tmp_path):
        p = _md(tmp_path, '---\ntheme: ../theme-ia101\ntitle: "Web Semantique - dotNetRDF"\n---\n\nX\n')
        rac.main([str(p), "--apply"])
        out = p.read_text(encoding="utf-8")
        assert 'title: "Web Sémantique - dotNetRDF"' in out
        assert "theme: ../theme-ia101" in out          # la config voisine reste intacte

    def test_info_value_is_cured(self, tmp_path):
        p = _md(tmp_path, "---\ninfo: IA 101 - algorithmes genetiques\n---\n\nX\n")
        rac.main([str(p), "--apply"])
        assert "info: IA 101 - algorithmes génétiques" in p.read_text(encoding="utf-8")

    def test_prose_key_itself_never_touched(self, tmp_path):
        # La cle est le groupe 1, reinjecte tel quel : seule la valeur est curee.
        p = _md(tmp_path, "---\ninfo: parametre\n---\n\nX\n")
        rac.main([str(p), "--apply"])
        out = p.read_text(encoding="utf-8")
        assert out.count("info:") == 1
        assert "info: paramètre" in out

    def test_prose_key_inside_fence_is_not_cured(self, tmp_path):
        # Dans une fence, `title:` peut etre un exemple de YAML montre au
        # lecteur : rien n'y est curable, cle comme valeur.
        p = _md(tmp_path, '# Doc\n\n```yaml\ntitle: "Theorie des jeux"\n```\n')
        rac.main([str(p), "--apply"])
        assert 'title: "Theorie des jeux"' in p.read_text(encoding="utf-8")

    def test_other_config_keys_stay_protected(self, tmp_path):
        # Whitelist de prose, jamais blacklist de config : une cle absente de la
        # liste reste protegee meme si sa valeur ressemble a du francais.
        p = _md(tmp_path, "---\nlayout: probleme-dense\ntransition: methode\n---\n\nX\n")
        rac.main([str(p), "--apply"])
        out = p.read_text(encoding="utf-8")
        assert "layout: probleme-dense" in out
        assert "transition: methode" in out


class TestMarkdownCodeProtected:
    def test_fenced_block_untouched(self, tmp_path):
        # Mesure : 64 occurrences, ex. pseudo-code `Agent-Simple-Resolution-Probleme`.
        p = _md(tmp_path, "Un parametre.\n\n```\nfonction Resolution-Probleme(percept)\n```\n")
        rac.main([str(p), "--apply"])
        out = p.read_text(encoding="utf-8")
        assert "Resolution-Probleme(percept)" in out
        assert "paramètre" in out

    def test_tilde_fence_untouched(self, tmp_path):
        p = _md(tmp_path, "~~~\nprobleme = 1\n~~~\n")
        rac.main([str(p), "--apply"])
        assert "probleme = 1" in p.read_text(encoding="utf-8")

    def test_inline_code_path_untouched(self, tmp_path):
        # Mesure : 30 occurrences, ex. `GenAI/RAG-et-Memoire-Semantique/`.
        p = _md(tmp_path, "> Notebook : `GenAI/RAG-et-Memoire-Semantique/` pour la methode.\n")
        rac.main([str(p), "--apply"])
        out = p.read_text(encoding="utf-8")
        assert "`GenAI/RAG-et-Memoire-Semantique/`" in out   # chemin reel preserve
        assert "méthode" in out                              # prose autour curee


class TestMarkdownHtmlAttributes:
    def test_src_and_style_untouched(self, tmp_path):
        # Mesure : 6 occurrences (03-logique:162, :1791).
        p = _md(tmp_path, '<img src="./images/img_007.png" style="top:60px" /> Le probleme.\n')
        rac.main([str(p), "--apply"])
        out = p.read_text(encoding="utf-8")
        assert 'src="./images/img_007.png"' in out
        assert "problème" in out

    def test_alt_is_deliberately_cured(self, tmp_path):
        # `alt=` est ABSENT du masque a dessein : l'inventaire #11508 demande de
        # curer le texte alternatif (lecteurs d'ecran, indexation).
        p = _md(tmp_path, '<img src="a.png" alt="Un probleme de methode" />\n')
        rac.main([str(p), "--apply"])
        out = p.read_text(encoding="utf-8")
        assert 'alt="Un problème de méthode"' in out
        assert 'src="a.png"' in out

    def test_html_comment_is_cured(self, tmp_path):
        # Verifie firsthand sur S1-argumentation:144.
        p = _md(tmp_path, "<!-- Toulmin : Donnees → Garantie -->\n")
        rac.main([str(p), "--apply"])
        assert "Données" in p.read_text(encoding="utf-8")


class TestMarkdownCoreInherited:
    def test_link_target_still_protected(self, tmp_path):
        # Bright-line heritee du coeur (defect #7135/#7145).
        p = _md(tmp_path, "Voir [le probleme](./Model-Selection-parametre.md).\n")
        rac.main([str(p), "--apply"])
        out = p.read_text(encoding="utf-8")
        assert "(./Model-Selection-parametre.md)" in out   # cible intacte
        assert "[le problème]" in out                      # texte d'affichage cure

    def test_case_preserved(self, tmp_path):
        p = _md(tmp_path, "# Probleme\n\nUn probleme.\n")
        rac.main([str(p), "--apply"])
        out = p.read_text(encoding="utf-8")
        assert "# Problème" in out and "Un problème." in out


class TestMarkdownStructurePreserved:
    def test_trailing_newline_preserved(self, tmp_path):
        p = _md(tmp_path, "Un parametre.\n")
        rac.main([str(p), "--apply"])
        assert p.read_text(encoding="utf-8").endswith(".\n")

    def test_absent_trailing_newline_preserved(self, tmp_path):
        p = _md(tmp_path, "Un parametre.")
        rac.main([str(p), "--apply"])
        assert not p.read_text(encoding="utf-8").endswith("\n")

    def test_blank_lines_preserved(self, tmp_path):
        # Analogue du defaut nbformat #4 (blank-line collapse) cote markdown.
        p = _md(tmp_path, "Un parametre.\n\n\nUne methode.\n")
        rac.main([str(p), "--apply"])
        assert p.read_text(encoding="utf-8") == "Un paramètre.\n\n\nUne méthode.\n"

    def test_untouched_file_is_byte_identical(self, tmp_path):
        original = "# Titre déjà accentué\n\nRien à curer ici.\n"
        p = _md(tmp_path, original)
        rac.main([str(p), "--apply"])
        assert p.read_text(encoding="utf-8") == original


class TestMarkdownLineEndings:
    """Les decks du depot sont incoherents : 02-resolution-problemes est
    committe en CRLF, 01-introduction en LF, et `.gitattributes` ne couvre pas
    `slides/**/*.md`. Ecrire LF sans regarder renormalisait le deck 02 en
    entier — 1605 lignes de diff pour 25 cures, donc un diff qui n'est plus
    accents-only.
    """

    def test_crlf_file_stays_crlf(self, tmp_path):
        p = tmp_path / "slides.md"
        p.write_bytes(b"# Titre\r\n\r\nUn parametre.\r\n")
        rac.main([str(p), "--apply"])
        raw = p.read_bytes()
        assert raw == "# Titre\r\n\r\nUn paramètre.\r\n".encode("utf-8")

    def test_lf_file_stays_lf(self, tmp_path):
        p = tmp_path / "slides.md"
        p.write_bytes(b"# Titre\n\nUn parametre.\n")
        rac.main([str(p), "--apply"])
        assert b"\r\n" not in p.read_bytes()

    def test_crlf_without_trailing_newline(self, tmp_path):
        p = tmp_path / "slides.md"
        p.write_bytes(b"# Titre\r\nUn parametre.")
        rac.main([str(p), "--apply"])
        raw = p.read_bytes()
        assert raw == "# Titre\r\nUn paramètre.".encode("utf-8")
        assert not raw.endswith(b"\n")


class TestMarkdownCli:
    def test_check_exits_1_when_cures_available(self, tmp_path):
        p = _md(tmp_path, "Un parametre.\n")
        assert rac.main([str(p), "--check"]) == 1

    def test_check_exits_0_when_clean(self, tmp_path):
        p = _md(tmp_path, "Un paramètre.\n")
        assert rac.main([str(p), "--check"]) == 0

    def test_scope_rejected_on_md(self, tmp_path):
        # --scope parle de cellules code : il n'a pas de sens sur un .md.
        p = _md(tmp_path, "Un parametre.\n")
        assert rac.main([str(p), "--check", "--scope"]) == 2

    def test_dry_run_does_not_write(self, tmp_path):
        original = "Un parametre.\n"
        p = _md(tmp_path, original)
        rac.main([str(p), "--dry-run"])
        assert p.read_text(encoding="utf-8") == original


# ---------------------------------------------------------------------------
# 7. faux negatif listes-seules + zone grise FR/EN (delta po-2024 sur #11548)
# ---------------------------------------------------------------------------
class TestListOnlySegmentNotFrontmatter:
    r"""_YAML_CONT_RE matche aussi les items de liste (`^\s*-\s`) : un segment
    fait uniquement de puces satisfaisait "toutes lignes = cles ou continuations"
    et etait protege comme frontmatter -> 0 cure silencieuse. Un frontmatter
    Slidev reel commence TOUJOURS par une cle : la premiere ligne non vide doit
    matcher _YAML_KEY_RE."""

    def test_list_only_slide_is_cured(self, tmp_path):
        deck = "---\ntheme: ../theme-ia101\n---\n\n---\n\n- Les strategies deployees par le modele\n- Le modele de theorie\n\n---\n"
        p = _md(tmp_path, deck)
        rac.cure_markdown(p, write=True)
        out = p.read_text(encoding="utf-8")
        assert "stratégies" in out and "modèle" in out

    def test_list_line_without_separator_is_cured(self, tmp_path):
        # variante minimale mesuree : pas meme de separateur ---
        p = _md(tmp_path, "- Les strategies deployees par le modele\n")
        res = rac.cure_markdown(p, write=False)
        assert res["cures"] >= 1

    def test_real_frontmatter_still_protected(self, tmp_path):
        deck = "---\nlayout: two-cols\n---\n\n- Les strategies du modele\n"
        p = _md(tmp_path, deck)
        rac.cure_markdown(p, write=True)
        out = p.read_text(encoding="utf-8")
        assert "layout: two-cols" in out  # cle intacte
        assert "stratégies" in out  # la liste, elle, est curee


class TestEnglishGrayZone:
    """Formes en collision FR/EN : curees seulement sur preuve POSITIVE de
    contexte francais. La detection negative (mots-outils EN) sous-detecte :
    `- **Value Iteration**` n'en porte aucun (FP mesure #11508, reproduit sur
    l'adaptateur #11548 : `The strategies of execution and the role of the
    model` -> `The stratégies of exécution and the rôle of the model`)."""

    def test_bare_english_term_skipped(self, tmp_path):
        p = _md(tmp_path, "**Value Iteration**\n**Policy Iteration**\n")
        rac.cure_markdown(p, write=True)
        assert "Itération" not in p.read_text(encoding="utf-8")

    def test_english_line_skipped(self, tmp_path):
        p = _md(tmp_path, "The strategies of execution and the role of the model\n")
        rac.cure_markdown(p, write=True)
        out = p.read_text(encoding="utf-8")
        assert out == "The strategies of execution and the role of the model\n"

    def test_reference_title_skipped(self, tmp_path):
        p = _md(tmp_path, "Boole, An Investigation of the Mathematical Theories of Logic\n")
        rac.cure_markdown(p, write=True)
        assert "Théories" not in p.read_text(encoding="utf-8")

    def test_french_line_same_form_cured(self, tmp_path):
        # la MEME forme sur une ligne a preuve FR est curee : decision par
        # contexte, jamais par mot
        p = _md(tmp_path, "- Les strategies deployees par le modele\n")
        rac.cure_markdown(p, write=True)
        assert "stratégies" in p.read_text(encoding="utf-8")

    def test_non_colliding_form_cured_without_fr_marker(self, tmp_path):
        # les formes HORS collision ne demandent pas de preuve FR : la cure
        # conservatrice est non-ambigue par construction du dictionnaire
        p = _md(tmp_path, "Un parametre et un probleme\n")
        rac.cure_markdown(p, write=True)
        out = p.read_text(encoding="utf-8")
        assert "paramètre" in out and "problème" in out


# ---------------------------------------------------------------------------
# #14613 : protections portees de la cure ad-hoc #14139 dans l'organe canonique
# (fences, inline-code, URLs nues) + cureur BRUYANT (rapport formes hors table)
# + extension ACCENT_PAIRS famille RL (formes context-free, ambigues exclues).
# ---------------------------------------------------------------------------
class Test14613FenceProtection:
    def test_fence_content_never_cured(self, tmp_path):
        # fences 22/24 de #14139 : sortie LITTERALE de programme. Accentuer une
        # transcription d'execution la falsifie (Stop & Repair) -- mesure
        # firsthand : l'organe canonique d'avant ce fix corrompait 7 fences.
        literal = ("```\nEntrainement PPO (graine 42, 10 000 pas) : "
                   "287 episodes explores, eval deterministe finale = 418.9\n```")
        nb = _nb([("markdown", "La recompense par episode est aleatoire.\n\n"
                               + literal + "\n\nLe reseau est cree.")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rac.cure_notebook(p, write=True)
        cured = json.loads(p.read_text(encoding="utf-8"))
        src = cured["cells"][0]["source"]
        # la fence reste byte-identique
        assert literal in src
        # la prose autour est curee
        assert "récompense" in src and "épisode" in src and "aléatoire" in src
        assert "réseau" in src and "créé" in src

    def test_fence_state_crosses_list_chunks(self, tmp_path):
        # source list : la fence s'ouvre dans un chunk et se ferme dans un
        # autre -- l'etat doit persister d'un chunk a l'autre de la meme cellule.
        nb = {"cells": [{"cell_type": "markdown",
                         "source": ["Prose avec recompense.\n", "```\n",
                                    "entrainement deterministe\n", "```\n",
                                    "Suite aleatoire.\n"],
                         "metadata": {}}],
              "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rac.cure_notebook(p, write=True)
        cured = json.loads(p.read_text(encoding="utf-8"))
        src = "".join(cured["cells"][0]["source"])
        assert "entrainement deterministe" in src  # inter-fence intact
        assert "récompense" in src and "aléatoire" in src  # prose curee


class Test14613InlineAndUrlProtection:
    def test_inline_code_span_not_accented(self, tmp_path):
        nb = _nb([("markdown", "La variable `recompense` accumule, la recompense "
                               "affichee est aleatoire.")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rac.cure_notebook(p, write=True)
        cured = json.loads(p.read_text(encoding="utf-8"))
        src = cured["cells"][0]["source"]
        assert "`recompense`" in src      # span de code intact
        assert "récompense" in src        # occurrence en prose curee
        assert "aléatoire" in src

    def test_bare_url_not_accented(self, tmp_path):
        # sur-accusation mesuree #14139 : le segment de chemin d'une URL n'est
        # pas de la prose francaise (guide x3 dans un chemin readthedocs).
        # NB : « episodes » dans le chemin est une forme EN table -- si l'URL
        # n'etait pas masquee, elle serait corrompue en « épisodes ».
        nb = _nb([("markdown", "Voir https://example.com/docs/evaluation/episodes.html "
                               "pour l episode complet et la metrique.")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rac.cure_notebook(p, write=True)
        cured = json.loads(p.read_text(encoding="utf-8"))
        src = cured["cells"][0]["source"]
        assert "https://example.com/docs/evaluation/episodes.html" in src  # URL intacte
        assert "épisode" in src and "métrique" in src  # la prose, elle, est curee


class Test14613RlFamilyAndReport:
    def test_rl_forms_cured(self, tmp_path):
        nb = _nb([("markdown", "L entrainement dure 287 episodes ; la metrique "
                               "d evaluation et les hyperparametres sont aleatoires, "
                               "les reseaux sont complementaires, reseau equivalent "
                               "a reperer, les cles de creation des recompenses.")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        rac.cure_notebook(p, write=True)
        cured = json.loads(p.read_text(encoding="utf-8"))
        src = cured["cells"][0]["source"]
        for form in ["entraînement", "épisodes", "métrique",
                     "hyperparamètres", "aléatoires", "réseaux", "complémentaires",
                     "réseau", "équivalent", "repérer", "clés", "création",
                     "récompenses"]:
            assert form in src, form
        # « evaluation » EXCLU de la table (test_excludes_en_valid_words,
        # exclusion EN-valide délibérée) : il reste stripped ET remonte dans
        # le rapport hors-table -- désalignement bruyant, pas muet (#14613).
        assert "evaluation" in src

    def test_ambiguous_rl_forms_still_not_cured(self, tmp_path):
        # #14613 point 3 : entraine/enregistre/recommande/cumule (present vs
        # participe homographes une fois desaccentues) EXCLUS de la table.
        nb = _nb([("markdown", "Il entraine le modele, l agent enregistre la video, "
                               "on recommande la methode, le gain cumule.")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        res = rac.cure_notebook(p, write=True)
        cured = json.loads(p.read_text(encoding="utf-8"))
        src = cured["cells"][0]["source"]
        for form in ["entraine", "enregistre", "recommande", "cumule"]:
            assert form in src, form
        # modele/methode/agent/video (deja en table, non ambigus) sont cures
        assert "modèle" in src and "méthode" in src
        assert res["cures"] == 2

    def test_hors_table_reported_when_cure_incomplete(self, tmp_path):
        # #14613 point 1 : un cureur qui ne peut pas atteindre le critere du
        # detecteur doit le DIRE -- « N formes hors table », pas un succes muet.
        # NB : le detecteur exige une forme accentuee jumelle dans le notebook
        # (controle positif interne) -- « enregistré » active le comptage de
        # « enregistre », qui reste hors table (ambigu, point 3).
        nb = _nb([("markdown", "La video s enregistre automatiquement. "
                               "Le trace a bien été enregistré. "
                               "La recompense est aleatoire.")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        res = rac.cure_notebook(p, write=True)
        src = json.loads(p.read_text(encoding="utf-8"))["cells"][0]["source"]
        assert "récompense" in src  # les formes EN table sont bien cures
        assert "enregistre" in res.get("hors_table", {})
        assert res["hors_table_total"] >= 1

    def test_no_hors_table_when_clean(self, tmp_path):
        nb = _nb([("markdown", "Tout est deja correctement accentué ici.")])
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        res = rac.cure_notebook(p, write=True)
        assert "hors_table" not in res
