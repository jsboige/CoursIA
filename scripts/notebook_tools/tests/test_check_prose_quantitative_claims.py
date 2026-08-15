"""Tests for scripts/notebook_tools/check_prose_quantitative_claims.py.

Le module est l'instrument central du drainage #9434 (PR #9476 MERGED) : il
refuse les compteurs quantitatifs ecrits a la main dans la prose, en cinq
classes (artifact / machine / env / stochastic / structural). 531 LOC, 0 test
avant ce fichier -- vraie lacune infrastructure.

Les tests verrouillent les COMPORTEMENTS DOCUMENTES :
- les 5 regex flaggent ce qu'ils doivent flagger ET epargnent les faux positifs
  pedagogiques documentes (« 4 joueurs », dimensions WxH, lib sans version) ;
- la classe ``structural`` est LEGITIME-exclue (jamais echec, header taxonomie) ;
- le gate ``stochastic`` exige la co-occurrence mot-clef + nombre (meme ligne) ;
- l'exemption ``generated`` (un fichier qui se declare genere porte legitimement
  des chiffres) ;
- la fonction ``_resolve_classes`` et le gate seed notebook.

Pattern herite de ``test_audit_c1_c3.py`` : sys.path.insert module-level,
helpers synthetiques, fonctions pures. Aucun appel git/subprocess (on ne teste
pas scan_diff, qui delegue a ``git diff``).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import check_prose_quantitative_claims as cqc  # noqa: E402


# --------------------------------------------------------------------------- #
#  Classe artifact (COUNT_RE) : mesure d'artefact vivant = flag ; pedagogie = non
# --------------------------------------------------------------------------- #


def test_count_re_flags_artifact_measures():
    """Les formes canoniques d'artefacts sont capturees : « (140 lignes) »,
    « ~525 lignes », « **224** notebooks », « 87 cellules », « 10 files »."""
    for snippet in ["140 lignes", "~525 lignes", "**224** notebooks",
                    "87 cellules", "10 files"]:
        assert cqc.COUNT_RE.search(snippet), f"devrait flagger {snippet!r}"


def test_count_re_spares_pedagogical_counts():
    """« 4 joueurs » et « 3 proprietes de Nash » sont du contenu pedagogique,
    pas de l'etat de depot : le nom (joueurs/proprietes) n'est pas un nom
    d'artefact (lignes/cellules/notebooks/modules/fichiers/files). Jamais flag."""
    for snippet in ["4 joueurs", "3 proprietes de Nash", "2 joueurs, 3 strategies"]:
        assert cqc.COUNT_RE.search(snippet) is None, (
            f"ne doit PAS flagger le contenu pedagogique {snippet!r}"
        )


def test_count_re_requires_number_before_noun():
    """« module 5 » (nombre APRES le nom) n'est pas un compteur d'artefact :
    le nombre doit PRECEDER immediatement le nom. Jamais flag."""
    assert cqc.COUNT_RE.search("module 5") is None
    assert cqc.COUNT_RE.search("le module numero 5") is None


# --------------------------------------------------------------------------- #
#  Classe machine (MACHINE_RE) : duree absolue machine-dependante
# --------------------------------------------------------------------------- #


def test_machine_re_flags_durations():
    """Durees canoniques : « 127 ms » (extrait de « 24-127 ms »), « ~144 ms »,
    « 0.006 ms », « ~1.9 sec », « 2 min », « 0.2 s », « 5ms »."""
    for snippet in ["24-127 ms", "~144 ms", "0.006 ms", "~1.9 sec",
                    "2 min", "0.2 s", "5ms"]:
        assert cqc.MACHINE_RE.search(snippet), f"devrait flagger {snippet!r}"


def test_machine_re_monoletter_s_requires_space():
    """L'unite monolettre « s » (secondes) exige un espace avant elle pour eviter
    les collisions avec suffixes/abreviations. « 0.2s » (sans espace) n'est PAS
    flage, alors que « 0.2 s » l'est -- invariant defensif documente."""
    assert cqc.MACHINE_RE.search("0.2 s") is not None
    assert cqc.MACHINE_RE.search("0.2s") is None


def test_issue_reference_not_flagged_as_measure():
    """Une reference d'issue/PR GitHub « #NNNN » suivie d'un mot commencant par
    s/m/ms/sec/min ne doit JAMAIS etre matchee comme une duree -- un nombre
    precedent immediatement un diese est une reference (issue/PR, couleur hex,
    ancre/titre markdown), pas une mesure.

    Incident fondateur (#9434 angle-mort t2) : ICT-21 portait « Issue : #5101. »
    et « amendé de #5101 s'en dérive » -> le scanner classait « 5101 s » en duree
    machine (2 FP confirmes sur origin/main). Idem un ledger « #015 Argument... »
    flagge comme « 015 s ». Fix : lookbehind « (?<![\\w.#]) » sur les 4 regex de
    mesure. La vraie mesure « ~50 s sur GPU » (precedee de ~, pas de #) reste
    capturee -- c'est le contrat du fix (corriger le FP sans perdre la mesure)."""
    # Issue/PR refs + mot en s/m/ms/sec/min : JAMAIS une duree machine.
    for snippet in ["amendé de #5101 s'en dérive",
                    "Issue : #5101.",
                    "ce notebook = #5101 ;",
                    "merge #866 sur claim non-verifie",
                    "couleur #333333 sur fond clair"]:
        assert cqc.MACHINE_RE.search(snippet) is None, (
            f"ne doit PAS flagger la reference #NNNN {snippet!r}"
        )
    # La vraie mesure (sans # precedent) reste capturee : contrat du fix.
    assert cqc.MACHINE_RE.search("prend ~50 s sur GPU") is not None
    assert cqc.MACHINE_RE.search("duree : 12 ms") is not None
    # Le guard « # » couvre les 4 classes de mesure : un numero reference n'est
    # ni un artefact, ni un speedup, ni une valeur stochastique.
    assert cqc.COUNT_RE.search("voir PR #140 lignes supprimees") is None
    assert cqc.STRUCTURAL_RE.search("ref issue #4x") is None
    assert cqc.STOCHASTIC_NUM_RE.search("score fitness #41.71") is None


def test_machine_re_reflexive_verb_not_flagged_as_seconds():
    """L'unite monolettre « s » (secondes) collidait avec le debut d'un verbe
    reflechi francais : « 80 s'ecoulent », « 3 s'appliquent » etaient matches
    comme les durees « 80 s », « 3 s ». Une mesure reelle n'est JAMAIS suivie
    immediatement d'une apostrophe ; un « s' » = debut de s'en/s'applique/
    s'appuie/s'etend, pas l'unite secondes.

    Incident fondateur (#9434 angle-mort t3) : 22 FP confirmes elimines sur
    origin/main (DALL-E 3, ICT-21, Infer-1/13, RL/Search READMEs...). Fix :
    lookahead final « (?![\\w-]) » -> « (?![\\w\\-'’-]) ». Les vraies mesures
    (« ~50 s sur GPU », « 12 s », « 0.2 s ») restent capturees."""
    for snippet in ["les annees 80 s'ecoulent",
                    "3 s'appliquent",
                    "les 5 s'enchainent",
                    "DALL-E 3 s'appuie sur CLIP",
                    "le notebook 6 s'attaque au reward sparse"]:
        assert cqc.MACHINE_RE.search(snippet) is None, (
            f"ne doit PAS flagger le verbe reflechi {snippet!r}"
        )
    # Les vraies durees (sans apostrophe apres) restent capturees.
    for snippet in ["prend ~50 s sur GPU", "duree : 12 s", "latence 0.2 s"]:
        assert cqc.MACHINE_RE.search(snippet) is not None, (
            f"devrait capturer la vraie mesure {snippet!r}"
        )


def test_student_pacing_re_matches_pedagogical_durations():
    """Le mot-cle « (Duree|Durée) (estimee|estimée) » est le signal TN pour le
    pacing pedagogique. Qu'il soit en H3, H2, bold ou isole, c'est l'unique
    cle d'exemption ligne-complet (arbitrage jsboige 14:05:37Z #9434)."""
    for snippet in ["### Duree estimee : 45 minutes",
                    "### Durée estimée : 60 minutes",
                    "## Duree estimee : 50 minutes",
                    "**Duree estimee** : 90 minutes",
                    "**Durée estimée** : 90 minutes",
                    "Duree estimee 25 minutes",
                    "Durée estimée 25 minutes"]:
        assert cqc.STUDENT_PACING_RE.search(snippet) is not None, (
            f"devrait reconnaitre le pacing {snippet!r}"
        )
    # Pas de faux positif sur texte sans le mot-cle.
    for snippet in ["la duree d'execution est ~50 s",
                    "notre estimateur converge en 100 iterations",
                    "estimate (quand le notebook re-tourne)"]:
        assert cqc.STUDENT_PACING_RE.search(snippet) is None, (
            f"ne doit PAS matcher hors mot-cle pacing {snippet!r}"
        )


def test_findings_in_text_exempts_student_pacing_lines():
    """End-to-end : une ligne portant « Duree estimee : X minutes » (TN
    pedagogique) ne contribue AUCUN finding machine, alors qu'une vraie
    wall-clock (sans le mot-cle) reste capturee. Les autres classes
    (artifact, env, stochastic) ne sont pas affectees par l'exemption.

    Incident fondateur (#9434 angle-mort t4, arbitrage 14:05:37Z) : 200
    findings FP sur origin/main (c.9687 drain list), fermes en vague
    14:05-14:06Z suite a l'arbitrage user. La ligne entiere est exoneree
    de la classe machine uniquement."""
    # Ligne TN pacing : 0 finding machine.
    out = cqc._findings_in_text(
        "### Duree estimee : 45 minutes",
        "loc",
        {"machine"},
    )
    assert out == [], f"pacing TN ne doit pas flagger : {out!r}"
    # Vraie wall-clock sur la ligne d'a cote : capturee.
    out = cqc._findings_in_text(
        "duree execution : ~144 ms",
        "loc",
        {"machine"},
    )
    assert out == [("loc", "machine", "~144 ms")]
    # Mix : la ligne pacing est TN, les autres classes inchangees.
    text = "\n".join([
        "### Duree estimee : 45 minutes",
        "duree execution : ~144 ms",
        "### **Duree estimee** : 90 minutes",
        "latence 12 s",
    ])
    out = cqc._findings_in_text(text, "loc", {"machine"})
    assert out == [("loc", "machine", "~144 ms"), ("loc", "machine", "12 s")]
    # Les autres classes (artifact, env, stochastic) ne sont pas affectees
    # par l'exemption : un « 140 lignes » colle a un artefact reste flague.
    out = cqc._findings_in_text(
        "### Duree estimee : 45 minutes sur 140 lignes",
        "loc",
        {"machine", "artifact"},
    )
    assert out == [("loc", "artifact", "140 lignes")]


# --------------------------------------------------------------------------- #
#  Classe env (ENV_RE) : version de librairie figee en prose
# --------------------------------------------------------------------------- #


def test_env_re_flags_library_versions():
    """« NumPy 2.4.2 », « PyTorch 2.1.0 », « Mathlib v4.31.0-rc1 » (regex
    s'arrete au \\b apres le troisieme groupe, le suffixe -rc1 est hors-match)
    sont flaggues : une version derive quand l'env monte."""
    assert cqc.ENV_RE.search("NumPy 2.4.2")
    assert cqc.ENV_RE.search("PyTorch 2.1.0")
    m = cqc.ENV_RE.search("Mathlib v4.31.0-rc1")
    assert m is not None and m.group(0) == "Mathlib v4.31.0"


def test_env_re_spares_library_without_version():
    """Une lib citee sans version (« NumPy » seul) ou avec version incomplete
    (« NumPy 2 » = 0 groupe .\\d+) n'est PAS flagee : il faut >=1 groupe .\\d+."""
    assert cqc.ENV_RE.search("Nous utilisons NumPy") is None
    assert cqc.ENV_RE.search("NumPy 2") is None


# --------------------------------------------------------------------------- #
#  Classe stochastic : co-occurrence mot-clef + nombre (meme ligne)
# --------------------------------------------------------------------------- #


def test_stochastic_requires_keyword_and_number_same_line():
    """Flagge « fitness 41.71 » (kw + >=2 decimales), PAS « 41.71 » seul
    (pas de mot-clef), PAS « fitness 41 » (pas de decimale)."""
    # kw + nombre a decimales -> flag
    assert cqc.STOCHASTIC_KW_RE.search("fitness 41.71")
    assert cqc.STOCHASTIC_NUM_RE.search("fitness 41.71")
    # nombre sans kw -> le nombre matche NUM mais la ligne manque le kw
    assert cqc.STOCHASTIC_KW_RE.search("41.71 final") is None
    # kw sans decimale suffisante -> NUM ne matche pas
    assert cqc.STOCHASTIC_NUM_RE.search("fitness 41") is None
    assert cqc.STOCHASTIC_NUM_RE.search("loss 0.001")  # 3 decimales OK


# --------------------------------------------------------------------------- #
#  Classe structural (LEGITIME-exclue) : speedup deterministe vs dimensions WxH
# --------------------------------------------------------------------------- #


def test_structural_re_flags_speedups_not_dimensions():
    """« 2.78e24x », « 4x », « 1,5x » sont des speedups deterministes (flag en
    opt-in) ; « 100x100 » et « 1280x720 » sont des dimensions WxH (le \\b apres
    le premier x echoue car suivi d'un chiffre -> jamais flag)."""
    for snippet in ["2.78e24x", "4x", "1,5x", "speedup 2.78e24"]:
        assert cqc.STRUCTURAL_RE.search(snippet), f"devrait reconnaitre {snippet!r}"
    for snippet in ["100x100", "1280x720", "grille 9x9"]:
        assert cqc.STRUCTURAL_RE.search(snippet) is None, (
            f"ne doit pas flagger la dimension WxH {snippet!r}"
        )


# --------------------------------------------------------------------------- #
#  _resolve_classes : branching de --class
# --------------------------------------------------------------------------- #


def test_resolve_classes_branching():
    """Rend (classes_a_detecter, est_purement_structural)."""
    assert cqc._resolve_classes("artifact") == ({"artifact"}, False)
    assert cqc._resolve_classes("machine") == ({"machine"}, False)
    assert cqc._resolve_classes("env") == ({"env"}, False)
    assert cqc._resolve_classes("stochastic") == ({"stochastic"}, False)
    assert cqc._resolve_classes("structural") == ({"structural"}, True)
    classes_all, structural_all = cqc._resolve_classes("all")
    assert structural_all is False
    assert classes_all == set(cqc.FLAGGABLE)  # artifact/machine/env/stochastic
    assert "structural" not in classes_all  # structural jamais dans 'all'


# --------------------------------------------------------------------------- #
#  structural ne fait JAMAIS echouer (header taxonomie #9434)
# --------------------------------------------------------------------------- #


def test_structural_never_fails_even_with_findings(capsys):
    """En mode structural_only, _emit_grouped retourne 0 (jamais d'echec) meme
    avec des findings, et affiche la banniere LEGITIME. C'est le contrat
    documente : structural est legitime (speedup deterministe), inventorie
    seulement, jamais signale."""
    findings = [("file.md", "structural", "4x"), ("file.md", "structural", "2x")]
    rc = cqc._emit_grouped(findings, strict=True, structural_only=True)
    captured = capsys.readouterr().out
    assert rc == 0, "structural ne doit JAMAIS faire echouer (strict inclus)"
    assert "LEGITIME" in captured or "structural" in captured


def test_flaggable_strict_returns_one_with_findings(capsys):
    """En mode flaggable (artifact) strict, _emit_grouped retourne 1 avec
    findings (REFUS) et 0 sans findings (OK). Advisory (strict=False) -> 0."""
    findings = [("a.md", "artifact", "140 lignes")]
    assert cqc._emit_grouped(findings, strict=True, structural_only=False) == 1
    assert cqc._emit_grouped(findings, strict=False, structural_only=False) == 0
    assert cqc._emit_grouped([], strict=True, structural_only=False) == 0
    assert "[OK]" in capsys.readouterr().out


# --------------------------------------------------------------------------- #
#  _declares_generated : exemption generateur proprietaire
# --------------------------------------------------------------------------- #


def test_declares_generated_detects_generator_headers():
    """Un en-tete qui revendique un generateur exonere le fichier (FR ou EN).

    La regex FR exige « fichier » IMMEDIATEMENT suivi de « genere » (sans mot
    intermediaire comme « est ») : « Ce fichier genere par cron » matche,
    « Ce fichier est genere » ne matche PAS (mot intermediaire).
    """
    assert cqc._declares_generated("Ce fichier genere par cron")
    assert cqc._declares_generated("auto-generated file")
    assert cqc._declares_generated("do not edit by hand")
    assert cqc._declares_generated("ne pas editer a la main")
    assert cqc._declares_generated("n'est pas maintenu a la main")
    # Prose normale : pas d'exemption.
    assert cqc._declares_generated("Ce notebook presente l'algorithme A*") is False
    assert cqc._declares_generated("Section 1 : introduction") is False


# --------------------------------------------------------------------------- #
#  _skipped : hors-perimetre (harnais, cache, vendored, genere)
# --------------------------------------------------------------------------- #


def test_skipped_paths():
    """Les chemins du harnais/cache/vendored sont sautes ; la prose livree non."""
    assert cqc._skipped(Path(".claude/rules/x.md")) is True
    assert cqc._skipped(Path("proj/.lake/build/foo.olean")) is True
    assert cqc._skipped(Path("a/b/.pytest_cache/y")) is True
    assert cqc._skipped(Path("_peters/Knots/Basic.lean")) is True
    assert cqc._skipped(Path("COURSE_CATALOG.generated.md")) is True
    assert cqc._skipped(Path("COURSE_CATALOG.generated.json")) is True
    # Prose livree a un etudiant : pas skippee.
    assert cqc._skipped(Path("MyIA.AI.Notebooks/Search/Astar.ipynb")) is False


# --------------------------------------------------------------------------- #
#  _notebook_is_seeded : gate stochastic (carnet seme = reproductible)
# --------------------------------------------------------------------------- #


def _write_nb(path: Path, cells: list[dict]) -> Path:
    path.write_text(
        json.dumps({"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}),
        encoding="utf-8",
    )
    return path


def test_notebook_is_seeded_detects_seed_in_code_cell(tmp_path):
    """Un carnet dont une cellule code contient np.random.seed est reproductible."""
    seeded = _write_nb(tmp_path / "seeded.ipynb", [
        {"cell_type": "code", "source": ["import numpy as np\nnp.random.seed(42)"]},
    ])
    assert cqc._notebook_is_seeded(seeded) is True
    unseeded = _write_nb(tmp_path / "unseeded.ipynb", [
        {"cell_type": "code", "source": ["x = np.random.rand(5)"]},
    ])
    assert cqc._notebook_is_seeded(unseeded) is False
    # Divers APIs de seed reconnues (torch, random, tf, jax).
    for seed_call in ["torch.manual_seed(0)", "random.seed(1)",
                      "tf.random.set_seed(7)", "rng = 42"]:
        nb = _write_nb(tmp_path / f"{seed_call[:4]}.ipynb", [
            {"cell_type": "code", "source": [seed_call]}])
        assert cqc._notebook_is_seeded(nb) is True, f"seed non reconnu: {seed_call!r}"


# --------------------------------------------------------------------------- #
#  _findings_in_text : catalogue end-to-end + generated-marker skip
# --------------------------------------------------------------------------- #


def test_findings_in_text_catalogs_and_skips_generated_markers():
    """Catalogue les findings par ligne ; saute les lignes portant un marqueur
    genere (COURSE_CATALOG.generated / CATALOG-STATUS)."""
    # artifact : deux findings sur une ligne.
    out = cqc._findings_in_text("On a 140 lignes et 87 cellules.", "loc", {"artifact"})
    assert out == [("loc", "artifact", "140 lignes"), ("loc", "artifact", "87 cellules")]
    # Ligne avec marqueur genere : entierement ignoree (le catalogue porte legitimement
    # des chiffres).
    out2 = cqc._findings_in_text("COURSE_CATALOG.generated 224 notebooks", "loc", {"artifact"})
    assert out2 == []
    out3 = cqc._findings_in_text("<!-- CATALOG-STATUS:START --> 43 notebooks", "loc", {"artifact"})
    assert out3 == []


def test_findings_in_text_stochastic_needs_keyword_on_same_line():
    """La ligne est l'unite de co-occurrence : nombre sans mot-clef -> 0 finding."""
    assert cqc._findings_in_text("fitness 41.71 final", "loc", {"stochastic"}) == [
        ("loc", "stochastic", "41.71")]
    assert cqc._findings_in_text("41.71 final sans contexte", "loc", {"stochastic"}) == []
