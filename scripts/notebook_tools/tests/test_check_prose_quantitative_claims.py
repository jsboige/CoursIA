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
- la fonction ``_resolve_classes`` et le gate seed notebook ;
- la carte ``_ipynb_output_lines`` et la frontiere du mode diff (#17729) : une
  charge utile de SORTIE ajoutee n'est pas de la prose, une ligne de source
  markdown portant le meme compteur l'est.

Pattern herite de ``test_audit_c1_c3.py`` : sys.path.insert module-level,
helpers synthetiques, fonctions pures. Les tests de ``scan_diff`` montent un
depot git jetable **hors** du depot de travail (``tmp_path``), avec
``core.autocrlf=false`` pour que l'arbre et le blob commite soient comparables
octet a octet.
"""

from __future__ import annotations

import json
import re
import subprocess
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


@pytest.mark.parametrize(
    "line",
    [
        "Sommets : 81 cellules de la grille (9x9)",
        "Ce notebook présente 81 cellules de la grille Sudoku.",
        "Ce notebook présente une grille Sudoku de 81 cellules.",
        "Dans ce carnet, la matrice de couverture exacte compte 729 lignes, une par couple cellule-valeur.",
        "This notebook presents 81 cells of the grid.",
        "The graph has 81 cells of the 9x9 grid as vertices.",
        "**729 lignes** = 9 lignes x 9 colonnes x 9 valeurs",
        "La matrice de couverture exacte compte 729 lignes, une par couple cellule-valeur.",
        "La matrice contient 324 colonnes x 729 lignes maximum.",
        "The exact-cover matrix has 729 lines, one for each cell-value pair.",
    ],
)
def test_artifact_detector_spares_explicit_domain_model_dimensions(line):
    """Les dimensions explicites d'un modele Sudoku ne sont pas des inventaires.

    81 cellules décrit les cases de la grille ; 729 lignes décrit les candidats
    de la matrice de couverture exacte. Ces quantités mathématiques stables ne
    doivent pas bloquer une PR pédagogique en mode ``--diff --strict``.
    """
    assert cqc._findings_in_text(line, "cours/sudoku.ipynb", {"artifact"}) == []


@pytest.mark.parametrize(
    "line, expected",
    [
        (
            "The notebook has 81 cells of the grid.",
            ["81 cells"],
        ),
        (
            "La matrice de données du fichier source a 120 lignes, une par couple cellule-valeur.",
            ["120 lignes"],
        ),
        (
            "Le notebook contient 81 cellules de code pour expliquer la grille Sudoku.",
            ["81 cellules"],
        ),
        (
            "Le fichier source compte 729 lignes de code pour construire la matrice.",
            ["729 lignes"],
        ),
        (
            "Le fichier source contient 729 lignes, une par couple cellule-valeur.",
            ["729 lignes"],
        ),
        (
            "Le fichier source fait 324 colonnes x 729 lignes.",
            ["729 lignes"],
        ),
        (
            "Matrice de couverture exacte : 729 lignes, une par couple cellule-valeur ; "
            "le notebook contient aussi 81 cellules de code.",
            ["81 cellules"],
        ),
        (
            "Matrice de couverture exacte : le code fait 80 lignes de code ; "
            "729 lignes, une par couple cellule-valeur.",
            ["80 lignes"],
        ),
    ],
)
def test_domain_context_does_not_hide_artifact_inventory_counts(line, expected):
    """Le contexte mathématique ne doit masquer aucun compte d'inventaire."""
    findings = cqc._findings_in_text(line, "cours/sudoku.ipynb", {"artifact"})
    assert [snippet for _location, _klass, snippet in findings] == expected


# --------------------------------------------------------------------------- #
#  Allowlist motivee de la classe artifact (#23111)
# --------------------------------------------------------------------------- #


def test_artifact_exemptions_are_motivated_and_point_at_real_files():
    """Chaque entree porte un chemin QUI EXISTE, un motif, et une raison ECRITE.

    Une exemption morte ressemble exactement a une exemption vivante : meme
    trio, meme silence. Le chemin est donc verifie contre l'arbre (une faute de
    frappe dans un chemin ne protegerait rien et ne se verrait pas), et la
    raison doit etre une phrase, pas un mot -- c'est elle qui rend l'arbitrage
    relisible sans reconstituer le fil de la PR."""
    repo_root = Path(__file__).resolve().parents[3]
    assert cqc.ARTIFACT_EXEMPTIONS, "allowlist vide : #23111 attend les occurrences Lean"
    for exemption in cqc.ARTIFACT_EXEMPTIONS:
        assert (repo_root / exemption.path).is_file(), (
            f"chemin d'exemption introuvable : {exemption.path!r}"
        )
        assert not any(ch in exemption.path for ch in "*?["), (
            f"un glob n'est pas un chemin : {exemption.path!r} (une exemption "
            f"large se perime en silence)"
        )
        assert exemption.motif.pattern.strip(), "motif vide"
        assert len(exemption.raison.split()) >= 8, (
            f"raison trop courte pour etre relue : {exemption.raison!r}"
        )


@pytest.mark.parametrize(
    "path, line",
    [
        (
            "MyIA.AI.Notebooks/SymbolicAI/Lean/GOL/conway_lean/README.md",
            "  - Gosper Glider Gun (36 cellules vivantes, période 30) parsé et vérifié",
        ),
        (
            "MyIA.AI.Notebooks/SymbolicAI/Lean/GOL/conway_lean/README.md",
            "- Pulsar (48 cellules) et pentadecathlon (p15) sont à la limite",
        ),
        (
            "MyIA.AI.Notebooks/SymbolicAI/Lean/GOL/conway_lean/README.en.md",
            "- Pulsar (48 cells) and pentadecathlon (p15) are borderline but pass `native_decide`",
        ),
        (
            "MyIA.AI.Notebooks/SymbolicAI/Lean/README.md",
            "reproduction réelle du dépôt piné `plby/HopfProblem` (248 818 lignes "
            "compilées en 1154 s, 0 sorry/0 axiom)",
        ),
        (
            "MyIA.AI.Notebooks/SymbolicAI/Lean/GOL/conway_lean/scripts/README.md",
            "fabriquée : la v1 du gun, 36 cellules fausses, passait le check de règle) ;",
        ),
    ],
)
def test_artifact_exemptions_cover_the_named_lean_occurrences(path, line):
    """Les faux positifs de SENS nommes par #23111 ne sont plus signales.

    « cellules vivantes » / « cellules » d'un canon du Jeu de la Vie comptent
    des cellules de l'automate ; « 248 818 lignes » mesure un run sur un depot
    externe pine ; les « 36 cellules » de `conway_lean/scripts/README.md » sont
    la population d'une transcription FABRIQUEE du canon, citee comme temoin
    d'echec du self-check — un nombre du recit de l'incident, pas un etat du
    depot. Supprimer ces nombres reecrirait le propos."""
    assert cqc._findings_in_text(line, path, {"artifact"}) == []


@pytest.mark.parametrize(
    "path, line",
    [
        # « Tranche 4 » (v5, 2026-11-07) du manifeste de preservation #14238
        # (PR #25120) : comptes de lignes figes de la curation de la version.
        (
            "docs/reference/branch-cleanup-manifest.README.md",
            "Le manifeste passe de **10 259** à **13 187** lignes ;",
        ),
        (
            "docs/reference/branch-cleanup-manifest.README.md",
            "les 2 930 lignes nouvelles s'y ajoutent",
        ),
        (
            "docs/reference/branch-cleanup-manifest.README.md",
            "`branch-cleanup-manifest.tsv.gz` (compressé gzip, 575 Ko, "
            "décompressé 1.65 Mo, **13 187 lignes**) — 6 colonnes",
        ),
        (
            "docs/reference/branch-cleanup-manifest.README.md",
            "- Selection reellement poussee (2 927 lignes)",
        ),
        (
            "docs/reference/branch-cleanup-manifest.README.md",
            "- Refus motives (9 lignes)",
        ),
    ],
)
def test_artifact_exemptions_cover_branch_cleanup_manifest_counts(path, line):
    """Les comptes de lignes du manifeste de preservation #14238 (section
    « Tranche 4 », v5) ne sont plus signales : ce sont des faits FIGES de la
    curation de cette version, re-mesurables a la commande de la section
    « Verification », pas un etat du depot qui deriverait a chaque ajout.
    Les supprimer reecrirait la preuve du geste (angle-mort du guard)."""
    assert cqc._findings_in_text(line, path, {"artifact"}) == []


def test_artifact_exemption_is_a_span_not_a_file_blanket():
    """L'exemption couvre le compteur sous son motif, PAS la ligne ou le fichier.

    Un vrai compteur de carnet sur la MEME ligne reste flague : c'est ce qui
    distingue une exemption motivee d'un couperet par fichier, qui avalerait en
    silence un compte ajoute plus tard."""
    path = "MyIA.AI.Notebooks/SymbolicAI/Lean/GOL/conway_lean/README.md"
    out = cqc._findings_in_text(
        "- Pulsar (48 cellules) et le carnet fait 87 cellules de code", path, {"artifact"}
    )
    assert [snippet for _loc, _klass, snippet in out] == ["87 cellules"]
    # …et un compte de cellules ordinaire ailleurs dans le MEME fichier aussi.
    out = cqc._findings_in_text("Le README annonce 36 cellules de code.", path, {"artifact"})
    assert [snippet for _loc, _klass, snippet in out] == ["36 cellules"]


def test_artifact_exemption_on_incident_narrative_is_a_span_not_a_blanket():
    """Temoin positif du 5e faux positif (#23111) : dans le MEME fichier
    `conway_lean/scripts/README.md`, le nombre du recit d'incident est exempte
    mais un vrai compte de carnet reste flague.

    Sans ce temoin, l'exemption pourrait se transformer en couperet par fichier
    sans qu'aucun test ne rougisse."""
    path = "MyIA.AI.Notebooks/SymbolicAI/Lean/GOL/conway_lean/scripts/README.md"
    exempte = "fabriquée : la v1 du gun, 36 cellules fausses, passait le check de règle) ;"
    assert cqc._findings_in_text(exempte, path, {"artifact"}) == []
    out = cqc._findings_in_text(
        "fabriquée : la v1 du gun, 36 cellules fausses — le carnet fait 19 cellules",
        path,
        {"artifact"},
    )
    assert [snippet for _loc, _klass, snippet in out] == ["19 cellules"]


def test_artifact_exemption_does_not_leak_across_files():
    """Le meme texte dans un AUTRE fichier n'est pas exempte : l'exemption est
    (fichier, motif), jamais un motif global qui suivrait le phrase dans le
    depot."""
    line = "- Pulsar (48 cellules) et pentadecathlon (p15)"
    out = cqc._findings_in_text(line, "autre/serie/README.md", {"artifact"})
    assert out == [("autre/serie/README.md", "artifact", "48 cellules")]


def test_artifact_exemption_uses_the_file_part_of_a_notebook_location():
    """Une cellule de carnet porte une location « <fichier> MD[<i>] » : la
    partie fichier suffit a apparier l'exemption, et le finding restitution
    garde la location complete."""
    path = "MyIA.AI.Notebooks/SymbolicAI/Lean/GOL/conway_lean/README.md"
    out = cqc._findings_in_text("Pulsar (48 cellules)", f"{path} MD[3]", {"artifact"})
    assert out == []
    out = cqc._findings_in_text("Le carnet fait 87 cellules", f"{path} MD[3]", {"artifact"})
    assert out == [(f"{path} MD[3]", "artifact", "87 cellules")]


def test_exemption_audit_separates_live_from_stale(tmp_path):
    """Une entree qui ne couvre plus rien est PERIMEE, pas silencieuse : elle ne
    protege aucun compteur et se lit pourtant comme une decision vivante."""
    first = cqc.ARTIFACT_EXEMPTIONS[0]
    target = tmp_path / first.path
    target.parent.mkdir(parents=True)
    target.write_text(
        "  - Gosper Glider Gun (36 cellules vivantes, période 30) parsé\n",
        encoding="utf-8",
    )
    live, stale = cqc._exemption_audit(tmp_path)
    assert [(e.path, n) for e, n in live] == [(first.path, 1)]
    # Les autres fichiers de l'allowlist n'existent pas sous tmp_path.
    assert len(stale) == len(cqc.ARTIFACT_EXEMPTIONS) - 1

    # Le propos est reecrit : le motif ne matche plus, l'entree est perimee
    # -- et l'occurrence redevient signalable, ce qui rend l'arbitrage a un
    # humain plutot que de le laisser mourir en silence.
    target.write_text("  - Gosper Glider Gun (36 cellules de carnet)\n", encoding="utf-8")
    live, stale = cqc._exemption_audit(tmp_path)
    assert live == []
    assert len(stale) == len(cqc.ARTIFACT_EXEMPTIONS)
    assert cqc._findings_in_text(
        "  - Gosper Glider Gun (36 cellules de carnet)", first.path, {"artifact"}
    ) == [(first.path, "artifact", "36 cellules")]


def test_exemption_audit_under_a_subtree_root_judges_the_named_file(tmp_path):
    """Sous ``--root <sous-arbre>``, une exemption vivante reste vivante (#24587).

    Les ``path`` de ``ARTIFACT_EXEMPTIONS`` sont ecrits depuis la racine du
    depot ; l'audit les resolvait depuis la racine SCANNEE, donc aucun ne
    designait un fichier existant et **les 12** se lisaient perimees, avec pour
    consigne de les retirer -- 100 % de faux positifs sur un dispositif vivant.
    """
    first = cqc.ARTIFACT_EXEMPTIONS[0]
    target = tmp_path / first.path
    target.parent.mkdir(parents=True)
    target.write_text("  - Gosper Glider Gun (36 cellules vivantes)\n", encoding="utf-8")
    subtree = tmp_path / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean"

    # Controle negatif : sans la racine du depot, l'entree se lit perimee --
    # c'est exactement le defaut que la correction ferme.
    _live, stale = cqc._exemption_audit(subtree)
    assert first.path in [e.path for e in stale]

    live, stale = cqc._exemption_audit(subtree, repo_root=tmp_path)
    assert [(e.path, n) for e, n in live] == [(first.path, 1)]
    assert len(stale) == len(cqc.ARTIFACT_EXEMPTIONS) - 1


def test_scan_all_under_a_subtree_root_still_applies_live_exemptions(tmp_path):
    """Le meme ecart faisait re-signaler le compteur pourtant arbitre (#24587).

    Le scan borne rendait ses chemins relatifs a la racine scannee : l'exemption
    ne pouvait apparier aucun d'eux, et la lane lisait un finding la ou un
    arbitrage humain avait deja tranche (les compteurs Conway sont des cellules
    de l'automate, pas des totaux de carnets).
    """
    first = cqc.ARTIFACT_EXEMPTIONS[0]
    target = tmp_path / first.path
    target.parent.mkdir(parents=True)
    target.write_text("  - Gosper Glider Gun (36 cellules vivantes)\n", encoding="utf-8")
    subtree = tmp_path / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean"

    assert cqc.scan_all(subtree, {"artifact"}) != []
    assert cqc.scan_all(subtree, {"artifact"}, repo_root=tmp_path) == []


def test_all_under_a_subtree_root_never_reports_a_live_exemption_as_perimee(
    tmp_path, monkeypatch, capsys
):
    """Non-regression par la CLI : le bloc ``--all`` reste muet sur la peremption.

    Une entree dont le motif matche encore le fichier qu'elle nomme ne doit
    jamais sortir dans ``[ALLOWLIST-PERIMEE]``, quel que soit le ``--root``.
    """
    exemption = cqc.ArtifactExemption(
        path="prose/README.md",
        motif=re.compile(r"Gosper Glider Gun \(36 cellules vivantes"),
        raison="fixture de test",
    )
    target = tmp_path / exemption.path
    target.parent.mkdir(parents=True)
    target.write_text("  - Gosper Glider Gun (36 cellules vivantes)\n", encoding="utf-8")
    monkeypatch.setattr(cqc, "ARTIFACT_EXEMPTIONS", (exemption,))
    monkeypatch.setattr(cqc, "_REPO_ROOT", tmp_path)
    monkeypatch.setattr(
        sys, "argv", ["cqc", "--all", "--root", str(tmp_path / "prose")]
    )

    assert cqc.main() == 0
    out = capsys.readouterr().out
    assert "[ALLOWLIST-PERIMEE]" not in out
    assert "[ALLOWLIST] 1 exemption" in out


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


def test_env_re_flags_table_and_backtick_forms():
    """Le critere 2 de #9434 presente les versions de lib en tableau markdown
    (« | numpy | 2.2.6 | Tirages gaussiens | ») : nom et version separes par
    « | », non par un espace simple. ENV_RE etait aveugle a cette forme (#14314)
    -- le guard rendait [OK] avant ET apres le drainage du critere 2. Les spans
    code (`` ` ``) autour du nom et/ou de la version sont tires aussi."""
    for snippet in ["| numpy | 2.2.6 |",
                    "| numpy | 2.2.6 | Tirages gaussiens |",
                    "| Mathlib | v4.31.0-rc1 |",
                    "`numpy` 2.2.6",
                    "`numpy` `2.2.6`",
                    "NumPy `2.4.2`",
                    "`numpy` | `2.2.6` |"]:
        assert cqc.ENV_RE.search(snippet) is not None, (
            f"devrait flagger la version en forme table/spans {snippet!r}"
        )
    m = cqc.ENV_RE.search("| numpy | 2.2.6 | Tirages gaussiens |")
    assert m.group(0) == "numpy | 2.2.6"


def test_env_re_flags_interpreter_version():
    """L'interpreteur Python porte une version au meme titre qu'une lib :
    « Python 3.13.3 » en prose est une mesure env figee (#14314). Meme seuil
    que les libs : le couple majeure.mineure est requis, « Python 3 » seul
    (adjectif/prefixe) suffit pas."""
    for snippet in ["Python 3.13.3", "environnement Python 3.13",
                    "python 3.12.2", "| Python | 3.13.3 |"]:
        assert cqc.ENV_RE.search(snippet) is not None, (
            f"devrait flagger la version d'interpreteur {snippet!r}"
        )
    for snippet in ["Python 3", "Nous codons en Python depuis 2019",
                    "Python est un langage interprete"]:
        assert cqc.ENV_RE.search(snippet) is None, (
            f"ne doit PAS flagger {snippet!r} (pas de version citee)"
        )


def test_env_re_spares_multiplier_reading():
    """Garde anti-FP du mot le plus courant de la liste : « X.Y fois/× » est un
    multiplicateur, pas une version d'interpreteur citee. Une version reelle
    reste capturee sur la meme ligne."""
    for snippet in ["Python 2.5 fois plus rapide", "Python 2.5× plus rapide"]:
        assert cqc.ENV_RE.search(snippet) is None, (
            f"ne doit PAS lire « fois » comme une version {snippet!r}"
        )
    assert cqc.ENV_RE.search("NumPy 2.4.2, Python 3.13.3") is not None


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


# --------------------------------------------------------------------------- #
#  _ipynb_output_lines : carte des charges utiles de SORTIE (#17729)
# --------------------------------------------------------------------------- #


def _dump_nb(path: Path, nb: dict) -> Path:
    """Ecrit un carnet au format pretty-print de nbformat (indent=1), en LF."""
    path.write_text(
        json.dumps(nb, indent=1, ensure_ascii=False) + "\n",
        encoding="utf-8", newline="\n",
    )
    return path


def test_ipynb_non_prose_lines_maps_payloads_and_code_sources(tmp_path):
    """Une charge utile de sortie, une valeur de source code et une valeur de
    source markdown sont, ligne a ligne, la meme chose (une chaine nue). Le
    bloc ``outputs`` et le ``cell_type`` les separent (#22564 D3)."""
    nb = {
        "cells": [
            {"cell_type": "markdown", "source": ["On a 140 lignes.\n"]},
            {"cell_type": "code", "source": ["print('x')\n"], "execution_count": 3,
             "outputs": [{"output_type": "stream", "name": "stdout",
                          "text": ["  Angel.lean   65 lignes\n"]}]},
            {"cell_type": "code", "source": ["y = 1\n"], "execution_count": 4,
             "outputs": []},
            {"cell_type": "code", "source": ["z = 2\n"]},
        ],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }
    path = _dump_nb(tmp_path / "mapped.ipynb", nb)
    lines = path.read_text(encoding="utf-8").splitlines()
    inside = cqc._ipynb_non_prose_lines(str(path))

    def _ln(needle: str) -> int:
        hits = [n for n, raw in enumerate(lines, 1) if needle in raw]
        assert len(hits) == 1, f"{needle!r} apparait {len(hits)} fois"
        return hits[0]

    assert _ln("On a 140 lignes") not in inside        # source markdown : LA prose visee
    assert _ln("print('x')") in inside                 # source code : non-prose (D3)
    assert _ln("Angel.lean") in inside                 # charge utile de sortie
    # `"outputs": []` se referme sur sa propre ligne : l'ouvrir avalerait la
    # cellule suivante, et avec elle toutes les sources du reste du fichier.
    assert _ln("z = 2") in inside                      # source code d'une cellule sans outputs
    assert _ln('"outputs": []') not in inside


# --------------------------------------------------------------------------- #
#  scan_diff : la frontiere sortie/source, mesuree de bout en bout (#17729)
# --------------------------------------------------------------------------- #


def _git(cwd: Path, *args: str) -> None:
    subprocess.run(
        ["git", *args], cwd=cwd, check=True, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )


def _commit_all(repo: Path, message: str) -> None:
    _git(repo, "add", "-A")
    _git(repo, "-c", "user.email=tests@invalid", "-c", "user.name=tests",
         "commit", "-m", message)


def test_scan_diff_skips_output_payloads_but_flags_source_prose(tmp_path, monkeypatch):
    """Meme compteur, meme forme : en charge utile de sortie il est legitime
    (« une cellule code qui compte et affiche... on ne la regarde pas »), en
    source markdown il est la prose que l'organe refuse."""
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init")
    # Sans ce reglage, un arbre CRLF face a un blob LF ferait apparaitre TOUT le
    # fichier comme ajoute : le test mesurerait un artefact de checkout.
    _git(repo, "config", "core.autocrlf", "false")

    nb_path = repo / "carnet.ipynb"
    output_cell = {"cell_type": "code", "source": ["print('x')\n"], "execution_count": 1,
                   "outputs": [{"output_type": "stream", "name": "stdout",
                                "text": ["  Angel.lean   65 lignes\n"]}]}
    _dump_nb(nb_path, {"cells": [{"cell_type": "code", "source": ["print('x')\n"],
                                  "outputs": [], "execution_count": None}],
                       "metadata": {}, "nbformat": 4, "nbformat_minor": 5})
    _commit_all(repo, "base")

    monkeypatch.chdir(repo)

    # 1) La re-execution remplace la sortie vide : rien n'est de la prose.
    _dump_nb(nb_path, {"cells": [output_cell],
                       "metadata": {}, "nbformat": 4, "nbformat_minor": 5})
    assert cqc.scan_diff("HEAD", {"artifact"}) == []

    # 2) On ajoute EN PLUS une ligne de prose markdown portant le meme compteur.
    _dump_nb(nb_path, {"cells": [
        {"cell_type": "markdown", "source": ["Le module fait 65 lignes.\n"]},
        output_cell], "metadata": {}, "nbformat": 4, "nbformat_minor": 5})
    found = cqc.scan_diff("HEAD", {"artifact"})
    assert [snippet for _loc, _klass, snippet in found] == ["65 lignes"]


def test_scan_diff_skips_code_cell_comments_but_flags_markdown_counts(tmp_path, monkeypatch):
    """#22564 D3 : les deux temoins mesures sur 11b_Materiel_Debit_Cout -- une
    docstring et un commentaire de ligne, chacun portant « 1 ligne ». En
    cellule *code* ce n'est pas de la prose ; le MEME compteur en markdown
    reste la prose que l'organe refuse. Sans le second volet, on ne saurait
    pas distinguer « corrige » de « devenu aveugle »."""
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init")
    _git(repo, "config", "core.autocrlf", "false")

    nb_path = repo / "carnet.ipynb"
    _dump_nb(nb_path, {"cells": [{"cell_type": "code", "source": ["pass\n"],
                                  "outputs": [], "execution_count": None}],
                       "metadata": {}, "nbformat": 4, "nbformat_minor": 5})
    _commit_all(repo, "base")
    monkeypatch.chdir(repo)

    # 1) Controle positif : les deux temoins de D3, en cellule CODE -> vert.
    code_cell = {"cell_type": "code", "execution_count": 1, "outputs": [],
                 "source": [('"""Octets VRAM par parametre : quantifie au .cuda() '
                             + '(bitsandbytes), forward 1 ligne."""\n'),
                            ("couche(x1)  # alloue les éventuels buffers de travail "
                             + "(négligeables sur 1 ligne)\n")]}
    _dump_nb(nb_path, {"cells": [code_cell],
                       "metadata": {}, "nbformat": 4, "nbformat_minor": 5})
    assert cqc.scan_diff("HEAD", {"artifact"}) == []

    # 2) Controle negatif : le MEME compteur, cette fois en cellule MARKDOWN.
    _dump_nb(nb_path, {"cells": [
        {"cell_type": "markdown",
         "source": ["Le cout marginal est negligeable sur 1 ligne.\n"]},
        code_cell],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5})
    found = cqc.scan_diff("HEAD", {"artifact"})
    assert [snippet for _loc, _klass, snippet in found] == ["1 ligne"]


def test_scan_diff_strict_accepts_domain_dimensions_but_keeps_inventory(
    tmp_path, monkeypatch, capsys
):
    """La porte diff/strict accepte la geometrie, mais refuse l'inventaire."""
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init")
    _git(repo, "config", "core.autocrlf", "false")
    nb_path = repo / "sudoku.ipynb"
    metadata = {"metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    _dump_nb(
        nb_path,
        {
            **metadata,
            "cells": [{"cell_type": "markdown", "source": ["Introduction.\n"]}],
        },
    )
    _commit_all(repo, "base")
    monkeypatch.chdir(repo)

    domain_cells = [
        {"cell_type": "markdown", "source": ["Sommets : 81 cellules de la grille (9x9)\n"]},
        {"cell_type": "markdown", "source": ["**729 lignes** = 9 lignes x 9 colonnes x 9 valeurs\n"]},
    ]
    _dump_nb(nb_path, {**metadata, "cells": domain_cells})
    findings = cqc.scan_diff("HEAD", {"artifact"})
    assert findings == []
    assert cqc._emit_grouped(findings, strict=True, structural_only=False) == 0
    capsys.readouterr()

    inventory = {"cell_type": "markdown", "source": ["Le carnet contient 81 cellules de code.\n"]}
    _dump_nb(nb_path, {**metadata, "cells": [*domain_cells, inventory]})
    findings = cqc.scan_diff("HEAD", {"artifact"})
    assert [snippet for _loc, _klass, snippet in findings] == ["81 cellules"]
    assert cqc._emit_grouped(findings, strict=True, structural_only=False) == 1
    assert "[REFUS]" in capsys.readouterr().out


# --------------------------------------------------------------------------- #
#  #20194 : un git diff en echec n'est pas une ardoise propre (fail-closed)
# --------------------------------------------------------------------------- #


def test_scan_diff_raises_on_unresolvable_range(tmp_path, monkeypatch):
    """Cas 3 de l'issue (mesure po-2024) : une revision introuvable rend
    rc=128 avec une sortie vide -- l'organe doit LEVER, pas rendre []."""
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init")
    _git(repo, "config", "core.autocrlf", "false")
    (repo / "f.txt").write_text("base\n", encoding="utf-8")
    _commit_all(repo, "base")
    monkeypatch.chdir(repo)

    with pytest.raises(cqc.DiffUnreadable, match="rc=128"):
        cqc.scan_diff("0000000000000000000000000000000000000000...HEAD", {"artifact"})


def test_scan_diff_raises_on_subprocess_error(monkeypatch):
    """Branche except (timeout, binaire absent) : meme garantie -- lever,
    jamais retourner [] (l'ancien chemin imprimait [ERREUR] puis rendait 0)."""

    def _boom(*_a, **_k):
        raise OSError("git introuvable")

    monkeypatch.setattr(cqc.subprocess, "run", _boom)
    with pytest.raises(cqc.DiffUnreadable, match="git introuvable"):
        cqc.scan_diff("origin/main...HEAD", {"artifact"})


def test_main_diff_failure_returns_two_and_never_ok(tmp_path, monkeypatch, capsys):
    """Controle du revert (#20194 acceptance) : un git diff rc!=0 a sortie
    VIDE doit rendre rc=2 et une sortie sans [OK]. Si l'on remet
    ``.stdout`` sans lire le code retour, ce test ROUGIT : le retour serait
    [] -> [OK] -> rc=0."""

    class _FakeProc:
        returncode = 129  # hors depot git
        stdout = ""       # vide : indistinguable d'un diff propre sans le rc
        stderr = "fatal: not a git repository"

    monkeypatch.setattr(cqc.subprocess, "run", lambda *_a, **_k: _FakeProc())
    monkeypatch.setattr(sys, "argv", ["cqc", "--diff", "origin/main...HEAD", "--strict"])
    rc = cqc.main()
    out = capsys.readouterr().out
    assert rc == 2, "un diff non mesurable doit rendre rc=2, pas 0"
    assert "[OK]" not in out, "jamais [OK] sur un diff non mesure"
    assert "[NON-MESURABLE]" in out
