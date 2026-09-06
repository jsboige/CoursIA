"""Tests for detect_repeated_prose.py — radotage intra-notebook.

Le contrat epingle : (1) le temoin fondateur Search-09c (puces section 5 vs
table section 7, pre-fix de la PR #14794) DOIT tirer sur le signal
paraphrase ; (2) le post-fix (renvoi d'une phrase) DOIT rester muet ; (3) le
signal verbatim tire sur le copier-colle reflowe ; (4) deux paragraphes
distincts partageant un vocabulaire de sujet restent muets. Pas de reseau,
pas de kernel.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from detect_repeated_prose import (MIN_CONTAINMENT, MIN_PARAPHRASE_CHARS,
                                   MIN_SHARED_RARE, detect)

FIXTURE = Path(__file__).parent / "fixtures" / "search09c_ponts_pair.json"


def nb(*md_sources):
    return {"cells": [{"cell_type": "markdown", "source": s, "outputs": []}
                      for s in md_sources],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def para_types(findings):
    return {f["type"] for f in findings}


def test_founding_fixture_fires_paraphrase():
    """La paire fondateur epinglee comme fixture (blob pre-fix = branche de
    la PR #14794, jamais mergee sur main : le replay doit vivre en fixture,
    pas en cat-file). Le signal B est le seul capable de la voir -- la
    paraphrase ne partage AUCUNE sequence verbatim."""
    fx = json.loads(FIXTURE.read_text(encoding="utf-8"))
    assert fx["provenance"]["founding_pr"] == 14794
    got = detect({"cells": fx["pre_cells"]})
    para = [f for f in got if f["type"] == "paraphrased_block"]
    assert para, "temoin fondateur muet : detecteur debranche"
    fwd = [f for f in para if f["cell"] == 0 and f["target_cell"] == 1]
    assert fwd, f"le finding ne pointe pas cell[9] -> cell[13] : {para}"
    f0 = fwd[0]
    assert len(f0["shared_rare"]) >= MIN_SHARED_RARE
    assert f0["containment"] >= MIN_CONTAINMENT
    # Le vocabulaire discriminant du cas fondateur est bien dans le temoin.
    for w in ("funnel", "pymc", "conspiration", "fantôme"):
        assert w in f0["shared_rare"], f"{w} absent du temoin"


def test_postfix_fixture_is_silent():
    """Le renvoi d'une phrase vers la section 7 (le fix lui-meme) ne doit
    plus declencher le signal paraphrase : l'organe ENDOSSE le fix."""
    fx = json.loads(FIXTURE.read_text(encoding="utf-8"))
    got = detect({"cells": fx["post_cells"]})
    assert not [f for f in got if f["type"] == "paraphrased_block"]


def test_verbatim_block_duplication_fires():
    dup = ("Ce paragraphe pedagogique de plus de cent vingt caracteres "
           "explique en detail pourquoi la recherche a ecart borne echoue "
           "sans heuristique adaptee, avec des exemples concrets mesures.")
    got = detect(nb(f"# Titre\n\n{dup}\n", f"## Autre section\n\n  {dup}  \n"))
    verb = [f for f in got if f["type"] == "verbatim_block"]
    assert len(verb) == 1
    assert len(verb[0]["occurrences"]) == 2
    cells = {o["cell"] for o in verb[0]["occurrences"]}
    assert cells == {0, 1}


def test_verbatim_below_threshold_silent():
    short = "Phrase courte repetee, sous le seuil."
    assert detect(nb(f"# A\n\n{short}", f"# B\n\n{short}")) == []


def test_distinct_topic_paragraphs_silent():
    """Deux paragraphes qui partagent le vocabulaire de sujet d'un notebook
    (funnel, variance, parametres -- typiques de l'intro et du TP) mais
    disent des choses differentes ne doivent PAS tirer."""
    p1 = ("Le funnel de la variance apparait quand des parametres derivent "
          "ensemble ; la geometrie contrainte restaure l'independance et le "
          "sampling redevient efficace sur les modeles hierarchiques "
          "profonds a nombreux niveaux.")
    p2 = ("En TP, on observera le funnel sur un modele a huit parametres : "
          "tracer la variance conditionnelle par niveau, puis comparer les "
          "chaines avant et apres reparametrisation non centree du "
          "predicteur hierarchique etudié en cours.")
    assert detect(nb(f"# A\n\n{p1}", f"# B\n\n{p2}")) == []


def test_intro_recap_mirror_fires():
    """Le miroir intro-plan / conclusion-recap est le premier pattern du
    corpus (containment 0.9+) : le signal doit le voir -- c'est du radotage
    structurel, juge par l'humain en advisory."""
    chapters = ("Tweety-2 basic logics, Tweety-3 advanced, Tweety-4 aspic+, "
                "Tweety-5 abstract argumentation, Tweety-7a extended "
                "frameworks, Tweety-8 agent dialogues, Tweety-9 preferences "
                "et Tweety-10 MLN structurent la serie autour des logiques "
                "d'argumentation graduees et de leurs semantiques.")
    intro = ("Dans ce notebook d'introduction nous installerons le socle "
             "Java et decouvrirons la serie : " + chapters)
    recap = ("Pour conclure ce notebook d'introduction, retenez le parcours "
             "de la serie pose ici : " + chapters)
    got = detect(nb(intro, recap))
    assert "paraphrased_block" in para_types(got)


def test_code_cells_ignored():
    dup = ("Ce paragraphe de plus de cent vingt caracteres, place dans des "
           "cellules CODE identiques, ne doit rien declencher : l'organe ne "
           "regarde que les cellules markdown du notebook pedagogique.")
    cells = [{"cell_type": "code", "source": f"# {dup}", "outputs": []},
             {"cell_type": "code", "source": f"# {dup}", "outputs": []}]
    assert detect({"cells": cells}) == []


def test_block_length_floor_respected():
    """Un bloc sous MIN_PARAPHRASE_CHARS ne peut pas tirer le signal B,
    meme pleinement contenu dans une autre cellule."""
    tiny = ("le funnel de pymc et le double-q de mgs avec l'anti fantome ict "
            "sont les trois ponts")
    assert len(tiny) < MIN_PARAPHRASE_CHARS
    big = ("Section ponts : " + tiny + " — detaille chacune des trois "
           "directions avec leurs liens et leurs relations profondes au "
           "trace de ce notebook de recherche sur la discrepance.")
    got = detect(nb(tiny, big))
    assert not [f for f in got if f["type"] == "paraphrased_block"
                and f["cell"] == 0]


def test_self_test_fixture_provenance_pinned():
    """La fixture doit citer son origine : sans preuve de provenance, un
    temoin mute silencieusement devient invérifiable (lecon fixture #14603)."""
    fx = json.loads(FIXTURE.read_text(encoding="utf-8"))
    prov = fx["provenance"]
    assert prov["pre_fix_commit"].startswith("4587dc7d")
    assert "Search-09c" in prov["notebook"]
