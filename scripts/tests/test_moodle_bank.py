#!/usr/bin/env python3
"""Banque de QCM : la passe de test exigee par #18223.

Ce que ce fichier garde
-----------------------
La banque `MyIA.AI.Notebooks/cross-series/qcm/` est un artefact commis, produit par
`scripts/notebook_tools/moodle_bank.py convert` depuis les exports XML Moodle
du Drive. Deux familles de derives sont possibles apres coup, et chacune a son
test :

- **une main edite la banque a la main** (question retiree, option cassee,
  bonne reponse effacee) : le format se casse sans que rien ne rougisse, car
  rien ne re-execute le convertisseur -- la source vit hors depot ;
- **le convertisseur derive** (regle de classification modifiee, cle de
  dedoublonnage affaiblie) : les comptes par theme bougent alors que la table
  de decision du mainteneur (28/09, issue #18223) est figee : 147 publiees,
  64 exclues C#, 29 differrees Big Data -- puis 146 apres le retrait du doublon
  ia2-010 (decision du 2026-10-06, #18285).

Le test verifie donc les invariants de FORMAT via l'organe `check` du
convertisseur lui-meme (une seule definition de la validite, pas deux), et les
COMPTES figes par la decision du mainteneur. Une re-conversion legitimate
(nouvelles questions publiees) fait bouger les comptes : le test se met a jour
dans la meme PR, avec l'explication du delta.

Le scanner se valide par ses faux negatifs
------------------------------------------
Les compteurs ne testent pas seulement le total : un theme qui perd une
question au profit d'un autre (classification deplacee) laisse le total intact
et le test aveugle. Les comptes par theme sont donc assertes individuellement,
d'apres la table de l'issue (15/36/19/24/21 + 32), moins ia2-010 retiree.
"""

import os
import re
import sys

import pytest
import yaml

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BANK = os.path.join(ROOT, "MyIA.AI.Notebooks", "cross-series", "qcm")
sys.path.insert(0, os.path.join(ROOT, "scripts", "notebook_tools"))

from moodle_bank import (  # noqa: E402
    DENTIST_TABLE,
    KEY_CORRECTIONS,
    PUBLICATION_POLICY,
    RETIRED,
    THEME_ID_PREFIX,
    apply_key_corrections,
    apply_publication_policy,
    check,
    html_to_text,
)

# Table de decision du mainteneur (28/09) -- issue #18223. Le total publie
# est la somme de ces comptes : un delta ici est un evenement a expliquer,
# pas un bruit. ia-2 : 36 -> 35, retrait du doublon ia2-010 (#18285, 06/10).
EXPECTED_PER_THEME = {
    "dl-evaluation-seance": 32,
    "ia-1-introduction-agents": 15,
    "ia-2-resolution-problemes": 35,
    "ia-3-logique-bases-connaissances": 19,
    "ia-4-systemes-probabilistes": 24,
    "ia-5-apprentissage": 21,
}
EXPECTED_TOTAL = sum(EXPECTED_PER_THEME.values())  # 146


def load_bank() -> dict[str, list[dict]]:
    bank = {}
    for fname in sorted(os.listdir(BANK)):
        if fname.endswith(".yaml"):
            with open(os.path.join(BANK, fname), encoding="utf-8") as fh:
                bank[fname[:-5]] = yaml.safe_load(fh) or []
    return bank


def test_bank_exists_with_expected_themes():
    bank = load_bank()
    assert set(bank) == set(EXPECTED_PER_THEME), (
        f"themes de la banque = {sorted(bank)} != decision mainteneur {sorted(EXPECTED_PER_THEME)}")


def test_counts_match_maintainer_decision_table():
    bank = load_bank()
    for theme, expected in EXPECTED_PER_THEME.items():
        assert len(bank[theme]) == expected, (
            f"{theme}: {len(bank[theme])} questions != {expected} (table #18223)")
    total = sum(len(qs) for qs in bank.values())
    assert total == EXPECTED_TOTAL


def test_check_organ_passes_on_committed_bank(capsys):
    """L'organe check du convertisseur doit valider la banque commise.

    Invariants portes par check() : identifiant unique, enonce non vide, source
    presente, >=2 options dont >=1 correcte, exactement 1 correcte si
    choix_unique, appariements complets, images referencees presentes.
    """
    rc = check(BANK)
    out = capsys.readouterr().out
    assert rc == 0, f"check() a rendu {rc} :\n{out}"


def test_check_flags_duplicate_options_as_attention(tmp_path, capsys):
    """Le detecteur d'options dupliquees a cles contradictoires signale en
    ATTENTION sans faire echouer l'organe. Banque synthetique : depuis le
    2026-10-06 (#18285), la banque commise n'en porte plus (ia2-008 etait un
    artefact de conversion, ia5-002 est dedoublonnee par KEY_CORRECTIONS).
    """
    rec = [{"id": "ia5-001", "theme": "ia-5-apprentissage", "type": "multichoice",
            "source": "test", "enonce": "Q ?", "choix_unique": True,
            "options": [{"texte": "A", "correcte": True}, {"texte": "A", "correcte": False},
                        {"texte": "B", "correcte": False}]}]
    (tmp_path / "ia-5-apprentissage.yaml").write_text(
        yaml.safe_dump(rec, allow_unicode=True), encoding="utf-8")
    rc = check(str(tmp_path))
    out = capsys.readouterr().out
    assert rc == 0, f"check() a rendu {rc} :\n{out}"
    assert "ia5-001" in out and "cles contradictoires" in out, out


def test_committed_bank_has_no_contradictory_duplicates(capsys):
    """Garde de #18285 : plus aucune option dupliquee a cles contradictoires."""
    rc = check(BANK)
    out = capsys.readouterr().out
    assert rc == 0, f"check() a rendu {rc} :\n{out}"
    assert "cles contradictoires" not in out, out


def test_superscripts_survive_conversion():
    """Les exports portent les puissances en <span vertical-align:super>. Les
    aplatir faisait de O(d^b) et O(db) deux options << O(db) >> a cles opposees
    (ia2-008, attribue a tort a la source Moodle par la relecture de 09/2026).
    Markup reel de l'export MSMEM4EN08 2018, retours a la ligne compris."""
    span = ('<span style="font-size:21.0pt;font-family:Georgia;font-style:italic">O(d</span>'
            '<span style="font-size:21.0pt;font-family:Georgia;\ncolor:black;font-style:\n'
            'italic;vertical-align:super">b/2</span><span style="font-size:21.0pt">) </span>')
    assert html_to_text(span) == "O(d^(b/2))"
    assert html_to_text('O(b<span style="vertical-align:super">d</span>)') == "O(b^d)"
    assert html_to_text('O(db<span style="vertical-align:super"></span>)') == "O(db)"
    assert html_to_text("O(b<sup>m</sup>)") == "O(b^m)"
    by_id = {q["id"]: q for qs in load_bank().values() for q in qs}
    textes = [o["texte"] for o in by_id["ia2-008"]["options"]]
    assert len(textes) == len(set(textes)), textes
    assert [o["texte"] for o in by_id["ia2-008"]["options"] if o["correcte"]] == ["O(db)"]


def _correct(by_id, qid):
    return [o["texte"] for o in by_id[qid]["options"] if o["correcte"]]


def test_key_corrections_applied_to_committed_bank():
    """Chaque correction decidee le 2026-10-06 (#18285) est dans la banque, avec
    sa note : une re-conversion ou une edition a la main qui la perd rougit."""
    by_id = {q["id"]: q for qs in load_bank().values() for q in qs}
    for qid, corr in KEY_CORRECTIONS.items():
        q = by_id[qid]
        textes = {o["texte"]: o["correcte"] for o in q["options"]}
        for texte, valeur in corr.get("cles", {}).items():
            assert textes[texte] is valeur, f"{qid}: '{texte}' devrait etre {valeur}"
        for old in corr.get("textes", {}):
            assert old not in textes, f"{qid}: '{old}' aurait du etre reecrit"
        assert "Correction de la relecture" in q.get("explication", ""), f"{qid}: note absente"
    assert _correct(by_id, "ia2-018") == ["2.4"]
    assert _correct(by_id, "ia2-019") == ["7.7"]
    assert _correct(by_id, "ia4-011") == ["59/64"]
    assert _correct(by_id, "ia4-018") == ["389.47€"]
    assert _correct(by_id, "ia5-007") == ["Réseaux de neurones artificiels"]


def test_key_correction_fails_loudly_when_source_drifts():
    """Une correction qui ne trouve plus son option ne doit jamais passer en
    silence : la source aurait change sous la decision du mainteneur."""
    rec = {"options": [{"texte": "62/65", "correcte": True}, {"texte": "59/64", "correcte": False}]}
    with pytest.raises(ValueError, match="ia4-011"):
        apply_key_corrections("ia4-011", rec)


def test_figure_references_present_in_enonces():
    """Chaque figure embarquee (fichier de images/) est referencee par l'enonce
    de sa question, et chaque question a figure embarquee porte la reference
    `images/` : revision NanoClaw #18263 (le strip des balises supprimait le
    <img> qui portait le chemin reecrit).

    Depuis la revue ai-01 du 28/09, `ia4-004` porte la figure **redessinee**
    (`images/ia4-004.png`) et non plus la photographie du manuel.
    """
    bank = load_bank()
    by_id = {q["id"]: q for qs in bank.values() for q in qs}
    for qid in ("ia2-027", "ia4-004"):
        enonce = by_id[qid]["enonce"]
        assert f"images/{qid}." in enonce, f"{qid}: reference images/ absente de l'enonce"
    assert "images/ia4-004.png" in by_id["ia4-004"]["enonce"], "ia4-004 doit pointer la figure redessinee"
    files = sorted(os.listdir(os.path.join(BANK, "images")))
    referenced = set()
    for q in by_id.values():
        referenced.update(re.findall(r"images/([^\s)>\]]+)", q["enonce"]))
    for f in files:
        assert f in referenced, f"images/{f}: fichier orphelin"


def test_images_ne_contient_que_du_redessine_ou_du_mainteneur():
    """Garde de la decision de publication (#18263, revue ai-01) : `images/`
    ne contient que la figure redessinee et les figures propres au cours. Les
    trois fichiers non republiables -- photographie d'une page du manuel
    (ia4-004.jpg), captures d'ecran de sa table (ia4-006/007.png) -- ont
    disparu du depot, et rien ne les reintroduit : la PUBLICATION_POLICY du
    convertisseur remplace leur extraction.
    """
    files = sorted(os.listdir(os.path.join(BANK, "images")))
    assert files == ["ia2-027.png", "ia4-004.png"], f"images/ = {files}"
    for qid in ("ia4-004", "ia4-006", "ia4-007", "ia2-010"):
        assert qid in PUBLICATION_POLICY, f"{qid}: decision de publication absente du convertisseur"


def test_publication_policy_remplace_les_figures_non_republiables():
    """Les trois modes de la politique, sur des enonces synthetiques : le
    convertisseur ne peut pas re-introduire une figure non republiable sans
    faire rougir ce test (la source XML vit hors depot).
    """
    source = "intro:\n\n[figure: @@PLUGINFILE@@/x.png]\n\nquestion ?"
    table = apply_publication_policy("table", source, "indifferent")
    assert "[figure" not in table and DENTIST_TABLE in table
    assert "0.108" in table and "0.576" in table, "les huit valeurs doivent etre restituees"
    externe = apply_publication_policy("external", source, "indifferent")
    assert externe.count("[figure externe non disponible]") == 1
    assert "dropbox" not in externe and "PLUGINFILE" not in externe


def test_enonces_a_tableau_conservent_leurs_lignes():
    """Le tableau markdown doit survivre a l'aller-retour YAML : un enonce
    re-emis en scalaire replie perdrait ses retours a la ligne et le tableau
    ne serait plus un tableau (d'ou le bloc litteral du BankDumper).
    """
    bank = load_bank()
    by_id = {q["id"]: q for qs in bank.values() for q in qs}
    for qid in ("ia4-006", "ia4-007"):
        enonce = by_id[qid]["enonce"]
        lignes = [l for l in enonce.splitlines() if l.startswith("|")]
        assert len(lignes) == 10, f"{qid}: {len(lignes)} lignes de tableau au lieu de 10"
        assert lignes[1] == "|---|---|---|---|", f"{qid}: ligne de separation absente"


def test_ia2010_retired_in_favour_of_ia2027(capsys):
    """ia2-010 (export 2018, figure Dropbox expiree) et ia2-027 (export 2020,
    figure embarquee) sont la meme question : decision du 2026-10-06 (#18285),
    seule ia2-027 reste. Plus aucune figure annoncee sans reference."""
    assert "ia2-010" in RETIRED
    ids = {q["id"] for qs in load_bank().values() for q in qs}
    assert "ia2-010" not in ids and "ia2-027" in ids
    rc = check(BANK)
    out = capsys.readouterr().out
    assert rc == 0, f"check() a rendu {rc} :\n{out}"
    assert "sans reference embarquee" not in out, out


def test_ids_stable_pattern_and_unique():
    bank = load_bank()
    ids = [q["id"] for qs in bank.values() for q in qs]
    assert len(ids) == len(set(ids)), "identifiants dupliques"
    prefix_by_theme = THEME_ID_PREFIX
    for theme, qs in bank.items():
        # une question retiree garde son numero : la sequence le saute
        sequence = (f"{prefix_by_theme[theme]}-{i:03d}" for i in range(1, 1000))
        expected = [qid for qid in sequence if qid not in RETIRED][:len(qs)]
        assert [q["id"] for q in qs] == expected, f"{theme}: ids hors de la sequence stable"


def test_no_published_csharp_or_bigdata():
    """Les lots exclus (C#) et differs (Big Data) ne doivent jamais fuiter
    dans la banque : ni par theme, ni par contenu de categorie dans la source."""
    bank = load_bank()
    for theme, qs in bank.items():
        assert "csharp" not in theme and "big-data" not in theme
        for q in qs:
            assert not re.search(r"C#|Big Data", q.get("enonce", "") or ""), (
                f"{q['id']}: enonce C#/Big Data dans un theme publie ({theme})")


def test_types_reconcile_with_inventory():
    """14 vrai/faux (tous evaluation de seance) et 1 appariement distinct --
    les << 3 appariements >> de l'inventaire initial etaient 3 occurrences
    verbatim de la meme question dans l'export JSBoige (mesure, issue #18223)."""
    bank = load_bank()
    all_q = [q for qs in bank.values() for q in qs]
    tf = [q for q in all_q if q["type"] == "truefalse"]
    matching = [q for q in all_q if q["type"] == "matching"]
    assert len(tf) == 14
    assert all(q["theme"] == "dl-evaluation-seance" for q in tf)
    assert len(matching) == 1
    assert matching[0]["theme"] == "ia-1-introduction-agents"
    assert len(matching[0]["appariements"]) >= 3


@pytest.mark.parametrize("theme", sorted(EXPECTED_PER_THEME))
def test_every_question_carries_verifier_contract(theme):
    """Contrat #18207 : la banque doit nourrir verifier(...) sans conversion.
    Champs minimaux par question, types Python corrects."""
    bank = load_bank()
    for q in bank[theme]:
        assert isinstance(q["enonce"], str) and q["enonce"].strip()
        assert isinstance(q["source"], str) and q["source"].strip()
        if q["type"] in ("multichoice", "truefalse"):
            assert isinstance(q["choix_unique"], bool)
            assert isinstance(q["options"], list) and len(q["options"]) >= 2
            for o in q["options"]:
                assert isinstance(o["texte"], str) and o["texte"].strip()
                assert isinstance(o["correcte"], bool)
