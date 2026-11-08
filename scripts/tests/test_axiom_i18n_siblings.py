#!/usr/bin/env python3
"""Pins de la decision i18n de la porte d'axiomes, lac par lac (#24107).

La porte d'axiomes derive sa surface (`'*'`) puis en retire les freres `_en`
(`filter_i18n_siblings`). Ce retrait etait muet sur la DECISION : le manifeste
ne portait aucune cle `axiom-include-i18n-siblings`, et le workflow
interpolait donc toujours son defaut `|| 'false'` -- la porte ne verifiait que
la moitie FR de chaque lac bilingue.

Ces tests pinent quatre joints :

1. chaque entree du manifeste porte une cle EXPLICITE (donc l'opt-in ne peut
   plus decide en silence par le defaut du workflow) ;
2. la cle du manifeste est egale a la decision RECOMPUTEE par l'organe
   (source-level, sans Lean) ;
3. le fichier de decisions porte la RAISON ecrite de chaque ecart assume --
   une decision `"false"` sans raison n'est pas une decision ;
4. le dispatcher propage la cle VERBATIM dans la matrice (le point 1 de
   l'issue ne vaut que si la cle arrive au job).

Run: python -m pytest scripts/tests/test_axiom_i18n_siblings.py
"""
import json
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
MANIFEST = REPO / "scripts/lean/ci_lakes.json"
DECISIONS = REPO / "scripts/lean/axiom_i18n_siblings_decisions.json"
ORGAN = REPO / "scripts/lean/axiom_i18n_siblings.py"

sys.path.insert(0, str(REPO / "scripts" / "lean"))
import axiom_i18n_siblings  # noqa: E402


def _manifest():
    return json.loads(MANIFEST.read_text(encoding="utf-8"))


def _decisions():
    return json.loads(DECISIONS.read_text(encoding="utf-8"))


def test_every_manifest_lake_carries_an_explicit_i18n_decision():
    """Aucune entree ne doit retomber sur le defaut `|| 'false'` du workflow.

    Le defaut du workflow est un filet de securite, pas une decision : une
    entree sans cle explicite est un lac dont la couverture i18n n'a jamais
    ete examinee, et qui se croit couvert parce que le job tourne.
    """
    entries = _manifest()["lakes"]
    assert entries, "le manifeste est vide"
    for entry in entries:
        assert "axiom-include-i18n-siblings" in entry, (
            f"{entry['lake']} : pas de cle explicite "
            f"`axiom-include-i18n-siblings` (le workflow retombe alors sur "
            f"son defaut 'false')")
        assert entry["axiom-include-i18n-siblings"] in ("true", "false"), (
            f"{entry['lake']} : la valeur doit etre la chaine 'true' ou "
            f"'false' (le workflow l'interpole comme chaine)")


def test_the_explicit_decision_matches_the_recomputed_measurement():
    """La cle du manifeste doit etre la decision RECOMPUTEE, pas une
    declaration de principe : l'organe remesure la surface `_en` de chaque
    lac (memes outils que la porte) et compare."""
    drifts = axiom_i18n_siblings._manifest_drift(
        axiom_i18n_siblings.report()[1])
    assert not drifts, "derive manifeste <-> mesure : " + " ; ".join(drifts)


def test_the_decisions_file_matches_the_recomputed_measurement():
    """Le fichier de decisions ne doit pas deriver de la mesure (ni
    decision, ni raison). C'est le garde-fou du drift : le manifeste porte
    la valeur, ce fichier porte la preuve."""
    drifts = axiom_i18n_siblings._decisions_drift(
        axiom_i18n_siblings.report()[1])
    assert not drifts, "derive fichier de decisions <-> mesure : " + \
        " ; ".join(drifts)


def test_every_decision_carries_a_written_reason():
    """Un `"false"` sans raison ecrite n'est pas une decision assumee, c'est
    un oubli : l'issue demande la raison de chaque ecart."""
    payload = _decisions()
    recorded = {r["lake"]: r for r in payload["lakes"]}
    assert recorded, "le fichier de decisions ne porte aucune lac"
    for lake, row in recorded.items():
        assert row["decision"] in ("true", "false"), lake
        assert row.get("reason", "").strip(), (
            f"{lake} : decision sans raison ecrite")
        if row["decision"] == "false":
            assert "ecart assume" in row["reason"] or "rien a" in row["reason"] \
                or "ne change rien" in row["reason"] or "sautee" in row["reason"], (
                f"{lake} : un ecart assume doit dire POURQUOI l'opt-in ne "
                f"s'applique pas -- lu : {row['reason']}")


def test_the_decisions_file_covers_exactly_the_manifest_lakes():
    """Une lac du manifeste sans decision (ou une decision sans lac) est un
    trou de la couverture : le fichier doit epouser le manifeste."""
    manifest_lakes = {e["lake"] for e in _manifest()["lakes"]}
    recorded = {r["lake"] for r in _decisions()["lakes"]}
    assert manifest_lakes == recorded, (
        f"ecart de couverture : {manifest_lakes ^ recorded}")


def test_the_dispatcher_propagates_the_key_verbatim():
    """Le point 1 de l'issue ne vaut que si la cle du manifeste ATTEINT le
    job : le dispatcher rend les entrees du manifeste telles quelles, sans
    filtre de cles. Un filtre ajoute plus tard rendrait la decision
    decorative -- le pin le voit."""
    sys.path.insert(0, str(REPO / "scripts" / "lean"))
    import lake_matrix_dispatch
    manifest = _manifest()
    # Le manifeste est dans GATE_SELF_COVER : un changement du manifeste
    # relance TOUS les lakes.
    assert "scripts/lean/ci_lakes.json" in lake_matrix_dispatch.GATE_SELF_COVER
    include = lake_matrix_dispatch.changed_lakes(
        ["scripts/lean/ci_lakes.json"], manifest)
    assert len(include) == len(manifest["lakes"])
    for entry in include:
        assert "axiom-include-i18n-siblings" in entry, (
            f"{entry['lake']} : le dispatcher a perd la cle i18n")


def test_the_matrix_step_interpolates_the_key():
    """Le pas de la porte doit lire la cle du manifeste, avec son filet de
    securite -- et le pas doit rester conditionne a la presence de la porte
    elle-meme (`axiom-target-modules`)."""
    wf = (REPO / ".github/workflows/lean-build.yml").read_text(encoding="utf-8")
    assert ("${{ matrix.axiom-include-i18n-siblings || 'false' }}" in wf), (
        "le workflow n'interpole plus la cle i18n du manifeste")
    assert "matrix.axiom-target-modules != ''" in wf, (
        "la jambe Proof integrity n'est plus conditionnee a la cle du "
        "manifeste")


def test_the_decision_organ_stays_lean_free():
    """L'organe de decision mesure les SOURCES : il ne doit lancer aucun Lean
    (verdict user du 2026-11-01 : la preuve de compilation est la CI, jamais
    un build local). Un organe qui lancerait `lake` violerait ce verdict et
    alourdirait chaque execution de la suite."""
    src = ORGAN.read_text(encoding="utf-8")
    # On ne cherche pas la CHAINE "lake build" : la docstring de l'organe la
    # cite (c'est elle qui explique ce que la derivation enumere). Ce qu'on
    # interdit est l'EXECUTION : un sous-processus, un appel systeme, ou le
    # lanceur Lean de la porte (`LeanVerifier`).
    for forbidden in ("subprocess", "os.system", "LeanVerifier(",
                      "check_axioms("):
        assert forbidden not in src, (
            f"l'organe de decision ne doit pas lancer Lean ({forbidden})")


def test_the_opt_in_lakes_have_a_non_empty_i18n_surface():
    """Un opt-in `"true"` sur une surface i18n VIDE ne change rien a la
    porte : c'est un `"false"` qui doit le dire. La mesure est la surface
    laissee hors porte (`i18n-modules` du fichier de decisions)."""
    for row in _decisions()["lakes"]:
        if row["decision"] == "true":
            assert row["i18n-modules"] > 0, (
                f"{row['lake']} : opt-in sans surface i18n")
