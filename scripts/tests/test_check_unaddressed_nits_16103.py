"""Tests pour les trois defauts de l'organe B.0 (#16103).

Defaut 1 -- un mot francais compose uniquement de lettres hexadecimales
(« effacee ») etait lu comme une empreinte citee : la levee d'ai-01 du
2026-09-14T02:45:56Z sur #16022 etait rendue « cite effacee ... absent
des commits ». Remede : un token cite doit porter AU MOINS un chiffre en
plus de l'exigence existante d'au moins une lettre.

Defaut 2 -- un rebase-amend (geste ordinaire, `gh pr update-branch`
compris) voide une levee valide : l'arbre du commit cite differe
mecaniquement de la tete apres rebase, donc tree_differs -> refus
BLOQUANT, alors que les fichiers de la PR sont byte-pour-byte identiques.
Remede : quand les arbres different, comparer les blobs des CHEMINS de
la PR (cartes chemin->blob des listings recursifs) ; identite exacte ->
artefact non bloquant reason="pr_files_unchanged" (le motif d'impression
existait deja, inatteignable depuis le retrait #15566). Fail-closed :
tout doute retombe sur le refus conservateur.

Defaut 3 -- crash cp1252 dans _print_unevaluated : le verdict OK etait
imprime puis l'organe crashait (rc=1 faux rouge) sur un commentaire a
relire contenant `→`. Remede : _ensure_utf8_stdout() aux entrees qui
impriment (gate, audit).
"""
import importlib.util
import io
import sys
from datetime import datetime, timezone
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_unaddressed_nits.py"

spec = importlib.util.spec_from_file_location("check_unaddressed_nits", CHECK_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits"] = mod
spec.loader.exec_module(mod)

MERGED = datetime(2026, 9, 14, 12, 0, tzinfo=timezone.utc)

CITED = "230b1194"  # 8 hex, lettres ET chiffre -> reste un SHA cite apres fix

LIFT = {
    "author": {"login": "myia-ai-01"},
    "createdAt": "2026-09-13T19:32:00Z",
    "body": "Levee de la reserve -- verifie firsthand sur 230b1194, "
            "l'arbre est propre.",
}


def run(**extra):
    data = {
        "number": 1234,
        "title": "t",
        "author": {"login": "jsboige"},
        "comments": [LIFT],
        "reviews": [],
        "commits": [{"oid": "f" * 40,
                     "committedDate": "2026-09-13T20:00:00Z"}],
        "files": [{"path": "a.py"}, {"path": "b.md"}],
    }
    data.update(extra)
    return mod.analyse(data, [], MERGED)


# ---------------------------------------------------------------------------
# Defaut 1 -- extraction d'empreintes
# ---------------------------------------------------------------------------

def test_defaut1_mot_francais_hexa_nest_pas_un_sha():
    """Repro #16103 : « effacee » (e-f-f-a-c-e-e, 7 lettres toutes dans
    [0-9a-f]) satisfaisait le motif hexa et etait extrait comme SHA."""
    cited = mod._cited_shas(
        "Levee -- verifie, le contenu effacee par le push est propre.")
    assert "effacee" not in cited
    assert cited == set()


def test_defaut1_vrai_sha_avec_chiffre_conserve():
    body = f"Levee de la reserve -- verifie firsthand sur {CITED}."
    assert mod._cited_shas(body) == {CITED}


def test_defaut1_token_lettres_seules_rejete_avec_controles():
    """Toute la classe : lettres-seules rejetees, numeriques-seules
    rejetees (regle existante), melange lettres+chiffre accepte."""
    assert mod._cited_shas("deadbeef") == set()          # lettres seules
    assert mod._cited_shas("20260830") == set()          # chiffres seuls (regle anterieure)
    assert mod._cited_shas("effacee2") == {"effacee2"}   # melange : reste candidat


# ---------------------------------------------------------------------------
# Defaut 2 -- rebase-amend : identite de CONTENU des fichiers de la PR
# ---------------------------------------------------------------------------

def _rebase_context(cited_blobs, head_blobs):
    """Fixtures du chemin rebase : SHA resolu rattache a la PR (#1234),
    arbres DIFFERENTS (rebase), cartes de blobs maitrisees."""
    return dict(
        _absent_sha_messages={CITED: "rebase: base rafraichie (#1234)"},
        _absent_sha_trees={CITED: "treeCITED"},
        _head_tree="treeHEAD",
        _absent_sha_blobs={CITED: cited_blobs},
        _head_blobs=head_blobs,
    )


def test_defaut2_rebase_fichiers_pr_intacts_est_artefact_non_bloquant():
    """Repro #16103 defaut 2 : apres rebase, arbre DIFFERENT mais blobs
    des chemins de la PR identiques -> rewind_artifact (non bloquant),
    plus voided_lift."""
    res = run(**_rebase_context(
        {"a.py": "blob1", "b.md": "blob2"},
        {"a.py": "blob1", "b.md": "blob2"}))
    assert res["voided_lifts"] == []
    assert len(res["rewind_artifacts"]) == 1
    art = res["rewind_artifacts"][0]
    assert art["sha"] == CITED
    assert art["reason"] == "pr_files_unchanged"


def test_defaut2_vrai_changement_de_contenu_reste_bloquant():
    """Symetrique (question posee par l'issue) : un vrai rembobinage de
    contenu -- un blob de la PR a change -- reste une reserve bloquante."""
    res = run(**_rebase_context(
        {"a.py": "blob1", "b.md": "blob2"},
        {"a.py": "blobMODIFIE", "b.md": "blob2"}))
    assert res["rewind_artifacts"] == []
    assert len(res["voided_lifts"]) == 1
    assert res["voided_lifts"][0]["sha"] == CITED
    assert res["voided_lifts"][0]["tree_differs"] is True


def test_defaut2_doute_carte_absente_retombe_sur_le_refus():
    """Fail-closed : cartes de blobs introuvables (API muette, listing
    tronque) -> refus conservateur, jamais une identite non prouvee."""
    res = run(**_rebase_context(
        {"a.py": "blob1", "b.md": "blob2"},
        None))  # _head_blobs = None : doute
    assert res["rewind_artifacts"] == []
    assert len(res["voided_lifts"]) == 1


def test_defaut2_chemin_absent_dune_carte_retombe_sur_le_refus():
    """Fail-closed : un chemin de la PR manquant a l'une des cartes (fichier
    ajoute par le rebase) n'est pas une identite prouvable."""
    res = run(**_rebase_context(
        {"a.py": "blob1"},                       # b.md absent cote cite
        {"a.py": "blob1", "b.md": "blob2"}))
    assert res["rewind_artifacts"] == []
    assert len(res["voided_lifts"]) == 1


def test_defaut2_sans_vue_fichiers_pr_pas_de_voie_permissive():
    """L'audit retro (sans `files`) ne peut JAMAIS emprunter l'echappatoire :
    pas de cartes, pas d'identite, refus conservateur inchange."""
    res = run(files=None, **_rebase_context(
        {"a.py": "blob1"}, {"a.py": "blob1"}))
    assert res["rewind_artifacts"] == []
    assert len(res["voided_lifts"]) == 1


def test_defaut2_meme_arbre_reste_le_premier_critere():
    """Regression #15556 : push muet (arbre identique) -> same_tree,
    independamment des cartes de blobs."""
    res = run(
        _absent_sha_messages={CITED: "wake-commit (#1234)"},
        _absent_sha_trees={CITED: "treeHEAD"},
        _head_tree="treeHEAD",
        _absent_sha_blobs={}, _head_blobs=None)
    assert res["voided_lifts"] == []
    assert res["rewind_artifacts"][0]["reason"] == "same_tree"


# ---------------------------------------------------------------------------
# Defaut 3 -- crash cp1252 de l'impression
# ---------------------------------------------------------------------------

UNEVAL_RESULT = {
    "unevaluated": [{
        "author": "reviewer",
        "at": "2026-09-14T03:00:00Z",
        "body": "commentaire a relire portant → et du texte",
        "after_last_commit": False,
    }],
    "unevaluated_total": 1,
}


def test_defaut3_repro_crash_cp1252_avant_remade():
    """Repro : sous stdout cp1252, l'impression du commentaire non evalue
    leve UnicodeEncodeError (le verdict OK etait deja imprime)."""
    old = sys.stdout
    sys.stdout = io.TextIOWrapper(io.BytesIO(), encoding="cp1252")
    try:
        with pytest.raises(UnicodeEncodeError):
            mod._print_unevaluated(UNEVAL_RESULT)
    finally:
        sys.stdout = old


def test_defaut3_ensure_utf8_stdout_guerit_limpression():
    """Remede : apres _ensure_utf8_stdout(), la meme impression passe et
    encode le caractere en utf-8."""
    old = sys.stdout
    buf = io.BytesIO()
    sys.stdout = io.TextIOWrapper(buf, encoding="cp1252")
    try:
        mod._ensure_utf8_stdout()
        mod._print_unevaluated(UNEVAL_RESULT)  # ne doit pas lever
        sys.stdout.flush()
        assert "→".encode("utf-8") in buf.getvalue()
    finally:
        sys.stdout = old


def test_defaut3_ensure_utf8_stdout_silencieux_si_non_reconfigurable():
    """Un stdout sans reconfigure (capture exotique, StringIO de test) ne
    fait pas echouer l'organe : le remede est silencieux, jamais bloquant."""

    class NoReconfigure(io.StringIO):
        def reconfigure(self, *a, **k):
            raise AttributeError("no reconfigure")

    old = sys.stdout
    sys.stdout = NoReconfigure()
    try:
        mod._ensure_utf8_stdout()  # ne doit pas lever
    finally:
        sys.stdout = old
