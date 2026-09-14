"""Tests pour les defauts de l'organe B.0 (#16103) livres par #16107.

Defaut 1 -- un mot francais compose uniquement de lettres hexadecimales
(« effacee ») etait lu comme une empreinte citee : la levee d'ai-01 du
2026-09-14T02:45:56Z sur #16022 etait rendue « cite effacee ... absent
des commits ». Remede : un token cite doit porter AU MOINS un chiffre en
plus de l'exigence existante d'au moins une lettre. Sans le chiffre, la
classe entiere des mots francais en [a-f] (effacee, decalee, efface...)
reste des empreintes fantomes.

Defaut 3 -- crash cp1252 dans _print_unevaluated : le verdict OK etait
imprime puis l'organe crashait (rc=1 faux rouge) sur un commentaire a
relire contenant `→`. Remede : _ensure_utf8_stdout() aux entrees qui
impriment (gate, audit), silencieux quand stdout n'est pas
reconfigurable.

Defaut 2 (rebase-amend : un arbre different ne doit plus voider une levee
dont les fichiers de la PR sont intacts) a ete livre independamment sur
`main` par #16037 (`fix(nits,#15973)` -- `_rebase_preserved_by_path` +
carte chemin->blob de la tete en un appel `git/trees?recursive=1`). Ce
fichier ne le redeclare donc PAS : la version mergee fait foi et ses
tests vivent dans `test_check_unaddressed_nits.py` (raisons
`rebase_preserved`, `same_tree`, chemins removed/renamed, cartes
absentes). Seuls 1 et 3 sont couverts ici.
"""
import importlib.util
import io
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_unaddressed_nits.py"

spec = importlib.util.spec_from_file_location("check_unaddressed_nits", CHECK_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits"] = mod
spec.loader.exec_module(mod)

CITED = "230b1194"  # 8 hex, lettres ET chiffre -> reste un SHA cite apres fix


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
