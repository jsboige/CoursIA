"""Tests pour #20066 -- le libelle « NON LEVE » ne doit pas affirmer sur le fond
ce que l'organe n'a pas mesure.

Defaut (#19594) : quand la levee cite un SHA rembobine par un push ulterieur,
`_rebase_preserved_by_path` exige un blob byte-identique a la tete pour chaque
chemin touche par le commit. Une PR qui continue de travailler sur les memes
fichiers echoue donc a cette identite et l'organe pose `tree_differs=True`.
Le libelle affichait alors « l'arbre DIFFERE de la tete : vraie reserve a
reposer » : une affirmation sur le fond que l'organe n'a jamais mesuree, il a
seulement constate que des blobs ont bouge.

Correctif (piste 1 de l'issue) : nommer ce qui a ete mesure, « blob modifie
depuis la levee, fond non verifie ». Seule la chaine change. Le verdict, le rc,
la cle `tree_differs` et la branche « arbre non comparable » restent identiques.

Aucun appel reseau : `_print_sha_notes` est pure, on lui passe le dict du
resultat et on lit la sortie standard.
"""
import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_unaddressed_nits.py"

spec = importlib.util.spec_from_file_location("check_unaddressed_nits", CHECK_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits"] = mod
spec.loader.exec_module(mod)

FORMULE_BLOB = "blob modifié depuis la levée, fond non vérifié"
ANCIENNE_FORMULE = "vraie réserve à reposer"
REFUS_CONSERVATEUR = "arbre non comparable, refus conservateur"


def _levee_rembobinee(tree_differs: bool) -> dict:
    """Resultat minimal : une levee rembobinee, arbre connu ou non."""
    return {
        "voided_lifts": [
            {
                "author": "jsboige",
                "at": "2026-10-07T02:18:00+00:00",
                "sha": "9621e67216",
                "tree_differs": tree_differs,
            }
        ]
    }


def _sortie(capsys, result: dict) -> str:
    mod._print_sha_notes(result)
    return capsys.readouterr().out


def test_arbre_different_nomme_le_blob_et_pas_le_fond(capsys):
    """Avant : « vraie réserve à reposer ». Après : la formule mesurée, et
    l'ancienne affirmation absente."""
    out = _sortie(capsys, _levee_rembobinee(tree_differs=True))
    assert FORMULE_BLOB in out
    assert ANCIENNE_FORMULE not in out
    assert REFUS_CONSERVATEUR not in out


def test_arbre_different_garde_la_ligne_non_levee(capsys):
    """Le verdict bloquant ne change pas : la ligne reste « [!] NON LEVE »."""
    out = _sortie(capsys, _levee_rembobinee(tree_differs=True))
    premiere = out.splitlines()[0]
    assert premiere.startswith("  [!] NON LEVE"), premiere
    assert "cite 9621e67216" in premiere


def test_arbre_non_comparable_garde_le_refus_conservateur(capsys):
    """Branche False inchangee : l'arbre n'est pas comparable, refus
    conservateur, et la nouvelle formule n'apparait pas."""
    out = _sortie(capsys, _levee_rembobinee(tree_differs=False))
    assert REFUS_CONSERVATEUR in out
    assert FORMULE_BLOB not in out
    assert ANCIENNE_FORMULE not in out
    assert out.splitlines()[0].startswith("  [!] NON LEVE")
