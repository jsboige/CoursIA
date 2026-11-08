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


# --- residuel de #20066 : le TROISIEME etat (aucun blob compare) -----------
#
# `tree_differs` dit que les deux arbres sont connus et differents ; il ne dit
# pas qu'un blob a ete compare. Quand `rewound_files_map` n'a pas d'entree
# pour le SHA, `sha_files` est vide et aucune comparaison n'a lieu : annoncer
# « blob modifie depuis la levee » est alors une affirmation que l'organe n'a
# pas mesuree.

AUCUN_BLOB = "aucun blob comparable"


def _levee_avec_etat(tree_differs: bool, blob_state) -> dict:
    """Resultat minimal portant l'etat de comparaison des blobs."""
    result = _levee_rembobinee(tree_differs)
    result["voided_lifts"][0]["blob_state"] = blob_state
    return result


def test_aucun_blob_comparable_n_annonce_pas_un_blob_modifie(capsys):
    """Le cas du commentaire de suivi du 2026-10-16 : arbres connus,
    `sha_files` vide, donc zero blob compare. Le refus reste, le mot change."""
    out = _sortie(capsys, _levee_avec_etat(True, mod._BLOB_UNCOMPARABLE))
    assert AUCUN_BLOB in out
    assert FORMULE_BLOB not in out
    assert out.splitlines()[0].startswith("  [!] NON LEVE")


def test_blob_compare_et_different_garde_la_formule_mesuree(capsys):
    """Etat explicite `differs` : au moins un blob a ete compare, la formule
    de la piste 1 reste celle qui decrit la mesure."""
    out = _sortie(capsys, _levee_avec_etat(True, mod._BLOB_DIFFERS))
    assert FORMULE_BLOB in out
    assert AUCUN_BLOB not in out


def test_entree_sans_etat_garde_le_libelle_historique(capsys):
    """Compatibilite : un resultat produit avant ce correctif (pas de cle
    `blob_state`) garde exactement le libelle de la piste 1."""
    out = _sortie(capsys, _levee_rembobinee(tree_differs=True))
    assert FORMULE_BLOB in out
    assert AUCUN_BLOB not in out


# --- l'etat lui-meme, sans passer par le libelle --------------------------

def test_etat_uncomparable_sur_donnee_absente():
    """Aucune donnee : rien n'a pu etre compare, et ce n'est pas un
    « different »."""
    assert mod._rebase_blob_state([], {"a": "x"}) == mod._BLOB_UNCOMPARABLE
    assert mod._rebase_blob_state([("a", "x", "modified", "")], {}) == mod._BLOB_UNCOMPARABLE
    # liste tronquee par l'API : une identite demi-prouvee n'est pas une preuve
    tronquee = [(f"f{i}", "b", "modified", "") for i in range(300)]
    assert mod._rebase_blob_state(tronquee, {"f0": "b"}) == mod._BLOB_UNCOMPARABLE
    # statut inconnu : refus conservateur, et aucun blob juge sur cette entree
    assert mod._rebase_blob_state([("a", "x", "weird", "")], {"a": "x"}) == mod._BLOB_UNCOMPARABLE


def test_etat_preserved_et_differs_sur_donnee_complete():
    """Controle positif des deux autres etats : identite prouvee vs blob
    reellement different."""
    assert mod._rebase_blob_state(
        [("a", "x", "modified", "")], {"a": "x"}) == mod._BLOB_PRESERVED
    assert mod._rebase_blob_state(
        [("a", "x", "modified", "")], {"a": "y"}) == mod._BLOB_DIFFERS
    # Une deletion arrive de l'API sans `sha` (champ vide) : la garde
    # « entree incomplete » rend `uncomparable`, jamais `preserved`. C'est le
    # comportement d'avant #20066 (`False`), et c'est le plus honnete -- aucun
    # blob de deletion n'est comparable. Le refus ne bouge donc pas.
    assert mod._rebase_blob_state(
        [("a", "", "removed", "")], {}) == mod._BLOB_UNCOMPARABLE


def test_contrat_booleen_de_15973_inchange():
    """`_rebase_preserved_by_path` reste un booleen : seul `preserved` est
    vrai, les deux autres etats refusent comme avant."""
    assert mod._rebase_preserved_by_path([("a", "x", "modified", "")], {"a": "x"}) is True
    assert mod._rebase_preserved_by_path([("a", "x", "modified", "")], {"a": "y"}) is False
    assert mod._rebase_preserved_by_path([], {"a": "x"}) is False


# --- residuel de #20066, piste 2 COMPLETE : la survie des SYMBOLES ----------
#
# Quand `blob_state == differs` (la PR a continue de travailler les memes
# fichiers), le fond de la levee reste verifiable : les def/class INTRODUITS
# par le commit rembobine existent-ils encore a la tete ? Survie complete =
# artefact non bloquant ; symbole absent = refus NOMME ; donnee manquante =
# refus `differs` courant (fail-closed, contrat de l'issue).

def test_introduced_symbols_extrait_defs_et_classes_des_lignes_ajoutees():
    """Seules les lignes AJOUTEES comptent : contexte et deletions ne
    produisent rien, async def et class sont extraits, ordre preserve."""
    patch = ("\n"
             " def contexte():\n"
             "     pass\n"
             "-def ancienne():\n"
             "+def nouvelle_fonction():\n"
             "+    pass\n"
             "+class NouvelleClasse:\n"
             "+    pass\n"
             "+    async def methode_async(self):\n"
             "+        pass\n")
    out = mod._introduced_symbols({"scripts/p.py": patch})
    assert out == {"scripts/p.py": ["nouvelle_fonction", "NouvelleClasse",
                                    "methode_async"]}


def test_introduced_symbols_ignore_non_python_et_vides():
    """Markdown, notebooks et patches absents ne donnent rien a verifier."""
    out = mod._introduced_symbols(
        {"docs/a.md": "+def f():\n+    pass\n",
         "nb/x.ipynb": "+def g():\n",
         "scripts/vide.py": "",
         "scripts/rien.py": "-def h():\n"})
    assert out == {}


def test_symbols_survive_head_tous_presents():
    """Le fichier de tete porte chaque symbole : all_survive + compte."""
    introduced = {"scripts/p.py": ["foo", "Bar"]}
    head = {"scripts/p.py": "blob1"}
    fetch = lambda sha: "class Bar:\n    pass\n\ndef foo():\n    return 1\n"
    res = mod._symbols_survive_head(introduced, head, fetch)
    assert res["verdict"] == "all_survive"
    assert res["checked"] == 2
    assert res["files"] == 1


def test_symbols_survive_head_symbole_manquant_nomme():
    """Un symbole disparu de la tete : verdict missing, le nom cite."""
    introduced = {"scripts/p.py": ["foo", "baz"]}
    head = {"scripts/p.py": "blob1"}
    fetch = lambda sha: "def foo():\n    return 1\n"  # baz parti
    res = mod._symbols_survive_head(introduced, head, fetch)
    assert res["verdict"] == "missing"
    assert res["missing"] == ["baz"]
    assert res["checked"] == 2


def test_symbols_survive_head_fichier_parti_de_la_tete():
    """Fichier absent de la tete : ses symboles sont manquants, sans fetch."""
    introduced = {"scripts/p.py": ["foo"]}
    def fetch(sha):
        raise AssertionError("aucun fetch ne doit avoir lieu pour un chemin absent")
    res = mod._symbols_survive_head(introduced, {}, fetch)
    assert res["verdict"] == "missing"
    assert res["missing"] == ["foo"]


def test_symbols_survive_head_blob_illisible_fail_closed():
    """Blob de tete illisible : no_data, jamais permissif."""
    def fetch(sha):
        raise RuntimeError("api down")
    res = mod._symbols_survive_head({"scripts/p.py": ["foo"]},
                                    {"scripts/p.py": "blob1"}, fetch)
    assert res["verdict"] == "no_data"
    assert res["reason"] == "blob_unreadable"


def test_libelle_artefact_symboles_survivants(capsys):
    """L'artefact symbols_survive est une ligne [i] non bloquante et dit la
    mesure : blobs modifies, symboles presents."""
    result = {"rewind_artifacts": [
        {"author": "jsboige", "at": "2026-10-07T02:18:00+00:00",
         "sha": "9621e67216", "reason": "symbols_survive"}]}
    out = _sortie(capsys, result)
    assert out.splitlines()[0].startswith("  [i] levee de jsboige")
    assert "symboles introduits par la levée tous présents à la tête" in out


def test_libelle_refus_nomme_les_symboles_absents(capsys):
    """Le refus avec symboles manquants est le SEUL qui parle de reserve :
    il nomme ce qui a disparu, mesure a l'appui."""
    result = {"voided_lifts": [
        {"author": "jsboige", "at": "2026-10-07T02:18:00+00:00",
         "sha": "9621e67216", "tree_differs": True,
         "blob_state": mod._BLOB_DIFFERS,
         "symbols": {"verdict": "missing",
                     "missing": ["fetch_latest_claim_stamps_bulk"],
                     "checked": 3}}]}
    out = _sortie(capsys, result)
    assert out.splitlines()[0].startswith("  [!] NON LEVE")
    assert "ABSENT(s) de la tête" in out
    assert "fetch_latest_claim_stamps_bulk" in out
    assert FORMULE_BLOB not in out


def test_libelle_refus_sans_verdict_symboles_garde_la_formule_mesuree(capsys):
    """no_data / pas de carte : rien n'a ete mesure sur le fond, la formule
    de la piste 1 reste celle qui decrit honnetement la mesure."""
    result = {"voided_lifts": [
        {"author": "jsboige", "at": "2026-10-07T02:18:00+00:00",
         "sha": "9621e67216", "tree_differs": True,
         "blob_state": mod._BLOB_DIFFERS,
         "symbols": {"verdict": "no_data", "reason": "blob_unreadable"}}]}
    out = _sortie(capsys, result)
    assert FORMULE_BLOB in out
    assert "ABSENT(s)" not in out
