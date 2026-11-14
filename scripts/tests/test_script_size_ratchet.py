"""T0 (#26364) -- cliquet de taille des scripts de coordination.

Le plan de remboursement de la dette (#26364) commence par un **cliquet** :
la taille des quinze scripts de coordination ne peut pas grossir, et un
script nouveau ne peut pas depasser 800 lignes.

Le principe est celui du cliquet d'exceptions de la politique des runners
(`scripts/ci/check_self_hosted_runner_policy.py`, invariant « la liste ne
fait que retrecir ») : l'etat verouillé est dans un **fichier de plafonds**
(`scripts/ci/script_size_ceilings.json`), et toute evolution de taille se
regarde au moment du merge, dans la PR, par une ligne motivee de ce fichier.
Un plafond releve sans justification visible est exactement ce que le
cliquet doit empecher.

Trois regles, mecaniques :

1. un script **epingle** (`tracked`) a exactement la taille enregistree --
   ni plus (il grossit), ni moins (une baisse doit abaisser le plafond) ;
2. un script **neuf** (absent de `tracked` ET de `known_large`) ne depasse
   pas `new_script_max_lines` (800 lignes) ;
3. `known_large` est l'etat des lieux au 13/11 : ces scripts depassaient
   deja le plafond des scripts neufs. Ils ne sont pas epingles (ils peuvent
   bouger), mais ils ne sont pas pour autant des scripts neufs : le plafond
   des 800 lignes ne leur est pas oppose.

Le comptage des lignes est `len(texte.splitlines())` : la derniere ligne compte
meme si le fichier ne se termine pas par un retour a la ligne, et une ligne
vide compte. C'est la convention de `wc -l` augmentee d'une unite pour un
fichier sans saut de ligne final -- le plafond ne doit pas derivationner
d'une unite selon que le fichier se termine par un retour a la ligne.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
CEILINGS = REPO_ROOT / "scripts" / "ci" / "script_size_ceilings.json"
SCRIPTS_DIR = REPO_ROOT / "scripts"

REQUIS = ("schema", "new_script_max_lines", "tracked", "known_large")


def _plafonds() -> dict[str, Any]:
    return json.loads(CEILINGS.read_text(encoding="utf-8"))


def _lignes(path: Path) -> int:
    """Nombre de lignes du fichier.

    `splitlines()` compte la derniere ligne meme si le fichier ne se termine
    pas par un retour a la ligne -- c'est la convention desiree : un fichier
    sans saut de ligne final porte une ligne de code de plus pour le lecteur
    que pour `wc -l`.
    """
    texte = path.read_text(encoding="utf-8", errors="replace")
    return len(texte.splitlines())


def test_le_fichier_de_plafonds_est_lisible_et_complet():
    """Un fichier de plafonds illisible ou incomplet desactive tout le
    cliquet : le test doit le dire, pas l'ignorer."""
    assert CEILINGS.is_file(), f"le fichier de plafonds est absent : {CEILINGS}"
    data = _plafonds()
    for cle in REQUIS:
        assert cle in data, f"la cle `{cle}` manque dans {CEILINGS.name}"
    assert isinstance(data["tracked"], dict) and data["tracked"], (
        "le registre `tracked` est vide : le cliquet ne porterait sur rien")
    assert isinstance(data["known_large"], list)
    assert isinstance(data["new_script_max_lines"], int)
    assert data["new_script_max_lines"] > 0


def test_chaque_entree_epinglee_porte_son_plafond_et_son_motif():
    """Chaque epinglage porte le DEUX informations : le plafond et le motif.

    Le motif est ce que le relecteur lit quand le plafond change : sans lui,
    un releve se distingue d'un abaissement.
    """
    for chemin, spec in _plafonds()["tracked"].items():
        assert isinstance(spec, dict), (
            f"`{chemin}` : l'epinglage doit etre un objet, pas un nombre seul")
        assert isinstance(spec.get("lines"), int) and spec["lines"] > 0, (
            f"`{chemin}` : le plafond `lines` est absent ou invalide")
        note = str(spec.get("note") or "").strip()
        assert note, f"`{chemin}` : l'epinglage ne porte aucun motif"


def test_chaque_script_epingle_existe_encore():
    """Un epinglage qui pointe un fichier disparu est un plafond perime :
    il ne borne plus rien, et il masque la disparition du script."""
    for chemin in sorted(_plafonds()["tracked"]):
        assert (REPO_ROOT / chemin).is_file(), (
            f"`{chemin}` est epingle mais absent du depot : le plafond est "
            "perime, retirer l'entree ou restaurer le fichier")


def test_aucun_script_epingle_ne_grossit_et_une_baisse_abaisse_son_plafond():
    """LE cliquet.

    La taille mesuree doit EQUALER le plafond enregistre : au-dessus, le
    script a grossi ; en dessous, le script a baisse et le plafond doit
    descendre avec lui (sinon le plafond ne borne plus rien et la baisse
    reste invisible).
    """
    echecs: list[str] = []
    for chemin, spec in sorted(_plafonds()["tracked"].items()):
        chemin_absolu = REPO_ROOT / chemin
        if not chemin_absolu.is_file():
            continue  # deja signale par test_chaque_script_epingle_existe_encore
        mesure = _lignes(chemin_absolu)
        plafond = int(spec["lines"])
        if mesure > plafond:
            echecs.append(
                f"{chemin} : {mesure} lignes, plafond {plafond} "
                f"(+{mesure - plafond}) -- le script a grossi ; relever le "
                "plafond dans scripts/ci/script_size_ceilings.json, avec son "
                "motif, dans cette PR"
            )
        elif mesure < plafond:
            echecs.append(
                f"{chemin} : {mesure} lignes, plafond {plafond} "
                f"({mesure - plafond}) -- le script a baisse, son plafond doit "
                "descendre d'autant (le cliquet ne fait que retrecir)"
            )
    assert not echecs, "\n".join(echecs)


def test_un_script_neuf_ne_depasse_pas_800_lignes():
    """Un script NEUF ne peut pas depasser le plafond des scripts neufs.

    `tracked` (epingle) et `known_large` (deja gros au 13/11) sont exclus :
    le plafond des 800 lignes ne s'applique qu'a ce qui n'existait pas.
    """
    plafonds = _plafonds()
    epingles = set(plafonds["tracked"])
    connus = set(plafonds["known_large"])
    maximum = int(plafonds["new_script_max_lines"])
    echecs: list[str] = []
    for chemin in sorted(SCRIPTS_DIR.rglob("*.py")):
        relatif = chemin.relative_to(REPO_ROOT).as_posix()
        if "__pycache__" in relatif:
            continue
        if relatif in epingles or relatif in connus:
            continue
        mesure = _lignes(chemin)
        if mesure > maximum:
            echecs.append(
                f"{relatif} : {mesure} lignes, plafond des scripts neufs "
                f"{maximum} -- scinder le module, ou l'epingler dans "
                "scripts/ci/script_size_ceilings.json avec son motif"
            )
    assert not echecs, "\n".join(echecs)


def test_un_script_connu_ne_peut_pas_revenir_dans_le_perimetre_des_neufs():
    """Un `known_large` qui passe sous le plafond des scripts neufs doit
    quitter la liste : la liste decrit un etat, pas une immunite.

    Sans ce controle, un script qui baisse resterait hors du cliquet des
    scripts neufs, alors qu'il y ferait droit.
    """
    plafonds = _plafonds()
    maximum = int(plafonds["new_script_max_lines"])
    restants: list[str] = []
    for chemin in sorted(plafonds["known_large"]):
        chemin_absolu = REPO_ROOT / chemin
        if not chemin_absolu.is_file():
            continue  # un fichier disparu n'est pas un plafond a revoir
        mesure = _lignes(chemin_absolu)
        if mesure <= maximum:
            restants.append(
                f"{chemin} : {mesure} lignes <= {maximum} -- il n'a plus sa "
                "place dans `known_large` : le retirer (il redevient un script "
                "et son plafond s'applique)"
            )
    assert not restants, "\n".join(restants)


if __name__ == "__main__":  # pragma: no cover
    import sys

    import pytest

    sys.exit(pytest.main([__file__]))
