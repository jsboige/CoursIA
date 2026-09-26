"""Contrats de check_trivial_diff (#15740) -- verdicts ancres sur les controles fondateurs.

Les valeurs ne sont pas symboliques : ce sont les nombres MESURES des PRs
nommees par l'acceptance de #15740. Un test qui echoue ici signifie que
l'organe a derive d'un verdict fonde par le user :

  #15630  1 fichier, +9/-0    « une PR de la taille d'une tranche de Mortadelle » -> TRIVIAL
  #15724  4 fichiers, +18/-2  « fine comme du papier a cigarette » (tete 8dfcd3942) -> TRIVIAL
  #15737  26 fichiers, +737/-19  la fournée demandée (x37,8 en lignes)          -> OK
  fix 2 lignes d'un bug critique (contre-exemple VERBATIM du user)              -> OK
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_trivial_diff import (  # noqa: E402
    TRIVIAL_CHANGED_LINES,
    assess,
    find_written_exception,
)

BODY_TRIVIAL_DOCS = (
    "## Sweep\n\n"
    "Grain: LIGHT/docs — lane myia-po-2025:CoursIA — prev: LIGHT/docs #15723\n\n"
    "Repare les headers orphelins des fichiers X et Y.\n"
)

BODY_TRIVIAL_LOW = (
    "Grain: LOW/docs — lane myia-po-2025:CoursIA — prev: LOW/docs #15617\n"
)

BODY_BUGFIX_2LINES = (
    "## Fix\n\n"
    "Grain: MED/tooling — lane myia-po-2023:CoursIA — prev: MED/tooling #15728\n\n"
    'Corrige le guard mort : len(probleme["tests"]) etait evalue avant le if probleme is None.\n'
)

BODY_EXCEPTION_15719 = (
    "## Sweep ORPHAN_TABLE_ROW\n\n"
    "Grain: LIGHT/docs — lane myia-po-2025:CoursIA — prev: LIGHT/docs #15723\n\n"
    "Repare les 2 derniers fichiers du scanner.\n\n"
    "Exception : residu final mesure — il ne reste que ces 2 fichiers, recensement joint.\n"
)


def _verdict(body, a, d, c=1):
    return assess(body, a, d, c)


# --- contrôles positifs (acceptance #15740) ---------------------------------

def test_control_positif_15630_mortadelle():
    """#15630 : 1 fichier, +9/-0, LOW/docs -- le user l'a nommee triviale."""
    out = _verdict(BODY_TRIVIAL_LOW, 9, 0, 1)
    assert out["verdict"] == "trivial"
    assert out["signals"]["genre_meta"] and out["signals"]["small_volume"]


def test_control_positif_15724_papier_cigarette():
    """#15724 tete 8dfcd3942 : 4 fichiers, +18/-2, LIGHT/docs -- trivial."""
    out = _verdict(BODY_TRIVIAL_DOCS, 18, 2, 4)
    assert out["verdict"] == "trivial"
    assert out["changed_lines"] == 20


# --- contrôles négatifs (acceptance #15740) ---------------------------------

def test_control_negatif_user_fix_2lignes_bug_reel():
    """Le contre-exemple VERBATIM du user : 2 lignes sur un bug critique passent.

    L'échappement se fait par la jambe GENRE (tooling n'est pas META) --
    SANS mécanisme d'exception. C'est le seul faux positif qui coûterait cher.
    """
    out = _verdict(BODY_BUGFIX_2LINES, 2, 1, 1)
    assert out["verdict"] == "ok"
    assert out["signals"]["genre_meta"] is False


def test_control_negatif_volume_15737_fournee():
    """#15737 : 26 fichiers, +737/-19 -- la fournée demandée, même tag LIGHT/docs."""
    out = _verdict(BODY_TRIVIAL_DOCS, 737, 19, 26)
    assert out["verdict"] == "ok"
    assert out["signals"]["small_volume"] is False


def test_control_negatif_genre_notebook():
    """Un petit diff notebook-python n'est jamais trivial par cet organe."""
    body = BODY_TRIVIAL_DOCS.replace("LIGHT/docs", "MED/notebook-python")
    out = _verdict(body, 9, 0, 1)
    assert out["verdict"] == "ok"


# --- exception écrite (#15719) ----------------------------------------------

def test_exception_ecrite_eteint_et_est_citee():
    """La forme « résidu final mesuré » éteint le warning ET l'organe cite la phrase."""
    out = _verdict(BODY_EXCEPTION_15719, 6, 2, 2)
    assert out["verdict"] == "ok"
    quoted = out["signals"]["written_exception"]
    assert quoted is not None
    assert "residu final mesure" in quoted.lower() or "résidu final mesuré" in quoted
    assert "èteint" in out["reason"] or "eteint" in out["reason"]


def test_exception_sans_portee_ne_compte_pas():
    """« résidu » seul (sans final/mesuré/restant) n'est pas une exception déclarée."""
    body = BODY_TRIVIAL_DOCS + "\nIl reste un résidu.\n"
    out = _verdict(body, 6, 2, 2)
    assert out["verdict"] == "trivial"


def test_find_written_exception_accents_et_null():
    assert find_written_exception(None) is None
    assert find_written_exception("rien ici") is None
    got = find_written_exception("Exception seulement résidu final mesuré (recensement joint).")
    assert got is not None and "résidu final mesuré" in got


# --- frontière de mot : marqueurs SNAKE_CASE (#16143) -----------------------

def test_marqueur_snake_case_seul_eteint_le_warning():
    """Un marqueur SNAKE_CASE écrit SEUL (sans prose autour) est reconnu.

    Défaut #16143, mesuré sur #15849 : le détecteur rendait `verdict: trivial`
    + `written_exception: null` sur un corps qui portait `FINAL_RESIDUAL` --
    exactement ce qu'il rend quand rien n'est invoqué, donc faux dans le sens
    qui ACCUSE l'auteur. La dernière ligne du tableau de l'issue (marqueur
    entouré de prose) masquait le défaut : elle passait par les mots de prose,
    pas par le marqueur.
    """
    for marker in ("FINAL_RESIDUAL", "RESIDU_FINAL_MESURE"):
        out = _verdict(BODY_TRIVIAL_DOCS + f"\n{marker}\n", 6, 2, 2)
        assert out["verdict"] == "ok", (marker, out["verdict"])
        assert out["signals"]["written_exception"] == marker, marker


def test_table_des_deux_colonnes_de_la_frontiere():
    """La colonne de DROITE compte autant que celle de gauche.

    Un test qui ne vérifierait que la gauche repasserait au vert avec les `\\b`
    simplement retirés, en rouvrant la sur-accusation (`finalement`,
    `finaliser`, `seulement`) -- l'erreur symétrique, et moins visible.
    """
    doit_accrocher = [
        "FINAL_RESIDUAL",
        "RESIDU_FINAL_MESURE",
        "final_residual",
        "residu final mesure",
        "Exception : FINAL_RESIDUAL reste a traiter",
    ]
    doit_rester_muet = [
        "finalement le sweep est termine",
        "il faut finaliser le recensement",
        "seulement deux fichiers restent",
        "le fichier finalise est commite",
        "definal",
        "exception sans portee",  # lexical seul = prose, pas une exception
    ]
    for line in doit_accrocher:
        assert find_written_exception(line) is not None, line
    for line in doit_rester_muet:
        assert find_written_exception(line) is None, line


def test_sans_frontiere_droite_final_mordrait_finalement():
    """Contrôle du raisonnement : c'est la frontière DROITE qui protège
    `finalement`, pas autre chose. La forme naïve (celle qu'on obtiendrait en
    retirant simplement les `\\b`) mord -- et c'est précisément la
    sur-accusation que le fix doit éviter."""
    naive = re.compile(r"(?<![a-z0-9])(?:final|dernier|seul)")
    assert naive.search("finalement")            # la forme naïve accuse
    assert find_written_exception("finalement") is None  # la forme livrée non


# --- verdict `empty` (#17359) ------------------------------------------------
#
# Les 4 PRs de la campagne réaccent #16638 (#16966/#16975/#16976/#16978) sont
# mesurées `{"changedFiles":0,"additions":0,"deletions":0}` : chaque branche
# porte un commit de réaccent substantiel puis des commits REPAIR-N qui
# l'annulent. Le contrôle qui prouve que le prédicat lit le DIFF et non la
# campagne est #16956 -- même campagne, même genre, même forme de branche.

BODY_EMPTY_LEAN_CAMPAIGN = (
    "## Réaccent Lean-16f\n\n"
    "Grain: MED/lean — lane myia-po-2027:CoursIA-2 — prev: MED/lean #16960\n\n"
    "Réaccent morphologique du notebook Conway Free Will Theorem.\n\n"
    "REPAIR-3 : revert des formes visees par la reserve morphologique.\n"
)

BODY_EMPTY_LIGHT_DOCS = (
    "## Sweep annulé\n\n"
    "Grain: LIGHT/docs — lane myia-po-2027:CoursIA-2 — prev: LIGHT/docs #16950\n\n"
    "Le sweep a été intégralement reverté en attente d'arbitrage.\n"
)


def test_empty_controle_positif_campagne_reaccent():
    """Contrôle POSITIF (#16975 tete 5eea88bb34, + les 3 autres) : diff nul.

    Les quatre portaient le même genre `lean` -- non-META -- donc la jambe
    genre du verdict `trivial` ne les voyait pas, et aucun organe ne nommait
    leur vacuité.
    """
    out = assess(BODY_EMPTY_LEAN_CAMPAIGN, 0, 0, 0)
    assert out["verdict"] == "empty"
    assert out["signals"]["empty_diff"] is True
    assert out["changed_files"] == 0
    # Le genre est REPORTÉ, mais il ne conditionne pas le verdict.
    assert out["genre"] == "lean"
    assert out["changed_lines"] == 0


def test_empty_est_independant_du_genre_et_du_tag():
    """Le prédicat est une seule jambe : ni le genre, ni le tag ne le filtrent.

    C'est le cas même des 4 PRs (#17359) : genre light ou non, taggé ou non,
    un diff nul est nul. Un PR vide sans tag est donc `empty`, pas `unknown`
    -- le tag manquant est gardé par son propre organe bloquant, et le router
    vers `unknown` reproduirait exactement le silence que ce verdict perce.
    """
    non_meta = assess(BODY_EMPTY_LEAN_CAMPAIGN, 0, 0, 0)
    meta = assess(BODY_EMPTY_LIGHT_DOCS, 0, 0, 0)
    sans_tag = assess("pas de tag ici, mais un diff nul", 0, 0, 0)

    assert non_meta["verdict"] == "empty"
    assert meta["verdict"] == "empty"
    assert sans_tag["verdict"] == "empty", sans_tag


def test_empty_controle_negatif_16956_meme_campagne():
    """Contrôle NÉGATIF (#16956, tete de branche `feature/16638-deaccent-lean4`,
    net 38/38) : même campagne, même genre -- le prédicat lit le diff, pas la
    campagne. Sans ce contrôle, un détecteur qui répondrait
    `empty` à tout ce qui vient de la campagne passerait au vert."""
    out = assess(BODY_EMPTY_LEAN_CAMPAIGN, 0, 38, 1)
    assert out["verdict"] != "empty", out
    assert out["changed_files"] == 1


def test_empty_controle_negatif_fix_2lignes_non_light():
    """Non-régression du contre-exemple VERBATIM du user (#15740) : une
    correction de 2 lignes sur un bug critique reste `ok`. Le verdict `empty`
    ne mesure pas une petitesse, il constate une absence."""
    out = assess(BODY_BUGFIX_2LINES, 2, 1, 1)
    assert out["verdict"] == "ok"
    assert out["verdict"] != "empty"


def test_empty_ne_reutilise_pas_l_exception_15719():
    """L'exception écrite éteint `trivial` (une fournée ramenée à son résidu
    mesuré), elle ne dit rien du vide : il n'y a pas de résidu à borner, le
    diff est nul. La phrase ne doit donc PAS transformer `empty` en `ok`."""
    out = assess(BODY_EMPTY_LEAN_CAMPAIGN + "\nException : residu final mesure, il ne reste que ce fichier.\n", 0, 0, 0)
    assert out["verdict"] == "empty", out


def test_empty_sans_additions_deletions_reste_empty():
    """Le prédicat est `changed_files == 0` seul : un payload qui omet les
    additions/deletions mais porte `changedFiles: 0` ne doit pas faire
    retomber l'organe sur `unknown`."""
    out = assess(BODY_EMPTY_LEAN_CAMPAIGN, None, None, 0)
    assert out["verdict"] == "empty"
    assert out["changed_lines"] is None


def test_empty_changed_files_absent_ne_force_pas_unknown():
    """`changedFiles` absent : la jambe vide est SAUTÉE, pas transformée en
    `unknown` -- sinon un payload qui omet le champ ferait taire le warning
    #15740 que l'organe doit déjà, alors que les deux autres verdicts ne
    lisent jamais ce champ."""
    out = assess(BODY_TRIVIAL_DOCS, 18, 2, None)
    assert out["verdict"] == "trivial", out


def test_empty_message_nomme_les_deux_sorties():
    """Le message doit nommer les deux sorties légitimes (restaurer le
    livrable, ou fermer la PR en l'écrivant) -- sinon le lecteur doit
    re-dériver quoi faire. Le verdict reste ADVISORY."""
    reason = assess(BODY_EMPTY_LEAN_CAMPAIGN, 0, 0, 0)["reason"]
    assert "restaurer le livrable" in reason
    assert "fermer la PR en l'ecrivant" in reason
    assert "ADVISORY" in reason


# --- états unknown (jamais de verdict sur absence de donnée, #14849) --------

def test_unknown_sans_tag_grain():
    out = _verdict("pas de tag ici", 5, 0, 1)
    assert out["verdict"] == "unknown"


def test_unknown_sans_stats():
    out = assess(BODY_TRIVIAL_DOCS, None, None, None)
    assert out["verdict"] == "unknown"


# --- ancrage du seuil --------------------------------------------------------

def test_barre_ancree_entre_les_controles_fondateurs():
    """Le bar doit séparer le plus gros trivial-verdicté (20) du plus petit batch (756)."""
    assert 20 < TRIVIAL_CHANGED_LINES < 756
