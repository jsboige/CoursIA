#!/usr/bin/env python3
"""Tests du registre anti-entropie (#23175).

L'organe porte un **instrument de resultat** par entree : une commande, et
la valeur que cette commande rend. Ce que ces tests verrouillent :

  1. **le verdict** — `AVANCE`, `STAGNE`, `RECULE` — dans les deux sens
     (moins c'est mieux, plus c'est mieux), et `PREMIERE MESURE` quand il
     n'y a pas encore de reference ;
  2. le **controle positif** exige par l'issue : le padding rend `RECULE`
     a la mesure du 2026-10-28 (813 contre une reference de 776) ;
  3. le **controle negatif** : une valeur qui va vers sa cible rend
     `AVANCE` ;
  4. l'**instrument** : une valeur absente n'est pas un zero, et le code
     de sortie d'un organe qui constate un ecart reel ne rend pas la
     mesure invalide ;
  5. le **commentaire** : il porte le marqueur, la valeur du jour, la
     reference et le verdict ;
  6. la **fraîcheur** : le registre ne commente pas toutes les demi-heures.

Les nombres viennent de mesures REELLES (issue #23175, 2026-10-28T20:45Z,
et la mesure de l'organe dans la meme journee).
"""

import datetime as dt
import importlib.util
import pathlib
import sys

import pytest

COORD = pathlib.Path(__file__).resolve().parent.parent / "coordination"
if str(COORD) not in sys.path:
    sys.path.insert(0, str(COORD))

_spec = importlib.util.spec_from_file_location(
    "anti_entropy_register", COORD / "anti_entropy_register.py")
aer = importlib.util.module_from_spec(_spec)
sys.modules["anti_entropy_register"] = aer
_spec.loader.exec_module(aer)

# La mesure du soir (2026-10-28), reprise de l'issue #23175 et remesuree
# par l'organe dans la meme journee.
PADDING_SOIR = 813.0
# La reference d'origine : mesuree le 2026-10-21 par l'instrument
# d'AVANT #23193. Elle reste une entree de test du verdict (une grandeur
# synthetique), mais elle n'est plus la reference du registre : comparer
# 38 (instrument courant) a 776 (ancien instrument) fabricait un verdict.
PADDING_REFERENCE = 776.0
# La reference REBASEE : meme arbre, mesure par l'instrument courant
# (`inventory_notebook_names.py` a d818b008b), sur un checkout ALIGNE sur
# la revision nommee (`origin/main` a 6135a06), mesuree le 2026-10-31.
#
# 38 et non 44 : l'instrument prend sa LISTE de carnets dans la revision
# nommee mais lit leur CONTENU dans l'arbre local. Sur un checkout aligne
# il rend 38 ; sur un checkout en retard (clone principal a d9aee247) il
# rend 44 -- l'ecart est exactement la serie Wavelet renommee par
# 6135a06. La reference est donc celle de l'ARBRE NOMME, mesuree dans
# les conditions ou l'instrument mesure ce qu'il dit mesurer.
PADDING_REFERENCE_REBASE = 38.0
# L'identite de l'instrument au moment du rebasage.
INSTRUMENT_PADDING = ("scripts/notebook_tools/inventory_notebook_names.py"
                       "@d818b008b5558d9a755c81d3d05e29ac23a9f823")


def entree(cle="padding-nommage", sens="descend", cible=0.0):
    return next(e for e in aer.REGISTRE if e.cle == cle) if sens else None


# --- le verdict --------------------------------------------------------------

@pytest.mark.parametrize("valeur,attendu", [
    (700.0, "AVANCE"),    # le padding baisse : on avance
    (776.0, "STAGNE"),    # rien ne bouge
    (813.0, "RECULE"),    # le padding monte : le chantier recule
    (900.0, "RECULE"),
])
def test_le_verdict_descend(valeur, attendu):
    assert aer.verdict(valeur, PADDING_REFERENCE, "descend") == attendu


@pytest.mark.parametrize("valeur,attendu", [
    (2.0, "AVANCE"),      # l'escalier se materialise
    (1.0, "STAGNE"),
    (0.0, "RECULE"),      # la pile recule
])
def test_le_verdict_ascend(valeur, attendu):
    assert aer.verdict(valeur, 1.0, "ascend") == attendu


def test_sans_reference_le_verdict_dit_premiere_mesure():
    assert aer.verdict(813.0, None, "descend") == "PREMIERE MESURE"


def test_une_valeur_absente_ne_compare_pas_a_une_reference():
    """Une valeur absente n'est pas une valeur : l'instrument a ete muet.

    Comparer `None` a une reference levait un `TypeError` qui cassait le
    cycle entier — et la reference existe presque toujours (celle portee
    par l'issue), donc le premier instrument muet suffisait.
    """
    assert aer.verdict(None, PADDING_REFERENCE, "descend") == \
        "INSTRUMENT ILLEGIBLE"
    assert aer.verdict(None, None, "descend") == "INSTRUMENT ILLEGIBLE"
    assert aer.verdict(None, PADDING_REFERENCE, "ascend") == \
        "INSTRUMENT ILLEGIBLE"


def test_un_sens_inconnu_est_une_erreur():
    with pytest.raises(ValueError):
        aer.verdict(1.0, 2.0, "baisse")


# --- le controle positif (exige par l'issue) ---------------------------------

def test_le_padding_rend_recule_a_la_mesure_du_soir():
    """Le controle positif de l'issue : « un controle positif sur le padding :
    il doit rendre RECULE a la mesure de ce soir ».

    Il tient dans les deux sens : contre la reference d'origine (776, une
    grandeur synthetique) et contre la reference rebassee du registre (44).
    Dans les deux cas la mesure du soir (813) est un RECULE."""
    e = entree("padding-nommage")
    assert e.reference is not None
    assert aer.verdict(PADDING_SOIR, PADDING_REFERENCE, e.sens) == "RECULE"
    assert aer.verdict(PADDING_SOIR, e.reference.valeur, e.sens) == "RECULE"


def test_le_controle_negatif_une_valeur_qui_va_vers_la_cible_rend_avance():
    """Le controle negatif de l'issue : « une entree dont la valeur bouge
    vers sa cible rend AVANCE »."""
    assert aer.verdict(700.0, PADDING_REFERENCE, "descend") == "AVANCE"
    assert aer.vers_cible(700.0, PADDING_REFERENCE, 0.0, "descend") is True
    assert aer.vers_cible(813.0, PADDING_REFERENCE, 0.0, "descend") is False


# --- l'instrument ------------------------------------------------------------

def test_extraire_un_chemin_dans_un_json():
    sortie = '{"by_classification": {"ambigu": 813, "conforme": 757}}'
    assert aer.extraire(sortie, ("chemin", "by_classification.ambigu")) == 813.0


def test_extraire_le_nombre_de_lignes():
    assert aer.extraire("a\n\nb\nc\n", ("lignes",)) == 3.0


def test_extraire_le_nombre_de_lignes_filtrees_par_suffixe():
    """Le filtre par suffixe aligne l'instrument sur sa cible : la cible
    de l'escalier est en CARNETS, donc un README de plus ne doit pas
    faire bouger la valeur."""
    sortie = "a.ipynb\nb.md\nc.ipynb\n"
    assert aer.extraire(sortie, ("lignes", ".ipynb")) == 2.0
    assert aer.extraire(sortie, ("lignes",)) == 3.0


def test_extraire_la_somme_de_deux_listes():
    sortie = '{"divergence": {"missing": [1, 2, 3], "phantom": [4]}}'
    assert aer.extraire(sortie, ("somme_listes", ("divergence.missing",
                                                  "divergence.phantom"))) == 4.0


def test_une_specification_inconnue_est_une_erreur():
    with pytest.raises(ValueError):
        aer.extraire("{}", ("inconnu",))


def test_age_jours_rend_un_age_positif():
    now = dt.datetime(2026, 10, 28, 22, 0, tzinfo=dt.UTC)
    # 1793220204 = 2026-10-28T20:43Z
    age = aer.extraire("1793220204", ("age_jours",), maintenant=now)
    assert 0.0 < age < 0.1


def test_age_jours_borne_a_zero_un_timestamp_futur():
    """Un timestamp dans le futur (horloge en avance) ne doit pas rendre un
    age NEGATIF : un age negatif se lirait « plus recent que maintenant »,
    ce qui n'est pas un ecart de mesure."""
    now = dt.datetime(2020, 1, 1, tzinfo=dt.UTC)
    assert aer.extraire("1793220204", ("age_jours",), maintenant=now) == 0.0


def test_la_valeur_publiee_se_relu_egalement():
    """La detection « la valeur a bouge » relit la valeur DANS le commentaire
    publie et la compare a la mesure du jour. Une valeur qui ne fait pas
    l'aller-retour rendrait la detection faussement negative (ou
    faussement positive a chaque passage)."""
    valeur = aer.extraire("1793220204", ("age_jours",))
    corps = aer.commentaire_du_jour(
        [{"cle": "catalogue-fraicheur", "issue": 5081, "titre": "t",
          "commande": ["git"], "sens": "descend", "valeur": valeur,
          "erreur": "", "reference": None, "verdict": "PREMIERE MESURE"}],
        "2026-10-28T23:00:00Z")
    assert aer._valeur_du_commentaire(corps, "catalogue-fraicheur") == valeur


def test_un_instrument_qui_echoue_ne_donne_pas_de_zero():
    """Une valeur absente n'est PAS un zero : c'est une mesure non faite."""
    e = aer.Entree(cle="cas", issue=1, titre="x",
                   commande=("python", "-c", "import sys; sys.exit(3)"),
                   extraction=("lignes",), sens="descend")
    valeur, erreur, _note = aer.mesurer(e)
    assert valeur is None
    assert erreur


def test_le_commentaire_publie_ne_publie_pas_de_chemin_de_machine():
    """Le commentaire est PUBLIC : y afficher le chemin absolu de
    l'interpreteur publie une empreinte de la machine
    (`C:\\Python314\\python.exe`)."""
    corps = aer.commentaire_du_jour(
        [{"cle": "padding-nommage", "issue": 5081, "titre": "t",
          "commande": [sys.executable, "scripts/notebook_tools/x.py", "--json"],
          "sens": "descend", "cible": 0.0, "valeur": 813.0, "erreur": "",
          "reference": None, "verdict": "RECULE"}],
        "2026-10-28T23:00:00Z")
    assert sys.executable not in corps
    assert "python scripts/notebook_tools/x.py --json" in corps


def test_un_code_de_sortie_non_nul_ne_rend_pas_la_mesure_invalide():
    """`check_catalog_freshness.py` sort 1 quand l'ecart constate est REEL :
    la valeur se lit quand meme."""
    e = aer.Entree(cle="cas", issue=1, titre="x",
                   commande=("python", "-c",
                             "import sys; print('{\"v\": 7}'); sys.exit(1)"),
                   extraction=("chemin", "v"), sens="descend")
    valeur, erreur, note = aer.mesurer(e)
    assert valeur == 7.0
    assert erreur == ""
    assert "rc=1" in note


def test_le_chemin_reel_ne_crashe_pas_quand_l_instrument_est_muet(monkeypatch):
    """Le chemin REEL (`mesurer_tout`), avec un instrument muet ET une
    reference presente : le verdict doit etre `INSTRUMENT ILLEGIBLE`.

    C'est le `TypeError` constate a la relecture : `verdict(None, …)`
    comparait `None` a une reference. Comme la reference de repli est
    portee par l'issue, elle existe presque toujours — le premier
    instrument muet suffisait a casser le cycle entier (traceback, aucune
    publication, aucun etat).
    """
    e = aer.Entree(cle="cas", issue=1, titre="x",
                   commande=(sys.executable, "-c", "import sys; sys.exit(3)"),
                   extraction=("lignes",), sens="descend",
                   reference=aer.Reference(776.0, "2026-10-21"))
    monkeypatch.setattr(aer, "_commentaires_marques", lambda issue: [])
    out = aer.mesurer_tout(registre=(e,),
                           now=dt.datetime(2026, 10, 29, 3, 0, tzinfo=dt.UTC))
    assert out[0]["valeur"] is None
    assert out[0]["verdict"] == "INSTRUMENT ILLEGIBLE"


# --- le commentaire ----------------------------------------------------------

def test_le_commentaire_porte_le_marqueur_et_les_trois_champs():
    entrees = [{
        "cle": "padding-nommage", "issue": 5081, "titre": "t",
        "commande": ["cmd"], "sens": "descend",
        "valeur": 813.0, "erreur": "",
        "reference": {"valeur": 776.0, "mesure_le": "2026-10-21"},
        "verdict": "RECULE",
    }]
    corps = aer.commentaire_du_jour(entrees, "2026-10-28T23:00:00Z")
    assert aer.MARQUEUR in corps
    assert "813" in corps
    assert "776" in corps
    assert "RECULE" in corps
    assert "#5081" in corps


def test_une_entree_sans_valeur_n_invente_pas_de_zero():
    entrees = [{
        "cle": "x", "issue": 1, "titre": "t", "commande": ["cmd"],
        "sens": "descend", "valeur": None, "erreur": "instrument muet",
        "reference": None, "verdict": "PREMIERE MESURE",
    }]
    corps = aer.commentaire_du_jour(entrees, "2026-10-28T23:00:00Z")
    assert "INSTRUMENT ILLEGIBLE" in corps
    assert "| 0 |" not in corps


# --- la fraicheur de la publication ------------------------------------------

def _corps(valeur):
    return (f"<!-- {aer.MARQUEUR} -->\n\n"
            "| entree | issue | valeur | reference (7 j) | sens | verdict |\n"
            "|---|---|---:|---:|---|---|\n"
            f"| `padding-nommage` | #5081 | {valeur} | 776 (2026-10-21) | "
            "descend | RECULE |\n")


def test_sans_commentaire_precedent_on_publie():
    due, motif = aer.due_pour_publier(None, [], aer.dt.datetime.now())
    assert due is True
    assert "premiere" in motif


def test_un_commentaire_de_la_journee_et_une_valeur_inchangee_ne_republie_pas():
    """Deux passages du meme cycle ne commentent pas deux fois."""
    now = dt.datetime.now(dt.UTC)
    dernier = {"created_at": (now - dt.timedelta(hours=3)).strftime(
        "%Y-%m-%dT%H:%M:%SZ"), "body": _corps(813.0)}
    entrees = [{"cle": "padding-nommage", "issue": 5081, "valeur": 813.0}]
    due, _motif = aer.due_pour_publier(dernier, entrees, now)
    assert due is False


def test_une_valeur_changee_oblige_a_republier():
    now = dt.datetime.now(dt.UTC)
    dernier = {"created_at": (now - dt.timedelta(hours=3)).strftime(
        "%Y-%m-%dT%H:%M:%SZ"), "body": _corps(813.0)}
    entrees = [{"cle": "padding-nommage", "issue": 5081, "valeur": 812.0}]
    due, motif = aer.due_pour_publier(dernier, entrees, now)
    assert due is True
    assert "changee" in motif


def test_un_commentaire_vexe_d_un_jour_se_rafreshit():
    """Le mandat veut le verdict lisible dans le cycle qui l'observe : un
    registre qui ne se republie que tous les sept jours masquerait un
    `RECULE` pendant une semaine."""
    now = dt.datetime.now(dt.UTC)
    dernier = {"created_at": (now - dt.timedelta(days=1, hours=1)).strftime(
        "%Y-%m-%dT%H:%M:%SZ"), "body": _corps(813.0)}
    entrees = [{"cle": "padding-nommage", "issue": 5081, "valeur": 813.0}]
    due, motif = aer.due_pour_publier(dernier, entrees, now)
    assert due is True
    assert "vieux" in motif


# --- le registre -------------------------------------------------------------

def test_le_registre_a_des_instruments_reels():
    """Chaque entree porte une commande et une extraction : l'issue demande
    « une commande, et la valeur que cette commande rend »."""
    for e in aer.REGISTRE:
        assert e.commande, e.cle
        assert e.extraction[0] in ("chemin", "lignes", "somme_listes",
                                   "age_jours"), e.cle
        assert e.sens in ("descend", "ascend"), e.cle
        assert e.issue > 0


def test_les_instruments_du_registre_existent_dans_le_depot():
    """L'instrument de chaque entree existe dans le depot.

    Le test doit porter sur l'ENTREE, pas sur le fait que le premier mot
    de la commande soit litteralement « python » : le registre y met
    `sys.executable` (un chemin absolu), donc la condition n'etait jamais
    vraie et le corps du test ne s'executait pas — un test qui passe sans
    rien verifier.
    """
    for e in aer.REGISTRE:
        if pathlib.Path(str(e.commande[0])).name.startswith("python"):
            assert len(e.commande) > 1, f"{e.cle} : commande sans script"
            chemin = pathlib.Path(str(e.commande[1]))
            if not chemin.is_absolute():
                chemin = aer.RACINE / chemin
            assert chemin.exists(), f"{e.cle} : {chemin} introuvable"


def test_l_escalier_compte_les_carnets_et_non_les_fichiers():
    """La cible de l'escalier est en CARNETS : l'instrument ne doit pas
    compter un README de plus comme une marche de l'escalier."""
    e = entree("dynamics-escalier")
    assert e.extraction == ("lignes", ".ipynb"), e.extraction
    assert ".ipynb" in e.note


def test_la_reference_du_padding_est_celle_de_l_issue():
    """La reference du padding est REBASEE sur l'instrument courant.

    Elle porte l'identite de l'instrument qui l'a produite : sans elle, une
    reference n'est pas comparable a la mesure du jour (cf
    `comparables`), et c'est ce qui produisait le verdict « AVANCE »
    fabrique sur l'entree « padding et nommage »."""
    e = entree("padding-nommage")
    assert e.reference.source == "issue #23175"
    assert e.reference.mesure_le == "2026-10-31"
    assert e.reference.valeur == PADDING_REFERENCE_REBASE
    assert e.reference.instrument == INSTRUMENT_PADDING
    # Et la reference rebasee est comparable a l'instrument courant.
    assert aer.comparables(INSTRUMENT_PADDING, e.reference.instrument)


def test_le_cliquet_lit_l_etat_des_verdicts():
    """Le cliquet du budget (#23174) lit l'etat ecrit par l'organe : un
    etat absent ne retient rien (fail-OPEN)."""
    etat = aer.lire_etat(str(pathlib.Path("C:/nonexistent/etat.json")))
    assert etat == {}


# --- la reference lue dans le commentaire publie -----------------------------

def _commentaire(valeur, reference, date):
    return (f"<!-- {aer.MARQUEUR} -->\n\n"
            "| entree | issue | valeur | reference (7 j) | sens | verdict |\n"
            "|---|---|---:|---:|---|---|\n"
            f"| `padding-nommage` | #5081 | {valeur} | {reference} | descend "
            "| RECULE |\n")


def test_la_reference_est_la_publication_dotee_de_sept_jours(monkeypatch):
    """La reference = la valeur portee par la publication la plus recente
    **dotee d'au moins sept jours**.

    Une publication declenchee par un CHANGEMENT de valeur peut dater de
    la veille : s'y fier daterait la reference d'un jour faux, et le
    verdict porterait sur 24 h au lieu de 7 jours.
    """
    commentaires = [
        {"created_at": "2026-10-21T20:00:00Z",
         "body": _commentaire(776, "— (pas de reference)", "2026-10-21")},
        {"created_at": "2026-10-28T20:00:00Z",
         "body": _commentaire(813, "776 (2026-10-21)", "2026-10-28")},
    ]
    monkeypatch.setattr(aer, "_commentaires_marques",
                        lambda issue: commentaires)
    now = dt.datetime(2026, 10, 28, 22, 0, tzinfo=dt.UTC)
    ref = aer.lire_reference(5081, "padding-nommage", now=now)
    assert ref is not None
    assert ref.valeur == 776.0
    assert ref.mesure_le == "2026-10-21"


def test_sans_sept_jours_d_historique_la_reference_est_absente(monkeypatch):
    """Tant qu'aucune publication n'a sept jours, la reference est ABSENTE.

    Le repli sur « la plus ancienne publication » remplacerait la
    reference de sept jours par une valeur de la veille : le verdict
    porterait alors sur un intervalle d'un jour au lieu de sept. L'appelant
    garde alors la reference de l'issue (la valeur mesuree il y a sept
    jours, publiee dans l'issue elle-meme).
    """
    commentaires = [
        {"created_at": "2026-10-27T20:00:00Z",
         "body": _commentaire(800, "— (pas de reference)", "2026-10-27")},
        {"created_at": "2026-10-28T20:00:00Z",
         "body": _commentaire(813, "800 (2026-10-27)", "2026-10-28")},
    ]
    monkeypatch.setattr(aer, "_commentaires_marques",
                        lambda issue: commentaires)
    now = dt.datetime(2026, 10, 28, 22, 0, tzinfo=dt.UTC)
    assert aer.lire_reference(5081, "padding-nommage", now=now) is None


def test_sans_commentaire_publie_la_reference_est_absente(monkeypatch):
    monkeypatch.setattr(aer, "_commentaires_marques", lambda issue: [])
    assert aer.lire_reference(5081, "padding-nommage") is None


def test_une_entree_absente_du_commentaire_n_a_pas_de_reference(monkeypatch):
    monkeypatch.setattr(aer, "_commentaires_marques",
                        lambda issue: [{"created_at": "2026-10-28T20:00:00Z",
                                        "body": _commentaire(813, "776", "2026-10-28")}])
    assert aer.lire_reference(5081, "autre-entree") is None


# --- la publication ----------------------------------------------------------

def test_la_publication_echoue_si_le_corpus_publie_est_trop_court(monkeypatch):
    """Un corps < 100 caracteres apres une publication depuis un fichier =
    le piege `-f body=@` a tire. La publication doit etre signalee KO."""
    import json as _json
    publie = f"<!-- {aer.MARQUEUR} -->\n@C:/tmp/f.md"
    monkeypatch.setattr(aer.subprocess, "run", lambda *a, **k: type(
        "R", (), {"returncode": 0,
                  "stdout": _json.dumps([{"body": publie}])})())
    assert aer._verifier_publication(5081, publie) is False


def test_la_publication_echoue_si_le_corpus_publie_est_un_payload_json(monkeypatch):
    """Le corps publie ne doit pas etre le PAYLOAD JSON complet passe
    comme corps : c'est le piege de transport, et il est long — la garde
    de longueur est structurellement aveugle a ce cas.

    Il ne porte pas le marqueur : la relecture, qui cherche le commentaire
    balise parmi les derniers commentaires, ne le trouve donc pas, et la
    publication est signalee KO."""
    import json as _json
    payload = _json.dumps({"body": "x" * 200})
    monkeypatch.setattr(aer.subprocess, "run", lambda *a, **k: type(
        "R", (), {"returncode": 0,
                  "stdout": _json.dumps([{"body": payload}])})())
    assert aer._verifier_publication(5081, "x" * 200) is False


def test_la_publication_reussit_si_le_corpus_publie_est_le_bon(monkeypatch):
    import json as _json
    corps = f"<!-- {aer.MARQUEUR} -->\n" + "x" * 200
    monkeypatch.setattr(aer.subprocess, "run", lambda *a, **k: type(
        "R", (), {"returncode": 0,
                  "stdout": _json.dumps([{"body": corps}])})())
    assert aer._verifier_publication(5081, corps) is True


def test_un_commentaire_tiers_intercale_ne_provoque_pas_de_faux_echec(monkeypatch):
    """Le fil de l'issue est actif et plusieurs lanes y ecrivent : un
    commentaire tiers peut arriver ENTRE le POST et la relecture.

    Lire « le dernier commentaire de l'issue » produirait alors un faux
    echec — et le cliquet avancerait sur une publication reelle mais non
    verifiee. La relecture cherche le commentaire BALISE parmi les
    derniers."""
    import json as _json
    corps = f"<!-- {aer.MARQUEUR} -->\n" + "x" * 200
    tiers = "commentaire d'une autre lane, sans marqueur"
    monkeypatch.setattr(aer.subprocess, "run", lambda *a, **k: type(
        "R", (), {"returncode": 0,
                  "stdout": _json.dumps([{"body": corps},
                                          {"body": tiers}])})())
    assert aer._verifier_publication(5081, corps) is True


# --- la pagination (defauts de la relecture du 2026-10-29) -------------------

def test_les_pages_du_fil_sont_collectees_et_non_une_seule(monkeypatch):
    """`gh api --paginate` CONCATENE les pages : une page JSON par page de
    reponse.

    Un `json.loads` de la sortie entiere echoue des la deuxieme page, et
    l'except rendait `[]` en silence : les references historiques
    disparaissaient, et la detection de premiere publication etait
    reactivee a chaque cycle.

    Deux pages, dont une seule porte le marqueur : le commentaire
    balise de la deuxieme page doit etre trouve, et le commentaire sans
    marqueur de la premiere ne doit rien contribuer."""
    import json as _json
    page1 = _json.dumps([{"created_at": "2026-10-20T10:00:00Z",
                          "body": "commentaire de fond, sans marqueur"}])
    page2 = _json.dumps([{"created_at": "2026-10-21T10:00:00Z",
                          "body": f"<!-- {aer.MARQUEUR} -->\n"
                                  + "x" * 200}])
    vus = {}

    def _run(cmd, **k):
        vus["cmd"] = cmd
        return type("R", (), {"returncode": 0,
                              "stdout": page1 + "\n" + page2 + "\n"})()

    monkeypatch.setattr(aer.subprocess, "run", _run)
    trouves = aer._commentaires_marques(5081)
    assert len(trouves) == 1, trouves
    assert aer.MARQUEUR in trouves[0]["body"]
    assert "--paginate" in vus["cmd"], "la lecture doit paginer"


def test_une_publication_au_dela_de_la_premiere_page_est_relu(monkeypatch):
    """Une issue de plus de trente commentaires porte notre publication
    RECENTE au-dela de la premiere page.

    `.[-10:]` sans `--paginate` selectionnait les dix derniers elements
    de la PREMIERE page : notre publication n'y etait pas, et une
    publication reelle etait declaree en echec.

    La relecture paginee doit trouver la publication, qu'elle soit
    precedee de trente commentaires anciens sans notre corps.

    Le temoin est **discriminant** : on verifie que la commande reellement
    emise PAGINE, et pas seulement le verdict. Une relecture qui rend
    `True` parce qu'elle n'a rien su lire (repli fail-open) passerait
    sinon ce test sans avoir rien verifie."""
    import json as _json
    corps = f"<!-- {aer.MARQUEUR} -->\n" + "x" * 200
    anciens = [{"created_at": "2026-10-20T10:00:00Z",
                 "body": f"commentaire ancien {i}"} for i in range(30)]
    # page 1 : les trente anciens ; page 2 : notre publication
    page1 = _json.dumps(anciens)
    page2 = _json.dumps([{"created_at": "2026-10-29T10:00:00Z", "body": corps}])
    vus = []

    def _run(cmd, **k):
        vus.append(cmd)
        return type("R", (), {"returncode": 0,
                              "stdout": page1 + "\n" + page2 + "\n"})()

    monkeypatch.setattr(aer.subprocess, "run", _run)
    assert aer._verifier_publication(5081, corps) is True
    assert vus, "la relecture doit avoir interroge l'API"
    assert "--paginate" in vus[0], f"la relecture doit paginer : {vus[0]}"


def test_la_publication_est_relue_par_son_identifiant_exact(monkeypatch):
    """Quand le POST a rendu l'URL du commentaire, la relecture vise CE
    commentaire : elle ne depend plus du volume de commentaires de
    l'issue, ni d'un commentaire tiers intercale."""
    import json as _json
    corps = f"<!-- {aer.MARQUEUR} -->\n" + "x" * 200
    vus = {}

    def _run(cmd, **k):
        vus["cmd"] = cmd
        return type("R", (), {"returncode": 0,
                              "stdout": _json.dumps([{"body": corps}])})()

    monkeypatch.setattr(aer.subprocess, "run", _run)
    assert aer._verifier_publication(5081, corps, 6480453395) is True
    assert "issues/comments/6480453395" in " ".join(vus["cmd"]), vus["cmd"]


def test_l_identifiant_du_commentaire_publie_est_lu_dans_la_sortie_du_post():
    """`gh issue comment` rend l'URL du commentaire cree : elle porte son
    identifiant, qui permet la relecture exacte."""
    sortie = "https://github.com/jsboige/CoursIA/issues/5081#issuecomment-6480453395\n"
    assert aer._identifiant_commentaire(sortie) == 6480453395
    assert aer._identifiant_commentaire("") is None
    assert aer._identifiant_commentaire("pas une URL") is None


def test_le_post_publie_puis_relu_par_son_identifiant(monkeypatch):
    """Le cycle complet : le POST rend une URL, la relecture vise le
    commentaire designe. Aucun second parcours du fil n'est necessaire."""
    corps = f"<!-- {aer.MARQUEUR} -->\n" + "x" * 200
    import json as _json
    appels = []

    def _run(cmd, **k):
        appels.append(cmd)
        if cmd[1] == "issue":
            return type("R", (), {
                "returncode": 0,
                "stdout": "https://github.com/jsboige/CoursIA/issues/5081"
                          "#issuecomment-6480453395\n"})()
        return type("R", (), {"returncode": 0,
                              "stdout": _json.dumps([{"body": corps}])})()

    monkeypatch.setattr(aer, "_token_gh", lambda: "jeton")
    monkeypatch.setattr(aer.subprocess, "run", _run)
    assert aer.publier(5081, corps) is True
    relire = [c for c in appels if "issues/comments/" in " ".join(c)]
    assert relire, "la relecture doit viser le commentaire par son identifiant"


def test_publier_refuse_une_identite_non_verifiee(monkeypatch):
    """Sans jeton resolvable ET sans compte actif verifie, l'organe ne
    publie pas.

    Le trousseau `gh` de la machine est partage et le compte actif
    bascule : une ecriture faite sous une identite non verifiee n'est pas
    levable par le coordinateur. Aucune ecriture ne doit partir."""
    monkeypatch.setattr(aer, "_token_gh", lambda: "")
    monkeypatch.setattr(aer, "_compte_actif_gh", lambda: "autre-compte")
    appels = []

    def _run(cmd, **k):
        appels.append(cmd)
        return type("R", (), {"returncode": 0, "stdout": "", "stderr": ""})()

    monkeypatch.setattr(aer.subprocess, "run", _run)
    assert aer.publier(5081, "x" * 200) is False
    assert appels == [], "aucune ecriture ne doit partir"


def test_le_payload_de_publication_est_un_fichier_temporaire(monkeypatch):
    """Le payload est un fichier TEMPORAIRE : un nom fixe laisse des debris
    quand `TEMP` est absent (Linux), et se fait ecraser par une execution
    concurrente (organe cron + relance manuelle) entre l'ecriture et le
    POST."""
    monkeypatch.setattr(aer, "_token_gh", lambda: "jeton")
    vus = {}

    def _run(cmd, **k):
        if "--body-file" in cmd:
            chemin = cmd[cmd.index("--body-file") + 1]
            vus["chemin"] = chemin
            vus["corps"] = pathlib.Path(chemin).read_text(encoding="utf-8")
        return type("R", (), {"returncode": 0, "stdout": "[]",
                              "stderr": ""})()

    monkeypatch.setattr(aer.subprocess, "run", _run)
    aer.publier(5081, "x" * 200)
    assert vus["corps"] == "x" * 200
    assert not pathlib.Path(vus["chemin"]).exists(), \
        "le fichier temporaire doit etre retire"
    assert vus["chemin"] != "anti_entropy_comment.md"


def test_un_dry_run_n_ecrit_pas_l_etat(monkeypatch, tmp_path):
    """Un dry-run qui ecrit l'etat a un effet de bord mesurable : l'etat
    est l'ENTREE du cliquet du budget (#23174). L'ecrire, c'est activer
    ou desactiver la retenue — sans que le lecteur sache qu'il a agi.
    """
    cible = tmp_path / "etat.json"
    monkeypatch.setenv(aer.ENV_ETAT, str(cible))

    mesure = [{"cle": "padding-nommage", "issue": 5081, "titre": "t",
               "commande": ["cmd"], "sens": "descend", "valeur": 813.0,
               "erreur": "", "reference": None, "verdict": "RECULE"}]
    monkeypatch.setattr(aer, "mesurer_tout",
                        lambda issue_filtre=None, now=None: mesure)
    monkeypatch.setattr(aer, "dernier_commentaire_issue", lambda issue: None)
    publie = []

    def _publier(issue, corps, dry_run=False):
        publie.append((issue, dry_run))
        return True

    monkeypatch.setattr(aer, "publier", _publier)

    aer.main(["--dry-run"])
    assert not cible.exists(), "le dry-run a ecrit l'etat du cliquet"

    aer.main([])
    assert cible.exists(), "le run reel n'a pas ecrit l'etat du cliquet"
    assert publie == [(5081, True), (5081, False)], publie


def test_un_echec_de_publication_sort_en_echec(monkeypatch, tmp_path):
    """Une publication qui echoue doit SORTIR en echec, pas en 0 muet.

    La reference se lit dans les commentaires PUBLIES : une publication qui
    echoue sans bruit fait perdre la fenetre de sept jours, et le verdict
    se fige sur une premiere mesure. L'etat reste ecrit — le verdict est
    mesure, independamment de la publication — mais le code de sortie le dit.
    """
    cible = tmp_path / "etat.json"
    monkeypatch.setenv(aer.ENV_ETAT, str(cible))

    mesure = [{"cle": "padding-nommage", "issue": 5081, "titre": "t",
               "commande": ["cmd"], "sens": "descend", "valeur": 813.0,
               "erreur": "", "reference": None, "verdict": "RECULE"}]
    monkeypatch.setattr(aer, "mesurer_tout",
                        lambda issue_filtre=None, now=None: mesure)
    monkeypatch.setattr(aer, "dernier_commentaire_issue", lambda issue: None)
    monkeypatch.setattr(aer, "publier",
                        lambda issue, corps, dry_run=False: False)

    rc = aer.main([])
    assert rc == 1, "un echec de publication doit sortir en 1"
    assert cible.exists(), "le verdict est mesure : l'etat reste ecrit"


def test_un_dry_run_ne_signale_pas_d_echec(monkeypatch, tmp_path):
    """Le dry-run ne publie rien PAR CONSTRUCTION : il ne doit donc pas
    sortir en echec."""
    cible = tmp_path / "etat.json"
    monkeypatch.setenv(aer.ENV_ETAT, str(cible))

    mesure = [{"cle": "padding-nommage", "issue": 5081, "titre": "t",
               "commande": ["cmd"], "sens": "descend", "valeur": 813.0,
               "erreur": "", "reference": None, "verdict": "RECULE"}]
    monkeypatch.setattr(aer, "mesurer_tout",
                        lambda issue_filtre=None, now=None: mesure)
    monkeypatch.setattr(aer, "dernier_commentaire_issue", lambda issue: None)
    monkeypatch.setattr(aer, "publier",
                        lambda issue, corps, dry_run=False: False)

    assert aer.main(["--dry-run"]) == 0


# --- l'identite de l'instrument ----------------------------------------------
#
# Une valeur n'est comparable a une autre que si le MEME instrument les a
# produites. Or un instrument change : #23193 (d818b008b) a corrige
# `inventory_notebook_names.py`, et sur le meme arbre l'ancien instrument
# rend 776 la ou le nouveau rend 44. Comparer les deux, c'est fabriquer un
# verdict qui ne dit rien du depot -- et le verdict fabrique s'ouvre a
# contresens dans le cliquet du budget de creation (#23174).

def test_l_identite_de_l_instrument_suit_le_sha_du_script(monkeypatch):
    """Un instrument qui est un script du depot est identifie par le sha du
    dernier commit qui a touche ce script : c'est la grandeur qui change
    quand l'instrument change."""
    def faux_run(cmd, timeout=600):
        if "log" in cmd and "inventory_notebook_names.py" in " ".join(cmd):
            return 0, "d818b008b5558d9a755c81d3d05e29ac23a9f823\n", ""
        return 1, "", ""
    monkeypatch.setattr(aer, "_run", faux_run)
    identite = aer.identite_instrument(
        ("python", "scripts/notebook_tools/inventory_notebook_names.py",
         "--json", "--base", "origin/main"))
    assert identite == INSTRUMENT_PADDING


def test_une_commande_git_a_une_identite_stable(monkeypatch):
    """Un instrument built-in de git n'a pas de version : son identite est
    la commande, et elle est la meme d'une publication a l'autre."""
    monkeypatch.setattr(aer, "_run", lambda cmd, timeout=600: (1, "", ""))
    commande = ("git", "ls-tree", "-r", "--name-only", "origin/main", "--",
                "MyIA.AI.Notebooks/GameTheory/Dynamics/")
    assert aer.identite_instrument(commande) == aer.identite_instrument(commande)
    assert aer.identite_instrument(commande).startswith("git:git ")


def test_une_identite_inconnue_ne_vaut_pas_comparabilite():
    """On ne presume jamais la comparabilite : une identite inconnue n'est
    pas une identite."""
    assert aer.comparables("a@1", "a@1") is True
    assert aer.comparables("a@1", "a@2") is False
    assert aer.comparables("", "a@1") is False
    assert aer.comparables("a@1", "") is False
    assert aer.comparables("", "") is False


def test_l_identite_de_l_instrument_est_inconnue_si_le_sha_ne_se_lit_pas(monkeypatch):
    monkeypatch.setattr(aer, "_run", lambda cmd, timeout=600: (1, "", ""))
    assert aer.identite_instrument(
        ("python", "scripts/notebook_tools/inventory_notebook_names.py")) == ""


def test_une_reference_transverse_est_refusee(monkeypatch):
    """La reference produite par un autre instrument n'est pas comparee :
    le verdict est `INSTRUMENT ILLEGIBLE`, et le motif est nomme."""
    e = aer.Entree(cle="x", issue=1, titre="t",
                   commande=("python", "scripts/notebook_tools/o.py"),
                   extraction=("lignes",), sens="descend", cible=0.0,
                   reference=aer.Reference(776.0, "2026-10-21", "issue #1",
                                          instrument="scripts/notebook_tools/o.py@ancien"))
    monkeypatch.setattr(aer, "mesurer",
                        lambda entree, maintenant=None: (44.0, "", ""))
    monkeypatch.setattr(aer, "identite_instrument",
                        lambda commande: "scripts/notebook_tools/o.py@nouveau")
    monkeypatch.setattr(
        aer, "lire_reference",
        lambda issue, cle, now=None: aer.Reference(776.0, "2026-10-21",
                                                    "commentaire publie",
                                                    instrument="scripts/notebook_tools/o.py@ancien"))
    monkeypatch.setattr(aer, "points_publies", lambda *a, **k: [])
    out = aer.mesurer_tout(registre=(e,))[0]
    assert out["verdict"] == "INSTRUMENT ILLEGIBLE"
    assert "transverse" in out["non_comparable"]
    assert out["reference"] is None


def test_une_reference_du_meme_instrument_est_comparee(monkeypatch):
    """Meme instrument des deux cotes : la comparaison a lieu, et elle rend
    ce qu'elle rend (ici STAGNE, la valeur du jour valant la reference)."""
    e = aer.Entree(cle="x", issue=1, titre="t",
                   commande=("python", "scripts/notebook_tools/o.py"),
                   extraction=("lignes",), sens="descend", cible=0.0,
                   reference=aer.Reference(44.0, "2026-10-30", "issue #1",
                                          instrument="scripts/notebook_tools/o.py@meme"))
    monkeypatch.setattr(aer, "mesurer",
                        lambda entree, maintenant=None: (44.0, "", ""))
    monkeypatch.setattr(aer, "identite_instrument",
                        lambda commande: "scripts/notebook_tools/o.py@meme")
    monkeypatch.setattr(aer, "lire_reference", lambda issue, cle, now=None: None)
    monkeypatch.setattr(aer, "points_publies", lambda *a, **k: [])
    out = aer.mesurer_tout(registre=(e,))[0]
    assert out["verdict"] == "STAGNE"
    assert out["non_comparable"] == ""
    assert out["reference"]["valeur"] == 44.0


def test_le_commentaire_publie_porte_l_identite_de_l_instrument():
    """La publication porte l'identite : c'est elle qui rendra la
    reference relisible, avec la valeur, dans sept jours."""
    e = {"cle": "padding-nommage", "issue": 5081, "titre": "Padding",
         "valeur": 44.0,
         "reference": {"valeur": 44.0, "mesure_le": "2026-10-30"},
         "sens": "descend", "cible": 0.0, "verdict": "STAGNE",
         "instrument": INSTRUMENT_PADDING,
         "commande": ("python", "scripts/notebook_tools/inventory_notebook_names.py")}
    corps = aer.commentaire_du_jour([e], "2026-10-31T00:00:00Z")
    assert "| instrument |" in corps
    assert INSTRUMENT_PADDING in corps


def test_l_identite_se_relit_dans_un_commentaire_publie():
    """Une publication qui porte la colonne se relit ; une publication
    ancienne (detail seul, script) ne donne PAS d'identite — le sha du
    script n'y est pas, et on ne presume pas qu'il n'a pas change."""
    corps = ("<!-- ANTI-ENTROPY-REGISTER -->\n\n"
             "| entree | issue | valeur | reference (7 j) | sens | verdict | instrument |\n"
             "|---|---|---:|---:|---|---|---|\n"
             f"| `padding-nommage` | #5081 | 44 | 44 (2026-10-30) | descend "
             f"| STAGNE | {INSTRUMENT_PADDING} |\n")
    assert aer.identite_du_commentaire(corps, "padding-nommage") == INSTRUMENT_PADDING

    ancien = ("<!-- ANTI-ENTROPY-REGISTER -->\n\n"
              "| entree | issue | valeur | reference (7 j) | sens | verdict |\n"
              "|---|---|---:|---:|---|---|\n"
              "| `padding-nommage` | #5081 | 44 | 776 (2026-10-21) | descend "
              "| RECULE |\n"
              "\n- `padding-nommage` (#5081) — Padding : `python "
              "scripts/notebook_tools/inventory_notebook_names.py --json`\n")
    assert aer.identite_du_commentaire(ancien, "padding-nommage") == ""


def test_une_publication_ancienne_a_commande_git_garde_son_identite():
    """Une commande git n'a pas de version : l'identite se relit dans le
    detail, et la comparaison transverse reste impossible a creer."""
    ancien = ("<!-- ANTI-ENTROPY-REGISTER -->\n\n"
              "- `catalogue-fraicheur` (#5081) — Catalogue : `git log -1 "
              "--format=%ct --grep scheduled auto-regenerate origin/main`\n")
    identite = aer.identite_du_commentaire(ancien, "catalogue-fraicheur")
    assert identite.startswith("git:git log -1")


# --- l'arbre mesure ----------------------------------------------------------
#
# L'instrument `inventory_notebook_names.py --base origin/main` prend sa
# LISTE de carnets dans la revision nommee (`git ls-tree`) et lit le
# CONTENU de chaque carnet dans l'ARBRE LOCAL (`open(path)`). Les deux ne
# concordent que si l'arbre local porte le meme contenu que la revision,
# dans le rayon que l'instrument lit.
#
# Mesure du 2026-10-31, meme `origin/main` (6135a06), meme instrument
# (d818b008b), deux checkouts : 38 sur le checkout aligne, 44 sur le clone
# principal en retard (d9aee247). L'ecart est exactement la serie Wavelet
# renommee par 6135a06. Sans garde, la valeur publiee decrirait un melange
# de deux arbres, et le verdict vaudrait pour aucun des deux.

def _run_avec_divergence(divergents):
    """Un `_run` qui repond a la seule question posee par le garde :
    quels fichiers divergent entre la revision nommee et l'arbre local."""
    def faux_run(cmd, timeout=600):
        args = [str(m) for m in cmd]
        if args[:2] == ["git", "diff"]:
            return 0, "".join(f + chr(10) for f in divergents), ""
        return 1, "", ""
    return faux_run


def test_le_garde_refuse_un_arbre_local_divergent(monkeypatch):
    monkeypatch.setattr(aer, "_run", _run_avec_divergence(
        ["MyIA.AI.Notebooks/ML/DataScienceWithAgents/04b-Wavelet-Scattering/"
         "WS-00a-Ondelettes-1D-from-scratch.ipynb"]))
    aligne, motif = aer.arbre_aligne(
        ("python", "scripts/notebook_tools/inventory_notebook_names.py",
         "--json", "--base", "origin/main"),
        "MyIA.AI.Notebooks")
    assert aligne is False
    # Le motif nomme les deux arbres et le fichier divergent : un refus
    # sans motif se lit comme une panne.
    assert "origin/main" in motif
    assert "WS-00a-Ondelettes-1D-from-scratch.ipynb" in motif


def test_le_garde_accepte_un_arbre_local_aligne(monkeypatch):
    monkeypatch.setattr(aer, "_run", _run_avec_divergence([]))
    aligne, motif = aer.arbre_aligne(
        ("python", "scripts/notebook_tools/inventory_notebook_names.py",
         "--json", "--base", "origin/main"),
        "MyIA.AI.Notebooks")
    assert aligne is True
    assert "meme contenu" in motif


def test_un_instrument_sans_rayon_declared_est_toujours_aligne(monkeypatch):
    """Un instrument qui ne lit que la revision qu'il nomme (un builtin git
    comme `git ls-tree`) declare un rayon vide : il n'y a rien a verifier.
    Et un instrument qui ne nomme aucune revision non plus."""
    monkeypatch.setattr(aer, "_run", lambda cmd, timeout=600: (1, "", ""))
    aligne, motif = aer.arbre_aligne(
        ("git", "ls-tree", "-r", "--name-only", "origin/main", "--", "x/"), "")
    assert aligne is True
    assert motif == ""
    aligne, motif = aer.arbre_aligne(
        ("python", "scripts/notebook_tools/o.py"), "MyIA.AI.Notebooks")
    assert aligne is True
    assert motif == ""


def test_la_mesure_est_refusee_quand_l_arbre_local_divergente(monkeypatch):
    """La mesure refusee ne porte PAS de verdict de comparaison : elle
    porte `INSTRUMENT ILLEGIBLE` et le motif de l refus."""
    e = aer.Entree(cle="x", issue=1, titre="t",
                   commande=("python", "scripts/notebook_tools/o.py",
                             "--base", "origin/main"),
                   extraction=("lignes",), sens="descend", cible=0.0,
                   reference=aer.Reference(38.0, "2026-10-31", "issue #1",
                                          instrument="scripts/notebook_tools/o.py@meme"),
                   arbre="MyIA.AI.Notebooks")
    monkeypatch.setattr(aer, "mesurer",
                        lambda entree, maintenant=None: (44.0, "", ""))
    monkeypatch.setattr(aer, "identite_instrument",
                        lambda commande: "scripts/notebook_tools/o.py@meme")
    monkeypatch.setattr(aer, "lire_reference",
                        lambda issue, cle, now=None: None)
    monkeypatch.setattr(aer, "_run", _run_avec_divergence(
        ["MyIA.AI.Notebooks/ML/WS-00a-Ondelettes-1D-from-scratch.ipynb"]))
    monkeypatch.setattr(aer, "points_publies", lambda *a, **k: [])
    out = aer.mesurer_tout(registre=(e,))[0]
    assert out["verdict"] == "INSTRUMENT ILLEGIBLE"
    assert "mesure refusee" in out["non_comparable"]
    # La reference de repli n'est pas non plus appliquee : elle decrirait
    # l'arbre nomme, pas l'arbre mesure.
    assert out["reference"] is None


def test_le_rayon_de_lecture_est_declare_par_l_entree():
    """Le rayon est une propriete de l'entree : c'est lui qui dit quel
    contenu l'instrument lit dans l'arbre local."""
    e = entree("padding-nommage")
    assert e.arbre == "MyIA.AI.Notebooks"
    # Les deux autres instruments ne lisent que la revision qu'ils nomment.
    assert entree("catalogue-fraicheur").arbre == ""
    assert entree("dynamics-escalier").arbre == ""


def test_le_commentaire_nomme_l_arbre_mesure():
    """Le commentaire dit sur quel arbre la valeur a ete prise."""
    e = {"cle": "padding-nommage", "issue": 5081, "titre": "Padding",
         "valeur": 38.0, "reference": None,
         "sens": "descend", "cible": 0.0, "verdict": "PREMIERE MESURE",
         "instrument": INSTRUMENT_PADDING,
         "commande": ("python", "scripts/notebook_tools/inventory_notebook_names.py"),
         "alignement": "l arbre local porte le meme contenu que `origin/main` "
                       "sur `MyIA.AI.Notebooks`"}
    corps = aer.commentaire_du_jour([e], "2026-10-31T00:00:00Z")
    assert "arbre : l arbre local porte le meme contenu" in corps


# --- la fenetre de comparaison -----------------------------------------------
#
# Pendant la fenetre de rebasage, la reference n'est pas une PUBLICATION de
# sept jours : c'est la valeur mesuree le jour du rebasage. Le verdict
# porte alors sur un intervalle plus court. Un lecteur qui ne le voit pas
# lit « STAGNE » comme « le chantier n'a pas bouge depuis sept jours » --
# c'est precisement le faux « AVANCE » qu'on vient de corriger. Le
# marqueur est donc porte par la mesure, la publication ET l'etat ecrit.

def _entree_de_test():
    return aer.Entree(
        cle="x", issue=1, titre="t",
        commande=("python", "scripts/notebook_tools/o.py"),
        extraction=("lignes",), sens="descend", cible=0.0,
        reference=aer.Reference(38.0, "2026-10-31", "issue #1",
                               instrument="scripts/notebook_tools/o.py@meme"))


def test_la_fenetre_de_rebasage_est_suspendue(monkeypatch):
    """Sans publication de sept jours, la reference est celle du rebasage :
    la fenetre est SUSPENDUE, et le dit (motif + date d'ouverture)."""
    e = _entree_de_test()
    monkeypatch.setattr(aer, "mesurer",
                        lambda entree, maintenant=None: (38.0, "", ""))
    monkeypatch.setattr(aer, "identite_instrument",
                        lambda commande: "scripts/notebook_tools/o.py@meme")
    monkeypatch.setattr(aer, "lire_reference",
                        lambda issue, cle, now=None: None)
    monkeypatch.setattr(aer, "points_publies", lambda *a, **k: [])
    out = aer.mesurer_tout(registre=(e,))[0]
    assert out["comparaison_suspendue"] is True
    assert "SUSPENDUE" in out["fenetre"]
    assert "2026-10-31" in out["fenetre"]
    assert "2026-11-07" in out["fenetre"]


def test_une_publication_de_sept_jours_ouvre_la_fenetre(monkeypatch):
    """Une reference venue d'une publication de sept jours : la fenetre est
    ACTIVE, rien n'est suspendu."""
    e = _entree_de_test()
    monkeypatch.setattr(aer, "mesurer",
                        lambda entree, maintenant=None: (30.0, "", ""))
    monkeypatch.setattr(aer, "identite_instrument",
                        lambda commande: "scripts/notebook_tools/o.py@meme")
    monkeypatch.setattr(
        aer, "lire_reference",
        lambda issue, cle, now=None: aer.Reference(
            38.0, "2026-10-24", "commentaire publie",
            instrument="scripts/notebook_tools/o.py@meme"))
    monkeypatch.setattr(aer, "points_publies", lambda *a, **k: [])
    out = aer.mesurer_tout(registre=(e,))[0]
    assert out["comparaison_suspendue"] is False
    assert "active" in out["fenetre"]


def test_le_commentaire_porte_la_fenetre(monkeypatch):
    """La publication dit si la comparaison est suspendue : le lecteur ne
    doit pas pouvoir lire « STAGNE » comme une mesure de sept jours."""
    e = _entree_de_test()
    monkeypatch.setattr(aer, "mesurer",
                        lambda entree, maintenant=None: (38.0, "", ""))
    monkeypatch.setattr(aer, "identite_instrument",
                        lambda commande: "scripts/notebook_tools/o.py@meme")
    monkeypatch.setattr(aer, "lire_reference",
                        lambda issue, cle, now=None: None)
    monkeypatch.setattr(aer, "points_publies", lambda *a, **k: [])
    out = aer.mesurer_tout(registre=(e,))[0]
    corps = aer.commentaire_du_jour([out], "2026-10-31T00:00:00Z")
    assert "SUSPENDUE" in corps
    assert "rebascage 2026-10-31" in corps


# --- la serie a instrument constant (le controle positif, VIF) ---------------
#
# Le controle positif exige par l'issue etait devenu MUET : il affirmait un
# `RECULE` ecrit en dur, sans jamais mesurer. Depuis le merge de #23193,
# l'instrument a change : la valeur du jour et la reference ne sont plus
# comparables, et le controle ne testait plus ce qu'il croyait tester.
#
# Ces tests exercent le controle sur la SERIE A INSTRUMENT CONSTANT : les
# points reels de l'entree, groupes par l'instrument qui les a produits.


def _entree_padding():
    return next(e for e in aer.REGISTRE if e.cle == "padding-nommage")


def test_le_controle_positif_rend_recule_sur_une_serie_reelle():
    """776 -> 813 -> 840 a instrument constant : RECULE.

    Ce sont les trois points REELS de l'entree (la reference inscrite dans
    l'issue, la publication balisee du 28/10, la mesure du 30/10), avec
    l'identite declaree de l'instrument qui les a produits. La tendance
    d'un groupe est le verdict entre sa premiere et sa derniere valeur,
    dans le sens de l'entree : le padding monte, donc il RECULE.
    """
    e = _entree_padding()
    groupes = aer.serie_par_instrument(
        e.commande, e.sens,
        [("2026-10-21", 776.0, "issue #23175", "instrument@avant-23193"),
         ("2026-10-28", 813.0, "publication du 28/10", "instrument@avant-23193"),
         ("2026-10-30", 840.0, "mesure du 30/10", "instrument@avant-23193")])
    assert len(groupes) == 1
    assert groupes[0]["tendance"] == "RECULE"
    assert [p["valeur"] for p in groupes[0]["points"]] == [776.0, 813.0, 840.0]


def test_la_serie_separe_les_instruments():
    """Deux instruments distincts donnent deux groupes : on ne les melange
    jamais, c'est precisement le defaut de #23193."""
    e = _entree_padding()
    groupes = aer.serie_par_instrument(
        e.commande, e.sens,
        [("2026-10-28", 813.0, "publication", "instrument@avant-23193"),
         ("2026-10-31", 38.0, "mesure du jour", "instrument@apres-23193")])
    assert len(groupes) == 2
    assert groupes[0]["tendance"] == "PREMIERE MESURE"
    assert groupes[1]["tendance"] == "PREMIERE MESURE"


def test_deux_mesures_du_meme_jour_ne_font_pas_une_tendance():
    """Une tendance se lit entre deux JOURS : deux publications du meme jour
    (a l'ocasion d'un evenement) ne sont pas un ecart de sept jours."""
    e = _entree_padding()
    groupes = aer.serie_par_instrument(
        e.commande, e.sens,
        [("2026-10-28T22:32:02Z", 0.08, "publication 1", "instrument@x"),
         ("2026-10-28T23:06:38Z", 0.1, "publication 2", "instrument@x")])
    assert groupes[0]["tendance"] == "SANS TENDANCE (mesures du meme jour)"


def test_un_point_sans_identite_est_laisse_de_cote(monkeypatch):
    """Un point dont l'identite ne peut pas etre etablie ne se compare a
    rien : il sort de la serie plutot que d'etre attribue au hasard."""
    monkeypatch.setattr(aer, "identite_instrument_a",
                        lambda commande, au: "")
    e = _entree_padding()
    groupes = aer.serie_par_instrument(
        e.commande, e.sens,
        [("2026-10-28", 813.0, "publication", ""),
         ("2026-10-31", 38.0, "mesure", "")])
    assert groupes == []


def test_les_points_historiques_declarent_leur_source():
    """Un point historique sans source est une valeur inventee."""
    e = _entree_padding()
    assert len(e.historique) >= 2
    for h in e.historique:
        assert h.source
        assert h.mesure_le


def test_l_identite_derivee_a_la_date_est_celle_des_points_declares():
    """L'identite declaree d'un point doit etre celle que l'organe derive
    LUI-MEME a la date du point. Sans cela, le groupe de la serie serait
    faux — et le controle positif porterait sur un mensonge.

    Le test est ignore sur un clone superficiel : l'historique de
    l'instrument n'y existe pas, et une identite non etablie ne prouve
    rien (c'est le principe que l'organe applique partout ailleurs).
    """
    e = _entree_padding()
    for h in e.historique:
        derivee = aer.identite_instrument_a(e.commande, h.mesure_le)
        if not derivee:
            pytest.skip("historique de l'instrument indisponible "
                        "(clone superficiel)")
        assert derivee == h.instrument, (
            f"l identite declaree ({h.instrument}) ne correspond pas a "
            f"l identite derivee au {h.mesure_le} ({derivee})")


def test_le_commentaire_publie_la_serie(monkeypatch):
    """La serie est PUBLIEE : c'est elle qui rend le controle positif lisible
    par un tiers, sans qu'il ait a rejouer la mesure."""
    e = aer.Entree(
        cle="x", issue=1, titre="t",
        commande=("python", "scripts/notebook_tools/o.py"),
        extraction=("lignes",), sens="descend", cible=0.0,
        historique=(aer.Reference(776.0, "2026-10-21", "issue #1",
                                  instrument="o.py@ancien"),))
    monkeypatch.setattr(aer, "mesurer",
                        lambda entree, maintenant=None: (840.0, "", ""))
    monkeypatch.setattr(aer, "identite_instrument",
                        lambda commande: "o.py@ancien")
    monkeypatch.setattr(aer, "points_publies", lambda *a, **k: [])
    monkeypatch.setattr(aer, "lire_reference",
                        lambda issue, cle, now=None: None)
    out = aer.mesurer_tout(registre=(e,))[0]
    corps = aer.commentaire_du_jour([out], "2026-10-31T00:00:00Z")
    assert "Serie a instrument constant" in corps
    assert "776" in corps and "840" in corps
    assert "**RECULE**" in corps


def test_la_mesure_refusee_n_entre_pas_dans_la_serie(monkeypatch):
    """Une mesure refusee (arbre divergent, instrument muet) ne decrit
    rien : elle n'entre pas dans la serie."""
    e = aer.Entree(
        cle="x", issue=1, titre="t",
        commande=("python", "scripts/notebook_tools/o.py"),
        extraction=("lignes",), sens="descend", cible=0.0,
        historique=(aer.Reference(776.0, "2026-10-21", "issue #1",
                                  instrument="o.py@ancien"),))
    monkeypatch.setattr(aer, "mesurer",
                        lambda entree, maintenant=None: (840.0, "", ""))
    monkeypatch.setattr(aer, "identite_instrument",
                        lambda commande: "o.py@ancien")
    monkeypatch.setattr(aer, "points_publies", lambda *a, **k: [])
    monkeypatch.setattr(aer, "lire_reference",
                        lambda issue, cle, now=None: None)
    monkeypatch.setattr(aer, "arbre_aligne",
                        lambda commande, rayon="": (False, "arbre divergent"))
    out = aer.mesurer_tout(registre=(e,))[0]
    for groupe in out["serie"]:
        for p in groupe["points"]:
            assert p["source"] != "mesure du jour"


def test_la_valeur_publiee_est_lue_dans_la_colonne_valeur():
    """La valeur d'une publication se lit dans la colonne `valeur` — pas
    dans la reference, ni dans le verdict."""
    corps = ("| `padding-nommage` | #5081 | 813 | 776 (2026-10-21) | "
             "descend | **RECULE** | `o.py@x` |")
    assert aer._valeur_publiee(corps, "padding-nommage") == 813.0
    assert aer._valeur_publiee(corps, "autre") is None
    assert aer._valeur_publiee("| `x` | #1 | — | — | descend | **STAGNE** |",
                               "x") is None


def test_l_instrument_reel_rend_encore_une_valeur():
    """Le controle est VIF : il mesure le VRAI instrument du depot.

    C'est le test qui aurait attrape un changement de la forme de la
    sortie de l'instrument (une cle renommee, un JSON restructure) : le
    couplage entre l'instrument et la specification d'extraction n'est
    verifie par aucun autre test.
    """
    e = _entree_padding()
    # `--base HEAD` plutot que `origin/main` : le test mesure l'ARBRE
    # LOCAL, qui existe toujours, et ne depend pas d'une reference
    # distante absente d'un clone CI.
    source = e.commande
    commande = tuple("HEAD" if i and source[i - 1] == "--base" else mot
                     for i, mot in enumerate(source))
    variante = aer.Entree(cle=e.cle, issue=e.issue, titre=e.titre,
                          commande=commande, extraction=e.extraction,
                          sens=e.sens, cible=e.cible, arbre=e.arbre)
    valeur, erreur, _ = aer.mesurer(variante)
    assert erreur == "", f"l instrument reel ne rend plus de valeur : {erreur}"
    assert valeur is not None and valeur >= 0
