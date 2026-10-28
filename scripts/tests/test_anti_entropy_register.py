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
PADDING_REFERENCE = 776.0


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


def test_un_sens_inconnu_est_une_erreur():
    with pytest.raises(ValueError):
        aer.verdict(1.0, 2.0, "baisse")


# --- le controle positif (exige par l'issue) ---------------------------------

def test_le_padding_rend_recule_a_la_mesure_du_soir():
    """Le controle positif de l'issue : « un controle positif sur le padding :
    il doit rendre RECULE a la mesure de ce soir »."""
    e = entree("padding-nommage")
    assert e.reference is not None
    assert e.reference.valeur == PADDING_REFERENCE
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
    for e in aer.REGISTRE:
        if e.commande[0] == "python":
            chemin = pathlib.Path(e.commande[1])
            assert chemin.exists(), f"{e.cle} : {chemin} introuvable"


def test_la_reference_du_padding_est_celle_de_l_issue():
    e = entree("padding-nommage")
    assert e.reference.source == "issue #23175"
    assert e.reference.mesure_le == "2026-10-21"


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
    monkeypatch.setattr(aer.subprocess, "run", lambda *a, **k: type(
        "R", (), {"returncode": 0,
                  "stdout": _json.dumps({"body": "@C:/tmp/f.md"})})())
    assert aer._verifier_publication(5081, "x" * 200) is False


def test_la_publication_echoue_si_le_corpus_publie_est_un_payload_json(monkeypatch):
    """Le corps publie ne doit pas parser en objet JSON portant une cle
    `body` : c'est le payload complet passe comme corps, et la garde de
    longueur est structurellement aveugle a ce cas (le corps est long)."""
    import json as _json
    payload = _json.dumps({"body": "x" * 200})
    monkeypatch.setattr(aer.subprocess, "run", lambda *a, **k: type(
        "R", (), {"returncode": 0,
                  "stdout": _json.dumps({"body": payload})})())
    assert aer._verifier_publication(5081, "x" * 200) is False


def test_la_publication_reussit_si_le_corpus_publie_est_le_bon(monkeypatch):
    import json as _json
    corps = "x" * 200
    monkeypatch.setattr(aer.subprocess, "run", lambda *a, **k: type(
        "R", (), {"returncode": 0,
                  "stdout": _json.dumps({"body": corps})})())
    assert aer._verifier_publication(5081, corps) is True


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
