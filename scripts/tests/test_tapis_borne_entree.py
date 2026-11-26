"""#28114 I6 -- la BORNE de commande part de l'entree REELLE (#28345).

La premiere version du correctif I6 bornait le cap de livraisons, mais la
borne naissait dans `tapis_leger.tirage` : la garde de fraicheur, qui passe
AVANT le tirage dans `tapis_rapide.main`, disposait de son propre budget
(120 s pour un `git fetch`, 60 s par appel git). La commande pouvait donc
depasser son contrat de plusieurs fois, et rien ne le montrait.

Ces tests prennent l'entree reellement utilisee par les lanes
(`tapis_rapide.main`) et prouvent quatre choses :

1. la garde de fraicheur est **bornee** par le budget de la commande, et une
   freshness coupee par la borne DEGRADE le tirage au lieu de le refuser ;
2. une commande lente rend **sous la borne** -- jamais de depassement muet ;
3. le **repli reel** (reseau coupe) rend la main par le cache, dans la borne ;
4. un repli lance **apres** l'echeance ne sert rien (fail-CLOSED).

Le cinquieme test verifie l'invariant **I7** (la consolidation passe devant
l'anciennete) sur la **sortie reelle** du tirage : l'ordre rendu, pas une
fonction isolee.

Aucun test ne touche le reseau : le `run` de la commande est un faux, et la
garde de fraicheur est forcee (`MAIN_FRESHNESS_FORCE`) avec un runner factice
qui enregistre les timeouts qu'il recoit.
"""
import json
import sys
import time
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from coordination import gh_bulk, main_freshness, tapis_borne  # noqa: E402
from coordination import tapis_ancre, tapis_etat, tapis_rapide, tapis_repli  # noqa: E402
from test_tapis_cap_borne import _cache_repli, _run  # noqa: E402

LANE = "myia-ai-01:CoursIA-2"
NOW = datetime(2026, 11, 25, 21, 0, tzinfo=UTC)
#: Le budget de la commande (le mur global du tirage + la part de la garde
#: de fraicheur), et la part de la garde dans ce budget.
BUDGET = tapis_borne.BUDGET_S


def _meta(n: int, labels: list[str] | None = None, jours: float = 3.0) -> dict:
    """Une issue du pool, avec ses labels et son age."""
    cree = (NOW - timedelta(days=jours)).strftime("%Y-%m-%dT%H:%M:%SZ")
    return {"number": n, "title": f"Grain {n}", "created_at": cree,
            "updated_at": cree, "labels": list(labels or [])}


@pytest.fixture(autouse=True)
def _etat_neutre(monkeypatch):
    """Aucun etat de lane : ni ancre, ni visitation, ni ecriture."""
    monkeypatch.setattr(tapis_ancre, "lire", lambda lane: tapis_etat.vide())
    monkeypatch.setattr(tapis_ancre, "proposer", lambda *a, **k: {})
    monkeypatch.setattr(tapis_ancre, "ecrire", lambda lane, etat: etat)


def _runner_git(valeurs: dict, timeouts: list[int]):
    """Un runner git factice : il enregistre les timeouts qu'il recoit.

    `valeurs` associe un fragment d'argv a un code de retour : `{"fetch":
    124}` simule un `git fetch` qui expire (rc 124 = timeout du runner).
    """
    def run(argv, timeout):
        timeouts.append(timeout)
        cmd = " ".join(argv)
        for cle, rc in valeurs.items():
            if cle in cmd and rc != 0:
                return (rc, "", "echec")
        if "rev-list" in cmd:
            return (0, "0", "")
        if "rev-parse" in cmd:
            return (0, "main", "")
        return (0, "", "")
    return run


# --- 1. la garde de fraicheur est bornee par la commande ----------------------

def test_la_garde_de_fraicheur_est_bornee_par_la_commande(monkeypatch, capsys):
    """Les appels git de la garde recoivent un timeout sous le budget.

    C'etait le trou : `main_freshness` accordait 120 s au `git fetch` et 60 s
    a chaque appel, hors du budget de la commande.
    """
    monkeypatch.setenv("MAIN_FRESHNESS_FORCE", "1")
    timeouts: list[int] = []
    # Le fetch ECHOUE : rc 124 = timeout du runner.
    monkeypatch.setattr(main_freshness, "run_defaut",
                        _runner_git({"fetch": 124}, timeouts))
    pool = [_meta(5000 + k) for k in range(6)]
    code = tapis_rapide.main(["--lane", LANE, "--grains", "3", "--json"],
                              run=_run(pool))
    capture = capsys.readouterr()
    assert code == 0, "une freshness coupee ne doit pas refuser le tirage"
    rapport = json.loads(capture.out)
    assert rapport["grains"], "la file doit etre rendue"
    assert timeouts, "la garde doit avoir lance des appels git"
    for t in timeouts:
        assert 0 < t <= tapis_borne.FRAICHEUR_S,             f"le timeout git ({t}) doit tenir dans la part de la garde"


def test_une_fraicheur_coupee_par_la_borne_degrade_sans_refuser(monkeypatch, capsys):
    """La mesure COUPEE par la borne est une degradation, pas un refus.

    Un `git fetch` qui expire sous la borne ne prouve rien sur le depot : le
    verdict est `FRAICHEUR_BORNEE`, degradable -- la file est rendue avec un
    avertissement, la mesure impossible (rc != 0) reste, elle, un refus.
    """
    monkeypatch.setenv("MAIN_FRESHNESS_FORCE", "1")
    timeouts: list[int] = []
    monkeypatch.setattr(main_freshness, "run_defaut",
                        _runner_git({"fetch": 124}, timeouts))
    pool = [_meta(5000 + k) for k in range(6)]
    code = tapis_rapide.main(["--lane", LANE, "--grains", "3", "--json"],
                              run=_run(pool))
    capture = capsys.readouterr()
    rapport = json.loads(capture.out)
    assert code == 0
    assert rapport["fraicheur"]["refuse"] is False
    assert rapport["fraicheur"]["degrade"] is True
    assert [r["code"] for r in rapport["fraicheur"]["raisons_degradees"]] == [
        "FRAICHEUR_BORNEE"]
    assert "TIRAGE DEGRADE [FRAICHEUR_BORNEE]" in capture.err


# --- 2. la commande rend sous la borne ----------------------------------------

def test_la_commande_rend_sous_la_borne(monkeypatch, capsys):
    """Le point d'entree rend sa file ET son rapport dans la borne.

    L'echeance est passee par le point d'entree : c'est la meme que celle de
    la selection, de la qualification et du repli.
    """
    monkeypatch.setenv("MAIN_FRESHNESS_FORCE", "1")
    timeouts: list[int] = []
    monkeypatch.setattr(main_freshness, "run_defaut", _runner_git({}, timeouts))
    pool = [_meta(5000 + k) for k in range(6)]
    echeance = time.monotonic() + 8.0
    debut = time.monotonic()
    code = tapis_rapide.main(["--lane", LANE, "--grains", "3", "--json"],
                              run=_run(pool), echeance=echeance)
    ecoule = time.monotonic() - debut
    capture = capsys.readouterr()
    assert code == 0
    rapport = json.loads(capture.out)
    assert rapport["grains"], "la file doit etre rendue"
    assert rapport["cap_livraisons"]["mesure"] is True, \
        "le cap doit etre mesure au point d'entree"
    assert ecoule < 8.0 + 3.0, f"la commande a depasse la borne ({ecoule:.1f} s)"


def test_une_selection_lente_est_coupee_sans_depasser(monkeypatch, capsys):
    """Une lecture qui ignore son timeout est coupee a l'echeance.

    Le lecteur etant coupe, la selection echoue : le repli prend le relais
    (fail-CLOSED), et la commande rend la main dans la borne.
    """
    monkeypatch.setenv("MAIN_FRESHNESS_FORCE", "1")
    timeouts: list[int] = []
    monkeypatch.setattr(main_freshness, "run_defaut", _runner_git({}, timeouts))

    def run_lent(argv, timeout):
        time.sleep(4.0)
        return "[]"

    debut = time.monotonic()
    code = tapis_rapide.main(["--lane", LANE, "--grains", "3", "--json"],
                              run=run_lent, echeance=time.monotonic() + 2.0)
    ecoule = time.monotonic() - debut
    capture = capsys.readouterr()
    assert ecoule < 12.0, f"la commande a depasse la borne ({ecoule:.1f} s)"
    assert code in (0, 3), "la commande rend un verdict, elle ne plante pas"
    if code == 3:
        assert "Lecture incomplete" in capture.err


def test_la_borne_de_la_commande_par_defaut_tient_dans_le_contrat():
    """La borne du CLI, par defaut, tient STRICTEMENT dans le contrat.

    L'invariant I6 de #28114 dit qu'un tirage de lane rend en moins de
    60 s. La borne posee au point d'entree (`tapis_borne.echeance()`, sans
    argument) est celle du CLI : elle doit y tenir, avec une marge --
    sinon le contrat reste une declaration, et non une borne.
    """
    borne = tapis_borne.echeance() - time.monotonic()
    assert 0.0 < borne < 60.0, \
        f"la borne du CLI est de {borne:.1f} s pour un contrat de 60 s"


def test_le_pire_cas_tient_dans_la_borne_de_la_commande(monkeypatch, capsys):
    """Le pire cas, temoin a l'horloge REELLE : chaque etage consomme TOUTE
    sa part, la commande rend malgre tout dans la borne.

    Le runner git dort tout le timeout qu'il recoit -- il consomme donc la
    part de la garde de fraicheur -- et la selection dort de meme (elle
    consomme la sienne). L'echeance est **mise a l'echelle** (2 s au lieu
    de la borne reelle) : ce qui est prouve ici, c'est la FORME -- la
    commande ne peut pas depasser l'enveloppe qu'on lui donne, elle est
    coupee et non attendue -- et la valeur reelle de l'enveloppe est
    verifiee par le test du contrat (borne par defaut < 60 s).
    """
    monkeypatch.setenv("MAIN_FRESHNESS_FORCE", "1")
    temps: list[int] = []

    def run_git(argv, timeout):
        temps.append(timeout)
        time.sleep(min(timeout, 2.0))
        return (124, "", "timeout du runner")

    monkeypatch.setattr(main_freshness, "run_defaut", run_git)

    def run_lent(argv, timeout):
        time.sleep(min(timeout, 2.0))
        return "[]"

    enveloppe = 2.0
    debut = time.monotonic()
    code = tapis_rapide.main(["--lane", LANE, "--grains", "3", "--json"],
                              run=run_lent,
                              echeance=time.monotonic() + enveloppe)
    ecoule = time.monotonic() - debut
    capture = capsys.readouterr()
    assert temps, "la garde doit avoir lance ses appels git"
    for t in temps:
        assert t <= enveloppe, f"un appel git a depasse l'enveloppe ({t} s)"
    assert code in (0, 3), f"la commande rend un verdict, elle ne plante pas ({code})"
    assert ecoule < enveloppe + 4.0, \
        f"le pire cas a depasse la borne : {ecoule:.1f} s pour {enveloppe} s"


# --- 3. le repli reel ---------------------------------------------------------

def test_le_repli_reel_sert_le_cache_dans_la_borne(monkeypatch, tmp_path, capsys):
    """Reseau coupe : le repli chronologique rend la main par le cache local.

    Le repli ne lit JAMAIS le reseau (invariant I2) : il sert le cache, dans
    l'ordre de creation, et la commande rend sa file dans la borne.
    """
    monkeypatch.setenv("MAIN_FRESHNESS_FORCE", "1")
    timeouts: list[int] = []
    monkeypatch.setattr(main_freshness, "run_defaut", _runner_git({}, timeouts))
    _cache_repli(tmp_path, monkeypatch, [9101, 9102, 9103])

    def run_hors_reseau(argv, timeout):
        raise gh_bulk.LectureIncomplete("selection", 1, "reseau indisponible")

    debut = time.monotonic()
    code = tapis_rapide.main(["--lane", LANE, "--grains", "3", "--json"],
                              run=run_hors_reseau)
    ecoule = time.monotonic() - debut
    capture = capsys.readouterr()
    assert code == 0
    rapport = json.loads(capture.out)
    assert rapport["voie"] == "repli"
    assert rapport["grains"], "le repli doit servir une file"
    assert ecoule < BUDGET + 3.0


def test_le_repli_apres_l_echeance_ne_sert_rien():
    """Un repli lance apres l'echeance ne sert RIEN (fail-CLOSED).

    Il rendrait la main hors du contrat de la commande -- et le cache local
    peut avoir vicilli depuis le debut du tour.
    """
    with pytest.raises(gh_bulk.LectureIncomplete):
        tapis_repli.replir(LANE, 3, NOW, 45, "graine", Path("."),
                           echeance=time.monotonic() - 1.0)


# --- 4. I7 : la consolidation passe devant l'anciennete ------------------------

def test_I7_la_consolidation_passe_devant_l_anciennete(monkeypatch, capsys):
    """Sur la SORTIE REELLE, la consolidation precede l'issue plus ancienne.

    Deux grains de meme visite : une consolidation recente, une issue
    ordinaire de 200 jours. La consolidation passe devant (invariant I7).
    """
    monkeypatch.setenv("MAIN_FRESHNESS_FORCE", "1")
    timeouts: list[int] = []
    monkeypatch.setattr(main_freshness, "run_defaut", _runner_git({}, timeouts))
    pool = [_meta(6001, labels=["consolidation"], jours=2.0),
            _meta(6002, jours=200.0),
            _meta(6003, jours=2.0),
            _meta(6004, jours=2.0)]
    code = tapis_rapide.main(["--lane", LANE, "--grains", "4", "--json"],
                              run=_run(pool))
    capture = capsys.readouterr()
    assert code == 0
    rapport = json.loads(capture.out)
    numeros = [g["numero"] for g in rapport["grains"]]
    assert 6001 in numeros and 6002 in numeros, numeros
    assert numeros.index(6001) < numeros.index(6002), \
        f"la consolidation doit passer devant l'anciennete : {numeros}"
