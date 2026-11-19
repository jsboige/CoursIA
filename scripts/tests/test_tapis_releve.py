"""Le RELEVE persistant : ce qu'il prouve, et ce qu'il ne prouve pas.

Mandat du coordinateur (19/11/2026, DM `coord2108-picker-decision`) :
« Couverture : enregistrer date, version du fil lu et verdict apres lecture
integrale ; sans preuve = inconnu » et « Une livraison enfant date son
parent, pas son frere ; elle ne vaut lecture d'aucun fil. »

Ces tests verrouillent les TROIS distinctions que le store porte :

- le **releve** (une lecture) et la **cle de service** (une livraison) sont
  deux etats distincts : une livraison ne cree aucun releve ;
- la cle **confirmee par le diff** prime sur la cle **candidate** ;
- une forme canonique est une forme de LIGNE, pas une mention en prose.
"""
from coordination import tapis_cle, tapis_releve
from coordination.tapis_rapide import Etat

LANE = "myia-ai-01:CoursIA-2"


def _etat(numero: int, parent: int | None = None) -> Etat:
    return Etat(numero, "grain %d" % numero, [], "2026-01-01T00:00:00Z",
                parent, parent or numero, False, False)


def _fil(nb: int = 3, identifiant: int = 7) -> list[dict]:
    return [{"id": identifiant + i,
             "createdAt": "2026-11-01T00:00:%02dZ" % i,
             "body": "commentaire %d" % i} for i in range(nb)]


# ---------------------------------------------------------------- le releve

def test_un_releve_enregistre_la_version_et_le_verdict():
    tapis_releve.enregistrer(100, "c3@abcd1234", tapis_releve.SERVIABLE, LANE)
    r = tapis_releve.relever(100)
    assert r is not None
    assert r["version"] == "c3@abcd1234"
    assert r["empreinte"] == "abcd1234"
    assert r["verdict"] == tapis_releve.SERVIABLE
    assert r["lane"] == LANE
    assert tapis_releve.connu(100)


def test_sans_preuve_le_fil_est_inconnu():
    """fail-CLOSED : un fil jamais lu n'est ni « lu » ni « non lu »."""
    assert tapis_releve.relever(999) is None
    assert tapis_releve.connu(999) is False
    assert tapis_releve.servable(999, "abcd1234") is False


def test_le_store_absent_ou_illisible_vaut_inconnu(monkeypatch, tmp_path):
    monkeypatch.setenv(tapis_releve.ENV_RELEVE, str(tmp_path / "absent"))
    assert tapis_releve.lire() == {tapis_releve.RELEVE: {}, tapis_releve.SERVICE: {}}
    assert tapis_releve.connu(1) is False
    # un store illisible ne leve pas : il vaut inconnu
    chemin = tapis_releve.chemin_releve()
    chemin.parent.mkdir(parents=True, exist_ok=True)
    chemin.write_text("{pas du json", encoding="utf-8")
    assert tapis_releve.connu(1) is False


def test_un_releve_perime_ne_tient_plus():
    """Le fil a bouge depuis la lecture : le releve est caduc."""
    fil = _fil()
    tapis_releve.enregistrer(100, tapis_releve.version_fil(fil),
                              tapis_releve.SERVIABLE)
    assert tapis_releve.servable(100, tapis_releve.empreinte(fil)) is True
    assert tapis_releve.servable(100, "deadbeef") is False


def test_un_verdict_non_servable_ne_tient_pas():
    fil = _fil()
    tapis_releve.enregistrer(100, tapis_releve.version_fil(fil), "GEL")
    assert tapis_releve.servable(100, tapis_releve.empreinte(fil)) is False


def test_la_version_du_fil_change_des_que_le_fil_change():
    a = _fil()
    b = _fil(nb=4)
    assert tapis_releve.empreinte(a) != tapis_releve.empreinte(b)
    assert tapis_releve.version_fil(a) != tapis_releve.version_fil(b)
    assert tapis_releve.empreinte(a) == tapis_releve.empreinte(_fil())


# ------------------------------------------- la livraison ne vaut pas lecture

def test_une_livraison_ne_cree_aucun_releve():
    """« Une livraison ... ne vaut lecture d'aucun fil. »"""
    tapis_releve.enregistrer_service(100, "2026-11-05T10:00:00Z",
                                     "PR #9 (diff couvre)", 9)
    assert tapis_releve.relever(100) is None
    assert tapis_releve.connu(100) is False
    assert tapis_releve.service(100)["pr"] == 9


def test_un_releve_ne_date_aucune_cle_de_service():
    tapis_releve.enregistrer(100, "c3@abcd1234", tapis_releve.SERVIABLE, LANE)
    assert tapis_releve.service(100) is None
    assert tapis_releve.service_connue() == {}


# ------------------------------------------------- la cle confirmee > candidat

def test_la_cle_confirmee_prime_sur_le_candidat():
    e = _etat(200)
    candidats = {200: [{"sha": "pr1", "date": "2026-11-19T10:00:00Z",
                        "canonique": True, "pr": 1}]}
    tapis_releve.enregistrer_service(200, "2026-11-01T09:00:00Z",
                                     "PR #7 (diff couvre)", 7)
    tapis_cle.appliquer([e], candidats)
    assert e.cle_service == "2026-11-01T09:00:00Z"
    assert "diff couvre" in e.cle_origine


def test_sans_confirmation_la_cle_candidate_reste():
    e = _etat(201)
    candidats = {201: [{"sha": "pr1", "date": "2026-11-19T10:00:00Z",
                        "canonique": True, "pr": 1}]}
    tapis_cle.appliquer([e], candidats)
    assert e.cle_service == "2026-11-19T10:00:00Z"


def test_la_livraison_d_un_enfant_date_le_parent_et_pas_le_frere():
    hub, enfant, frere = _etat(300), _etat(301, parent=300), _etat(302)
    tapis_releve.enregistrer_service(301, "2026-11-05T10:00:00Z",
                                     "PR #9 (diff couvre)", 9)
    tapis_cle.appliquer([hub, enfant, frere], {})
    assert hub.cle_service == "2026-11-05T10:00:00Z"
    assert enfant.cle_service == "2026-11-05T10:00:00Z"
    assert frere.cle_service is None


# ------------------------------------------------------- la forme canonique

def test_les_formes_canoniques_sont_canoniques():
    for texte in ("See #27338", "Closes #27338", "Part of #27338",
                  "Fix(portee,#27338)", "fix: something #27338"):
        assert tapis_cle.est_canonique(texte, 27338), texte


def test_une_mention_en_prose_ne_candidate_pas():
    """Sonde adverse Hermes (19/11) : la prose ne couvre pas."""
    for texte in ("le fix de #201",
                  "Rebase sur le fix #27242",
                  "as we see #201 shows growth",
                  "Sur #27338",
                  "le ticket #27338 reste ouvert"):
        assert not tapis_cle.est_canonique(texte, 201), texte
