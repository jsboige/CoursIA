from datetime import datetime, timezone
from pathlib import Path
import sys
import time
from types import SimpleNamespace

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import gh_bulk, tapis_borne, tapis_leger  # noqa: E402
from coordination import tapis_leger_fenetre as fenetre  # noqa: E402
from coordination import tapis_voie_leger  # noqa: E402


def test_voie_leger_donne_au_tirage_sa_part(monkeypatch, capsys):
    """Le point d'entree de la commande passe au tirage la part du tirage,
    pas celle de la selection seule : c'est elle que la qualification,
    fail-CLOSED, partage avec la lecture du pool (#28884)."""
    vues = {}

    def tirage(lane, grains, maintenant, jours, graine, depot, run, budget_s,
               echeance=None):
        vues['budget_s'] = budget_s
        return {'grains': [1]}, 0

    monkeypatch.setattr(tapis_leger, 'tirage', tirage)
    args = SimpleNamespace(lane='lane', grains=8, jours=45, json=True)
    code = tapis_voie_leger.servir(args, Path('.'), None,
                                   datetime.now(timezone.utc), 'g', None,
                                   echeance=time.monotonic() + 60)
    capsys.readouterr()
    assert code == 0
    assert vues['budget_s'] == tapis_voie_leger.TIRAGE_S


def test_part_du_tirage_tient_dans_lenveloppe_de_la_commande():
    """La part du tirage laisse a la garde de fraicheur au moins la marge du
    contrat (55 s pour un tirage qui rend en moins de 60 s)."""
    assert tapis_voie_leger.TIRAGE_S <= tapis_borne.BUDGET_S - 5


def test_cap_reserve_qualification_et_file_intacte(monkeypatch):
    candidat = SimpleNamespace(numero=42)
    capture = {}

    def cap(file, ordre, lane, maintenant, prs_ouvertes, **kwargs):
        capture['echeance'] = kwargs['echeance']
        return file, [], False, None

    monkeypatch.setattr(fenetre, 'passer_et_replir', cap)
    monkeypatch.setattr(fenetre, 'qualifier', lambda file, *a, **k: (file, {}, None))
    monkeypatch.setattr(fenetre, 'rapport', lambda *a, **k: {})
    classe = {'grains': [candidat], 'conteneurs': [], 'prs': [], 'metas': [], 'etats': []}
    rapport, code = fenetre.servir(classe, [candidat], {}, {}, 'lane', 8,
                                   datetime.now(timezone.utc), 7, 'g', Path('.'),
                                   None, {'selection_s': 0}, 0, 30, echeance=100)
    assert capture['echeance'] == 85
    assert rapport['cap_livraisons']['mesure'] is False
    assert code == 0


def test_repli_cap_absent_ne_masque_pas_exception(monkeypatch):
    monkeypatch.setattr(fenetre.tapis_cap_livraisons, 'passer',
                        lambda *a, **k: ([], [], True))
    def repli():
        raise gh_bulk.LectureIncomplete('selection', 'repli', 'cache absent')
    assert fenetre.passer_et_replir([], [], 'lane', datetime.now(timezone.utc), [],
                                   repli=repli, pool_ouvert=True) == ([], [], True, None)


def test_repli_inaccessible_signale_cause_qualification(monkeypatch):
    monkeypatch.setattr(fenetre, 'passer_et_replir', lambda *a, **k: ([], [], False, None))
    monkeypatch.setattr(fenetre, 'qualifier',
                        lambda *a, **k: ([], {'budget_epuise': True}, None))
    def repli(*args, **kwargs):
        raise gh_bulk.LectureIncomplete('selection', 'repli', 'cache absent')
    monkeypatch.setattr(fenetre.tapis_repli, 'replir', repli)
    classe = {'grains': [], 'conteneurs': [], 'prs': []}
    with pytest.raises(gh_bulk.LectureIncomplete, match='budget de qualification epuise ; repli : cache absent'):
        fenetre.servir(classe, [], {}, {}, 'lane', 8, datetime.now(timezone.utc),
                       7, 'g', Path('.'), None, {}, 0, 30, echeance=100)


def test_echec_qualification_et_repli_preserve_les_deux_causes(monkeypatch):
    monkeypatch.setattr(fenetre, 'passer_et_replir', lambda *a, **k: ([], [], False, None))
    monkeypatch.setattr(fenetre, 'qualifier',
                        lambda *a, **k: ([], {}, RuntimeError('fil illisible')))

    def repli(*args, **kwargs):
        raise gh_bulk.LectureIncomplete('selection', 'repli', 'cache absent')

    monkeypatch.setattr(fenetre.tapis_repli, 'replir', repli)
    classe = {'grains': [], 'conteneurs': [], 'prs': []}
    with pytest.raises(gh_bulk.LectureIncomplete, match='qualification : fil illisible ; repli : cache absent'):
        fenetre.servir(classe, [], {}, {}, 'lane', 8, datetime.now(timezone.utc),
                       7, 'g', Path('.'), None, {}, 0, 30, echeance=100)


def test_lecture_du_cap_resserree_sur_la_machine_de_la_lane():
    """La lecture du cap ne demande a GitHub que les corps qui citent la
    machine de la lane (#28884) : 931 PR et 9,5 s pour en retenir 3."""
    vus = []

    def run_commande(argv, timeout):
        vus.append(list(argv))
        return "[]"

    argv = ["gh", "pr", "list", "--state", "merged", "--search",
            "merged:>=2026-11-20 merged:<2026-11-23", "--limit", "1000",
            "--json", "number,body,mergedAt"]
    fenetre.lanceur_cap_resserre(run_commande, "myia-po-2026:CoursIA-3")(argv, 5)
    assert vus == [["gh", "pr", "list", "--state", "merged", "--search",
                    'merged:>=2026-11-20 merged:<2026-11-23 "myia-po-2026" in:body',
                    "--limit", "1000", "--json", "number,body,mergedAt"]]
    assert argv[6] == "merged:>=2026-11-20 merged:<2026-11-23", \
        "l'argv de l'appelant n'est pas modifie"


def test_lecture_du_cap_sans_lanceur_ni_recherche_passe_telle_quelle():
    """Sans lanceur injecte, ni sans `--search` dans l'argv : le lanceur passe
    tel quel -- la lecture integrale reste correcte, seulement plus lente."""
    assert fenetre.lanceur_cap_resserre(None, "lane") is None
    vus = []
    lancer = fenetre.lanceur_cap_resserre(lambda argv, timeout: vus.append(argv) or "[]",
                                          "machine:workspace")
    assert lancer(["gh", "pr", "list"], 3) == "[]"
    assert vus == [["gh", "pr", "list"]]


def test_le_cap_lit_par_le_lanceur_resserre():
    """Par l'entree reelle de la fenetre, chaque tranche du cap porte le
    qualifieur de machine : sans lui, la lecture reprendrait son volume."""
    vus = []

    def run_commande(argv, timeout):
        vus.append(argv[argv.index("--search") + 1])
        return "[]"

    _file, _temoins, mesure, rendu = fenetre.passer_et_replir(
        [], [], "myia-po-2026:CoursIA-3", datetime.now(timezone.utc), [],
        run_commande=run_commande)
    assert mesure is True and rendu is None
    assert vus, "le cap doit avoir lu au moins une tranche"
    for recherche in vus:
        assert recherche.startswith("merged:>="), recherche
        assert recherche.endswith(' "myia-po-2026" in:body'), recherche
