"""Tests de la lecture page par page des revues, mesure APPROVE -> merge (#25510).

Suite soeur de `test_measure_approve_to_merge.py` (points 7 et 8 de sa
docstring), scindee le 2026-11-27 : ce module portait ces temoins et depassait
le plafond des scripts neufs (805 lignes pour 800, `test_script_size_ratchet.py`).
Les quatre temoins ci-dessous sont deplaces a l'identique ; aucun n'est perdu.

- **les revues se lisent page par page** : une page unique peut omettre
  l'approbation recente d'une PR tres commentee ;
- **un plafond de pages atteint sur une page pleine est dit** : une PR dont les
  revues ne sont pas lues en entier sort du denominateur (`revues_incompletes`)
  -- jamais classee « sans approbation » alors que l'approbation est sur une
  page non lue.

Les appels reseau sont remplaces par une fonction `api` factice : les tests ne
dependent ni du reseau ni du quota.
"""

from __future__ import annotations

import sys
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import measure_approve_to_merge as m  # noqa: E402
from test_measure_approve_to_merge import _pr, _revue  # noqa: E402

def test_revues_suit_les_pages(monkeypatch):
    """Temoin : sur une page unique, l'approbation recente disparaissait.

    Une PR tres commentee porte son approbation sur une page suivante ; le
    lecteur doit la trouver, sinon la PR est classee « tete anterieure » a tort.
    """
    monkeypatch.setattr(m, "PAR_PAGE", 2)
    tete = "abc"
    pages = {
        1: [_revue("autre", "COMMENTED", tete, "2026-11-26T07:00:00Z"),
            _revue("autre", "COMMENTED", tete, "2026-11-26T07:05:00Z")],
        2: [_revue("myia-ai-01", "APPROVED", tete, "2026-11-26T08:00:00Z")],
    }

    def faux_api(chemin: str) -> list[dict]:
        if "/reviews" not in chemin:
            return []
        return pages.get(int(chemin.rsplit("page=", 1)[1]), [])

    monkeypatch.setattr(m, "api", faux_api)
    lues, completes = m.revues(9)
    assert len(lues) == 3
    assert completes is True
    ligne = m.classer(_pr(9, tete, "2026-11-26T10:30:00Z"), lues, "myia-ai-01")
    assert ligne["classe"] == "tete_exacte"
    assert ligne["heures"] == 2.5


def test_revues_page_pleine_au_plafond_n_a_pas_de_preuve_d_exhaustivite(monkeypatch):
    """Temoin : le plafond atteint sur une page pleine ne disait rien.

    Les pages 1 et 2 sont pleines et la page 3 existe : la lecture bornee a
    deux pages rend un prefixe. Rien ne prouve qu'elle a tout vu, et
    `complete` doit le dire. La page 3 n'est pas demandee -- le plafond borne
    la depense.
    """
    monkeypatch.setattr(m, "PAR_PAGE", 2)
    demandees: list[int] = []

    def faux_api(chemin: str) -> list[dict]:
        page = int(chemin.rsplit("page=", 1)[1])
        demandees.append(page)
        return [_revue("autre", "COMMENTED", "abc", f"2026-11-26T0{page}:00:00Z")] * 2

    monkeypatch.setattr(m, "api", faux_api)
    lues, completes = m.revues(9, max_pages=2)
    assert len(lues) == 4
    assert completes is False
    assert demandees == [1, 2]


def test_une_approbation_au_dela_du_plafond_n_est_pas_dite_absente(monkeypatch):
    """Temoin : l'approbation a la tete exacte etait sur la page non lue.

    Le prefixe lu ne contient aucune approbation. Classe tel quel, il
    concluait « sans approbation » : la PR sortait du denominateur alors
    qu'elle est approuvee a sa tete. Une lecture incomplete ne classe pas.
    """
    monkeypatch.setattr(m, "PAR_PAGE", 2)
    pages = {
        1: [_revue("autre", "COMMENTED", "abc", "2026-11-26T06:00:00Z")] * 2,
        2: [_revue("autre", "COMMENTED", "abc", "2026-11-26T07:00:00Z")] * 2,
        3: [_revue("myia-ai-01", "APPROVED", "abc", "2026-11-26T08:00:00Z")],
    }

    def faux_api(chemin: str) -> list[dict]:
        return pages.get(int(chemin.rsplit("page=", 1)[1]), [])

    monkeypatch.setattr(m, "api", faux_api)
    lues, completes = m.revues(9, max_pages=2)
    assert completes is False
    ligne = m.classer(_pr(9, "abc", "2026-11-26T10:30:00Z"), lues, "myia-ai-01",
                      revues_completes=completes)
    assert ligne["classe"] == "revues_incompletes"
    agregat = m.resume([ligne])
    assert agregat["sans_approbation"] == 0
    assert agregat["tete_anterieure"] == 0
    assert agregat["tete_exacte"]["n"] == 0
    assert agregat["revues_incompletes"] == 1


def test_revues_incompletes_ne_classe_pas_meme_avec_une_ancienne_approbation():
    """Le prefixe porte une approbation sur une tete anterieure.

    Les pages non lues peuvent en porter une sur la tete courante : le
    classement « tete anterieure » n'est pas sur non plus.
    """
    pr = _pr(10, "nouvelle", "2026-11-26T10:30:00Z")
    revues = [_revue("myia-ai-01", "APPROVED", "ancienne", "2026-11-25T08:00:00Z")]
    ligne = m.classer(pr, revues, "myia-ai-01", revues_completes=False)
    assert ligne["classe"] == "revues_incompletes"
    assert ligne["heures"] is None
