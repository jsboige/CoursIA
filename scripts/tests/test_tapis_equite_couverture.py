"""Tests de l'invariant de couverture du tapis rapide (#27590).

Le mandat du 16/11 (« toute issue doit etre visitée au moins une fois avant
qu'une autre le soit deux fois ») impose qu'une issue jamais visitée passe
devant une issue déjà visitée. Ces cas sont la suite directe des tests de
`scripts/tests/test_tapis_rapide.py` ; ils y ont été extraits pour tenir ce
fichier à sa taille enregistrée (cliquet de taille des scripts) sans que la
couverture de l'invariant ne baisse.
"""
import sys
from datetime import UTC, datetime
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import tapis_rapide as tr

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

NOW = datetime(2026, 11, 13, 12, 0, tzinfo=UTC)
LANE = "myia-po-2024:CoursIA-2"


def _etat(numero: int, titre: str, *, conteneur: bool = False, visites: int = 0,
          famille: int = 1) -> tr.Etat:
    return tr.Etat(numero=numero, titre=titre, labels=["epic"] if conteneur else [],
                   cree_le="2026-10-01T00:00:00Z", parent=None, famille=famille,
                   conteneur=conteneur, consolidation=False, visites=visites)


def test_une_issue_jamais_visitee_passe_avant_une_issue_deja_visitee():
    """Invariant de couverture (#27590) : dans le tour servi, une issue jamais
    visitée passe devant une issue deja visitée -- **conteneur compris**.

    Le conteneur passe apres les grains (#26926), mais apres les grains JAMAIS
    VISITES : sinon le mandat du 16/11 (« toute issue doit etre visitée au
    moins une fois avant qu'une autre le soit deux fois ») se mesure violé
    (mesure du 25/11 : six issues en violation, toutes au dernier tour).
    """
    grain = _etat(1, "grain deja visite", visites=3)
    conteneur = _etat(2, "[EPIC] conteneur jamais visite", conteneur=True, famille=2)
    file = tr.ordonner([grain, conteneur], LANE, NOW, 8)
    assert [e.numero for e in file] == [2, 1]


def test_le_conteneur_deja_visite_passe_apres_le_grain():
    """Le cas voisin qui n'ecarte pas : les deux issues deja visitees, le
    conteneur reste apres le grain (#26926). La regle #26926 n'est pas
    relachee -- elle est seulement prioritisee face a l'invariant de couverture
    quand le conteneur n'a jamais ete servi."""
    grain = _etat(1, "grain deja visite", visites=3)
    conteneur = _etat(2, "[EPIC] conteneur deja visite", conteneur=True,
                      visites=2, famille=2)
    file = tr.ordonner([grain, conteneur], LANE, NOW, 8)
    assert [e.numero for e in file] == [1, 2]
