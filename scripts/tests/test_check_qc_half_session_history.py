#!/usr/bin/env python3
"""Tests du recensement #20286 (dependance a la longueur de history()).

Le script recense les strategies QC dont la garde suppose que la demande
d'historique est servie en entier. Chaque test ecrit un fragment de strategie
synthetique et verifie le verdict rendu par l'organe.

Ce que ces tests verrouillent :
- la classification (EXPOSE / RISQUE / PROTEGE / INCONNU) ;
- la resolution des expressions portees par la fenetre double canonique
  (``self.WINDOWS[-1]``, ``max(self.WINDOWS)``, defauts de parametre) ;
- la **portee** des variables locales : deux fonctions peuvent utiliser le
  meme nom pour deux valeurs differentes, et la mesure ne doit pas confondre
  les deux (regression mesuree sur ``lookback`` : 278 dans un training,
  26 dans un scoring).
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))

import check_qc_half_session_history as census  # noqa: E402

SHORTFALL = 21


def _rows(tmp_path, source, name="strategy.py"):
    path = tmp_path / name
    path.write_text(source, encoding="utf-8")
    return census.analyse_file(str(path), SHORTFALL)


def _one(tmp_path, source):
    rows = _rows(tmp_path, source)
    assert len(rows) == 1, "une seule occurrence attendue, obtenu %r" % (rows,)
    return rows[0]


def test_meme_expression_expose(tmp_path):
    """La garde reprend la demande : elle suppose la fenetre servie en entier."""
    row = _one(tmp_path, """
class Strategy:
    def go(self, symbol):
        history = self.history(symbol, 100, Resolution.DAILY)
        if len(history) < 100:
            return 0.0
        return 1.0
""")
    assert row["classe"] == "EXPOSE"
    assert row["demande_num"] == 100
    assert row["seuil_num"] == 100


def test_fenetre_double_protege(tmp_path):
    """Demande = 2 x seuil : perdre la moitie de la fenetre ne change rien."""
    row = _one(tmp_path, """
class Strategy:
    def go(self, symbol):
        history = self.history(symbol, 2 * 100, Resolution.DAILY)
        if len(history) < 100:
            return 0.0
        return 1.0
""")
    assert row["classe"] == "PROTEGE"


def test_marge_intermediaire_risque(tmp_path):
    """Marge superieure au raccourcissement, mais demande < 2 x seuil."""
    row = _one(tmp_path, """
class Strategy:
    def go(self, symbol):
        history = self.history(symbol, 150, Resolution.DAILY)
        if len(history) < 100:
            return 0.0
        return 1.0
""")
    assert row["classe"] == "RISQUE"
    assert row["demande_num"] == 150
    assert row["seuil_num"] == 100


def test_marge_sous_raccourcissement_expose(tmp_path):
    """Marge de 5 barres : la garde bascule des que la demi-seance coupe."""
    row = _one(tmp_path, """
class Strategy:
    def go(self, symbol):
        history = self.history(symbol, 105, Resolution.DAILY)
        if len(history) < 100:
            return 0.0
        return 1.0
""")
    assert row["classe"] == "EXPOSE"
    assert "5" in row["raison"]


def test_index_de_liste_constante(tmp_path):
    """``self.WINDOWS[-1]`` : la forme canonique de la fenetre double #20330."""
    row = _one(tmp_path, """
class Strategy:
    WINDOWS = [10, 21, 63]

    def go(self, symbol):
        n = self.WINDOWS[-1]
        history = self.history(symbol, n, Resolution.DAILY)
        if len(history) < n:
            return 0.0
        return 1.0
""")
    assert row["classe"] == "EXPOSE"
    assert row["demande_num"] == 63
    assert row["seuil_num"] == 63


def test_max_de_liste_constante(tmp_path):
    """``max(self.WINDOWS)`` : l'extremum d'une liste constante."""
    row = _one(tmp_path, """
class Strategy:
    WINDOWS = [10, 21, 63]

    def go(self, symbol):
        n = max(self.WINDOWS)
        history = self.history(symbol, n + 5, Resolution.DAILY)
        if len(history) < n:
            return 0.0
        return 1.0
""")
    assert row["classe"] == "EXPOSE"
    assert row["demande_num"] == 68
    assert row["seuil_num"] == 63


def test_attribut_pose_dans_initialize(tmp_path):
    """Liste d'attributs d'instance posee dans initialize()."""
    row = _one(tmp_path, """
class Strategy:
    def initialize(self):
        self.windows = [2, 5, 10, 21]

    def go(self, symbol):
        n = max(self.windows)
        history = self.history(symbol, n, Resolution.DAILY)
        if len(history) < n:
            return 0.0
        return 1.0
""")
    assert row["classe"] == "EXPOSE"
    assert row["demande_num"] == 21


def test_defaut_de_parametre(tmp_path):
    """``self.lookback = lookback`` avec ``lookback=252`` en defaut."""
    row = _one(tmp_path, """
class Strategy:
    def __init__(self, lookback=252):
        self.lookback = lookback

    def go(self, symbol):
        history = self.history(symbol, self.lookback + 5, Resolution.DAILY)
        if len(history) < self.lookback:
            return 0.0
        return 1.0
""")
    assert row["classe"] != "INCONNU"
    assert row["demande_num"] == 257
    assert row["seuil_num"] == 252


def test_locales_homonymes_isolees(tmp_path):
    """Deux fonctions, le meme nom local, deux valeurs : pas de confusion.

    Regression mesuree : une table de constantes globale donnait au training
    la valeur du scoring (demande 26 au lieu de 257), ce qui classait a tort
    la occurrence en EXPOSE « seuil superieur a la demande ».
    """
    rows = _rows(tmp_path, """
class Strategy:
    def initialize(self):
        self.training = 252
        self.feature = 21

    def train(self, symbol):
        lookback = self.training + 5
        history = self.history(symbol, lookback, Resolution.DAILY)
        if len(history) < self.training:
            return None

    def score(self, symbol):
        lookback = self.feature + 5
        history = self.history(symbol, lookback, Resolution.DAILY)
        if len(history) < self.feature:
            return None
""")
    assert len(rows) == 2
    by_function = {row["fonction"]: row for row in rows}
    train = by_function["train"]
    score = by_function["score"]
    assert (train["demande_num"], train["seuil_num"]) == (257, 252)
    assert (score["demande_num"], score["seuil_num"]) == (26, 21)


def test_expression_non_resolue_inconnu(tmp_path):
    """Une expression inconnue reste INCONNU : l'organe ne devine pas."""
    row = _one(tmp_path, """
class Strategy:
    def go(self, symbol):
        history = self.history(symbol, self.inconnu + 5, Resolution.DAILY)
        if len(history) < self.inconnu:
            return 0.0
        return 1.0
""")
    assert row["classe"] == "INCONNU"


def test_sans_garde_aucune_occurrence(tmp_path):
    """Pas de garde de longueur : rien a recenser."""
    rows = _rows(tmp_path, """
class Strategy:
    def go(self, symbol):
        history = self.history(symbol, 100, Resolution.DAILY)
        return history["close"].values[-1]
""")
    assert rows == []


def test_syntaxe_invalide_signalee(tmp_path):
    """Un fichier illisible ne fait pas echouer l'organe en silence."""
    rows = _rows(tmp_path, "class Strategy(:\n    pass\n")
    assert len(rows) == 1
    assert rows[0]["classe"] == "ERREUR"


def test_verdicts_du_repertoire_reel():
    """Invariant du recensement sur l'arbre du depot.

    On n'y fige pas la **liste** des occurrences EXPOSE : elle change a chaque
    correctif (fenetre double) et un test qui la figerait rougirait sur la
    PR qui corrige un site. On y fige l'invariant qui doit, lui, tenir dans le
    temps :

    - l'organe **mesure** tout l'arbre : aucune occurrence ne reste INCONNU
      (une expression non resolue est un angle mort de l'organe, pas un
      verdict) ;
    - chaque occurrence porte une raison et une ligne.
    """
    rows = []
    for rel_path, abs_path in census.iter_projects(str(REPO_ROOT), census.DEFAULT_PROJECTS):
        for finding in census.analyse_file(abs_path, SHORTFALL):
            finding["fichier"] = rel_path.replace("\\", "/")
            rows.append(finding)

    assert rows, "le depot doit contenir des occurrences a recenser"
    inconnus = [row for row in rows if row["classe"] == "INCONNU"]
    assert not inconnus, "expressions non resolues : %s" % (
        [(row["fichier"], row["ligne"], row["raison"]) for row in inconnus],)
    for row in rows:
        assert row.get("raison"), row
        assert row.get("ligne"), row
        assert row["classe"] in ("EXPOSE", "RISQUE", "PROTEGE", "ERREUR"), row


@pytest.mark.parametrize("shortfall", [21])
def test_shortfall_parametrable(tmp_path, shortfall):
    """Le raccourcissement de mesure est un parametre de l'organe."""
    row = _one(tmp_path, """
class Strategy:
    def go(self, symbol):
        history = self.history(symbol, 110, Resolution.DAILY)
        if len(history) < 100:
            return 0.0
        return 1.0
""")
    # marge 10 : sous 21 -> EXPOSE, au-dessus de 10 -> RISQUE
    assert row["classe"] == ("EXPOSE" if 10 < shortfall else "RISQUE")
