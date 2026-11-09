"""Tests du pli 5 Origami Wolfram (#23093) : verdict d'outil, controle, mesure.

Couverture :

- le controle de correction rejoue un modele ecrit a la main, et il attrape une
  erreur d'arithmetique (il l'a fait pendant la mise au point : l'attente
  « arêtes = 2 par evenement » etait fausse, la bibliotheque avait raison) ;
- la loi de puissance retrouve un exposant connu sur une serie fabriquee ;
- la selection de modele tranche entre affine et loi de puissance, et elle
  attrape le piege mesure : une serie exactement affine ajustee en loi de
  puissance rend un exposant inferieur a 1 avec un R2 trompeur ;
- les bandes de classement sont celles declarees, bornes comprises ;
- le moteur absent ne produit aucun chiffre, il produit un verdict ;
- le determinisme est verifie a graine egale ;
- les invariants mesures du chemin unique sont verifies (formes affines).

Les tests qui exigent le moteur sont sautes si le paquet est absent : le module
n'est pas une dependance dure du depot, et un saut n'est pas un acquittement.
"""

from __future__ import annotations

import math

import pytest

from scripts.hypergraph_rewrite import pli5_engine as engine


# --- controle de correction et invariants mesures -------------------------


def test_controle_de_correction_passe():
    pytest.importorskip("setreplace", reason="moteur setreplace absent (pip install setreplace)")
    calibration = engine.calibrate()
    assert calibration["passed"] is True
    assert all(p["ok"] for p in calibration["points"])


def test_le_controle_discrimine_une_attente_fausse(monkeypatch):
    """Le controle doit rougir si le modele attendu est faux."""
    pytest.importorskip("setreplace", reason="moteur setreplace absent")
    faux = dict(engine.CALIBRATION)
    faux["expected"] = {1: {"edges": 99, "atoms": 99}}
    monkeypatch.setattr(engine, "CALIBRATION", faux)
    assert engine.calibrate()["passed"] is False


def test_determinisme_a_graine_egale():
    pytest.importorskip("setreplace", reason="moteur setreplace absent")
    spec = engine.RULES["branchante"]
    premier = engine.growth(spec["rule"], spec["initial"], series=(5,))
    second = engine.growth(spec["rule"], spec["initial"], series=(5,))
    assert premier == second


def test_invariants_du_chemin_unique():
    """Formes mesurees : chaine 1*n+1 arêtes, branchante 2*n+2, atomes n+1."""
    pytest.importorskip("setreplace", reason="moteur setreplace absent")
    chaine = engine.growth(engine.RULES["chaine"]["rule"], engine.RULES["chaine"]["initial"])
    branchante = engine.growth(engine.RULES["branchante"]["rule"], engine.RULES["branchante"]["initial"])
    for row in chaine:
        assert row["edges"] == row["events_applied"] + 1
        assert row["atoms"] == row["events_applied"] + 1
    for row in branchante:
        assert row["edges"] == 2 * row["events_applied"] + 2
        assert row["atoms"] == row["events_applied"] + 1


def test_la_sonde_de_capacites_voit_les_membres_de_classe(monkeypatch):
    """Falsification de la revue : une enumeration portee par la CLASSE doit etre vue.

    La sonde d'origine ne lisait que `dir(module)` ; elle rendait `False` sur un
    moteur qui exposait l'enumeration sur sa classe, c'est-a-dire sur un resultat
    qu'elle annoncait mesurer sans le regarder.
    """
    import sys
    import types

    faux = types.ModuleType("setreplace")

    class HypergraphSystem:  # noqa: D401 - doublure minimale
        def all_events_multiway(self):
            raise NotImplementedError

        def enumerate_all_states(self):
            raise NotImplementedError

    faux.HypergraphSystem = HypergraphSystem
    faux.set_replace = lambda *a, **k: None
    monkeypatch.setitem(sys.modules, "setreplace", faux)
    caps = engine.capabilities()
    assert caps["multiway_available"] is True
    assert "class:HypergraphSystem" in caps["multiway_surface"]
    assert sorted(caps["multiway_surface"]["class:HypergraphSystem"]) == [
        "all_events_multiway",
        "enumerate_all_states",
    ]


def test_la_sonde_de_capacites_compte_les_surfaces_parcourues():
    """La sonde rend ce qu'elle a regarde : module ET chaque classe publique."""
    pytest.importorskip("setreplace", reason="moteur setreplace absent")
    caps = engine.capabilities()
    assert caps["scanned"]["module"] >= 10
    assert "class:HypergraphSystem" in caps["scanned"]
    assert caps["scanned"]["class:HypergraphSystem"] >= 15


def test_occurrences_mesure_une_frontiere_qui_varie():
    """La frontiere d'occurrences VARIE : c'est une mesure, pas une identite.

    L'ancien temoin (`max_consumers`) valait 1 sur toute regle ; celui-ci doit
    rendre une serie qui n'est pas constante, sans quoi il ne mesure rien non plus.
    """
    pytest.importorskip("setreplace", reason="moteur setreplace absent")
    chaine = engine.occurrences(engine.RULES["chaine"]["rule"], engine.RULES["chaine"]["initial"], n_events=8)
    branchante = engine.occurrences(
        engine.RULES["branchante"]["rule"], engine.RULES["branchante"]["initial"], n_events=8
    )
    serie_chaine = [r["distinct_next_states"] for r in chaine["rows"]]
    assert len(set(serie_chaine)) > 1, serie_chaine
    assert chaine["max_distinct_next_states"] > 1
    assert branchante["max_distinct_next_states"] != chaine["max_distinct_next_states"]
    # Le chemin applique reste unique : c'est une propriete structurelle, dite comme telle.
    assert all(r["applied_here"] == 1 for r in chaine["rows"])
    assert "pas un temoin" in chaine["note"]


def test_moteur_absent_ne_produit_aucun_chiffre(monkeypatch):
    def leve():
        raise ImportError("setreplace absent (simule)")

    monkeypatch.setattr(engine, "_import_engine", leve)
    resultat = engine.measure()
    assert resultat["engine"]["setreplace_available"] is False
    assert resultat["verdict"]["verdict"] in engine.VERDICTS
    assert "growth" not in resultat
    assert "fits" not in resultat


# --- ajustements et selection de modele (sans moteur) --------------------


def test_loi_de_puissance_retrouve_un_exposant_connu():
    xs = [1, 2, 4, 8, 16]
    ys = [3 * x**2 for x in xs]
    fit = engine.fit_power_law(xs, ys)
    assert fit["slope"] == pytest.approx(2.0, abs=1e-9)
    assert fit["r2"] == pytest.approx(1.0, abs=1e-12)


def test_affine_retrouve_pente_et_ordonnee():
    xs = [1, 2, 3, 5, 8, 13]
    ys = [2 * x + 2 for x in xs]
    fit = engine.fit_affine(xs, ys)
    assert fit["slope"] == pytest.approx(2.0, abs=1e-9)
    assert fit["intercept"] == pytest.approx(2.0, abs=1e-9)


def test_selection_de_modele_attrape_le_piege_de_la_loi_de_puissance():
    """Une serie exactement affine ne doit pas etre classee « sous-lineaire »."""
    xs = list(engine.EVENTS_SERIES)
    ys = [x + 1 for x in xs]
    comparaison = engine.compare_models(xs, ys)
    assert comparaison["chosen"] == "affine"
    assert comparaison["affine"]["slope"] == pytest.approx(1.0, abs=1e-9)
    # Le piege est bien present : la loi de puissance ajustee en log-log rend un exposant < 1.
    assert comparaison["power_law"]["slope"] < 1.0
    assert engine.classify_exponent(comparaison["power_law"]["slope"]) == "sous-lineaire"
    assert comparaison["classification"].startswith("affine")
    # Et les deux R2 ne vivent pas dans le meme espace : celui du log est plus haut.
    assert comparaison["power_law"]["r2"] != comparaison["power_law_raw"]["r2"]


def test_selection_de_modele_compare_le_meme_espace():
    """Le R2 compare est celui de `y` pour les deux modeles, jamais celui de `log(y)`.

    Sur `y = 100 + x`, l'ancienne comparaison confrontait R2(log) = 0,865 au R2 brut
    de l'affine (1,0000) : l'affine gagnait, mais pour une raison d'echelle. Ici les
    deux R2 portent sur `y`, et l'affine gagne parce qu'elle decrit la serie.
    """
    xs = list(engine.EVENTS_SERIES)
    ys = [100 + x for x in xs]
    comparaison = engine.compare_models(xs, ys)
    assert comparaison["chosen"] == "affine"
    assert comparaison["affine"]["r2"] == pytest.approx(1.0, abs=1e-12)
    assert comparaison["power_law_raw"]["r2"] < comparaison["affine"]["r2"]
    # L'ecart d'espace reste lisible : les deux R2 de la loi de puissance different.
    assert abs(comparaison["power_law"]["r2"] - comparaison["power_law_raw"]["r2"]) > 1e-3


def test_egalite_donne_la_loi_de_puissance():
    """Tie-break declare : a egalite la loi de puissance l'emporte (regle ecrite)."""
    xs = [1, 2, 3, 5, 8, 13, 21]
    ys = list(xs)  # y = x : les deux modeles rendent exactement R2 = 1
    comparaison = engine.compare_models(xs, ys)
    assert comparaison["affine"]["r2"] == pytest.approx(1.0, abs=1e-12)
    assert comparaison["power_law_raw"]["r2"] == pytest.approx(1.0, abs=1e-9)
    assert comparaison["chosen"] == "power-law"


def test_selection_de_modele_retient_la_loi_de_puissance_si_elle_decrit_mieux():
    xs = [1, 2, 4, 8, 16, 32]
    ys = [2 * x**2 for x in xs]
    comparaison = engine.compare_models(xs, ys)
    assert comparaison["chosen"] == "power-law"
    assert comparaison["classification"] == "super-lineaire"


@pytest.mark.parametrize(
    "alpha, attendu",
    [(0.5, "sous-lineaire"), (0.849, "sous-lineaire"), (0.85, "lineaire"), (1.149, "lineaire"), (1.15, "super-lineaire"), (3.0, "super-lineaire")],
)
def test_bandes_declarees_bornes_comprises(alpha, attendu):
    assert engine.classify_exponent(alpha) == attendu


def test_exposant_hors_bande():
    assert engine.classify_exponent(math.nan) == "hors-bande"


def test_verdict_reste_dans_les_cinq_valeurs():
    faux_probe = {"setreplace_available": False, "wolfram": {"wolframscript": None, "wolfram_kernel": None, "install_dir_present": False}}
    assert engine.tool_verdict(faux_probe, None)["verdict"] == "RECOVERABLE-USER-HAND"
    assert engine.tool_verdict(faux_probe, None)["verdict"] in engine.VERDICTS


def test_verdict_epuise_la_voie_sota_en_premier():
    """Moteur Wolfram present ET alternative installee : la voie SOTA gagne.

    L'ancienne version rendait `RECOVERABLE-LOCAL` des que le paquet etait la, donc
    un verdict sous-optimal rendu en silence sur une machine Wolfram.
    """
    probe = {
        "setreplace_available": True,
        "wolfram": {"wolframscript": "C:/wolframscript.exe", "wolfram_kernel": None, "install_dir_present": True},
    }
    verdict = engine.tool_verdict(probe, {"multiway_available": False})
    assert verdict["verdict"] == "SOTA-OK"
    # Et `caps` entre dans le motif : la surface multiway mesuree est dite.
    assert "sans enumeration multiway" in verdict["motive"]
    # Sans Wolfram, l'alternative ouverte reprend la main.
    probe_sans_wolfram = {
        "setreplace_available": True,
        "wolfram": {"wolframscript": None, "wolfram_kernel": None, "install_dir_present": False},
    }
    assert engine.tool_verdict(probe_sans_wolfram, {"multiway_available": False})["verdict"] == "RECOVERABLE-LOCAL"
