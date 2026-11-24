#!/usr/bin/env python3
"""`decision_local_check.py` ne doit jamais produire une mesure vide.

Contexte
---------
L'organe de verification locale du Decision Index (Pli 1 de #18204, livre par
#21921) mesure l'exactitude, la calibration (ECE) et le score de Brier de
modeles de decision servis localement, puis confronte l'ordre mesure a l'ordre
publie par l'index.

Deux defauts faisaient qu'un **run vert ne mesurait rien** (#23616) :

1. `parse_modele` lisait le suffixe `:N` comme la limite **avant** de separer le
   device. `#cuda:0` — un index de carte — devenait donc « device cuda,
   limite 0 ». La grammaire documentee ne permettait pas d'ecrire un index.
2. Une limite nulle etait acceptee sans erreur. L'agregat produit portait un
   temps de chargement et un pic de VRAM **reels**, mais aucune metrique
   (exactitude, ECE, Brier) ; le run sortait en 0 et l'agregat etait ecrit
   comme un resultat. Ecrit comme cela, il passait pour une mesure.

Ces tests gardent les deux refus (spec illisible, mesure vide), l'echelle
d'echec (3) et le chemin nominal. Aucun acces reseau, aucun modele : `jiwo`,
`torch`, `load_items` et `evalue_modele` sont remplaces par des doublures.
"""

import importlib.util
import json
import sys
import types
from pathlib import Path

import pytest

_MOD_PATH = Path(__file__).resolve().parent.parent / "genai-stack" / "decision_local_check.py"
_spec = importlib.util.spec_from_file_location("decision_local_check", _MOD_PATH)
organ = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(organ)

LIMITE_DEFAUT = 300  # `--limit` par defaut de l'organe


# ---- doublures --------------------------------------------------------------------

def _faux_dependances(monkeypatch):
    """`jiwo` et `torch` sans GPU : l'organe n'en a besoin que pour l'environnement."""
    torch = types.ModuleType("torch")
    torch.__version__ = "faux"
    torch.cuda = types.SimpleNamespace(is_available=lambda: False)
    jiwo = types.ModuleType("jiwo")
    jiwo.__version__ = "faux"
    monkeypatch.setitem(sys.modules, "torch", torch)
    monkeypatch.setitem(sys.modules, "jiwo", jiwo)


def _items(nom, limite, graine):
    """Tranche minimale : trois items QCM par jeu."""
    return [
        {"id": f"{nom}-{index}", "dataset": nom, "question": f"question {index}",
         "options": ["un", "deux", "trois", "quatre"], "reponse": index % 4}
        for index in range(3)
    ]


def _evalueuse(vide):
    """Rend un `evalue_modele` qui mesure les items de la tranche, ou n'en mesure aucun."""
    def _evalue(modele, tranches, max_length):
        lignes = []
        par_jeu = {}
        for nom, items in tranches.items():
            locales = [] if vide else [
                {"id": item["id"], "correct": True, "p_gold": 0.8,
                 "confiance": 0.8, "brier": 0.2, "nb_options": 4}
                for item in items
            ]
            par_jeu[nom] = organ.agrege(locales)
            lignes.extend(locales)
        return {
            "id": modele["id"], "depot": modele["depot"],
            "revision": modele["revision"] or "main (v2)", "device": modele["device"],
            "limite_par_jeu": modele["limite"], "chargement_s": 0.0, "evaluation_s": 0.0,
            "vram_peak_go": None, "par_jeu": par_jeu,
            "global": organ.agrege(lignes), "items": lignes,
        }
    return _evalue


# ---- lecture de la spec -----------------------------------------------------------

class TestParseModele:
    """La spec d'un modele est un argument : elle doit etre lue sans ambiguite."""

    def test_limite_nulle_refusee(self):
        """`#cuda:0` se lisait « device cuda, limite 0 » : il doit etre refuse."""
        with pytest.raises(organ.SpecModeleInvalide) as echec:
            organ.parse_modele("eljiwo/jiwo-0.8b@v1#cuda:0", "cuda", LIMITE_DEFAUT)
        assert "index de carte" in str(echec.value)

    def test_limite_non_entiere_refusee(self):
        with pytest.raises(organ.SpecModeleInvalide):
            organ.parse_modele("eljiwo/jiwo-0.8b@v1#cuda:abc", "cuda", LIMITE_DEFAUT)

    def test_index_de_device_ecrit_avec_une_barre(self):
        """`#cuda/0` designe la carte 0 : la grammaire sait enfin l'ecrire."""
        modele = organ.parse_modele("eljiwo/jiwo-0.8b@v1#cuda/0", "cpu", LIMITE_DEFAUT)
        assert modele["device"] == "cuda:0"
        assert modele["limite"] == LIMITE_DEFAUT

    def test_index_de_device_avec_limite(self):
        modele = organ.parse_modele("eljiwo/jiwo-0.8b@v1#cuda/1:100", "cpu", LIMITE_DEFAUT)
        assert modele["device"] == "cuda:1"
        assert modele["limite"] == 100

    def test_index_de_device_illisible_refuse(self):
        with pytest.raises(organ.SpecModeleInvalide):
            organ.parse_modele("eljiwo/jiwo-0.8b@v1#cuda/x", "cpu", LIMITE_DEFAUT)

    def test_forme_legacy_device_et_limite_conservee(self):
        """La forme documentee `#cpu:100` garde son sens : device cpu, limite 100."""
        modele = organ.parse_modele("eljiwo/jiwo-4b@v2#cpu:100", "cuda", LIMITE_DEFAUT)
        assert modele["device"] == "cpu"
        assert modele["limite"] == 100

    def test_spec_sans_device_ni_limite(self):
        modele = organ.parse_modele("eljiwo/jiwo-0.8b@v1", "cuda", LIMITE_DEFAUT)
        assert modele["device"] == "cuda"
        assert modele["limite"] == LIMITE_DEFAUT
        assert modele["revision"] == "v1"
        assert modele["depot"] == "eljiwo/jiwo-0.8b"

    def test_device_vide_refuse(self):
        with pytest.raises(organ.SpecModeleInvalide):
            organ.parse_modele("eljiwo/jiwo-0.8b@v1#", "cuda", LIMITE_DEFAUT)


# ---- invariant de mesure ----------------------------------------------------------

class TestVerifieMesure:
    """Une mesure sans item n'est pas une mesure."""

    def test_mesure_vide_refusee(self):
        modele = {"id": "eljiwo/jiwo-0.8b@v1", "limite": 0}
        with pytest.raises(organ.MesureVide):
            organ.verifie_mesure(modele, {"global": {"items": 0}})

    def test_mesure_non_vide_acceptee(self):
        modele = {"id": "eljiwo/jiwo-0.8b@v1", "limite": 10}
        organ.verifie_mesure(modele, {"global": {"items": 3, "exactitude": 0.5}})


# ---- comportement de la ligne de commande ------------------------------------------

class TestMain:
    """Le refus doit etire bruyant, et ne rien ecrire."""

    def test_limite_nulle_refusee(self):
        with pytest.raises(SystemExit) as sortie:
            organ.main(["--model", "eljiwo/jiwo-0.8b@v1", "--limit", "0"])
        assert sortie.value.code == 2

    def test_spec_illisible_refusee_avant_tout_travail(self):
        """Le refus ne doit rien charger : ni jeu de donnees, ni modele."""
        with pytest.raises(SystemExit) as sortie:
            organ.main(["--model", "eljiwo/jiwo-0.8b@v1#cuda:0", "--limit", "20"])
        assert sortie.value.code == 2

    def test_mesure_vide_refusee_sans_agregat(self, monkeypatch, tmp_path):
        """Un run qui ne mesure rien echoue en 3 et n'ecrit aucun agregat."""
        _faux_dependances(monkeypatch)
        monkeypatch.setattr(organ, "load_items", _items)
        monkeypatch.setattr(organ, "evalue_modele", _evalueuse(vide=True))
        sortie_json = tmp_path / "agregat.json"

        code = organ.main(["--model", "eljiwo/jiwo-0.8b@v1", "--limit", "20",
                           "--json", str(sortie_json)])

        assert code == 3
        assert not sortie_json.exists()

    def test_mesure_nominale_ecrit_l_agregat(self, monkeypatch, tmp_path):
        """Controle positif : le chemin nominal reste vert et ecrit son agregat."""
        _faux_dependances(monkeypatch)
        monkeypatch.setattr(organ, "load_items", _items)
        monkeypatch.setattr(organ, "evalue_modele", _evalueuse(vide=False))
        sortie_json = tmp_path / "agregat.json"

        code = organ.main(["--model", "eljiwo/jiwo-0.8b@v1", "--limit", "20",
                           "--json", str(sortie_json)])

        assert code == 0
        assert sortie_json.exists()
        agregat = json.loads(sortie_json.read_text(encoding="utf-8"))
        mesure = agregat["modeles"]["eljiwo/jiwo-0.8b@v1"]
        assert mesure["global"]["items"] == 9  # 3 jeux x 3 items
        assert mesure["global"]["exactitude"] == 1.0
