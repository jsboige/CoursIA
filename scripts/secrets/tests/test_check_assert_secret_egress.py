#!/usr/bin/env python3
"""#17276 -- tests du garde `check_assert_secret_egress.py`.

Le test qui porte le plus est `test_le_faux_positif_mesure_ne_declenche_pas` :
c'est la forme reellement rencontree sur le corpus (`for token in ("sae", ...)`),
et c'est elle qui decide du §3 de l'issue -- un garde qui la signalerait serait
du bruit permanent, et la conclusion serait « regle de revue », pas « garde ».

Les autres tests pinent la forme fautive et la forme de remplacement, dans les
deux sens : ce qui doit declencher, et ce qui ne doit pas.

Ce module n'exige AUCUN secret (ni `.secrets/master.env`, absent d'un checkout
neuf) : tout est synthetique et pur.
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_assert_secret_egress as guard  # noqa: E402


def sites_of(tmp_path: Path, source: str) -> list[dict]:
    """Ecrit la source dans un fichier jetable et rend les sites detectes."""
    p = tmp_path / "test_cas.py"
    p.write_text(source, encoding="utf-8")
    return guard.scan_file(p)


# --- ce qui NE doit PAS declencher ------------------------------------------


def test_le_faux_positif_mesure_ne_declenche_pas(tmp_path):
    """`token` est aussi un mot legitime non-secret : boucle sur un litteral.

    Forme relevee sur `MyIA.AI.Notebooks/IIT/ICT-Series/ict/tests/
    test_lens_endpoints.py` L140. La valeur ne PEUT pas etre un secret.
    """
    src = (
        "import unittest\n"
        "class T(unittest.TestCase):\n"
        "    def test_x(self):\n"
        "        msg = 'sae/state/recon_mse'\n"
        "        for token in ('sae', 'state', 'recon_mse'):\n"
        "            self.assertIn(token, msg)\n"
    )
    assert sites_of(tmp_path, src) == []


def test_affectation_a_un_litteral_ne_declenche_pas(tmp_path):
    """Un identifiant lie a un litteral est une constante, pas un secret runtime."""
    src = (
        "import unittest\n"
        "API_KEY = 'valeur-de-test-en-clair'\n"
        "class T(unittest.TestCase):\n"
        "    def test_x(self):\n"
        "        self.assertEqual(API_KEY, 'valeur-de-test-en-clair')\n"
    )
    assert sites_of(tmp_path, src) == []


@pytest.mark.parametrize("form", ["assertTrue", "assertFalse"])
def test_la_forme_qui_n_interpole_pas_ne_declenche_pas(tmp_path, form):
    """`assertTrue(x is None)` n'imprime que le booleen, jamais la valeur.

    C'est la forme de remplacement proposee par l'issue : elle ne doit pas
    declencher, sinon le garde pousserait a defaire son propre correctif.
    """
    src = (
        "import unittest\n"
        "from commands.models import _get_hf_token\n"
        "class T(unittest.TestCase):\n"
        "    def test_x(self):\n"
        "        self.%s(_get_hf_token() is None)\n" % form
    )
    assert sites_of(tmp_path, src) == []


def test_un_identifiant_sans_rapport_ne_declenche_pas(tmp_path):
    src = (
        "import unittest\n"
        "class T(unittest.TestCase):\n"
        "    def test_x(self):\n"
        "        self.assertEqual(compute_total(), 42)\n"
    )
    assert sites_of(tmp_path, src) == []


# --- ce qui DOIT declencher -------------------------------------------------


def test_la_forme_fautive_mesuree_declenche(tmp_path):
    """L'instance d'origine, verbatim de #17276."""
    src = (
        "import os, unittest\n"
        "from commands import models\n"
        "class T(unittest.TestCase):\n"
        "    def test_hf_token_none_when_no_env_no_files(self):\n"
        "        self.assertIsNone(models._get_hf_token())\n"
    )
    found = sites_of(tmp_path, src)
    assert len(found) == 1
    assert found[0]["assert"] == "assertIsNone"
    assert found[0]["id"] == ["_get_hf_token"]


def test_assert_equal_sur_un_appel_declenche(tmp_path):
    src = (
        "import unittest\n"
        "from commands.models import _get_hf_token\n"
        "class T(unittest.TestCase):\n"
        "    def test_x(self):\n"
        "        self.assertEqual(_get_hf_token(), 'hf_test123')\n"
    )
    found = sites_of(tmp_path, src)
    assert len(found) == 1
    assert found[0]["assert"] == "assertEqual"


def test_un_getenv_declenche(tmp_path):
    src = (
        "import os, unittest\n"
        "class T(unittest.TestCase):\n"
        "    def test_x(self):\n"
        "        self.assertIsNotNone(os.getenv('HF_TOKEN'))\n"
    )
    assert len(sites_of(tmp_path, src)) == 1


def test_un_message_explicite_qui_reference_la_valeur_declenche(tmp_path):
    """`msg=` est le cas ou la fuite ne vient pas de `unittest` mais de l'auteur."""
    src = (
        "import unittest\n"
        "from commands.models import _get_hf_token\n"
        "class T(unittest.TestCase):\n"
        "    def test_x(self):\n"
        "        tok = _get_hf_token()\n"
        "        self.assertTrue(tok is not None, f'jeton lu: {tok}')\n"
    )
    assert len(sites_of(tmp_path, src)) == 1


def test_un_attribut_secret_issu_d_un_appel_declenche(tmp_path):
    src = (
        "import unittest\n"
        "class T(unittest.TestCase):\n"
        "    def test_x(self):\n"
        "        self.assertEqual(load_settings().api_key, 'x')\n"
    )
    assert len(sites_of(tmp_path, src)) == 1


# --- la portee : le test qui protege les 14 faux positifs mesures -------------


def test_le_chainage_ne_fuit_pas_hors_de_sa_fonction(tmp_path):
    """Une variable locale est LOCALE. Test de non-regression le plus important.

    La premiere version du chainage prenait l'arbre ENTIER : un seul
    `result = _get_hf_token()` (L121 de test_genai_stack_round4.py) faisait
    basculer 14 assertions d'AUTRES methodes -- `result` y valant tour a tour
    `profile_current()`, `check_fit(4096)`, `execute(args)` -- soit **14 faux
    positifs sur 16 sites (87.5%)**. Ici la methode B ne doit RIEN produire.

    Sans ce test, un « simplifions ce parcours en un seul `ast.walk` » remet le
    taux a 87.5% en silence : le garde reste vert sur sa baseline, et le bruit
    ne se voit qu'a la prochaine introduction.
    """
    src = (
        "import unittest\n"
        "from commands.models import _get_hf_token\n"
        "class T(unittest.TestCase):\n"
        "    def test_le_jeton(self):\n"
        "        result = _get_hf_token()\n"
        "        self.assertEqual(result, 'hf_test')\n"
        "    def test_autre_chose(self):\n"
        "        result = compute_total()\n"
        "        self.assertEqual(result, 42)\n"
    )
    found = sites_of(tmp_path, src)
    assert len(found) == 1, "seule la methode qui lit le jeton doit produire un site"
    assert found[0]["line"] == 6


def test_un_litteral_injecte_par_le_test_reste_un_site(tmp_path):
    """Limite CONNUE et assumee, epinglee ici pour qu'elle soit un choix lisible.

    Forme de L114/L122 de test_genai_stack_round4.py : le test injecte lui-meme
    un litteral via `patch.dict(os.environ, {...})`, donc le "secret" ne peut
    pas etre un vrai jeton -- mais le garde ne sait pas lire ca. Il constate la
    violation de CONTRAT (assertion interpolante sur valeur issue d'un appel),
    pas le danger. La revue tranche ; le garde ne pretend pas trancher.

    Piner ce comportement evite qu'il passe un jour pour un bug et soit
    "corrige" par une heuristique sur `patch.dict` dont le taux de faux
    positifs n'aurait pas ete mesure.
    """
    src = (
        "import os, unittest\n"
        "from unittest.mock import patch\n"
        "from commands.models import _get_hf_token\n"
        "class T(unittest.TestCase):\n"
        "    @patch.dict(os.environ, {'HUGGINGFACE_TOKEN': 'hf_from_alt'})\n"
        "    def test_x(self):\n"
        "        result = _get_hf_token()\n"
        "        self.assertEqual(result, 'hf_from_alt')\n"
    )
    assert len(sites_of(tmp_path, src)) == 1


# --- le mode --check, qui est celui de la CI --------------------------------


def _patch(tmp_path, monkeypatch, sites, baseline_keys):
    baseline = tmp_path / "baseline.json"
    baseline.write_text(json.dumps({"entries": baseline_keys}), encoding="utf-8")
    monkeypatch.setattr(guard, "DEFAULT_BASELINE", baseline)
    monkeypatch.setattr(guard, "scan", lambda: sites)


def test_check_est_vert_sur_les_sites_connus(tmp_path, monkeypatch, capsys):
    sites = [{"file": "a.py", "line": 1, "assert": "assertIsNone",
              "id": ["tok"], "expr": "tok()", "key": "a.py::assertIsNone::tok::tok()"}]
    _patch(tmp_path, monkeypatch, sites, [sites[0]["key"]])
    assert guard.main(["--check"]) == 0
    assert "0 nouveau" in capsys.readouterr().out


def test_check_rougit_sur_un_site_nouveau(tmp_path, monkeypatch, capsys):
    """Le coeur du garde : l'etat actuel est vert, la PROCHAINE introduction rougit."""
    known = {"file": "a.py", "line": 1, "assert": "assertIsNone",
             "id": ["tok"], "expr": "tok()", "key": "a.py::assertIsNone::tok::tok()"}
    fresh = {"file": "b.py", "line": 9, "assert": "assertEqual",
             "id": ["_get_hf_token"], "expr": "_get_hf_token()",
             "key": "b.py::assertEqual::_get_hf_token::_get_hf_token()"}
    _patch(tmp_path, monkeypatch, [known, fresh], [known["key"]])
    assert guard.main(["--check"]) == 1
    out = capsys.readouterr().out
    assert "NOUVEAU" in out
    assert "b.py" in out
    assert "assertTrue(x is None)" in out, "le message doit nommer la forme correcte"


def test_baseline_absente_traite_comme_vide(tmp_path, monkeypatch):
    """Une baseline illisible ne doit pas faire passer en silence (regle 1)."""
    monkeypatch.setattr(guard, "DEFAULT_BASELINE", tmp_path / "absente.json")
    assert guard.load_baseline(guard.DEFAULT_BASELINE) == []


def test_un_fichier_illisible_ne_fait_pas_planter_le_scan(tmp_path):
    assert guard.scan_file(tmp_path / "inexistant.py") == []
