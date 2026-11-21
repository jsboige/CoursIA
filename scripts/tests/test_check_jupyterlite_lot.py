"""Tests du garde post-deploiement du lot JupyterLite (#27550).

Le garde lit le manifeste **du site publie** et sonde chaque URL du lot.
Ces tests verrouillent la resolution des URL (le prefixe du depot ne doit
pas se cumuler) et les trois verdicts : lot en ligne, lien casse, manifeste
absent (lot non deploye -- ce n'est pas un lien casse).

Aucun test ne touche le reseau : les sondes sont remplacees.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "ci" / "check_jupyterlite_lot.py"

BASE = "https://example.test/CoursIA"


def _load():
    sys.path.insert(0, str(SCRIPT.parent))
    import check_jupyterlite_lot as mod  # noqa: WPS433
    return mod


def _manifeste(nb: int = 2) -> dict:
    return {
        "source": "critere-pyodide-2.1",
        "taille": nb,
        "carnets": [
            {
                "chemin": "MyIA.AI.Notebooks/SerieA/carnet%d.ipynb" % k,
                "fichier": "carnet%d.ipynb" % k,
                "serie": "SerieA",
                "files": "/CoursIA/jupyterlite/files/carnet%d.ipynb" % k,
                "lab": "/CoursIA/jupyterlite/lab/index.html?path=carnet%d.ipynb" % k,
            }
            for k in range(nb)
        ],
    }


def test_le_manifeste_est_cherche_a_la_racine_du_site() -> None:
    """Le manifeste vit sous /jupyterlite/ de la racine du site."""
    mod = _load()
    assert mod._url_manifeste(BASE, "/jupyterlite/manifest.json") == \
        BASE + "/jupyterlite/manifest.json"


def test_les_urls_du_manifeste_ne_sont_pas_prefixees_deux_fois() -> None:
    """Les chemins du manifeste portent deja le prefixe du depot.

    Les recoller a la racine du site (/CoursIA/CoursIA/...) produirait une
    URL qui repond 404 -- un lien casse fabrique par le garde lui-meme.
    """
    mod = _load()
    assert mod._url_carnet(BASE, "/CoursIA/jupyterlite/files/a.ipynb") == \
        "https://example.test/CoursIA/jupyterlite/files/a.ipynb"


def test_un_chemin_sans_prefixe_est_colle_a_la_racine_du_site() -> None:
    """Un manifeste construit sans prefixe reste resolvable."""
    mod = _load()
    assert mod._url_carnet(BASE, "/jupyterlite/files/a.ipynb") == \
        "https://example.test/jupyterlite/files/a.ipynb"


def test_une_url_absolue_est_laissee_telle_quelle() -> None:
    """Un manifeste qui porte une URL complete n'est pas retouche."""
    mod = _load()
    assert mod._url_carnet(BASE, "https://cdn.test/a.ipynb") == "https://cdn.test/a.ipynb"


def _run(mod, monkeypatch, manifest, statuts, **kwargs):
    """Remplace la sonde HTTP et la lecture du manifeste."""
    monkeypatch.setattr(mod, "_probe", lambda url, timeout=20.0: statuts.get(url, 404))
    return mod.run_check(BASE, **kwargs)


def test_un_lot_en_ligne_ne_rougit_pas(monkeypatch) -> None:
    """Toutes les URLs du lot repondent : verdict vert."""
    mod = _load()
    urls = ["https://example.test/CoursIA/jupyterlite/files/carnet%d.ipynb" % k
            for k in range(2)]
    urls += ["https://example.test/CoursIA/jupyterlite/lab/index.html?path=carnet%d.ipynb" % k
             for k in range(2)]

    class _Reponse:
        def __init__(self, data):
            self._data = data

        def read(self):
            return json.dumps(self._data).encode("utf-8")

        def __enter__(self):
            return self

        def __exit__(self, *args):
            return False

        status = 200

    monkeypatch.setattr(mod.urllib.request, "urlopen",
                        lambda *a, **k: _Reponse(_manifeste()))
    result = _run(mod, monkeypatch, _manifeste(), {u: 200 for u in urls})
    assert result.found is True
    assert result.checked == 4
    assert result.ok == 4
    assert result.broken == []
    assert result.instrument_errors == []


def test_un_carnet_casse_est_signale(monkeypatch) -> None:
    """Un carnet absent du site est signale, avec son URL et son statut."""
    mod = _load()

    class _Reponse:
        def read(self):
            return json.dumps(_manifeste(1)).encode("utf-8")

        def __enter__(self):
            return self

        def __exit__(self, *args):
            return False

        status = 200

    monkeypatch.setattr(mod.urllib.request, "urlopen",
                        lambda *a, **k: _Reponse())
    result = _run(mod, monkeypatch, _manifeste(1),
                  {"https://example.test/CoursIA/jupyterlite/files/carnet0.ipynb": 404,
                   "https://example.test/CoursIA/jupyterlite/lab/index.html?path=carnet0.ipynb": 200})
    assert len(result.broken) == 1
    assert result.broken[0]["status"] == 404
    assert result.broken[0]["kind"] == "files"
    assert result.broken[0]["notebook"] == "MyIA.AI.Notebooks/SerieA/carnet0.ipynb"


def test_un_manifeste_absent_n_est_pas_un_lien_casse(monkeypatch) -> None:
    """Aucun lot publie : rien n'est annonce, donc rien n'est casse."""
    mod = _load()
    import urllib.error

    def _404(*args, **kwargs):
        raise urllib.error.HTTPError("url", 404, "Not Found", None, None)

    monkeypatch.setattr(mod.urllib.request, "urlopen", _404)
    result = mod.run_check(BASE)
    assert result.found is False
    assert result.broken == []
    assert result.instrument_errors == []


def test_un_manifeste_illisible_est_un_defaut_d_instrument(monkeypatch) -> None:
    """Un manifeste qui ne se parse pas : defaut d'instrument (rc 2), pas
    un lien casse -- les deux ne se confondent pas."""
    mod = _load()

    class _Reponse:
        def read(self):
            return b"{pas du json"

        def __enter__(self):
            return self

        def __exit__(self, *args):
            return False

        status = 200

    monkeypatch.setattr(mod.urllib.request, "urlopen", lambda *a, **k: _Reponse())
    result = mod.run_check(BASE)
    assert result.found is False
    assert result.broken == []
    assert result.instrument_errors


def test_un_carnet_sans_url_dans_le_manifeste_est_signale(monkeypatch) -> None:
    """Un manifeste incomplet (URL manquante) est un defaut d'instrument :
    on ne peut pas dire que le carnet est en ligne."""
    mod = _load()

    class _Reponse:
        def read(self):
            return json.dumps({"carnets": [{"chemin": "a.ipynb"}]}).encode("utf-8")

        def __enter__(self):
            return self

        def __exit__(self, *args):
            return False

        status = 200

    monkeypatch.setattr(mod.urllib.request, "urlopen", lambda *a, **k: _Reponse())
    result = mod.run_check(BASE)
    assert result.instrument_errors
    assert result.broken == []
