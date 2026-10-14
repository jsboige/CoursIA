"""Tests de `scripts/notebook_tools/verify_arxiv_ids.py`.

Aucun acces reseau : le transport est monkeypatche. Ce qui est teste est la
**semantique des verdicts**, c'est-a-dire ce que l'outil a le droit d'affirmer
quand il n'a rien pu lire -- la question qui a fonde le correctif du
2026-09-21 (EPIC #11168).

Les deux cas de regression, nominativement :

1. `test_absent_id_is_notfound_not_a_guard_failure` -- un ID inexistant est une
   **mesure** (`notfound`), pas un echec du garde-fou. Avant le correctif,
   `totalResults=0` etait rapporte comme « echec », ce qui rendait le verdict
   `ID-FANTOME` **structurellement inprononcable**.
2. `test_transport_never_yields_a_verdict_and_exits_2` -- une panne de transport
   ne rend **aucun** verdict et sort en code 2. Avant le correctif, 90 IDs sous
   limitation de debit arXiv sortaient `ok:false` avec un **code 0**.
"""
import sys
import urllib.error
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.notebook_tools import verify_arxiv_ids as V  # noqa: E402


class _Resp:
    def __init__(self, body):
        self._body = body

    def read(self):
        return self._body

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        return False


def _feed(entries):
    """Construit un flux Atom minimal, de la forme que rend l'API arXiv."""
    parts = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<feed xmlns="http://www.w3.org/2005/Atom">',
    ]
    for e in entries:
        parts.append("<entry>")
        parts.append(f"<id>http://arxiv.org/abs/{e['id']}</id>")
        parts.append(f"<title>{e.get('title', 'Untitled')}</title>")
        for name in e.get("authors", []):
            parts.append(f"<author><name>{name}</name></author>")
        parts.append(f"<published>{e.get('published', '2017-06-12T17:57:34Z')}</published>")
        parts.append("</entry>")
    parts.append("</feed>")
    return "\n".join(parts).encode("utf-8")


def _opener(body):
    return lambda req, timeout=None: _Resp(body)


def _raiser(exc):
    def _f(req, timeout=None):
        raise exc
    return _f


def _http_error(code="406", reason="Not Acceptable"):
    return urllib.error.HTTPError(
        "https://export.arxiv.org/api/query", int(code), reason, {}, None
    )


@pytest.fixture
def fast(monkeypatch):
    """Neutralise les attentes entre tentatives : les tests restent instantanes."""
    monkeypatch.setattr(V.time, "sleep", lambda *_a, **_k: None)


# --- Cas nominal -----------------------------------------------------------

def test_valid_entry_yields_ok_with_metadata(monkeypatch, fast):
    body = _feed([{
        "id": "1706.03762v7",
        "title": "Attention\n  Is All You Need",
        "authors": ["Ashish Vaswani", "Noam Shazeer"],
    }])
    monkeypatch.setattr(V.urllib.request, "urlopen", _opener(body))

    rec = V.query_one("1706.03762", tries=1, base_delay=0)

    assert rec["verdict"] == "ok"
    assert rec["title"] == "Attention Is All You Need"  # espaces normalises
    assert rec["authors"] == ["Ashish Vaswani", "Noam Shazeer"]
    assert rec["published"].startswith("2017")


def test_versioned_entry_matches_bare_requested_id(monkeypatch, fast):
    """L'API rend `v7` pour l'ID demande sans suffixe : ce n'est pas un absent."""
    monkeypatch.setattr(
        V.urllib.request, "urlopen",
        _opener(_feed([{"id": "1706.03762v7"}])),
    )
    assert V.query_one("1706.03762", tries=1, base_delay=0)["verdict"] == "ok"


def test_prefixed_id_is_matched(monkeypatch, fast):
    """Les IDs a prefixe (`cs/0011047`) sont la forme majoritaire du depot."""
    monkeypatch.setattr(
        V.urllib.request, "urlopen",
        _opener(_feed([{"id": "cs/0011047v2"}])),
    )
    assert V.query_one("cs/0011047", tries=1, base_delay=0)["verdict"] == "ok"


# --- Regression 1 : un ID inexistant est une MESURE ------------------------

def test_absent_id_is_notfound_not_a_guard_failure(monkeypatch, fast):
    """`totalResults=0` + aucune entree = `notfound`, jamais `transport`.

    C'est le verdict `ID-FANTOME` de l'EPIC #11168. La version precedente le
    rapportait comme « echec du garde-fou », dans la meme classe qu'une panne
    reseau -- l'outil ne pouvait donc jamais le prononcer.
    """
    empty = (
        b'<?xml version="1.0" encoding="UTF-8"?>'
        b'<feed xmlns="http://www.w3.org/2005/Atom">'
        b'<opensearch:totalResults xmlns:opensearch="http://a9.com/-/spec/opensearch/1.1/">0'
        b"</opensearch:totalResults></feed>"
    )
    monkeypatch.setattr(V.urllib.request, "urlopen", _opener(empty))

    rec = V.query_one("9999.99999", tries=1, base_delay=0)

    assert rec["verdict"] == "notfound"
    assert rec["verdict"] != "transport"
    assert rec["error"] is None
    assert rec["title"] is None


def test_feed_containing_another_entry_is_notfound_for_this_id(monkeypatch, fast):
    """Un flux valide qui ne porte PAS cet ID reste un `notfound` mesure."""
    monkeypatch.setattr(
        V.urllib.request, "urlopen",
        _opener(_feed([{"id": "1706.03762v7"}])),
    )
    assert V.query_one("1234.5678", tries=1, base_delay=0)["verdict"] == "notfound"


# --- Regression 2 : un transport ne rend AUCUN verdict ---------------------

def test_transport_never_yields_a_verdict_and_exits_2(monkeypatch, fast):
    """HTTP 406 sur toutes les tentatives -> `transport`, et sortie 2."""
    monkeypatch.setattr(V.urllib.request, "urlopen", _raiser(_http_error("406")))

    with pytest.raises(V.TransportError) as exc:
        V.query_one("1706.03762", tries=3, base_delay=0)
    assert "406" in str(exc.value)

    monkeypatch.setattr(
        V, "query_one",
        lambda aid, tries=4, base_delay=3.0: (_ for _ in ()).throw(
            V.TransportError("HTTP 406 Not Acceptable")
        ),
    )
    rc = V.main(["--ids", "1706.03762", "--delay", "0"])
    assert rc == V.TRANSPORT_EXIT == 2


def test_transient_failure_is_retried_then_succeeds(monkeypatch, fast):
    """Un 406 isole ne doit pas condamner un ID : le repli exponentiel le sauve."""
    calls = {"n": 0}
    body = _feed([{"id": "1706.03762v7", "title": "Attention Is All You Need"}])

    def flaky(req, timeout=None):
        calls["n"] += 1
        if calls["n"] < 3:
            raise _http_error("406")
        return _Resp(body)

    monkeypatch.setattr(V.urllib.request, "urlopen", flaky)
    rec = V.query_one("1706.03762", tries=4, base_delay=0)

    assert calls["n"] == 3          # deux echecs, puis succes
    assert rec["verdict"] == "ok"


def test_non_retryable_status_fails_immediately(monkeypatch, fast):
    """Un 404 n'est pas transitoire : inutile de le reessayer."""
    calls = {"n": 0}

    def blocked(req, timeout=None):
        calls["n"] += 1
        raise _http_error("404", "Not Found")

    monkeypatch.setattr(V.urllib.request, "urlopen", blocked)
    with pytest.raises(V.TransportError):
        V.query_one("1706.03762", tries=4, base_delay=0)
    assert calls["n"] == 1


def test_empty_body_is_transport_not_absence(monkeypatch, fast):
    """Un corps vide n'est pas « aucune entree » : ce n'est pas une mesure."""
    monkeypatch.setattr(V.urllib.request, "urlopen", _opener(b""))
    with pytest.raises(V.TransportError):
        V.query_one("1706.03762", tries=1, base_delay=0)


def test_unparsable_xml_is_transport(monkeypatch, fast):
    monkeypatch.setattr(V.urllib.request, "urlopen", _opener(b"<html>502 Bad Gateway</html"))
    with pytest.raises(V.TransportError):
        V.query_one("1706.03762", tries=1, base_delay=0)


# --- `verify_ids` : le lot ne propage pas l'echec d'un ID aux autres -------

def test_one_transport_does_not_contaminate_the_other_ids(monkeypatch, fast):
    """Chaque ID porte SON verdict : un non-mesurable ne contamine pas ses voisins."""
    def per_id(req, timeout=None):
        url = req.full_url if hasattr(req, "full_url") else str(req)
        if "1706.03762" in url:
            raise _http_error("406")
        return _Resp(_feed([{"id": "1234.5678v1", "title": "A Paper"}]))

    monkeypatch.setattr(V.urllib.request, "urlopen", per_id)
    results = V.verify_ids(["1706.03762", "1234.5678"], delay=0, tries=1, base_delay=0)

    assert [r["verdict"] for r in results] == ["transport", "ok"]


def test_exit_code_is_zero_only_when_every_id_is_measured(monkeypatch, fast, tmp_path, capsys):
    def per_id(req, timeout=None):
        url = req.full_url if hasattr(req, "full_url") else str(req)
        if "absent" in url:
            return _Resp(b'<?xml version="1.0"?><feed xmlns="http://www.w3.org/2005/Atom"/>')
        return _Resp(_feed([{"id": "1706.03762v7"}]))

    monkeypatch.setattr(V.urllib.request, "urlopen", per_id)
    out = tmp_path / "verdicts.json"

    # un `ok` et un `notfound` : les deux sont des mesures -> 0
    rc = V.main(["--ids", "1706.03762,absent.12345", "--delay", "0", "--tries", "1",
                 "--base-delay", "0", "--out", str(out)])
    assert rc == 0
    assert out.exists()
    import json
    verdicts = [r["verdict"] for r in json.loads(out.read_text(encoding="utf-8"))]
    assert verdicts == ["ok", "notfound"]
    assert "ABSENT" in capsys.readouterr().out


def test_ids_may_come_from_a_file(tmp_path):
    f = tmp_path / "ids.txt"
    f.write_text("# commentaire\n1706.03762\n\ncs/0011047\n", encoding="utf-8")
    assert V._read_ids(str(f)) == ["1706.03762", "cs/0011047"]
