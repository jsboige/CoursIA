import json
import os
from pathlib import Path
import socket
import subprocess
import sys
import time
from urllib.error import URLError
from urllib.request import Request, urlopen

import pytest
from rdflib import Graph, RDF

sys.path.insert(0, str(Path(__file__).resolve().parent))
import service

TOOLS = Path(__file__).resolve().parent.parent


@pytest.fixture
def generated_graph(tmp_path):
    entries = [
        {'path': 'Demo/Part/A.ipynb', 'title': 'Premier', 'serie': 'Demo',
         'sous_serie': 'Part', 'prerequisite': 'Bases'},
        {'path': 'Demo/B.ipynb', 'title': 'Second', 'serie': 'Demo'},
    ]
    catalog = tmp_path / 'catalog.json'
    catalog.write_text(json.dumps(entries), encoding='utf-8')
    output = tmp_path / 'graph.ttl'
    subprocess.run([sys.executable, str(TOOLS / 'generate_curriculum_rdf.py'),
                    '--catalog', str(catalog), '--output', str(output)], check=True)
    return output


def test_queries_match_sparql_and_invalid_inputs(generated_graph):
    graph = service.load(generated_graph)
    sparql = list(graph.query('''PREFIX c: <https://github.com/jsboige/CoursIA/vocab/cursus#>
        SELECT ?s WHERE { ?s a c:Series }'''))
    assert len(service.handle(graph, {'action': 'series'})['results']) == len(sparql) == 1
    assert service.handle(graph, {'action': 'path', 'path': 'Demo/Part/A.ipynb'})['results'] == ['Demo', 'Part', 'Premier']
    assert service.handle(graph, {'action': 'prerequisites', 'path': 'Demo/Part/A.ipynb'})['results'] == ['Bases']
    assert 'non renseignés' in service.handle(graph, {'action': 'prerequisites', 'path': 'Demo/B.ipynb'})['results'][0]
    assert service.handle(graph, {'action': 'path', 'path': 'absent'})['status'] == 'not_found'
    assert service.handle(graph, {'action': []})['status'] == 'invalid'
    assert service.handle(graph, {'action': 'path', 'path': 1})['status'] == 'invalid'
    assert service.handle(graph, None)['status'] == 'invalid'
    assert service.handle(graph, {'action': 'path', 'path': '\" } UNION { ?s ?p ?o'})['status'] == 'not_found'


def test_shacl_rejects_invalid_graph(generated_graph, tmp_path):
    graph = Graph().parse(generated_graph)
    notebook = next(graph.subjects(RDF.type, service.reader.VOCAB.Notebook))
    graph.remove((notebook, service.reader.VOCAB.inSeries, None))
    broken = tmp_path / 'broken.ttl'
    graph.serialize(destination=broken, format='turtle')
    with pytest.raises(ValueError, match='SHACL'):
        service.load(broken)


def test_http_gateway(generated_graph):
    with socket.socket() as sock:
        sock.bind(('127.0.0.1', 0))
        port = sock.getsockname()[1]
    process = subprocess.Popen([sys.executable, str(Path(service.__file__)), '--graph', str(generated_graph), '--port', str(port)], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)
    url = f'http://127.0.0.1:{port}/curriculum/query'
    def post(body):
        request = Request(url, data=json.dumps(body).encode(), headers={'Content-Type': 'application/json'})
        with urlopen(request, timeout=5) as response:
            return json.load(response)
    try:
        deadline = time.monotonic() + 35
        while True:
            try:
                result = post({'action': 'series'})
                break
            except (URLError, TimeoutError):
                if process.poll() is not None or time.monotonic() >= deadline:
                    raise
                time.sleep(.25)
        assert result['status'] == 'ok' and len(result['results']) == 1
        assert post({'action': 'path', 'path': 'Demo/Part/A.ipynb'})['results'] == ['Demo', 'Part', 'Premier']
        assert post({'action': 'prerequisites', 'path': 'Demo/Part/A.ipynb'})['results'] == ['Bases']
        assert post({'action': 'path'})['status'] == 'invalid'
        assert post({'action': 'path', 'path': 'absent'})['status'] == 'not_found'
    finally:
        import signal
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        process.wait(timeout=10)
