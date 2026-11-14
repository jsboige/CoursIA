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

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'notebook_tools' / 'curriculum_gateway'))
import service

TOOLS = Path(__file__).resolve().parents[1] / 'notebook_tools'


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


def await_gateway(post, process, log, log_path, timeout=90):
    deadline = time.monotonic() + timeout
    while True:
        try:
            return post({'action': 'series'})
        except (URLError, TimeoutError):
            if process.poll() is not None or time.monotonic() >= deadline:
                log.flush()
                pytest.fail("Gateway indisponible :\n" + log_path.read_text(encoding="utf-8"))
            time.sleep(.25)


def test_gateway_failure_shows_log(tmp_path):
    log_path = tmp_path / 'failed.log'
    class DeadProcess:
        def poll(self):
            return 1
    def fail_post(_request):
        raise URLError('refus')
    with log_path.open('w+', encoding='utf-8') as log:
        log.write('kernel error: explicit test witness')
        with pytest.raises(pytest.fail.Exception, match='kernel error: explicit test witness'):
            await_gateway(fail_post, DeadProcess(), log, log_path)


def test_http_gateway(generated_graph, tmp_path):
    # Le kernel doit employer le même Python que pytest, même si le runner
    # possède un autre kernelspec python3 dans son environnement partagé.
    kernelspec = tmp_path / "jupyter" / "kernels" / "python3"
    kernelspec.mkdir(parents=True)
    (kernelspec / "kernel.json").write_text(json.dumps({
        "argv": [sys.executable, "-m", "ipykernel_launcher", "-f", "{connection_file}"],
        "display_name": "Python du test", "language": "python",
    }), encoding="utf-8")
    env = os.environ.copy()
    env["JUPYTER_PATH"] = str(tmp_path / "jupyter")
    log_path = tmp_path / "gateway.log"
    with socket.socket() as sock:
        sock.bind(('127.0.0.1', 0))
        port = sock.getsockname()[1]
    log = log_path.open('w+', encoding='utf-8')
    process = subprocess.Popen([sys.executable, str(Path(service.__file__)), '--graph', str(generated_graph), '--port', str(port)], stdout=log, stderr=subprocess.STDOUT, env=env, start_new_session=True)
    url = f'http://127.0.0.1:{port}/curriculum/query'
    def post(body):
        request = Request(url, data=json.dumps(body).encode(), headers={'Content-Type': 'application/json'})
        with urlopen(request, timeout=5) as response:
            return json.load(response)
    try:
        result = await_gateway(post, process, log, log_path)
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
        log.close()


def test_route_distinguishes_reader_error_from_invalid_json(generated_graph, monkeypatch, capsys):
    graph = service.load(generated_graph)

    def invalid_path(_graph, _path):
        raise ValueError('cycle de sous-séries : exemple')

    monkeypatch.setattr(service.reader, 'path_for', invalid_path)
    route = ''.join(service.seed_notebook(generated_graph)['cells'][1]['source'])
    request = {'body': json.dumps({'action': 'path', 'path': 'Demo/Part/A.ipynb'})}
    exec(route, {'json': json, 'service': service, 'graph': graph, 'REQUEST': request})
    result = json.loads(capsys.readouterr().out)
    assert result == {'status': 'invalid', 'error': 'cycle de sous-séries : exemple'}

    exec(route, {'json': json, 'service': service, 'graph': graph, 'REQUEST': {'body': '{'}})
    result = json.loads(capsys.readouterr().out)
    assert result == {'status': 'invalid', 'error': 'JSON invalide'}


def test_unexpected_type_error_is_not_reported_as_invalid_json(generated_graph, monkeypatch, capsys):
    graph = service.load(generated_graph)

    def broken_path(_graph, _path):
        raise TypeError('défaut inattendu')

    monkeypatch.setattr(service.reader, 'path_for', broken_path)
    route = ''.join(service.seed_notebook(generated_graph)['cells'][1]['source'])
    request = {'body': json.dumps({'action': 'path', 'path': 'Demo/Part/A.ipynb'})}
    with pytest.raises(TypeError, match='défaut inattendu'):
        exec(route, {'json': json, 'service': service, 'graph': graph, 'REQUEST': request})
    assert capsys.readouterr().out == ''
