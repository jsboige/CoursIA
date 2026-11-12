#!/usr/bin/env python3
"""Adaptateur HTTP local pour le lecteur du graphe du cursus."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile

TOOLS = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(TOOLS))
import query_curriculum as reader
from generate_curriculum_rdf import validate_graph


def load(path: Path):
    graph = reader.load_graph([path])
    conforms, report = validate_graph(graph)
    if not conforms:
        raise ValueError('Graphe non conforme SHACL : ' + report)
    return graph


def handle(graph, request: object) -> dict:
    if not isinstance(request, dict):
        return {'status': 'invalid', 'error': 'Objet JSON attendu'}
    action = request.get('action')
    if action not in ('series', 'path', 'prerequisites'):
        return {'status': 'invalid', 'error': 'Action attendue : series, path ou prerequisites'}
    if action == 'series':
        return {'status': 'ok', 'results': reader.list_series(graph)}
    path = request.get('path')
    if not isinstance(path, str) or not path.strip():
        return {'status': 'invalid', 'error': 'Chemin du carnet requis'}
    try:
        result = (reader.path_for(graph, path) if action == 'path'
                  else reader.prerequisites_for(graph, path))
    except KeyError:
        return {'status': 'not_found', 'error': 'Carnet inconnu'}
    except ValueError as exc:
        return {'status': 'invalid', 'error': str(exc)}
    return {'status': 'ok', 'results': result}


def seed_notebook(graph_path: Path) -> dict:
    """Construit le seed Kernel Gateway dans un répertoire temporaire."""
    startup = (
        'import sys, json\n'
        f'sys.path.insert(0, {str(Path(__file__).resolve().parent)!r})\n'
        'import service\n'
        f'graph = service.load(service.Path({str(graph_path.resolve())!r}))\n'
    )
    route = '''# POST /curriculum/query
try:
    request = json.loads(REQUEST) if isinstance(REQUEST, str) else REQUEST
    body = request.get("body", {}) if isinstance(request, dict) else request
    if isinstance(body, str):
        body = json.loads(body)
except json.JSONDecodeError:
    print(json.dumps({"status": "invalid", "error": "JSON invalide"}))
else:
    print(json.dumps(service.handle(graph, body), ensure_ascii=False))
'''
    def cell(source):
        return {'cell_type': 'code', 'metadata': {}, 'source': source.splitlines(True),
                'execution_count': None, 'outputs': []}
    return {'cells': [cell(startup), cell(route)], 'metadata': {'kernelspec': {
        'display_name': 'Python 3', 'language': 'python', 'name': 'python3'}},
        'nbformat': 4, 'nbformat_minor': 5}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--graph', type=Path, required=True, help='export Turtle validé au démarrage')
    parser.add_argument('--port', type=int, default=8899)
    args = parser.parse_args()
    try:
        load(args.graph)
    except (OSError, ValueError) as exc:
        print(f'Graphe invalide : {exc}', file=sys.stderr)
        return 2
    with tempfile.TemporaryDirectory(prefix='coursia-curriculum-gateway-') as directory:
        seed = Path(directory) / 'service.ipynb'
        seed.write_text(json.dumps(seed_notebook(args.graph)), encoding='utf-8')
        return subprocess.call([sys.executable, str(TOOLS / 'kernel_gateway_service.py'),
                                str(seed), '--port', str(args.port)])


if __name__ == '__main__':
    raise SystemExit(main())
