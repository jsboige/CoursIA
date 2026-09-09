from __future__ import annotations

import json
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPT_DIR))

from detect_smartcontract_drift import (  # noqa: E402
    compare_snapshots,
    main,
    scan_notebook,
)


def _nb(cells):
    return {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _md(source):
    return {"cell_type": "markdown", "source": source, "metadata": {}}


def _code(source, output=""):
    outputs = []
    if output:
        outputs.append({"output_type": "stream", "name": "stdout", "text": output})
    return {
        "cell_type": "code",
        "source": source,
        "metadata": {},
        "execution_count": 1 if outputs else None,
        "outputs": outputs,
    }


def _ids(findings):
    return {finding["rule_id"] for finding in findings}


def test_detects_unpacked_user_operation():
    notebook = _nb([
        _md("# Account abstraction ERC-4337"),
        _code("struct UserOperation {\n address sender;\n uint256 callGasLimit;\n}"),
    ])
    findings = scan_notebook(Path("SC-10.ipynb"), notebook)
    assert "ERC4337_LEGACY_USER_OPERATION" in _ids(findings)


def test_historical_user_operation_is_exempt():
    notebook = _nb([
        _md("## Historique : structure legacy v0.6, ne pas utiliser aujourd'hui"),
        _code("struct UserOperation { address sender; }"),
    ])
    assert scan_notebook(Path("history.ipynb"), notebook) == []


def test_detects_retired_networks_but_not_historical_mentions():
    current = _nb([
        _md("Déployez maintenant sur Goerli puis Polygon Mumbai."),
    ])
    historical = _nb([
        _md("Historique : Goerli et Mumbai sont des réseaux retirés."),
    ])
    assert _ids(scan_notebook(Path("current.ipynb"), current)) == {
        "RETIRED_GOERLI_NETWORK",
        "RETIRED_POLYGON_MUMBAI_NETWORK",
    }
    assert scan_notebook(Path("history.ipynb"), historical) == []


def test_printed_foundry_suite_is_detected():
    notebook = _nb([
        _md("# Foundry forge test"),
        _code("print('forge test --match-contract CounterTest')", "forge test ..."),
    ])
    assert "FOUNDRY_SUITE_PRINTED_ONLY" in _ids(
        scan_notebook(Path("SC-12.ipynb"), notebook)
    )


def test_real_foundry_subprocess_suppresses_printed_only():
    notebook = _nb([
        _md("# Foundry forge test"),
        _code("print('forge test --fuzz-runs 512')", "forge test --fuzz-runs 512"),
        _code(
            "import subprocess\nforge = '/bin/forge'\n"
            "result = subprocess.run([forge, 'test'])\nprint(result.stdout)",
            "Suite result: 512 tests passed",
        ),
    ])
    assert "FOUNDRY_SUITE_PRINTED_ONLY" not in _ids(
        scan_notebook(Path("SC-13.ipynb"), notebook)
    )


def test_invoked_foundry_helper_suppresses_printed_only():
    notebook = _nb([
        _md("# Foundry forge build"),
        _code(
            "import subprocess\ndef compile_contract(forge):\n"
            "    return subprocess.run([forge, 'build'])"
        ),
        _code("print('forge build')\ncompile_contract(forge)", "Compiler run successful"),
    ])
    assert "FOUNDRY_SUITE_PRINTED_ONLY" not in _ids(
        scan_notebook(Path("compiled.ipynb"), notebook)
    )


def test_exercise_and_solidity_mock_cheatcodes_are_not_findings():
    notebook = _nb([
        _md("# Exercice"),
        _code("# TODO etudiant\nprint('forge test')\npass"),
        _code("# TODO: Ecrivez les tests\nprint('forge test -vvv')"),
        _code(
            "contract MockExternal {}\n"
            "vm.prank(alice);\nvm.mockCall(target, data, result);"
        ),
    ])
    assert scan_notebook(Path("exercise.ipynb"), notebook) == []


def test_delta_tolerates_inherited_debt_and_blocks_new_rule():
    inherited = {
        "findings": [{
            "rule_id": "RETIRED_GOERLI_NETWORK",
            "notebook": "SC.ipynb",
            "cell": 1,
            "evidence": "Goerli",
        }]
    }
    head = {"findings": inherited["findings"] + [{
        "rule_id": "FOUNDRY_SUITE_PRINTED_ONLY",
        "notebook": "SC.ipynb",
        "cell": 2,
        "evidence": "forge test",
    }]}
    assert compare_snapshots(inherited, inherited) == []
    assert [item["rule_id"] for item in compare_snapshots(inherited, head)] == [
        "FOUNDRY_SUITE_PRINTED_ONLY"
    ]


def test_cli_exit_codes(tmp_path):
    clean = tmp_path / "clean.ipynb"
    clean.write_text(json.dumps(_nb([_md("# Solidity local")])) , encoding="utf-8")
    assert main([str(clean), "--check", "--json"]) == 0

    dirty = tmp_path / "dirty.ipynb"
    dirty.write_text(json.dumps(_nb([_md("Deploy to Goerli")])) , encoding="utf-8")
    assert main([str(dirty), "--check", "--json"]) == 1

    broken = tmp_path / "broken.ipynb"
    broken.write_text("not json", encoding="utf-8")
    assert main([str(broken), "--json"]) == 2

    base = tmp_path / "base.json"
    head = tmp_path / "head.json"
    base.write_text(
        json.dumps({"findings": [], "errors": [{"notebook": "broken"}]}),
        encoding="utf-8",
    )
    head.write_text(json.dumps({"findings": [], "errors": []}), encoding="utf-8")
    assert main([
        "--compare-base", str(base), "--compare-head", str(head), "--json"
    ]) == 2
