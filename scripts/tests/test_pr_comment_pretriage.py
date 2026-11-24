"""Tests du pre-tri des fils de commentaires (organe de lecture externe).

Le reseau n'est jamais appele ici : seules les fonctions pures sont testees.
"""

import importlib.util
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ORGAN_PATH = HERE.parent / "coordination" / "pr_comment_pretriage.py"
spec = importlib.util.spec_from_file_location("pr_comment_pretriage", ORGAN_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["pr_comment_pretriage"] = mod
spec.loader.exec_module(mod)


def test_strip_fences_retire_un_enveloppe_de_code():
    assert mod.strip_fences("```json\n{\"a\": 1}\n```") == '{"a": 1}'
    assert mod.strip_fences('{"a": 1}') == '{"a": 1}'


def test_parse_lenient_accepte_un_json_tronque():
    texte = 'Voici le resultat : {"commentaires": [{"n": 1, "role": "reserve"}'
    parsed = mod.parse_lenient(texte)
    assert parsed["commentaires"][0]["n"] == 1
    assert parsed["commentaires"][0]["role"] == "reserve"


def test_parse_lenient_echoue_sans_json_recoverable():
    try:
        mod.parse_lenient("pas du json du tout")
    except ValueError:
        return
    raise AssertionError("ValueError attendue")


def test_is_bot_reconnait_les_logins_de_bot():
    assert mod.is_bot("github-actions[bot]")
    assert mod.is_bot("clusterManager-Myia[bot]")
    assert mod.is_bot("github-actions")
    assert not mod.is_bot("jsboige")
    assert not mod.is_bot("myia-ai-01")


def test_le_prompt_ne_contient_pas_les_sauts_de_ligne_du_commentaire():
    """Le mini copie la decoupe : les commentaires sont donnes tels quels,
    sans aplatissement (regle de craft mesuree le 21/10)."""
    prompt = mod.TEMPLATE.format(
        num=1, titre="t", body="b", commentaires="--- commentaire 1 ---\nligne 1\nligne 2")
    assert "ligne 1\nligne 2" in prompt


def test_pretriage_chemin_non_dry_compte_humains_bots_et_reviews(monkeypatch):
    """Chemin non-dry (dry_run=False) : le resume rend humains/bots/reviews_nonbot
    sans lever de NameError. Avant le fix, la ligne `bots` lisait `humains`
    (nom indefini) : le chemin dry-run rendait, le chemin reel plantait
    (review #21885, point 1)."""
    pr_json = {
        "title": "t", "body": "b", "state": "OPEN", "headRefOid": "abc123",
        "comments": [
            {"author": {"login": "github-actions[bot]"}, "createdAt": "2026-10-20T00:00:00Z", "body": "CI"},
            {"author": {"login": "dependabot"}, "createdAt": "2026-10-20T01:00:00Z", "body": "bump"},
            {"author": {"login": "myia-ai-01"}, "createdAt": "2026-10-20T02:00:00Z", "body": "reserve"},
            {"author": {"login": "jsboige"}, "createdAt": "2026-10-20T03:00:00Z", "body": "info"},
        ],
        "reviews": [
            {"author": {"login": "github-actions[bot]"}, "state": "COMMENTED"},
            {"author": {"login": "clusterManager-Myia"}, "state": "COMMENTED"},
        ],
    }
    monkeypatch.setattr(mod, "gh", lambda args: json.dumps(pr_json))
    monkeypatch.setattr(
        mod, "call_model",
        lambda m, s, u, out, max_tokens=3000:
        {"http": 200, "latence": 0.1, "tokens_in": 10, "tokens_out": 5},
    )
    r = mod.pretriage(21885, "frognano-4b", dry_run=False)
    assert "dry_run" not in r          # bien le chemin non-dry, pas le dry-run
    assert r["commentaires"] == 4
    assert r["humains"] == 2
    assert r["bots"] == 2
    assert r["reviews_nonbot"] == 1
    assert r["reviews_nonbot_detail"] == [("clusterManager-Myia", "COMMENTED")]


def test_main_retourne_1_si_la_sortie_est_tronquee(monkeypatch, capsys):
    """main() non-dry rend 1 quand le modele restitue moins de commentaires qu'il
    n'y a de commentaires humains : branche de troncature (review #21885, point 2)."""
    pr_json = {
        "title": "t", "body": "b", "state": "OPEN", "headRefOid": "abc123",
        "comments": [
            {"author": {"login": "a"}, "createdAt": "2026-10-20T00:00:00Z", "body": "x"},
            {"author": {"login": "b"}, "createdAt": "2026-10-20T01:00:00Z", "body": "y"},
            {"author": {"login": "c"}, "createdAt": "2026-10-20T02:00:00Z", "body": "z"},
        ],
        "reviews": [],
    }

    def fake_call_model(m, s, u, out, max_tokens=3000):
        # le modele ne restitue que 2 des 3 commentaires humains -> tronque
        Path(out).write_text('{"commentaires": [{"n": 1}, {"n": 2}]}', encoding="utf-8")
        return {"http": 200, "latence": 0.1, "tokens_in": 1, "tokens_out": 1}

    monkeypatch.setattr(mod, "gh", lambda args: json.dumps(pr_json))
    monkeypatch.setattr(mod, "call_model", fake_call_model)
    monkeypatch.setattr(sys, "argv", ["pr_comment_pretriage.py", "21885"])
    rc = mod.main()
    assert rc == 1
    out = capsys.readouterr().out
    assert "AVERTISSEMENT" in out and "2/3" in out
