"""Tests causaux du poster de dossiers (#18412).

Un controle positif par refus (ligne 1 parasite, REPLACE_WITH restant, marqueur
de fermeture absent, erreur de forme du parse_dossier, tete perimee,
double-stamp d'une autre lane, gate illisible, PAYLOAD-TRAP) plus le chemin
nominal simule pour les deux familles -- gh et les gates sont entierement
monkeypatches, aucun reseau.
"""

import importlib.util
import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
SCRIPTS_DIR = HERE.parent
spec = importlib.util.spec_from_file_location(
    "post_dossier", SCRIPTS_DIR / "coordination" / "post_dossier.py"
)
mod = importlib.util.module_from_spec(spec)
sys.modules["post_dossier"] = mod
spec.loader.exec_module(mod)

LANE = "myia-po-2024:CoursIA"
OTHER_LANE = "myia-po-2026:CoursIA"
HEAD = "0123456789abcdef0123456789abcdef01234567"


def _adjoint_body(**overrides: str) -> str:
    fields = {name: "1" for name in sorted(mod.adjoint_gate.REQUIRED_FIELDS)}
    # Un READY doit etre coherent AVANT le POST (#19312) : le poster rejoue
    # desormais les controles auto-portants du gate. Le fixture decrit donc ce
    # que le gate accepterait, sinon les chemins nominaux seraient refuses par
    # ce controle et non par le sujet du test.
    fields.update(
        {
            "lane": LANE,
            "pr": "101",
            "head": HEAD,
            "verdict": "READY",
            "checks": "latest-wins-green",
            # REQUIRED_FIELDS pose "1" partout : ces trois-la ne sont pas des
            # entiers et le gate les refuse a cette valeur. Le fixture
            # d'origine les portait tels quels -- c'est exactement le dossier
            # incoherent que #19312 fait refuser AVANT le POST.
            "complete": "true",
            "body": "read",
            "b0": "clear",
            "scope": "pass",
            "domain": "pass",
            "organ": mod.adjoint_gate.ORGAN_NAME,
            "organ-command": f"{mod.adjoint_gate.ORGAN_NAME} --derive-verdict 101",
            "organ-rc": "0",
        }
    )
    fields.update(overrides)
    return (
        mod.adjoint_gate.START
        + "\n"
        + "\n".join(f"{key}: {value}" for key, value in fields.items())
        + "\n"
        + mod.adjoint_gate.END
        + "\n"
    )


def _closure_body() -> str:
    return (
        mod.closure_gate.START
        + "\n"
        + "\n".join(
            [
                "schema: 1",
                f"lane: {LANE}",
                "issue: 55",
                "verdict: CLOSE",
                "acceptance:",
                "- critere 1 couvert par la PR merger",
                "residue: none",
                "open-prs: 0",
                "comments-reviewed: 3",
            ]
        )
        + "\n"
        + mod.closure_gate.END
        + "\n"
    )


class GhRouter:
    """gh_json simule : route pr view / api comments et enregistre les appels."""

    def __init__(self, head: str = HEAD, published_body: str | None = None):
        self.head = head
        self.published_body = published_body
        self.calls: list[list[str]] = []

    def __call__(self, args: list[str]):
        self.calls.append(list(args))
        if args[0] == "pr":
            return {"headRefOid": self.head}
        if args[0] == "api":
            assert args[1].endswith("/comments"), f"unexpected endpoint: {args[1]}"
            assert "--input" in args, "POST must go through --input, never -f body=@"
            payload_path = Path(args[args.index("--input") + 1])
            body = json.loads(payload_path.read_text(encoding="ascii"))["body"]
            return {
                "id": 999,
                "body": self.published_body if self.published_body is not None else body,
            }
        raise AssertionError(f"unexpected gh call: {args}")


class GateStub:
    """run_gate simule : rc et lane du dossier existant canned."""

    def __init__(self, rc: int, lane: str | None = None):
        self.rc = rc
        self.lane = lane
        self.seen: list[tuple[str, int]] = []

    def __call__(self, family, repo, target):
        self.seen.append((family.key, target))
        payload = {"verdict": "STUB"}
        if self.lane is not None:
            if family.key == "pr":
                payload["dossier"] = {"lane": self.lane}
            else:
                payload["lane"] = self.lane
        return self.rc, json.dumps(payload)


def _write(tmp_path: Path, body: str) -> Path:
    target = tmp_path / "dossier.md"
    target.write_text(body, encoding="utf-8")
    return target


def test_parasite_line1_refused_before_any_gh_call(tmp_path, monkeypatch):
    body = "GH-IDENTITY (WARN, poursuite sous compte actif): no oauth token\n" + _adjoint_body()
    monkeypatch.setattr(mod, "gh_json", lambda args: (_ for _ in ()).throw(AssertionError("gh must not be called")))
    rc = mod.main(["--pr", "101", "--file", str(_write(tmp_path, body)), "--lane", LANE])
    assert rc == mod.EXIT_REFUSED


def test_replace_with_remaining_refused(tmp_path, monkeypatch):
    body = _adjoint_body(verdict="REPLACE_WITH_READY_OR_BLOCKED")
    monkeypatch.setattr(mod, "gh_json", lambda args: (_ for _ in ()).throw(AssertionError("gh must not be called")))
    rc = mod.main(["--pr", "101", "--file", str(_write(tmp_path, body)), "--lane", LANE])
    assert rc == mod.EXIT_REFUSED


def test_missing_closing_marker_refused(tmp_path, monkeypatch):
    body = _adjoint_body().replace(mod.adjoint_gate.END + "\n", "")
    monkeypatch.setattr(mod, "gh_json", lambda args: (_ for _ in ()).throw(AssertionError("gh must not be called")))
    rc = mod.main(["--pr", "101", "--file", str(_write(tmp_path, body)), "--lane", LANE])
    assert rc == mod.EXIT_REFUSED


def test_parse_errors_refused(tmp_path, monkeypatch):
    body = _adjoint_body()
    body = body.replace("checks: latest-wins-green\n", "")
    monkeypatch.setattr(mod, "gh_json", lambda args: (_ for _ in ()).throw(AssertionError("gh must not be called")))
    rc = mod.main(["--pr", "101", "--file", str(_write(tmp_path, body)), "--lane", LANE])
    assert rc == mod.EXIT_REFUSED


def test_incoherent_domain_refused_before_any_gh_call(tmp_path, monkeypatch, capsys):
    """#19312 -- un READY avec ``domain: ci`` est refuse par le POSTER.

    Le gate le refusait deja, mais seulement APRES le POST : il demande
    l'instantane de la PR, donc il ne tourne qu'une fois le dossier publie. Sur
    #19207, deux dossiers sont partis ainsi et ont du etre supprimes a la main.
    Ce controle positif exige qu'aucun appel gh ne parte.
    """
    router = GhRouter()
    monkeypatch.setattr(mod, "gh_json", router)
    monkeypatch.setattr(mod, "run_gate", GateStub(rc=1))
    body = _adjoint_body(domain="ci")
    rc = mod.main(["--pr", "101", "--file", str(_write(tmp_path, body)), "--lane", LANE])
    assert rc == mod.EXIT_REFUSED
    assert router.calls == [], "le refus doit preceder tout appel gh"
    assert "domain must be 'pass' or 'not-applicable'" in capsys.readouterr().err


def test_incoherent_organ_command_refused_before_any_gh_call(tmp_path, monkeypatch, capsys):
    """Le controle auto-portant est parametre par la cible : une commande
    d'organe qui nomme une AUTRE PR est refusee, et toujours sans appel gh."""
    router = GhRouter()
    monkeypatch.setattr(mod, "gh_json", router)
    monkeypatch.setattr(mod, "run_gate", GateStub(rc=1))
    body = _adjoint_body(**{
        "organ-command": f"{mod.adjoint_gate.ORGAN_NAME} --derive-verdict 999",
    })
    rc = mod.main(["--pr", "101", "--file", str(_write(tmp_path, body)), "--lane", LANE])
    assert rc == mod.EXIT_REFUSED
    assert router.calls == []
    assert "--derive-verdict 101" in capsys.readouterr().err


def test_stale_head_refused(tmp_path, monkeypatch):
    router = GhRouter(head="f" * 40)
    monkeypatch.setattr(mod, "gh_json", router)
    monkeypatch.setattr(mod, "run_gate", GateStub(rc=1))
    monkeypatch.setattr(mod, "rerun_gate", lambda family, repo, target: 0)
    rc = mod.main(["--pr", "101", "--file", str(_write(tmp_path, _adjoint_body())), "--lane", LANE])
    assert rc == mod.EXIT_REFUSED
    # Rien n'a ete poste : seul l'appel pr view a eu lieu.
    assert all(call[0] == "pr" for call in router.calls)


def test_double_stamp_other_lane_refused(tmp_path, monkeypatch):
    router = GhRouter()
    monkeypatch.setattr(mod, "gh_json", router)
    monkeypatch.setattr(mod, "run_gate", GateStub(rc=0, lane=OTHER_LANE))
    rc = mod.main(["--pr", "101", "--file", str(_write(tmp_path, _adjoint_body())), "--lane", LANE])
    assert rc == mod.EXIT_REFUSED
    assert not any(call[0] == "api" for call in router.calls)


def test_double_stamp_rc3_with_supersedes_posts_through(tmp_path, monkeypatch, capsys):
    """#19420 -- gate rc 3 (BLOCKED intact), lane tierce, refutation explicite :
    le dossier porte ``supersedes`` et ``supersedes-why`` non vide, donc le
    poster accepte le re-stamp et le gate rejoue."""
    router = GhRouter()
    monkeypatch.setattr(mod, "gh_json", router)
    monkeypatch.setattr(mod, "run_gate", GateStub(rc=3, lane=OTHER_LANE))
    monkeypatch.setattr(mod, "rerun_gate", lambda family, repo, target: 0)
    body = _adjoint_body(
        verdict="BLOCKED",  # le noueau dossier peut etre READY ou BLOCKED ; on
        # garde BLOCKED pour exercer le chemin rc 3 sans contradiction muette.
        supersedes="5",
        **{"supersedes-why": "checks devenus verts a la meme tete, dossier de l'adjoint a l'arret (#19420)"},
    )
    rc = mod.main(["--pr", "101", "--file", str(_write(tmp_path, body)), "--lane", LANE])
    assert rc == 0  # gate rejoue rend 0 (le gate decide la refutation)
    assert any(call[0] == "api" for call in router.calls)
    # Pas de message d'anti-double-stamp dans la sortie
    assert "anti-double-stamp" not in capsys.readouterr().err


def test_double_stamp_rc3_without_supersedes_refused(tmp_path, monkeypatch, capsys):
    """#19420 -- gate rc 3, lane tierce, dossier SANS refute explicite :
    le poster refuse comme avant (anti-double-stamp)."""
    router = GhRouter()
    monkeypatch.setattr(mod, "gh_json", router)
    monkeypatch.setattr(mod, "run_gate", GateStub(rc=3, lane=OTHER_LANE))
    body = _adjoint_body(verdict="BLOCKED")
    rc = mod.main(["--pr", "101", "--file", str(_write(tmp_path, body)), "--lane", LANE])
    assert rc == mod.EXIT_REFUSED
    assert not any(call[0] == "api" for call in router.calls)
    err = capsys.readouterr().err
    assert "anti-double-stamp" in err
    assert "supersedes" in err  # le message d'erreur pointe le champ manquant


def test_double_stamp_rc3_with_empty_supersedes_why_refused(tmp_path, monkeypatch, capsys):
    """#19420 -- supersedes renseigne mais supersedes-why vide : refus (intention
    muette, le gate mute contradiction #18934 n'a rien a juger)."""
    router = GhRouter()
    monkeypatch.setattr(mod, "gh_json", router)
    monkeypatch.setattr(mod, "run_gate", GateStub(rc=3, lane=OTHER_LANE))
    body = _adjoint_body(
        verdict="BLOCKED",
        supersedes="5",
        **{"supersedes-why": ""},
    )
    rc = mod.main(["--pr", "101", "--file", str(_write(tmp_path, body)), "--lane", LANE])
    assert rc == mod.EXIT_REFUSED
    assert "anti-double-stamp" in capsys.readouterr().err


def test_double_stamp_rc0_with_supersedes_refused(tmp_path, monkeypatch, capsys):
    """#19420 -- rc 0 (READY intact) reste refuse meme avec supersedes : un
    second tampon READY n'ouvre pas une guerre de dossiers. La garde anti-
    double-stamp reste ferme, distincte du cas rc 3."""
    router = GhRouter()
    monkeypatch.setattr(mod, "gh_json", router)
    monkeypatch.setattr(mod, "run_gate", GateStub(rc=0, lane=OTHER_LANE))
    body = _adjoint_body(
        supersedes="5",
        **{"supersedes-why": "checks devenus verts"},
    )
    rc = mod.main(["--pr", "101", "--file", str(_write(tmp_path, body)), "--lane", LANE])
    assert rc == mod.EXIT_REFUSED
    assert not any(call[0] == "api" for call in router.calls)
    err = capsys.readouterr().err
    assert "anti-double-stamp" in err
    # Le message est l'ancien (rc 0) -- pas le nouveau (rc 3).
    assert "a re-stamp is licite only for its own lane" in err


def test_gate_unknown_refused(tmp_path, monkeypatch):
    monkeypatch.setattr(mod, "gh_json", GhRouter())
    monkeypatch.setattr(mod, "run_gate", GateStub(rc=2))
    rc = mod.main(["--pr", "101", "--file", str(_write(tmp_path, _adjoint_body())), "--lane", LANE])
    assert rc == mod.EXIT_REFUSED


def test_same_lane_restamp_posts_and_exits_with_gate_rc(tmp_path, monkeypatch):
    router = GhRouter()
    monkeypatch.setattr(mod, "gh_json", router)
    monkeypatch.setattr(mod, "run_gate", GateStub(rc=3, lane=LANE))
    monkeypatch.setattr(mod, "rerun_gate", lambda family, repo, target: 3)
    rc = mod.main(["--pr", "101", "--file", str(_write(tmp_path, _adjoint_body())), "--lane", LANE])
    assert rc == 3  # poste, puis sortie au rc du gate rejoue
    assert any(call[0] == "api" for call in router.calls)


def test_nominal_pr_path_posts_through_input(tmp_path, monkeypatch):
    router = GhRouter()
    monkeypatch.setattr(mod, "gh_json", router)
    monkeypatch.setattr(mod, "run_gate", GateStub(rc=1))
    monkeypatch.setattr(mod, "rerun_gate", lambda family, repo, target: 0)
    rc = mod.main(["--pr", "101", "--file", str(_write(tmp_path, _adjoint_body())), "--lane", LANE])
    assert rc == 0
    post = next(call for call in router.calls if call[0] == "api")
    assert post[1] == "repos/jsboige/CoursIA/issues/101/comments"


def test_nominal_issue_path_skips_head_check(tmp_path, monkeypatch):
    router = GhRouter()
    seen_gates: list[tuple[str, int]] = []

    def fake_run_gate(family, repo, target):
        seen_gates.append((family.key, target))
        return 1, "{}"

    monkeypatch.setattr(mod, "gh_json", router)
    monkeypatch.setattr(mod, "run_gate", fake_run_gate)
    monkeypatch.setattr(mod, "rerun_gate", lambda family, repo, target: 0)
    rc = mod.main(["--issue", "55", "--file", str(_write(tmp_path, _closure_body())), "--lane", LANE])
    assert rc == 0
    # Aucun appel pr view : le champ head n'existe que pour la famille PR.
    assert all(call[0] == "api" for call in router.calls)
    assert seen_gates == [("issue", 55)]


def test_payload_trap_detected_post_post(tmp_path, monkeypatch, capsys):
    clean = _adjoint_body()
    router = GhRouter(published_body=json.dumps({"body": clean}))
    monkeypatch.setattr(mod, "gh_json", router)
    monkeypatch.setattr(mod, "run_gate", GateStub(rc=1))
    rc = mod.main(["--pr", "101", "--file", str(_write(tmp_path, clean)), "--lane", LANE])
    assert rc == mod.EXIT_REFUSED
    stderr = capsys.readouterr().err
    assert "PAYLOAD-TRAP" in stderr
    assert "999" in stderr  # l'id du commentaire piege, pour le PATCH de remediation
