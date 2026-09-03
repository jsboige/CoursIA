"""
test_idle_monitor.py — coverage de v4/idle_monitor.py (suspension du sidecar
tts-fishaudio-idle-monitor pendant une fenetre de chaine LLM->TTS).

Epic #1028 residu 2. Avant ce module, la seule parade etait un geste manuel
(``docker stop tts-fishaudio-idle-monitor``) a ne pas oublier -- sur le livre
complet les phases p3+p4 (~36 min sans appel TTS) laissaient le monitor tuer
``tts-fishaudio`` avant p5 (385/385 echecs, #14059).

Hermetique CPU-only : ``_docker`` est monkeypatche, aucun appel docker reel.
Pattern d'import de test_canonical.py (sys.path parent + ``v4.<module>``).
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

_v4_parent = Path(__file__).resolve().parent.parent.parent  # 04-Applications/
if str(_v4_parent) not in sys.path:
    sys.path.insert(0, str(_v4_parent))

import v4.idle_monitor as im  # noqa: E402


# ---------------------------------------------------------------------------
# chain_needs_suspension — la matrice des formes de chaine
# ---------------------------------------------------------------------------
def test_chain_needs_suspension_matrix():
    """p5 seul : non. LLM avant p5 : oui. p5 avant les LLM : non. Sans p5 : non."""
    assert im.chain_needs_suspension(["p5"]) is False
    assert im.chain_needs_suspension(["p3", "p4", "p5"]) is True
    assert im.chain_needs_suspension(["p5", "p3"]) is False
    assert im.chain_needs_suspension(["p3", "p4"]) is False
    assert im.chain_needs_suspension(["p6", "p7"]) is False
    # La chaine complete du livre (cas nominal du run live #14059).
    assert im.chain_needs_suspension(
        ["p0", "p1", "p1_5", "p2", "p3", "p4", "p5", "p6", "p7"]
    ) is True


# ---------------------------------------------------------------------------
# suspended_idle_monitor — les 4 situations d'execution
# ---------------------------------------------------------------------------
class _FakeDocker:
    """Rejoue une session docker : inspect -> stop -> start."""

    def __init__(self, inspect_rc=0, inspect_out="true\n", stop_rc=0, start_rc=0):
        self.inspect_rc, self.inspect_out = inspect_rc, inspect_out
        self.stop_rc, self.start_rc = stop_rc, start_rc
        self.calls: list[list[str]] = []

    def __call__(self, args):
        self.calls.append(list(args))
        result = subprocess.CompletedProcess(
            args=["docker", *args], returncode=0, stdout="", stderr=""
        )
        if args[:2] == ["inspect", "-f"]:
            result = subprocess.CompletedProcess(
                args=["docker", *args],
                returncode=self.inspect_rc,
                stdout=self.inspect_out,
                stderr="",
            )
        elif args[0] == "stop":
            result = subprocess.CompletedProcess(
                args=["docker", *args], returncode=self.stop_rc, stdout="", stderr=""
            )
        elif args[0] == "start":
            result = subprocess.CompletedProcess(
                args=["docker", *args], returncode=self.start_rc, stdout="", stderr=""
            )
        return result

    def commands(self):
        return [" ".join(c[:2]) for c in self.calls]


def test_suspends_and_restarts_when_monitor_running(monkeypatch, capsys):
    """Monitor actif + chaine LLM->TTS : stop au debut, start a la fin."""
    fake = _FakeDocker()
    monkeypatch.setattr(im, "_docker", fake)
    with im.suspended_idle_monitor(["p3", "p4", "p5"]) as suspended:
        assert suspended is True
        # Pendant la fenetre : le monitor est deja stoppe, rien d'autre.
        assert fake.commands() == ["inspect -f", "stop tts-fishaudio-idle-monitor"]
    assert "suspendu pour la fenetre" in capsys.readouterr().out
    assert fake.commands()[-1] == "start tts-fishaudio-idle-monitor"


def test_restart_guaranteed_on_chain_failure(monkeypatch):
    """Une exception dans la fenetre redemarre quand meme le monitor."""
    fake = _FakeDocker()
    monkeypatch.setattr(im, "_docker", fake)
    try:
        with im.suspended_idle_monitor(["p3", "p5"]):
            raise RuntimeError("phase p5 FAILED")
    except RuntimeError:
        pass
    assert fake.commands() == [
        "inspect -f",
        "stop tts-fishaudio-idle-monitor",
        "start tts-fishaudio-idle-monitor",
    ]


def test_noop_when_monitor_absent(monkeypatch, capsys):
    """Monitor arrete/inexistant : chaine sans suspension, aucun start sauvage."""
    fake = _FakeDocker(inspect_out="false\n")
    monkeypatch.setattr(im, "_docker", fake)
    with im.suspended_idle_monitor(["p3", "p5"]) as suspended:
        assert suspended is False
    assert fake.commands() == ["inspect -f"]
    assert "sans suspension" in capsys.readouterr().out


def test_stop_failure_does_not_block_the_chain(monkeypatch, capsys):
    """Stop en echec : la chaine continue (WARN), aucun start (rien n'a ete arrete)."""
    fake = _FakeDocker(stop_rc=1)
    monkeypatch.setattr(im, "_docker", fake)
    with im.suspended_idle_monitor(["p3", "p5"]) as suspended:
        assert suspended is False
    assert fake.commands() == ["inspect -f", "stop tts-fishaudio-idle-monitor"]
    assert "WARN" in capsys.readouterr().out


def test_docker_absent_tolerated(monkeypatch):
    """Docker absent de la machine (OSError) : la chaine continue sans suspension."""

    def _no_docker(args):
        raise OSError("docker: command not found")

    monkeypatch.setattr(im, "_docker", _no_docker)
    # monitor_is_running doit avaler l'OSError...
    assert im.monitor_is_running() is False
    # ...et la fenetre reste franchissable.
    with im.suspended_idle_monitor(["p3", "p5"]) as suspended:
        assert suspended is False
