from __future__ import annotations

import dataclasses
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

import pytest

# The controller is the Windows-confinement companion of the runner manager
# (#12704): idempotent re-registration of ephemeral runners. The apply paths
# below assume the manager module resolves beside the controller.
CI_DIR = Path(__file__).parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

SPEC = importlib.util.spec_from_file_location(
    "runner_controller", CI_DIR / "runner_controller.py"
)
ctl = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = ctl
SPEC.loader.exec_module(ctl)


class FakeRun:
    """Enregistre chaque invocation et sert des reponses calees sur argv."""

    def __init__(self, *, runners: list[dict] | None = None, token: str = "t" * 40,
                 schtasks_error: str | None = None) -> None:
        self.calls: list[tuple[tuple, dict | None]] = []
        self.runners = runners or []
        self.token = token
        self.schtasks_error = schtasks_error

    def __call__(self, argv, **kwargs):
        self.calls.append((tuple(argv), kwargs.get("env")))
        cmd = " ".join(str(a) for a in argv)
        if cmd.startswith("gh api repos/") and "actions/runners" in cmd \
                and "--method" not in cmd:
            lines = "".join(json.dumps(r) + "\n" for r in self.runners)
            return subprocess.CompletedProcess(argv, 0, stdout=lines, stderr="")
        if "--method" in cmd and "--jq" in cmd and ".token" in cmd:
            return subprocess.CompletedProcess(argv, 0, stdout=self.token + "\n", stderr="")
        if cmd.startswith("schtasks"):
            if self.schtasks_error:
                return subprocess.CompletedProcess(argv, 1, stdout="", stderr=self.schtasks_error)
            return subprocess.CompletedProcess(argv, 0, stdout="", stderr="")
        return subprocess.CompletedProcess(argv, 0, stdout="", stderr="")


@pytest.fixture()
def prof(tmp_path):
    root = tmp_path / "fast-guards"
    return ctl.Profile(
        name="test-fast-guards",
        hostname="test-host",
        repository="jsboige/CoursIA",
        runner_name="test-fast-guards",
        account=r".\coursia-runner",
        root=root,
        work=root / "_work",
        log_root=tmp_path / "logs",
        labels=("self-hosted", "coursia-ephemeral", "coursia-fast-guards"),
        version="2.336.0",
        archive_url="https://example.invalid/runner.zip",
        archive_sha256="a" * 64,
        sensitive_templates=(),
    )


def argv_of(fake: FakeRun, needle: str) -> list[tuple]:
    return [c for c in fake.calls if needle in " ".join(c[0])]


def test_status_plan_lists_actions_without_applying(prof):
    fake = FakeRun(runners=[])
    plan = ctl.plan_for(prof, fake)
    assert plan["planned_actions"] == ["fetch-registration-token", "register", "verify"]
    assert not argv_of(fake, "--method POST")  # lecture seule, aucun token negocie


def test_ensure_noop_when_runner_online(prof, monkeypatch):
    fake = FakeRun(runners=[{"name": "test-fast-guards", "status": "online", "busy": False}])
    seen: list[str] = []
    monkeypatch.setattr(ctl, "apply_register", lambda *a, **k: seen.append("register"))
    result = ctl.apply_ensure(prof, fake)
    assert result == {"action": "noop", "reason": "runner already online"}
    assert seen == []  # un runner online n'est jamais re-enregistre


def test_ensure_registers_when_absent(prof, monkeypatch):
    fake = FakeRun(runners=[])
    seen: list[str] = []
    monkeypatch.setenv(ctl.ACCOUNT_PASSWORD_ENV, "pw")
    monkeypatch.setattr(ctl, "apply_register", lambda *a, **k: seen.append("register"))
    monkeypatch.setattr(ctl, "apply_verify", lambda *a, **k: seen.append("verify"))
    result = ctl.apply_ensure(prof, fake)
    assert result == {"action": "registered"}
    assert seen == ["register", "verify"]
    posts = argv_of(fake, "registration-token")
    assert posts, "un token frais doit etre negocie a chaque re-enregistrement"


def test_ensure_requires_password_before_any_token(prof, monkeypatch):
    fake = FakeRun(runners=[])
    monkeypatch.delenv(ctl.ACCOUNT_PASSWORD_ENV, raising=False)
    with pytest.raises(ctl.Broken, match="COURSIA_RUNNER_ACCOUNT_PASSWORD"):
        ctl.apply_ensure(prof, fake)
    assert not argv_of(fake, "--method POST")  # fail-closed avant tout appel reseau


def test_ensure_token_never_in_argv_and_popped_after(prof, monkeypatch):
    fake = FakeRun(runners=[], token="S" * 48)
    monkeypatch.setenv(ctl.ACCOUNT_PASSWORD_ENV, "pw")
    monkeypatch.setattr(ctl, "apply_register", lambda *a, **k: None)
    monkeypatch.setattr(ctl, "apply_verify", lambda *a, **k: None)
    ctl.apply_ensure(prof, fake)
    assert os.environ.get(ctl.REGISTRATION_TOKEN_ENV) is None
    for argv, _ in fake.calls:
        assert "S" * 48 not in " ".join(str(a) for a in argv)


def test_deregister_noop_when_absent_everywhere(prof):
    fake = FakeRun(runners=[])
    result = ctl.apply_deregister(prof, fake)
    assert result["action"] == "noop"
    assert not argv_of(fake, "remove-token")


def test_deregister_pins_the_real_github_remove_token_route(prof):
    # La route GitHub est `remove-token`. L'ancien `removal-token` rendait 404
    # (chemin inexistant, mesure ai-01 msg-20260828T190411) : un retour du typo
    # doit rougir ici, pas dormir jusqu'a la session d'activation elevee.
    fake = FakeRun(runners=[{"name": "test-fast-guards", "status": "online", "busy": False}])
    result = ctl.apply_deregister(prof, fake)
    assert result == {"action": "deregistered"}
    posts = argv_of(fake, "actions/runners/remove-token")
    assert posts, "le token de deregistration doit venir de la route remove-token"
    argv = " ".join(str(a) for a in posts[0][0])
    assert f"repos/{prof.repository}/actions/runners/remove-token" in argv
    assert "actions/runners/removal-token" not in argv


def test_task_xml_deterministic_and_pinned(prof):
    first, second = ctl.task_xml(prof), ctl.task_xml(prof)
    assert first == second  # deux generations = meme etat (idempotence)
    assert "PT60S" in first
    assert "IgnoreNew" in first
    assert "PT10M" in first  # un tick ne peut pas vivre plus de 10 minutes


def test_task_action_reads_password_from_file_never_embeds_it(prof):
    action = ctl.task_action(prof)
    assert "runner_pwd.txt" in action  # lit le fichier machine local conventionnel
    assert "ensure --profile test-fast-guards --apply" in action
    assert "controller.log" in action


# Le document porte un namespace par defaut : un XPath sans prefixe ne matche aucun
# element (`find` rend None sur un document pourtant bien forme), il faut la forme
# `{uri}nom`. Sans cette constante, le test d'echappement passerait a cote en silence.
TASK_NS = "http://schemas.microsoft.com/windows/2004/02/mit/task"


def task_arguments(prof) -> str:
    root = ET.fromstring(ctl.task_xml(prof))
    return root.find(".//{" + TASK_NS + "}Arguments").text


def test_task_xml_is_well_formed(prof):
    """`schtasks /Create /XML` refuse un document malforme. Le corps de la tache
    porte le `&` de l'operateur d'appel PowerShell : non echappe, il rend l'XML
    invalide. Ce test manquait -- le defaut ne se revelait qu'en session elevee,
    donc une fenetre UAC utilisateur payait la decouverte (mesure #20174)."""
    ET.fromstring(ctl.task_xml(prof))


def test_task_xml_escaping_roundtrips_to_the_launcher_path(prof, tmp_path):
    """L'echappement doit rester reversible apres le deplacement du corps vers le
    VBS : le chemin du lanceur part desormais dans `Arguments`, et un `&` dans la
    racine des runners est licite sur Windows. Un echappement de trop casserait
    le chemin sans casser le XML -- l'autre moitie du meme defaut (#20174)."""
    dotted = dataclasses.replace(prof, root=tmp_path / "a&b" / "fast-guards")
    args = task_arguments(dotted)
    assert "a&b" in args
    assert "&amp;" not in args


def test_task_xml_runs_a_hidden_launcher_not_an_interpreter(prof):
    """Temoin negatif du defaut #24706 : la tache se repete toutes les 60 s sans
    condition « utilisateur absent ». Un `pwsh.exe` declare comme `<Command>`
    ouvre donc une console a chaque tick (60 par heure). L'action doit passer par
    `wscript.exe`, qui ne cree aucune fenetre."""
    root = ET.fromstring(ctl.task_xml(prof))
    command = root.find(".//{" + TASK_NS + "}Command").text
    assert command == "wscript.exe"
    args = task_arguments(prof)
    assert "pwsh.exe" not in args
    assert args.startswith("//B //Nologo ")  # //B : pas de boite de dialogue WSH
    assert args.endswith('"') and args.count('"') == 2  # uniquement autour du chemin


def test_task_launcher_hides_the_window_and_waits_for_the_real_command(prof):
    """Le lanceur porte le `0` (fenetre masquee), le MEME corps que l'ancienne
    action, et attend la fin du tick en propagant son code de sortie (review
    #24707 : `False` rendait la main aussitot -- succes muet sur echec du
    controleur, et ticks qui se chevauchent malgre IgnoreNew)."""
    text = ctl.task_launcher(prof)
    assert 'CreateObject("WScript.Shell")' in text
    assert ', 0, True)' in text  # 0 = masque, True = attendre la fin
    assert "WScript.Quit rc" in text
    assert "pwsh.exe -NoProfile -NonInteractive -WindowStyle Hidden" in text
    assert "ensure --profile test-fast-guards --apply" in text
    assert "runner_pwd.txt" in text
    assert "controller.log" in text


def test_task_launcher_is_a_well_formed_vbs_literal(prof):
    """Le corps PowerShell est enveloppe de guillemets : non doubles en VBScript,
    la chaine se termine au premier `"` interne et le lanceur casse en silence
    (WScript ne rend pas d'erreur a la tache)."""
    text = ctl.task_launcher(prof)
    run_line = next(line for line in text.splitlines() if "shell.Run(" in line)
    body = run_line.split("shell.Run(", 1)[1].rsplit(")", 1)[0]
    assert body.count('"') % 2 == 0  # litteral ferme
    assert '-Command ""' in body  # guillemets doubles a l'interieur du litteral


@pytest.mark.skipif(sys.platform != "win32", reason="cscript n'existe que sur Windows")
def test_task_launcher_propagates_the_child_exit_code(prof, tmp_path):
    """Review #24707 : un lanceur reellement lance doit rendre le code de sortie
    du script enfant -- l'echec d'un tick doit se VOIR dans LastTaskResult, pas
    se fondre dans un succes muet. Execute le generateur, pas une copie : seule
    l'artifact produit prouve que `Run(..., True)` + `WScript.Quit rc` portent
    le rc jusqu'a la sortie cscript."""
    launcher = tmp_path / ctl.TASK_LAUNCHER_NAME
    for child_rc in (3, 0):  # echec d'abord (l'exigence), succes en temoin
        launcher.write_text(
            ctl.task_launcher(
                prof,
                command=(
                    "pwsh.exe -NoProfile -NonInteractive -Command "
                    f'"exit {child_rc}"'
                ),
            ),
            encoding="ascii",
        )
        completed = subprocess.run(
            ["cscript", "//B", "//Nologo", str(launcher)],
            capture_output=True, text=True, encoding="utf-8",
            errors="replace", timeout=120,
        )
        assert completed.returncode == child_rc, (
            f"enfant exit {child_rc} -> cscript rend {completed.returncode} "
            f"(stdout={completed.stdout!r}, stderr={completed.stderr!r})"
        )


def test_task_launcher_path_is_derived_from_the_profile(prof, tmp_path):
    """Un chemin code en dur deplacerait le defaut sur une autre machine, et le
    controle de non-regression cesserait de couvrir l'installation reelle."""
    path = ctl.task_launcher_path(prof)
    assert path == prof.root.parent / "launchers" / ctl.TASK_LAUNCHER_NAME
    other = dataclasses.replace(prof, root=tmp_path / "elsewhere" / "fast-guards")
    assert ctl.task_launcher_path(other) != path
    assert prof.root.parent.as_posix() in path.as_posix()


def test_task_install_writes_the_launcher_the_xml_points_at(prof, monkeypatch):
    """Le VBS est ecrit par le generateur, pas pose a la main : c'est ce qui fait
    survivre le durcissement a la reinstalation, alors qu'un durcissement de la
    tache est annule au `schtasks /Create /F` suivant (mesure 2026-11-04)."""
    monkeypatch.setattr(ctl, "_is_elevated", lambda: True)
    fake = FakeRun()
    result = ctl.apply_task_install(prof, fake)
    launcher = Path(result["launcher"])
    assert launcher == ctl.task_launcher_path(prof)
    assert launcher.read_text(encoding="ascii") == ctl.task_launcher(prof)
    # L'XML passe a schtasks porte bien le chemin du VBS ecrit juste avant.
    xml_calls = argv_of(fake, "controller-task.xml")
    assert xml_calls
    installed = Path(xml_calls[0][0][5]).read_text(encoding="utf-16")
    assert "<Command>wscript.exe</Command>" in installed
    assert str(launcher) in installed


def test_task_xml_carries_the_run_level_in_principals(prof):
    """Le niveau d'execution est une propriete du PRINCIPAL de la tache : il doit
    voyager dans l'XML des la creation. Le porter apres coup par
    `schtasks /Change /RL HIGHEST` fait reclamer le mot de passe du compte et
    suspend une session elevee non interactive (mesure 2026-11-04, #24700).

    `UserId` est volontairement absent : le principal par defaut est le compte
    appelant, ce qui garde le script independant de la machine."""
    root = ET.fromstring(ctl.task_xml(prof))
    principals = root.find("{" + TASK_NS + "}Principals")
    assert principals is not None, "un XML sans <Principals> ne porte aucun RunLevel"
    principal = principals.find("{" + TASK_NS + "}Principal")
    assert principal is not None and principal.get("id") == "Author"
    run_level = principal.find("{" + TASK_NS + "}RunLevel")
    assert run_level is not None and run_level.text == "HighestAvailable"
    assert principal.find("{" + TASK_NS + "}UserId") is None


def test_task_install_never_asks_schtasks_to_change_the_run_level(prof, monkeypatch):
    """Le `/Change /RL HIGHEST` posterieur a la creation est le blocage : il ne
    doit plus exister dans le chemin d'installation, quelle que soit la forme."""
    monkeypatch.setattr(ctl, "_is_elevated", lambda: True)
    fake = FakeRun()
    ctl.apply_task_install(prof, fake)
    schtasks = [" ".join(str(a) for a in c[0]) for c in fake.calls
                if str(c[0][0]) == "schtasks"]
    assert schtasks, "l'installation doit appeler schtasks au moins une fois"
    assert not [c for c in schtasks if "/Change" in c], schtasks
    assert [c for c in schtasks if "/Create" in c and "/XML" in c], schtasks


def test_task_install_cli_dry_run_outputs_validated_xml_without_side_effects(
    prof, monkeypatch, capsys,
):
    """Le dry-run doit montrer le document qui sera inscrit, après validation,
    sans demander l'élévation, écrire de fichier ni appeler schtasks."""
    validations: list[str] = []
    commands: list[tuple] = []
    original_validate = ctl._validate_task_xml

    def validate(xml: str) -> None:
        original_validate(xml)
        validations.append(xml)

    monkeypatch.setattr(ctl, "load_profile", lambda name, profiles: prof)
    monkeypatch.setattr(ctl, "_validate_task_xml", validate)
    monkeypatch.setattr(
        ctl, "_is_elevated",
        lambda: pytest.fail("le dry-run ne doit pas sonder l'élévation"),
    )
    monkeypatch.setattr(
        ctl.subprocess, "run",
        lambda *args, **kwargs: commands.append(args) or pytest.fail(
            "le dry-run ne doit lancer aucune commande système"
        ),
    )

    assert ctl.main(["task-install", "--profile", prof.name]) == ctl.EXIT_OK
    output = json.loads(capsys.readouterr().out)
    assert output["planned_actions"] == ["create-scheduled-task"]
    xml = output["xml"]
    ET.fromstring(xml)
    assert validations == [xml]
    assert commands == []
    assert not (prof.root.parent / "logs" / "controller-task.xml").exists()


def test_task_xml_malformed_is_caught_before_elevation(prof, monkeypatch):
    """La garde d'elevation passait AVANT la construction de l'XML : un dry-run
    non-eleve ne pouvait donc structurellement pas voir un document malforme.
    Le controle est desormais en amont, et ce test fige cet ordre."""
    monkeypatch.setattr(ctl, "_is_elevated", lambda: False)
    monkeypatch.setattr(ctl, "task_xml", lambda p: "<Task><Actions></Task>")
    with pytest.raises(ctl.Broken, match="malformed"):
        ctl.apply_task_install(prof, FakeRun())


def test_task_install_requires_elevation(prof, monkeypatch):
    monkeypatch.setattr(ctl, "_is_elevated", lambda: False)
    with pytest.raises(ctl.Broken, match="elevated"):
        ctl.apply_task_install(prof, FakeRun())


def test_task_remove_absent_task_is_explicit_success(prof, monkeypatch):
    monkeypatch.setattr(ctl, "_is_elevated", lambda: True)
    fake = FakeRun(schtasks_error="ERROR: The system cannot find the file specified.")
    result = ctl.apply_task_remove(prof, fake)
    assert result["action"] == "task-removed"  # second passage = succes explicite


def test_task_remove_real_error_refuses(prof, monkeypatch):
    monkeypatch.setattr(ctl, "_is_elevated", lambda: True)
    fake = FakeRun(schtasks_error="ERROR: Access is denied.")
    with pytest.raises(ctl.Broken, match="schtasks /Delete failed"):
        ctl.apply_task_remove(prof, fake)


# ---------------------------------------------------------------------------
# Le journal porte la raison de l'echec (Maintenance#75, mesure du 04/11)
# ---------------------------------------------------------------------------

PWSH = shutil.which("pwsh.exe") or shutil.which("pwsh")
WINDOWS = sys.platform == "win32"


def test_task_action_redirige_tout_le_flux_vers_le_journal(prof):
    """Le corps ecrit SA sortie ET la raison de son echec dans controller.log.

    La redirection shell `*>>` ne portait que la DERNIERE instruction : un
    echec preparatoire partait vers la sortie invisible de la tache, et le
    journal restait absent ou vide alors que le code retour portait 1
    (mesure 2026-11-04 : controller.log vide a 17:57, res=1).
    """
    body = ctl.task_action(prof)
    assert "*>>" not in body, "la redirection shell ne couvre que la derniere instruction"
    assert "[IO.File]::AppendAllText($log," in body
    assert "$out = & " in body and "2>&1 | Out-String" in body
    assert "$code = $LASTEXITCODE;" in body
    # un executable introuvable ne met pas `$LASTEXITCODE` a jour : `$null`
    # ne doit pas pouvoir passer pour un succes (`exit $null` rend 0)
    assert "if ($null -eq $code)" in body
    assert "exit $code" in body
    # le chemin d'echec ecrit la raison, puis rend un code non nul
    assert "} catch {" in body
    assert "ERREUR" in body
    assert "exit 1" in body


@pytest.mark.skipif(not (WINDOWS and PWSH), reason="pwsh absent (poste Windows requis)")
def test_echec_preparatoire_ecrit_la_raison_dans_le_journal(prof):
    """Execution reelle : le fichier de mot de passe manque -> le corps echoue,
    le code retour vaut 1 ET le journal existe avec la raison de l'echec.

    Temoin du defaut : avant ce correctif, le meme corps rendait 1 avec un
    journal ABSENT (l'erreur partait vers la sortie invisible de la tache).
    """
    body = ctl.task_action(prof)
    completed = subprocess.run(
        [PWSH, "-NoProfile", "-NonInteractive", "-Command", body],
        capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=300,
    )
    log = prof.root.parent / "logs" / "controller.log"
    assert completed.returncode == 1
    assert log.is_file(), "le journal doit exister meme quand le corps echoue"
    text = log.read_text(encoding="utf-8")
    assert text.strip(), "le journal ne doit pas etre vide"
    assert "runner_pwd.txt" in text, "le journal doit nommer la cause"


@pytest.mark.skipif(not (WINDOWS and PWSH), reason="pwsh absent (poste Windows requis)")
def test_le_code_retour_de_l_organe_traverse_le_corps(prof):
    """La commande lancee rend 3 -> le corps rend 3, et sa sortie est journalisee.

    `command` remplace la commande du controleur : le test ne peut pas lancer
    `ensure --apply` (il enregistre un runner sur GitHub).
    """
    secrets = prof.root.parent / "secrets" / "runner_pwd.txt"
    secrets.parent.mkdir(parents=True, exist_ok=True)
    secrets.write_text("mot-de-passe\n", encoding="utf-8")
    body = ctl.task_action(
        prof,
        command=[sys.executable, "-c", "import sys; print('sortie organe'); sys.exit(3)"],
    )
    completed = subprocess.run(
        [PWSH, "-NoProfile", "-NonInteractive", "-Command", body],
        capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=300,
    )
    log = prof.root.parent / "logs" / "controller.log"
    assert completed.returncode == 3, "le code retour de l'organe doit traverser"
    assert "sortie organe" in log.read_text(encoding="utf-8")


@pytest.mark.skipif(not (WINDOWS and PWSH), reason="pwsh absent (poste Windows requis)")
def test_un_executable_introuvable_ne_rend_pas_un_code_nul(prof):
    """Un executable introuvable rend 1, et le journal nomme la cause.

    Mesure sur les deux moteurs du poste (pwsh 7 et Windows PowerShell 5.1) :
    l'exception « commande introuvable » est **terminante** pour le `try` du
    corps -- elle est donc attrapee par le `catch`, qui ecrit la raison dans
    le journal et rend 1. Le rc ne ment donc pas sur ce chemin.

    Ce temoin verrouille ce comportement, et non pas une correction : le
    controle negatif (garde du corps retiree) le laisse VERT, parce que le
    `catch` couvre deja le cas. Il deviendrait ROUGE le jour ou l'exception
    cesserait d'etre terminante -- le `$LASTEXITCODE` resterait `$null`,
    `exit $null` rendrait 0, et le journal serait vide.
    """
    secrets = prof.root.parent / "secrets" / "runner_pwd.txt"
    secrets.parent.mkdir(parents=True, exist_ok=True)
    secrets.write_text("mot-de-passe\n", encoding="utf-8")
    absent = prof.root.parent / "absent" / "command_inexistante.exe"
    body = ctl.task_action(prof, command=[str(absent)])
    completed = subprocess.run(
        [PWSH, "-NoProfile", "-NonInteractive", "-Command", body],
        capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=300,
    )
    log = prof.root.parent / "logs" / "controller.log"
    assert completed.returncode == 1, "un executable introuvable ne doit pas rendre 0"
    assert log.is_file(), "le journal doit porter la raison de l'echec"
    text = log.read_text(encoding="utf-8")
    assert text.strip(), "le journal ne doit pas etre vide"
    assert "command_inexistante" in text, "le journal doit nommer la commande absente"
