"""Le kernelspec du job est verifie, pas suppose (#28501).

Le geste precedent etait un `if python -c "import ipykernel" ; then ... ;
else echo "ipykernel absent" ; fi` : quand l'import echouait, le step
imprimait un message et rendait SUCCES. Le job continuait sans noyau
enregistre, et l'echec n'apparaitrait que plus loin -- sur un noyau que
Jupyter resout ailleurs.

Ces tests couvrent les quatre controles du script
`scripts/ci/verify_job_kernelspec.py` :

1. l'enregistrement est FATAL quand `ipykernel` manque ;
2. le kernelspec EFFECTIVEMENT RESOLU est celui du job (repertoire de
   ressources sous le repertoire du job) ;
3. `argv[0]` est l'interpreteur du job ;
4. l'ENVIRONNEMENT du lanceur est celui du job -- deux virtualenvs
   distincts partagent le meme binaire, et rien d'autre que le prefixe
   ne les distingue.

Plus le controle negatif du noyau absent : un job sans noyau ne peut pas
lancer la legende papermill, ce n'est pas un incident, c'est un echec.
"""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

import pytest

import verify_job_kernelspec as vks


def _faux_run(returncode: int, stdout: str = "", stderr: str = ""):
    """Un `subprocess.run` factice, avec la meme forme que le vrai."""
    def _run(*args, **kwargs):
        return subprocess.CompletedProcess(
            args=args, returncode=returncode, stdout=stdout, stderr=stderr)
    return _run


def _noyau_absent(nom: str = vks.KERNEL_NAME):
    """Lever `KernelAbsent`, comme le fait une resolution sans noyau."""
    raise vks.KernelAbsent("le kernelspec `python3` n'est pas resolu")


def test_a_conforming_spec_has_no_violation(tmp_path):
    """CONTROLE POSITIF : tout est conforme, aucune violation."""
    job_dir = tmp_path / "ks"
    spec_dir = job_dir / "kernels" / "python3"
    spec_dir.mkdir(parents=True)

    violations = vks.controler(
        [sys.executable, "-m", "ipykernel_launcher"],
        str(spec_dir),
        sys.executable,
        str(job_dir),
    )

    assert violations == [], f"un spec conforme ne doit rien signaler : {violations}"


def test_two_environments_sharing_a_binary_are_told_apart(tmp_path):
    """CONTROLE NEGATIF : meme binaire, environments DIFFERENTS.

    Deux virtualenvs distincts pointent sur le meme binaire : leurs
    lanceurs ont le meme `realpath`, et rien d'autre que l'ENVIRONNEMENT ne
    les distingue. Comparer les chemins seule accepterait donc le mauvais
    virtualenv -- qui demarre sans erreur, et rend un succes SILENCIEUX.
    """
    job_dir = tmp_path / "ks"
    spec_dir = job_dir / "kernels" / "python3"
    spec_dir.mkdir(parents=True)
    # Deux CHEMINS differents qui designent le MEME fichier.
    lanceur_job = tmp_path / "envA" / "bin" / "python"
    lanceur_job.parent.mkdir(parents=True)
    lanceur_job.write_text("", encoding="utf-8")
    faux_autre = tmp_path / "envB" / "bin" / ".." / ".." / "envA" / "bin" / "python"
    assert os.path.realpath(faux_autre) == os.path.realpath(lanceur_job)

    prefixes = {os.path.normcase(str(lanceur_job)): "/job", os.path.normcase(str(faux_autre)): "/autre"}

    violations = vks.controler(
        [str(faux_autre), "-m", "ipykernel_launcher"],
        str(spec_dir),
        str(lanceur_job),
        str(job_dir),
        prefixes=lambda executable: prefixes.get(os.path.normcase(executable)),
    )

    assert len(violations) == 1, violations
    assert "environnement different" in violations[0], violations[0]


def test_two_environments_sharing_a_binary_and_a_prefix_are_accepted(tmp_path):
    """CONTROLE POSITIF : meme binaire ET meme environnement, rien a dire.

    Le meme virtualenv designe par deux chemins ne doit pas declencher le
    controle d'environnement : sinon le job rougirait sur lui-meme.
    """
    job_dir = tmp_path / "ks"
    spec_dir = job_dir / "kernels" / "python3"
    spec_dir.mkdir(parents=True)
    lanceur = tmp_path / "envA" / "bin" / "python"
    lanceur.parent.mkdir(parents=True)
    lanceur.write_text("", encoding="utf-8")
    meme = tmp_path / "envA" / "bin" / ".." / "bin" / "python"

    violations = vks.controler(
        [str(meme), "-m", "ipykernel_launcher"],
        str(spec_dir),
        str(lanceur),
        str(job_dir),
        prefixes=lambda executable: "/job",
    )

    assert violations == [], f"un meme environnement ne doit rien signaler : {violations}"


def test_a_spec_resolved_outside_the_job_directory_is_reported(tmp_path):
    """CONTROLE NEGATIF : le spec resolu est hors du repertoire du job.

    C'est le cas que l'isolation pretend corriger : la lecture a echappe au
    repertoire du job, et le noyau qui demarre appartient a un autre job.
    """
    job_dir = tmp_path / "ks"
    job_dir.mkdir()
    spec_dir = tmp_path / "partage" / "kernels" / "python3"

    violations = vks.controler(
        [sys.executable, "-m", "ipykernel_launcher"],
        str(spec_dir),
        sys.executable,
        str(job_dir),
    )

    assert len(violations) == 1, violations
    assert "hors du job" in violations[0], violations[0]


def test_a_spec_pointing_at_another_interpreter_is_reported(tmp_path):
    """CONTROLE NEGATIF : le noyau ne lance pas le Python du job."""
    job_dir = tmp_path / "ks"
    spec_dir = job_dir / "kernels" / "python3"
    spec_dir.mkdir(parents=True)
    autre = tmp_path / "autre-python.exe"
    autre.write_text("", encoding="utf-8")

    violations = vks.controler(
        [str(autre), "-m", "ipykernel_launcher"],
        str(spec_dir),
        sys.executable,
        str(job_dir),
    )

    assert len(violations) == 1, violations
    assert "interpreteur different" in violations[0], violations[0]


def _environnement_type_virtualenv(racine: Path, base: str) -> Path:
    """Construit un environnement TYPE virtualenv : meme binaire, autre prefixe.

    Un virtualenv est un repertoire qui porte un `pyvenv.cfg` et dont le
    lanceur est un lien symbolique sur l'interpreteur de base. Deux de ces
    environnements ont donc le MEME `realpath` de lanceur, et des
    `sys.prefix` differents -- exactement le cas ou la comparaison des
    chemins ne distingue plus rien.
    """
    bin_dir = racine / "bin"
    bin_dir.mkdir(parents=True)
    lanceur = bin_dir / "python"
    lanceur.symlink_to(base)
    (racine / "pyvenv.cfg").write_text(
        f"home = {sys.base_prefix}\n"
        "include-system-site-packages = false\n",
        encoding="utf-8")
    return lanceur


@pytest.mark.skipif(os.name != "posix",
                    reason="le lien symbolique qui porte le virtualenv "
                           "demande POSIX")
def test_two_real_environments_sharing_a_binary_are_told_apart(tmp_path):
    """TEMOIN REEL : deux virtualenvs distincts, un seul binaire.

    Le cas mesure par l'adjoint : deux lanceurs de virtualenv distincts ont
    le meme `realpath` et des `sys.prefix` differents. Le repertoire de
    ressources du noyau est bien DANS le dossier du job -- et pourtant le
    noyau demarre un environnement qui n'est pas celui du job. Sans le
    controle d'environnement, ce job rendrait un SUCCES SILENCIEUX.
    """
    job_dir = tmp_path / "ks"
    spec_dir = job_dir / "kernels" / "python3"
    spec_dir.mkdir(parents=True)
    lanceur_job = _environnement_type_virtualenv(tmp_path / "envA", sys.executable)
    lanceur_noyau = _environnement_type_virtualenv(tmp_path / "envB", sys.executable)

    assert os.path.realpath(lanceur_job) == os.path.realpath(lanceur_noyau), (
        "le témoin suppose deux lanceurs de meme binaire : "
        f"{os.path.realpath(lanceur_job)} != {os.path.realpath(lanceur_noyau)}")

    prefixe_job = vks.prefixe_de(str(lanceur_job))
    prefixe_noyau = vks.prefixe_de(str(lanceur_noyau))
    if prefixe_job is None or prefixe_noyau is None:
        pytest.skip("l'interpreteur de cette machine ne repond pas sur son prefixe")
    if prefixe_job == prefixe_noyau:
        pytest.skip("les deux environnements n'exposent pas de prefixe distinct "
                    "ici : le virtualenv n'est pas reconnu")

    violations = vks.controler(
        [str(lanceur_noyau), "-m", "ipykernel_launcher"],
        str(spec_dir),
        str(lanceur_job),
        str(job_dir),
    )

    assert len(violations) == 1, violations
    assert "environnement different" in violations[0], violations[0]


@pytest.mark.skipif(os.name != "posix",
                    reason="le lien symbolique qui porte le virtualenv "
                           "demande POSIX")
def test_the_job_environment_passes_its_own_control(tmp_path):
    """CONTROLE POSITIF, en conditions REELLES : le job ne se signale pas lui-meme.

    Le meme environnement designe par un autre chemin ne doit declencher
    aucune violation : le controle doit etre capable de distinguer les
    DEUX environnement, pas de les confondre tous les deux.
    """
    job_dir = tmp_path / "ks"
    spec_dir = job_dir / "kernels" / "python3"
    spec_dir.mkdir(parents=True)
    lanceur = _environnement_type_virtualenv(tmp_path / "envA", sys.executable)
    alias = lanceur.parent / ".." / "bin" / "python"

    violations = vks.controler(
        [str(alias), "-m", "ipykernel_launcher"],
        str(spec_dir),
        str(lanceur),
        str(job_dir),
    )

    assert violations == [], f"le job ne doit pas se signaler lui-meme : {violations}"


def test_a_missing_kernel_is_reported(tmp_path):
    """CONTROLE NEGATIF : un noyau absent est un ECHEC, pas un incident."""
    violations = vks.controler(None, None, sys.executable, str(tmp_path))

    assert len(violations) == 1, violations
    assert "noyau absent" in violations[0], violations[0]


def test_an_unresolvable_kernel_is_detected_for_real():
    """Le noyau absent est detecte par la resolution REELLE de Jupyter.

    Sans ce controle, la fonction pourrait rendre un spec vide au lieu de
    lever : le job passerait avec un noyau inexistant.
    """
    with pytest.raises(vks.KernelAbsent):
        vks.resoudre_le_noyau("noyau-qui-n-existe-pas-#28501")


def test_the_job_directory_is_required(monkeypatch, tmp_path, capsys):
    """Un job non isole est un INCIDENT : rien ne peut etre mesure."""
    monkeypatch.delenv(vks.JOB_DIR_VAR, raising=False)

    rc = vks.main([])

    assert rc == vks.RC_INCIDENT
    assert vks.JOB_DIR_VAR in capsys.readouterr().err


def test_a_conforming_job_passes(monkeypatch, tmp_path, capsys):
    """Le job conforme passe : le controle ne doit pas estonner par erreur."""
    job_dir = tmp_path / "ks"
    spec_dir = job_dir / "kernels" / "python3"
    spec_dir.mkdir(parents=True)
    monkeypatch.setenv(vks.JOB_DIR_VAR, str(job_dir))
    monkeypatch.setattr(vks, "ipykernel_importable", lambda i: (True, ""))
    monkeypatch.setattr(vks, "enregistrer", lambda i: (True, ""))
    monkeypatch.setattr(
        vks, "resoudre_le_noyau",
        lambda nom=vks.KERNEL_NAME: ([sys.executable, "-m", "ipykernel_launcher"],
                                      str(spec_dir)))

    rc = vks.main(["--register"])

    assert rc == vks.RC_OK, capsys.readouterr().err


def test_the_job_fails_when_ipykernel_cannot_be_imported(monkeypatch, tmp_path,
                                                          capsys):
    """CONTROLE NEGATIF : le cas que l'ancien shell absorbait.

    `ipykernel` absent de l'interpreteur du job doit rendre le job ROUGE.
    C'est exactement le defaut signale : l'ancien `else` imprimait un
    message et rendait succes.
    """
    job_dir = tmp_path / "ks"
    job_dir.mkdir()
    monkeypatch.setenv(vks.JOB_DIR_VAR, str(job_dir))
    monkeypatch.setattr(
        vks, "ipykernel_importable",
        lambda i: (False, "No module named 'ipykernel'"))
    monkeypatch.setattr(vks, "resoudre_le_noyau", _noyau_absent)

    rc = vks.main(["--register"])

    assert rc != vks.RC_OK, "un ipykernel absent doit rendre le job rouge"
    sortie = capsys.readouterr().err
    assert "ipykernel absent" in sortie, sortie


def test_the_job_fails_when_the_registration_fails(monkeypatch, tmp_path,
                                                    capsys):
    """CONTROLE NEGATIF : un enregistrement rate est un echec du job."""
    job_dir = tmp_path / "ks"
    spec_dir = job_dir / "kernels" / "python3"
    spec_dir.mkdir(parents=True)
    monkeypatch.setenv(vks.JOB_DIR_VAR, str(job_dir))
    monkeypatch.setattr(vks, "ipykernel_importable", lambda i: (True, ""))
    monkeypatch.setattr(vks, "enregistrer", lambda i: (False, "boom"))
    monkeypatch.setattr(
        vks, "resoudre_le_noyau",
        lambda nom=vks.KERNEL_NAME: ([sys.executable, "-m", "ipykernel_launcher"],
                                      str(spec_dir)))

    rc = vks.main(["--register"])

    assert rc != vks.RC_OK, "un enregistrement rate doit rendre le job rouge"
    assert "enregistrement" in capsys.readouterr().err


def test_the_job_fails_when_the_resolved_kernel_is_absent(monkeypatch, tmp_path,
                                                          capsys):
    """CONTROLE NEGATIF : pas de noyau resolu = job rouge."""
    job_dir = tmp_path / "ks"
    job_dir.mkdir()
    monkeypatch.setenv(vks.JOB_DIR_VAR, str(job_dir))
    monkeypatch.setattr(vks, "resoudre_le_noyau", _noyau_absent)

    rc = vks.main([])

    assert rc != vks.RC_OK, "un noyau absent doit rendre le job rouge"
    assert "noyau absent" in capsys.readouterr().err


def test_the_registration_uses_the_interpreter_of_the_job(monkeypatch):
    """L'enregistrement se fait avec l'interpreteur du job, pas un autre.

    C'est le defaut #28500 : le noyau enregistre doit demarrer le Python du
    job. La commande construite doit donc employer cet interpreteur-la.
    """
    appele: dict = {}

    def faux_run(*args, **kwargs):
        appele["cmd"] = kwargs.get("args") or (args[0] if args else None)
        return subprocess.CompletedProcess(
            args=[], returncode=0, stdout="installed", stderr="")

    monkeypatch.setattr(vks.subprocess, "run", faux_run)

    reussi, _ = vks.enregistrer(sys.executable)

    assert reussi
    commande = list(appele["cmd"])
    assert commande[0] == sys.executable, commande
    assert commande[1:3] == ["-m", "ipykernel"], commande
    assert "install" in commande and "--user" in commande, commande
    assert "python3" in commande, commande


def test_the_import_check_reports_a_missing_module(monkeypatch):
    """L'import manquant est signale, pas avale."""
    monkeypatch.setattr(
        vks.subprocess, "run",
        _faux_run(1, stderr="No module named 'ipykernel'"))

    importable, sortie = vks.ipykernel_importable(sys.executable)

    assert not importable
    assert "ipykernel" in sortie


def test_the_script_fails_when_the_resolved_kernel_is_not_the_job_one(tmp_path):
    """TEMOIN NEGATIF, en conditions REELLES : le script sort en erreur.

    Le repertoire du job est vide : le kernelspec resolu ne peut pas y
    etre. Le script doit donc echouer -- que le noyau soit absent, ou
    resolu ailleurs. Ce temoin ne simule rien : il execute le script du
    depot, dans un environnement ou le noyau du job n'existe pas.
    """
    job_dir = tmp_path / "ks"
    job_dir.mkdir()
    env = dict(os.environ)
    env[vks.JOB_DIR_VAR] = str(job_dir)
    env["JUPYTER_PATH"] = str(job_dir)
    script = Path(vks.__file__).resolve()

    fait = subprocess.run(
        [sys.executable, str(script)], env=env, capture_output=True, text=True,
        encoding="utf-8", errors="replace", timeout=300, check=False)

    assert fait.returncode != 0, (
        "le script a rendu SUCCES alors que le noyau du job n'existe pas : "
        f"{fait.stdout}")
    assert "noyau" in (fait.stdout + fait.stderr).lower()


if __name__ == "__main__":
    for fn in (
        test_a_conforming_spec_has_no_violation,
        test_two_environments_sharing_a_binary_are_told_apart,
        test_two_environments_sharing_a_binary_and_a_prefix_are_accepted,
        test_a_spec_resolved_outside_the_job_directory_is_reported,
        test_a_spec_pointing_at_another_interpreter_is_reported,
        test_a_missing_kernel_is_reported,
        test_an_unresolvable_kernel_is_detected_for_real,
        test_the_job_directory_is_required,
        test_a_conforming_job_passes,
        test_the_job_fails_when_ipykernel_cannot_be_imported,
        test_the_job_fails_when_the_registration_fails,
        test_the_job_fails_when_the_resolved_kernel_is_absent,
        test_the_registration_uses_the_interpreter_of_the_job,
        test_the_import_check_reports_a_missing_module,
        test_the_script_fails_when_the_resolved_kernel_is_not_the_job_one,
    ):
        fn()
        print(f"OK: {fn.__name__}")
    if os.name == "posix":
        for fn in (
            test_two_real_environments_sharing_a_binary_are_told_apart,
            test_the_job_environment_passes_its_own_control,
        ):
            fn()
            print(f"OK: {fn.__name__}")
    print("All tests passed.")
