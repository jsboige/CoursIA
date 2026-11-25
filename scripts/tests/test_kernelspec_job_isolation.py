"""Le kernelspec `python3` est ISOLÉ par job (#28501, suite du steer ai-01).

Le parc auto-heberge fait tourner plusieurs jobs SIMULTANEMENT sur un meme
hote, et tous partagent le meme `HOME`. L'enregistrement du kernelspec
`python3` ecrit dans le repertoire UTILISATEUR : deux jobs enregistrent
`python3` vers deux interpreteurs differents, dans le MEME fichier.

Mesure (po-2026, 25/11, hors parc, deux Python de slots) : 33 changements
d'argv et 5 echecs en 6 s. La suite n'y est pas : le kernelspec change de
main entre l'enregistrement et la lecture.

Le remede : un repertoire de kernelspec PAR JOB. Une seule paire de
variables d'environnement redirige les DEUX operations :

- l'ECRITURE : `install_kernel_spec(user=True)` ecrit dans
  `jupyter_data_dir()/kernels`, et `jupyter_data_dir()` lit
  `JUPYTER_DATA_DIR` ;
- la LECTURE : `jupyter_path("kernels")` place `JUPYTER_PATH` EN PREMIER,
  et `find_kernel_specs` ne retient que le PREMIER `kname` trouve.

Mesures sur jupyter_client 8.x / jupyter_core 5.x (poste po-2026, 25/11) :
`JUPYTER_DATA_DIR=B` -> `install_kernel_spec(user=True)` ecrit
`B/kernels/python3` ; `JUPYTER_PATH=A` + `JUPYTER_DATA_DIR=B` ->
`get_kernel_spec("python3")` rend l'argv de A, pas celui de B.

Ce module verifie trois choses, dont deux sont des controles NEGATIFS :

1. la COURSE est reelle -- deux jobs qui partagent un repertoire se
   parasitent, et le test le montre ;
2. l'ISOLATION la supprime -- deux jobs qui ont chacun leur repertoire
   ne se parasitent plus, et le repertoire partage reste intact ;
3. le CABLAGE -- le job qui appelle le script d'installation declare
   l'isolation AVANT l'etape d'installation. Ce controle est ROUGE sur
   `main` : c'est lui qui fait la PR.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]

WORKFLOW = REPO_ROOT / ".github" / "workflows" / "scripts-tests.yml"

# Les deux variables qui decalent l'ecriture ET la lecture.
ISOLATION_VARS = ("JUPYTER_DATA_DIR", "JUPYTER_PATH")

# Un jeton d'identite de JOB : sans lui, le repertoire serait partage par
# tous les jobs de la flotte (le cas observe).
JOB_IDENTITY_TOKENS = ("GITHUB_RUN_ID", "github.run_id")

# Le script d'installation partage.
INSTALL_SCRIPT = "install_scripts_tests_deps.sh"

# Le nom de noyau que papermill demande dans ce job.
KERNEL_ARG = "-k python3"

# Programme-enfant : enregistre un kernelspec `python3` dont l'argv porte un
# marqueur, attend que l'autre enfant soit enregistre, puis rend l'argv
# qu'il RESOUT. Les deux enfants lisent APRES les deux enregistrements :
# dans un repertoire partage, le fichier est celui du dernier ecrivain --
# ou n'existe plus, si les deux ecritures se sont croisees.
CHILD = r'''
import json
import os
import sys
import time

from jupyter_client.kernelspec import KernelSpecManager

marker, work_dir, tag = sys.argv[1], sys.argv[2], sys.argv[3]

# Libere le partenaire meme si ce processus meurt ensuite.
open(os.path.join(work_dir, "started-" + tag), "w").close()

source = os.path.join(work_dir, "source-" + tag)
os.makedirs(source, exist_ok=True)
with open(os.path.join(source, "kernel.json"), "w", encoding="utf-8") as handle:
    json.dump(
        {
            "argv": [marker, "-m", "ipykernel_launcher", "-f", "{connection_file}"],
            "display_name": "python3",
            "language": "python",
            "metadata": {},
        },
        handle,
    )

manager = KernelSpecManager()
manager.install_kernel_spec(source, kernel_name="python3", user=True)

# Barriere : chaque enfant annonce son enregistrement, puis attend celui de
# l'autre. Apres la barriere, les deux ecritures sont terminees.
open(os.path.join(work_dir, "written-" + tag), "w").close()
other = "B" if tag == "A" else "A"
deadline = time.time() + 10
while not os.path.exists(os.path.join(work_dir, "written-" + other)):
    if time.time() > deadline:
        break
    time.sleep(0.02)

print(manager.get_kernel_spec("python3").argv[0])
'''


def _child_env(data_dir: Path, path_dir: Path) -> dict[str, str]:
    """L'environnement d'un enfant : les deux variables d'isolation.

    Les variables du CI sont retirees d'abord -- un `JUPYTER_PATH` herite
    parasiterait la mesure.
    """
    env = dict(os.environ)
    env.pop("JUPYTER_PATH", None)
    env.pop("JUPYTER_DATA_DIR", None)
    env["JUPYTER_DATA_DIR"] = str(data_dir)
    env["JUPYTER_PATH"] = str(path_dir)
    return env


def _run_pair(tmp_path: Path, shared: bool) -> dict[str, dict[str, str]]:
    """Fait tourner deux enfants concurrents et rend le resultat de chacun.

    `shared=True` : les deux enfants ecrivent dans le MEME repertoire (la
    course). `shared=False` : chacun a le sien (l'isolation).
    """
    work = tmp_path / "work"
    work.mkdir()
    dir_a = tmp_path / "ks-partage" if shared else tmp_path / "ks-A"
    dir_b = dir_a if shared else tmp_path / "ks-B"

    markers = {"A": "/interpreteur/job-A", "B": "/interpreteur/job-B"}
    processes = {}
    for tag, spec_dir in (("A", dir_a), ("B", dir_b)):
        processes[tag] = subprocess.Popen(
            [sys.executable, "-c", CHILD, markers[tag], str(work), tag],
            env=_child_env(spec_dir, spec_dir),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
        )

    runs: dict[str, dict[str, str]] = {}
    for tag, process in processes.items():
        stdout, stderr = process.communicate(timeout=180)
        runs[tag] = {
            "returncode": str(process.returncode),
            "stdout": stdout.strip(),
            "stderr": stderr.strip(),
        }
    return runs


def test_two_jobs_sharing_one_kernelspec_dir_cross_talk(tmp_path):
    """TEMOIN NEGATIF : la course est reelle.

    Les deux enfants ecrivent dans le meme repertoire. L'invariant du job
    -- "je resout MON noyau" -- ne peut pas y tenir : soit l'ecriture
    elle-meme echoue (les deux `copytree` se croisent : l'un supprime le
    repertoire que l'autre vient de creer), soit l'un des deux resout
    l'argv de l'autre. Les deux formes sont le defaut mesure par po-2026
    (33 changements d'argv et 5 echecs en 6 s).
    """
    runs = _run_pair(tmp_path, shared=True)

    violated = []
    for tag in ("A", "B"):
        if runs[tag]["returncode"] != "0":
            violated.append(f"{tag} : ecriture en echec ({runs[tag]['stderr'][:120]})")
        elif runs[tag]["stdout"] != f"/interpreteur/job-{tag}":
            violated.append(f"{tag} : a resolu {runs[tag]['stdout']}")

    assert violated, (
        "aucun des deux jobs n'a ete affecte par la course -- le temoin "
        "negatif ne prouve rien"
    )


def test_two_jobs_with_isolated_dirs_do_not_cross_talk(tmp_path):
    """L'ISOLATION : chacun resout SON noyau, jamais celui du voisin."""
    runs = _run_pair(tmp_path, shared=False)

    for tag in ("A", "B"):
        assert runs[tag]["returncode"] == "0", (
            f"enfant {tag} a echoue : {runs[tag]['stderr'][:200]}"
        )
        assert runs[tag]["stdout"] == f"/interpreteur/job-{tag}", (
            f"le job {tag} a resolu {runs[tag]['stdout']} au lieu de son "
            f"propre noyau"
        )


def test_an_isolated_job_does_not_write_the_shared_directory(tmp_path):
    """L'ECRITURE est isolee : le repertoire partage reste intact.

    C'est le versant mesurable de l'isolation : sans
    `JUPYTER_DATA_DIR`, l'enregistrement atterrit dans le repertoire
    utilisateur -- partage avec tous les jobs de l'hote.
    """
    from jupyter_core.paths import jupyter_data_dir

    # Le repertoire PARTAGE est celui qu'un job SANS isolation viserait : les
    # variables d'isolation sont retirees le temps de la mesure.
    saved = {
        name: os.environ.pop(name)
        for name in ("JUPYTER_DATA_DIR", "JUPYTER_PATH")
        if name in os.environ
    }
    try:
        shared = Path(jupyter_data_dir()) / "kernels"
    finally:
        os.environ.update(saved)

    before = sorted(p.name for p in shared.glob("*")) if shared.is_dir() else []

    _run_pair(tmp_path, shared=False)

    after = sorted(p.name for p in shared.glob("*")) if shared.is_dir() else []
    assert after == before, (
        f"un job isole a ecrit dans le repertoire partage {shared} "
        f"({set(after) - set(before)})"
    )


def _workflow_jobs() -> dict:
    """Les jobs du workflow, en YAML."""
    document = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))
    return document["jobs"]


def _dump(node: object) -> str:
    """Le YAML d'un noeud, sans coupure de ligne (le texte doit rester lisible)."""
    return yaml.safe_dump(node, width=1000000, sort_keys=False)


def _installing_job() -> tuple[str, dict]:
    """Le job qui appelle le script d'installation partage."""
    jobs = _workflow_jobs()
    installing = [
        name for name, job in jobs.items() if INSTALL_SCRIPT in _dump(job)
    ]
    assert len(installing) == 1, (
        f"le workflow doit avoir exactement un job qui appelle "
        f"{INSTALL_SCRIPT} : {installing}"
    )
    return installing[0], jobs[installing[0]]


def test_the_installing_job_declares_the_isolation():
    """CABLAGE : le job qui installe l'environnement isole le kernelspec.

    Temoin ROUGE sur `main` : sans cette declaration, deux jobs
    concurrents ecrivent le meme fichier.
    """
    name, job = _installing_job()
    steps = job["steps"]
    install_index = next(
        index
        for index, step in enumerate(steps)
        if INSTALL_SCRIPT in _dump(step)
    )

    # L'isolation doit etre declaree AVANT l'etape d'installation : sinon
    # l'enregistrement part dans le repertoire partage.
    isolation = _dump(job.get("env", {})) + _dump(steps[:install_index])
    for variable in ISOLATION_VARS:
        assert variable in isolation, (
            f"{name} ne declare pas {variable} avant l'etape d'installation "
            f"-- l'enregistrement du kernelspec part dans le repertoire "
            f"partage de l'hote"
        )
    assert "$GITHUB_ENV" in isolation, (
        f"{name} ne propage pas l'isolation aux etapes suivantes -- la "
        f"lecture du noyau (papermill) viserait un autre repertoire"
    )
    assert any(token in isolation for token in JOB_IDENTITY_TOKENS), (
        f"{name} utilise un repertoire de kernelspec CONSTANT -- il serait "
        f"partage par tous les jobs de la flotte ; il doit porter "
        f"l'identite du job"
    )


def test_the_isolated_job_is_the_one_that_launches_the_kernel():
    """Le noyau papermill est lance DANS le job isole.

    `JUPYTER_PATH` n'agit que sur les etapes du job qui le declare : un
    lancement de noyau dans un autre job viserait le repertoire partage.
    """
    name, job = _installing_job()

    assert KERNEL_ARG in _dump(job), (
        f"le job {name} ne lance pas papermill avec `{KERNEL_ARG}` -- le "
        f"couplage noyau/kernelspec ne serait pas mesurable"
    )


if __name__ == "__main__":
    for fn in (
        test_two_jobs_sharing_one_kernelspec_dir_cross_talk,
        test_two_jobs_with_isolated_dirs_do_not_cross_talk,
        test_an_isolated_job_does_not_write_the_shared_directory,
        test_the_installing_job_declares_the_isolation,
        test_the_isolated_job_is_the_one_that_launches_the_kernel,
    ):
        fn()
        print(f"OK: {fn.__name__}")
    print("All tests passed.")
