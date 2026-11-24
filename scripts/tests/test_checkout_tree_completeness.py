"""#26468 : l'etape « l'arbre est-il complet ? » du job `scripts-tests`.

Quand le fetch PROMISOR du checkout meurt (garde de debit, lien coupe), le
`git checkout` sort en 128 et l'ARBRE RESTE ABSENT ou a moitie ecrit. Les
etapes de plancher du job sont en `if: always()` : sans controle, elles
s'executent quand meme sur cet arbre et echouent sur des messages qui
nominent autre chose que la cause (« No module named pytest », plancher de
collecte a zero) -- une panne d'infrastructure fait alors rougir un check
REQUIS sur le fond.

Ce test rejoue le SCRIPT REEL de l'etape (extrait du workflow, pas une
copie) sur deux fixtures :

- arbre complet -> rc=0, l'etape laisse passer ;
- arbre amputé -> rc=1, et la sortie NOMME la cause et le remede.

Aucun reseau, aucun git distant : la fixture est un depot local d'une
poignee de fichiers.

Note d'environnement : sur Windows, `bash` designe souvent le lanceur WSL,
qui rend une sortie UTF-16 et echoue sur un script local. Le test cherche
donc un bash POSIX REEL (Git Bash d'abord), et se SAUTE s'il n'en trouve
pas -- plutot que d'echouer sur une cause qui n'est pas celle qu'il teste.
"""
from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest
import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = REPO_ROOT / ".github" / "workflows" / "scripts-tests.yml"
JOB = "scripts-tests"
STEP_ID = "tete_arbre"


def _bash_posix() -> str | None:
    """Un bash qui execute un script local et rend une sortie ASCII lisible."""
    candidats: list[str] = []
    if os.name == "nt":
        for chemin in (r"C:\Program Files\Git\bin\bash.exe",
                       r"C:\Program Files\Git\usr\bin\bash.exe"):
            if Path(chemin).exists():
                candidats.append(chemin)
    trouve = shutil.which("bash")
    if trouve:
        candidats.append(trouve)
    for candidat in candidats:
        try:
            probe = subprocess.run([candidat, "-c", "echo probe"],
                                   capture_output=True, text=True,
                                   encoding="utf-8", errors="replace", timeout=20)
        except (OSError, subprocess.SubprocessError):
            continue
        if probe.returncode == 0 and probe.stdout.strip() == "probe":
            return candidat
    return None


BASH = _bash_posix()
pytestmark = pytest.mark.skipif(BASH is None,
                                reason="aucun bash POSIX executable (le bash du PATH "
                                       "peut etre le lanceur WSL)")


def _script_de_l_etape() -> str:
    """Le script de l'etape tel qu'il est dans le workflow (source unique)."""
    data = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))
    etapes = data["jobs"][JOB].get("steps") or []
    for etape in etapes:
        if etape.get("id") == STEP_ID:
            return str(etape.get("run") or "")
    raise AssertionError(f"l'etape id={STEP_ID!r} est absente de {WORKFLOW.name}")


def _depot(tmp_path: Path) -> Path:
    """Un depot local avec trois fichiers, et un HEAD."""
    depot = tmp_path / "depot"
    depot.mkdir()
    (depot / "a.txt").write_text("a\n", encoding="utf-8")
    (depot / "sous").mkdir()
    (depot / "sous" / "b.txt").write_text("b\n", encoding="utf-8")
    (depot / "c.txt").write_text("c\n", encoding="utf-8")
    for args in (["init", "-q"], ["add", "-A"]):
        subprocess.run(["git", "-C", str(depot), *args], check=True,
                       capture_output=True)
    subprocess.run(["git", "-C", str(depot), "-c", "user.email=ci@example.invalid",
                    "-c", "user.name=CI", "commit", "-q", "-m", "fixture"],
                   check=True, capture_output=True)
    return depot


def _rejouer(tmp_path: Path, depot: Path) -> subprocess.CompletedProcess:
    script = tmp_path / "etape.sh"
    script.write_text(_script_de_l_etape(), encoding="utf-8", newline="\n")
    env = dict(os.environ)
    # `cd "$GITHUB_WORKSPACE"` : le repertoire courant EST la fixture, donc
    # un chemin relatif evite toute conversion de chemin Windows/POSIX.
    env["GITHUB_WORKSPACE"] = "."
    env.pop("RUNNER_TEMP", None)
    return subprocess.run([BASH, str(script)], capture_output=True, text=True,
                          encoding="utf-8", errors="replace", cwd=str(depot),
                          env=env, timeout=120)


def test_un_arbre_complet_passe(tmp_path):
    depot = _depot(tmp_path)
    proc = _rejouer(tmp_path, depot)
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "complet" in proc.stdout


def test_un_arbre_ampute_est_nomme(tmp_path):
    """Le cas du checkout interrompu : un fichier declare par le commit est
    absent du disque -> l'etape sort en 1 et NOMME la cause."""
    depot = _depot(tmp_path)
    (depot / "c.txt").unlink()
    proc = _rejouer(tmp_path, depot)
    assert proc.returncode == 1, proc.stdout + proc.stderr
    assert "arbre incomplet" in proc.stdout
    assert "c.txt" in proc.stdout
    # Le remede STRUCTUREL est cite : le miroir de l'hote, pas un contournement.
    assert "miroir" in proc.stdout


def test_un_head_illisible_est_nomme(tmp_path):
    """Sans l'objet du commit (le fetch lui-meme a echoue), l'etape le dit
    au lieu de croire l'arbre vide."""
    depot = tmp_path / "pas-un-depot"
    depot.mkdir()
    proc = _rejouer(tmp_path, depot)
    assert proc.returncode == 1, proc.stdout + proc.stderr
    assert "HEAD" in proc.stdout


def test_les_planchers_exigent_le_succes_de_l_etape_d_arbre():
    """Les etapes de plancher sont conditionnees : sans arbre, elles ne
    doivent pas produire un verdict qui nomme autre chose que la cause."""
    data = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))
    etapes = data["jobs"][JOB].get("steps") or []
    condition = f"steps.{STEP_ID}.outcome == 'success'"
    plancher = [e for e in etapes
                if "always()" in str(e.get("if")) and e.get("id") != STEP_ID]
    assert plancher, "aucune etape de plancher en if: always() -- le garde a disparu"
    for etape in plancher:
        assert condition in str(etape.get("if")), etape.get("name")


def test_la_politique_de_debit_du_job_est_calibree_sur_le_tir():
    """Le job declare sa fenetre de debit : 1 octet/s sur 5 min.

    Le seuil du superviseur (1 024 o/s sur 90 s) est calibre sur des
    transferts courts ; le checkout tire l'arbre entier (1,51 Gio) en une
    requete promisor, et le silence du serveur pendant le calcul du pack
    n'est pas un reseau mort. On garde la garde, on elargit sa fenetre.
    """
    data = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))
    env = data["jobs"][JOB].get("env") or {}
    assert env.get("GIT_HTTP_LOW_SPEED_LIMIT") == "1"
    assert env.get("GIT_HTTP_LOW_SPEED_TIME") == "300"
