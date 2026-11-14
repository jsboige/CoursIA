"""Persistance du slot RESERVE de la verification de `main` (ai-01).

`create-main-slot.sh` (tranche T-L de #25510) sait creer un slot reserve et
le verifier. Il ne sait pas le faire REVI[V]IR : rien ne le recree au boot,
et rien ne surveille sa disparition.

Or le job CPU de `main` est un job REQUIS : tant qu'il n'a pas de verdict,
`main` n'est pas verifie. Le slot reserve est sa seule place propre
(mesure du 2026-11-12 : plus de 27 minutes de file, 31 runners occupes par
des PRs). Un slot reserve qui ne revient pas apres un reboot rend cette
garantie illusoire -- et le job de `main` attend de nouveau derriere les
PRs, exactement comme avant T-L.

Ce test porte la MOITIE PERSISTANCE : l'unite systemd de boot, le timer de
verification, et le wrapper qui les appelle. Il est verifie **par son
comportement** : le wrapper est execute avec un `docker` et un organe
FAUX (dans un repertoire temporaire), et ce qui est reellement appele est
mesure.

Trois garde-fous structurent ce test :

1. le **verrou de defauts** : le wrapper repete le nom du conteneur, donc
   il repete les defauts de `create-main-slot.sh`. Un defaut qui diverge
   produirait un wrapper qui verifie un conteneur qui n'existe pas -- un
   ecran vert sur du vide. Le test lit les DEUX fichiers et compare ;
2. le **jamais-supprimer** : le slot n'est pas un artefact ephemere. Ni le
   wrapper ni l'organe ne doivent pouvoir le detruire, et le mode `stop`
   de l'unite ne doit pas le faire ;
3. le **secret non duplique** : le jeton est relu dans `master.env` a
   chaque invocation, jamais dans l'unite, jamais sur la ligne de commande.
"""
from __future__ import annotations

import os
import re
import shutil
import stat
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
PERSIST_AI01 = (REPO_ROOT / "scripts" / "ci" / "docker" / "linux-runner" / "persist" / "ai-01")

WRAPPER = PERSIST_AI01 / "coursia-main-slot-start.sh"
SERVICE = PERSIST_AI01 / "coursia-main-slot.service"
CHECK_SERVICE = PERSIST_AI01 / "coursia-main-slot-check.service"
TIMER = PERSIST_AI01 / "coursia-main-slot-check.timer"
ORGANE = PERSIST_AI01 / "create-main-slot.sh"


def _bash() -> str:
    bash = shutil.which("bash")
    if bash is None:
        pytest.skip("bash absent : le wrapper est un script bash")
    return bash


def _run(script: Path, *args: str, env: dict[str, str] | None = None) -> subprocess.CompletedProcess:
    environment = dict(os.environ)
    environment.pop("GH_TOKEN", None)
    if env:
        environment.update(env)
    return subprocess.run(
        [_bash(), str(script), *args],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        env=environment, timeout=120,
    )


# --- 1. les fichiers de reference existent ---------------------------------


def test_les_quatre_fichiers_existent():
    for chemin in (WRAPPER, SERVICE, CHECK_SERVICE, TIMER):
        assert chemin.is_file(), f"fichier de reference absent : {chemin}"


def test_le_wrapper_est_un_script_bash():
    """Les copies de reference de `persist/` sont en `100644` dans l'index
    (convention du depot : le bit executable vit sur la copie VIVANTE
    deployee sous /usr/local/bin, pas dans le depot)."""
    premiere = WRAPPER.read_text(encoding="utf-8").splitlines()[0]
    assert premiere.startswith("#!") and "bash" in premiere, premiere


def test_les_fichiers_sh_passent_la_syntaxe_bash():
    for chemin in (WRAPPER, ORGANE):
        proc = subprocess.run([_bash(), "-n", str(chemin)], capture_output=True, text=True,
                              encoding="utf-8", errors="replace")
        assert proc.returncode == 0, f"syntaxe bash invalide dans {chemin} : {proc.stderr}"


# --- 2. l'unite de boot : le patron du superviseur -------------------------


def _sections(chemin: Path) -> dict[str, str]:
    """Le contenu d'un fichier d'unite, section par section."""
    sections: dict[str, list[str]] = {}
    courante = ""
    for ligne in chemin.read_text(encoding="utf-8").splitlines():
        ligne = ligne.strip()
        if ligne.startswith("[") and ligne.endswith("]"):
            courante = ligne[1:-1]
            sections[courante] = []
        elif ligne and not ligne.startswith("#") and courante:
            sections[courante].append(ligne)
    return {k: "\n".join(v) for k, v in sections.items()}


def test_l_unite_demande_docker_sans_le_rendre_obligatoire():
    """`Wants=` et NON `Requires=` (#14347 item 2) : un docker.service en
    echec au boot doit retarder l'unite, pas la faire sortir de la liste
    des unites -- une unite sortie ne revient qu'a la main."""
    sections = _sections(SERVICE)
    assert "docker.service" in sections["Unit"]
    assert "Requires=docker.service" not in sections["Unit"]
    assert "After=docker.service" in sections["Unit"]


def test_les_cles_startlimit_sont_dans_unit_et_pas_dans_service():
    """Mesure du 2026-09-07 : `systemd-analyze verify` rend « Unknown key
    name 'StartLimitIntervalSec' in section 'Service', ignoring ». Une
    clause ignoree ne refuse rien."""
    sections = _sections(SERVICE)
    assert "StartLimitIntervalSec=" in sections["Unit"]
    assert "StartLimitBurst=" in sections["Unit"]
    assert "StartLimit" not in sections.get("Service", "")


def test_l_unite_est_oneshot_avec_restart_on_failure():
    """`Restart=always` est refuse sur une unite `oneshot` ; `on-failure`
    est ce qui rejoue une creation qui a echoue au boot."""
    sections = _sections(SERVICE)
    assert "Type=oneshot" in sections["Service"]
    assert "Restart=on-failure" in sections["Service"]
    assert "RemainAfterExit=yes" in sections["Service"]


def test_l_unite_appelle_le_wrapper_pour_le_demarrage_et_l_arret():
    sections = _sections(SERVICE)
    assert "coursia-main-slot-start.sh start" in sections["Service"]
    assert "coursia-main-slot-start.sh stop" in sections["Service"]


def test_l_unite_pose_home_parce_que_l_organe_en_a_besoin():
    """`create-main-slot.sh` compose son repertoire de base avec `$HOME`,
    et `set -u` le ferait echouer si HOME n'est pas pose."""
    sections = _sections(SERVICE)
    assert "Environment=HOME=" in sections["Service"]


def test_le_timer_couvre_le_demarrage_et_les_periodes():
    sections = _sections(TIMER)
    assert "OnBootSec=" in sections["Timer"]
    assert "OnUnitActiveSec=" in sections["Timer"]
    # Sans `Persistent=true`, le premier trou apres un reboot est
    # exactement celui qu'on voulait couvrir.
    assert "Persistent=true" in sections["Timer"]
    assert "coursia-main-slot-check.service" in sections["Timer"]


def test_l_unite_de_verification_appelle_le_mode_check():
    sections = _sections(CHECK_SERVICE)
    assert "coursia-main-slot-start.sh check" in sections["Service"]


# --- 3. le verrou de defauts ----------------------------------------------


def _defaut(texte: str, variable: str) -> str:
    """Le defaut d'une variable d'environnement, lu dans sa forme
    `${VAR:-defaut}` -- celle qu'emploient les DEUX fichiers."""
    motif = re.compile(rf'\$\{{{re.escape(variable)}:-(?P<v>[^}}]+)\}}')
    trouve = motif.search(texte)
    assert trouve, f"defaut introuvable pour {variable}"
    return trouve.group("v")


@pytest.mark.parametrize("variable", ["COURSIA_MAIN_PREFIX", "COURSIA_MAIN_SLOT"])
def test_les_defauts_du_wrapper_sont_ceux_de_l_organe(variable):
    """Le wrapper repete le nom du conteneur pour distinguer « absent » de
    « arrete » : un defaut qui diverge le ferait verifier un conteneur qui
    n'existe pas -- un ecran vert sur du vide."""
    assert _defaut(WRAPPER.read_text(encoding="utf-8"), variable) == \
        _defaut(ORGANE.read_text(encoding="utf-8"), variable)


def test_les_deux_fichiers_epinglent_le_meme_daemon_docker():
    """Le daemon du slot est celui de la distro (`unix:///var/run/
    docker-ce.sock`, mesure ai-01 du 2026-11-14) : c'est le seul qui porte
    l'image `coursia-linux-runner:2.338.0`. Le daemon du contexte par
    defaut (Docker Desktop) ne la porte pas.

    Le wrapper exporte deja `DOCKER_HOST` ; l'organe doit faire pareil.
    Sinon un `--apply` lance DIRECTEMENT (hors wrapper) vise le mauvais
    daemon -- et l'echec survient APRES le mint du jeton
    d'enregistrement, qui est a usage unique : le slot ne peut plus etre
    cree sur le bon daemon."""
    assert _defaut(WRAPPER.read_text(encoding="utf-8"), "COURSIA_MAIN_DOCKER_HOST") == \
        _defaut(ORGANE.read_text(encoding="utf-8"), "COURSIA_MAIN_DOCKER_HOST")
    assert _defaut(ORGANE.read_text(encoding="utf-8"), "COURSIA_MAIN_DOCKER_HOST") == \
        "unix:///var/run/docker-ce.sock"
    assert "export DOCKER_HOST" in _corps(ORGANE), \
        "l'organe doit exporter DOCKER_HOST (le pin n'est pas dans un commentaire)"


def test_la_racine_des_volumes_ne_depend_pas_de_home():
    """Sous systemd, l'unite pose `HOME=/root` ; a la main, `$HOME` est le
    home de l'operateur. Deux racines = deux jeux de volumes = l'etat du
    runner (son registre) n'est pas le meme selon qui a cree le slot."""
    defaut = _defaut(ORGANE.read_text(encoding="utf-8"), "COURSIA_MAIN_BASE")
    assert defaut.startswith("/"), f"la racine des volumes doit etre absolue : {defaut}"
    assert "$HOME" not in defaut, \
        f"la racine des volumes ne doit pas dependre de HOME : {defaut}"


# --- 4. les invariants de securite du wrapper ------------------------------


def _corps(chemin: Path) -> str:
    """Le corps du fichier, bandeau de commentaire retire."""
    texte = chemin.read_text(encoding="utf-8")
    return "\n".join(ligne for ligne in texte.splitlines() if not ligne.lstrip().startswith("#"))


def test_le_wrapper_ne_supprime_jamais_un_slot():
    """Un slot reserve n'est pas un artefact ephemere ; `create-main-slot.sh`
    refuse lui-meme de supprimer un slot."""
    corps = _corps(WRAPPER)
    for interdit in ("docker rm", "docker rmi", "docker rm -f"):
        assert interdit not in corps, f"le wrapper ne doit jamais executer '{interdit}'"


def test_le_wrapper_epingle_le_daemon_docker_de_la_distro():
    """Sans epinglage, le slot repartirait sur le daemon de Docker Desktop,
    rattache a la session utilisateur -- et l'echec serait muet."""
    corps = _corps(WRAPPER)
    assert "COURSIA_MAIN_DOCKER_HOST:-unix:///var/run/docker-ce.sock" in corps


def test_le_secret_est_relu_dans_master_env_et_jamais_copie():
    corps = _corps(WRAPPER)
    assert "GH_RUNNERS_ADMIN_TOKEN" in corps
    assert "master.env" in corps
    # Aucun jeton en clair, aucun jeton sur la ligne de commande.
    assert "ghp_" not in corps and "github_pat_" not in corps
    lignes = [l for l in corps.splitlines() if "GH_RUNNERS_ADMIN_TOKEN" in l]
    # L'extraction doit etre une RELECTURE (sed), jamais une affectation.
    assert any("sed -n" in l for l in lignes), (
        "le jeton doit etre RELU dans master.env, jamais affecte en dur")
    for ligne in lignes:
        assert not re.search(r'GH_RUNNERS_ADMIN_TOKEN\s*=\s*["\'][^"\'$]', ligne), (
            f"affectation en dur d'un jeton : {ligne}")


def test_le_mode_stop_ne_supprime_rien():
    proc = _run(WRAPPER, "stop")
    assert proc.returncode == 0, proc.stderr
    assert "PAS supprime" in proc.stdout or "pas supprime" in proc.stdout.lower()


# --- 5. le comportement du mode `check` (organe factice) -------------------


def _organe_factice(tmp_path: Path) -> tuple[Path, Path]:
    """Un organe factice qui journalise ses arguments."""
    journal = tmp_path / "organe.log"
    script = tmp_path / "organe.sh"
    script.write_text(
        "#!/usr/bin/env bash\n"
        f'printf "%s\\n" "$*" >> "{journal}"\n'
        "exit 0\n",
        encoding="utf-8",
    )
    script.chmod(script.stat().st_mode | stat.S_IEXEC)
    return script, journal


def _docker_factice(tmp_path: Path, present: bool, running: bool = True) -> Path:
    """Un `docker` factice sur le PATH : absent, ou present et arrete."""
    dossier = tmp_path / "bin"
    dossier.mkdir(exist_ok=True)
    shim = dossier / "docker"
    if not present:
        corps = "#!/usr/bin/env bash\nif [ \"$1\" = \"inspect\" ]; then exit 1; fi\nexit 0\n"
    elif running:
        corps = ("#!/usr/bin/env bash\n"
                 "if [ \"$1\" = \"inspect\" ]; then echo true; exit 0; fi\nexit 0\n")
    else:
        corps = ("#!/usr/bin/env bash\n"
                 "if [ \"$1\" = \"inspect\" ]; then echo false; exit 0; fi\nexit 0\n")
    shim.write_text(corps, encoding="utf-8")
    shim.chmod(shim.stat().st_mode | stat.S_IEXEC)
    return dossier


def test_le_mode_check_appelle_l_organe(tmp_path):
    """Le verdict de conformance est celui de l'organe, pas celui du wrapper."""
    organe, journal = _organe_factice(tmp_path)
    bin_dir = _docker_factice(tmp_path, present=True, running=True)
    proc = _run(WRAPPER, "check", env={
        "COURSIA_MAIN_SLOT_SCRIPT": str(organe),
        "COURSIA_MAIN_PREFIX": "coursia-test-jetable",
        "PATH": f"{bin_dir}{os.pathsep}{os.environ.get('PATH', '')}",
    })
    assert proc.returncode == 0, proc.stderr
    assert "--check" in journal.read_text(encoding="utf-8")


def test_un_slot_absent_est_cree_puis_verifie(tmp_path):
    """Le cas du boot : le slot n'existe pas -> creation, puis controle."""
    organe, journal = _organe_factice(tmp_path)
    bin_dir = _docker_factice(tmp_path, present=False)
    master = tmp_path / "master.env"
    master.write_text("GH_RUNNERS_ADMIN_TOKEN=jeton-de-test\n", encoding="utf-8")
    proc = _run(WRAPPER, "check", env={
        "COURSIA_MAIN_SLOT_SCRIPT": str(organe),
        "COURSIA_MAIN_PREFIX": "coursia-test-jetable",
        "COURSIA_MASTER_ENV": str(master),
        "PATH": f"{bin_dir}{os.pathsep}{os.environ.get('PATH', '')}",
    })
    assert proc.returncode == 0, proc.stderr
    appels = journal.read_text(encoding="utf-8")
    assert "--apply" in appels, f"un slot absent doit etre cree : {appels}"
    assert "--check" in appels, f"la creation doit etre suivie d'un controle : {appels}"


def test_un_slot_arrete_est_redemarre_sans_etre_recree(tmp_path):
    """Le jeton d'enregistrement est a usage unique et l'etat du runner vit
    dans le volume de configuration : un slot arrete se REDEMARRE, il ne se
    recree pas."""
    organe, journal = _organe_factice(tmp_path)
    bin_dir = _docker_factice(tmp_path, present=True, running=False)
    proc = _run(WRAPPER, "check", env={
        "COURSIA_MAIN_SLOT_SCRIPT": str(organe),
        "COURSIA_MAIN_PREFIX": "coursia-test-jetable",
        "PATH": f"{bin_dir}{os.pathsep}{os.environ.get('PATH', '')}",
    })
    assert proc.returncode == 0, proc.stderr
    appels = journal.read_text(encoding="utf-8")
    assert "--apply" not in appels, f"un slot arrete ne doit pas etre recree : {appels}"
    assert "--check" in appels


def test_le_mode_start_cree_le_slot_absent(tmp_path):
    organe, journal = _organe_factice(tmp_path)
    bin_dir = _docker_factice(tmp_path, present=False)
    master = tmp_path / "master.env"
    master.write_text("GH_RUNNERS_ADMIN_TOKEN=jeton-de-test\n", encoding="utf-8")
    proc = _run(WRAPPER, "start", env={
        "COURSIA_MAIN_SLOT_SCRIPT": str(organe),
        "COURSIA_MAIN_PREFIX": "coursia-test-jetable",
        "COURSIA_MASTER_ENV": str(master),
        "PATH": f"{bin_dir}{os.pathsep}{os.environ.get('PATH', '')}",
    })
    assert proc.returncode == 0, proc.stderr
    assert "--apply" in journal.read_text(encoding="utf-8")


def test_un_master_env_illisible_est_un_echec_nomme(tmp_path):
    """Pas de secret sans source : l'echec doit nommer la cause."""
    organe, _ = _organe_factice(tmp_path)
    bin_dir = _docker_factice(tmp_path, present=False)
    proc = _run(WRAPPER, "start", env={
        "COURSIA_MAIN_SLOT_SCRIPT": str(organe),
        "COURSIA_MAIN_PREFIX": "coursia-test-jetable",
        "COURSIA_MASTER_ENV": str(tmp_path / "absent.env"),
        "PATH": f"{bin_dir}{os.pathsep}{os.environ.get('PATH', '')}",
    })
    assert proc.returncode != 0
    assert "master.env" in proc.stderr
