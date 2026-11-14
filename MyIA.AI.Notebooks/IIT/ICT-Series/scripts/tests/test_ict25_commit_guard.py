"""Test du contrat de la garde de commit ICT-25 (prevol + surveillance de run).

Ce que ce test prouve
---------------------
  1. `commit_status` lit la marge **et** le plafond de commit du siege, et le
     plafond n'est jamais inferieur a la marge disponible.
  2. `CommitStatus.describe()` dit le plafond quand il est mesurable et le dit
     absent quand il ne l'est pas -- la telemetrie ne fabrique pas un chiffre.
  3. `CommitWatch.maybe_sample` n'echantillonne qu'aux steps de la periode.
  4. Il conserve la marge **minimale** observee sur toute la duree du run.
  5. Il leve `CommitGuardAbort` sous le plancher de run -- la garde de prevol
     seule ne protegeait pas un bras ne pendant une heure creuse (#24674).
  6. Il ne coupe pas a la valeur exacte du plancher (comparaison stricte : un
     plancher doit se lire « sous », pas « sous ou egal », sinon la valeur
     nommee dans l'aide n'est pas la valeur respectee).
  7. Une mesure impossible ne coupe jamais le run et n'avertit **qu'une fois**
     (marshaler un avertissement par step noierait le journal du trainer).
  8. Le plancher de run reste sous le seuil de demarrage : sinon tout run sain
     avorte a sa premiere mesure, et la garde devient une panne.
  9. `ict25_arms.py` branche effectivement la garde : import du module,
     callback passe au trainer, options de CLI, et champs de telemetrie dans
     l'artefact -- plus le refus des planchers incoherents et la trace d'arret
     (review #24711, points 3-4).
 10. Sous Linux la grandeur lue suit le mode ``vm.overcommit_memory`` : le
     commit (``CommitLimit``/``Committed_AS``) en mode strict 2, seul mode ou le
     noyau l'applique ; la memoire disponible (``MemAvailable``+``SwapFree``)
     en modes 0, 1 ou inconnu -- cas mesure sur les runners d'ai-01 (#24800).

Le test n'a **aucune dependance lourde** (ni torch, ni transformers) : il
tourne partout, y compris en CI sans GPU. Il est executable par pytest et
directement (`python test_ict25_commit_guard.py`).

Issue : #24674 (suite de #24180).
"""
import sys
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from ict25_commit_guard import (  # noqa: E402
    DEFAULT_MIN_RUN_HEADROOM_GO,
    DEFAULT_MIN_START_HEADROOM_GO,
    CommitGuardAbort,
    CommitStatus,
    CommitWatch,
    _linux_status_from_text,
    commit_status,
)

GO = 1024 ** 3


def _stub_status(*avail_go, limit_go=80.0):
    """Fabrique un status_fn qui rend les valeurs donnees, dans l'ordre."""
    valeurs = list(avail_go)
    appels = {"n": 0}

    def _fn():
        appels["n"] += 1
        if not valeurs:
            return None
        valeur = valeurs.pop(0)
        if valeur is None:
            return None
        plafond = None if limit_go is None else int(limit_go * GO)
        return CommitStatus(int(valeur * GO), plafond)

    _fn.appels = appels
    return _fn


def test_status_measurable_on_this_platform():
    statut = commit_status()
    if sys.platform == "win32":
        # Sur Windows la mesure est toujours disponible : un None signale une
        # structure MEMORYSTATUSEX mal dimensionnee (GlobalMemoryStatusEx rend
        # alors ERROR_INVALID_PARAMETER 87), pas une limite de la plateforme.
        # Ce defaut a ete introduit puis attrape ici le 2026-11-04 : la garde
        # se declarait « non mesurable » sur un siege ou elle mesure tres bien.
        assert statut is not None, "GlobalMemoryStatusEx n'a rien rendu sur win32"
    if statut is None:
        print("  (plateforme sans mesure de commit : contrat teste sur stubs)")
        return
    # La marge nulle est un ETAT REEL, pas un defaut de mesure : sous Linux la
    # garde lit ``CommitLimit - Committed_AS`` et **clampe a 0** une valeur qui
    # peut etre negative quand l'overcommit est autorise (``Committed_AS``
    # depasse alors ``CommitLimit``). C'est precisement l'etat que la garde
    # existe pour detecter -- l'exiger strictement positif faisait echouer la
    # suite des qu'un runner heberge etait charge, et rougissait des PR qui ne
    # touchaient pas ce module (#24457, #24640, mesure 2026-11-05).
    #
    # Ce qui reste verifie, et qui n'est pas vacant : le zero doit venir du
    # clamp sur une comptabilite de commit reellement lue, jamais d'une lecture
    # cassee qui rendrait 0 par accident.
    if statut.avail_bytes == 0 and sys.platform.startswith("linux"):
        meminfo = Path("/proc/meminfo")
        if meminfo.is_file():
            valeurs = {}
            for ligne in meminfo.read_text(encoding="utf-8", errors="replace").splitlines():
                cle, sep, reste = ligne.partition(":")
                if sep:
                    valeurs[cle] = reste.split()
            assert "CommitLimit" in valeurs and "Committed_AS" in valeurs, (
                "marge nulle alors que le noyau ne publie pas la comptabilite "
                f"de commit : lecture cassee, pas un etat du siege -- {statut}"
            )
            limite = int(valeurs["CommitLimit"][0]) * 1024
            engage = int(valeurs["Committed_AS"][0]) * 1024
            assert engage >= limite, (
                f"marge nulle sans sur-engagement : limite={limite} engage={engage}"
            )
            print(f"  (marge nulle assumee : engage {engage} >= limite {limite})")
    if statut.avail_bytes > 0:
        assert statut.limit_bytes is None or statut.limit_bytes >= statut.avail_bytes, (
            f"plafond {statut.limit_bytes} < marge {statut.avail_bytes}"
        )


def test_linux_sur_engagement_clampe_a_zero():
    """Sous-engagement depasse : la marge est nulle, pas negative ni inventee."""
    texte = (
        "MemTotal:       16000000 kB\n"
        "CommitLimit:     8000000 kB\n"
        "Committed_AS:   12000000 kB\n"
    )
    # Le clamp n'existe qu'en mode strict (#24801) : hors mode 2, la marge se
    # lit par MemAvailable + SwapFree, absents de ce texte.
    statut = _linux_status_from_text(texte, overcommit_mode=2)
    assert statut is not None, "une comptabilite de commit presente doit se lire"
    assert statut.avail_bytes == 0, f"marge attendue 0 (clamp), lu {statut}"
    assert statut.limit_bytes == 8_000_000 * 1024, statut.limit_bytes
    assert statut.used_pct == 100.0, statut.used_pct


def test_describe_with_and_without_limit():
    avec = CommitStatus(int(4.2 * GO), int(79.6 * GO))
    texte = avec.describe()
    assert "4.2 Go" in texte and "79.6 Go" in texte, texte
    assert "94.7" in texte or "94.8" in texte, f"pourcentage attendu ~94,7 : {texte}"

    sans = CommitStatus(int(7.5 * GO), None)
    texte = sans.describe()
    assert "7.5 Go" in texte and "plafond non mesurable" in texte, texte
    assert sans.used_pct is None


def test_describe_with_zero_limit_does_not_raise():
    # limite = 0 : pas un plafond, mais limit_gb vaut alors 0.0 (pas None) --
    # l'ancien ``is None`` formatat used_pct=None avec :.1f => TypeError au
    # moment precis ou la garde doit parler (review #24711, point 2).
    plafond_nul = CommitStatus(int(4.2 * GO), 0)
    assert plafond_nul.used_pct is None
    texte = plafond_nul.describe()
    assert "4.2 Go" in texte and "plafond non mesurable" in texte, texte


def test_watch_ignores_off_period_steps():
    fn = _stub_status(9.0)
    watch = CommitWatch(min_run_headroom_go=4.0, every_steps=5, status_fn=fn,
                        log=lambda m: None)
    assert watch.maybe_sample(1) is None
    assert watch.maybe_sample(4) is None
    assert fn.appels["n"] == 0, "la garde a mesure hors periode"
    statut = watch.maybe_sample(5)
    assert statut is not None and fn.appels["n"] == 1
    assert watch.samples == 1


def test_watch_tracks_min_over_samples():
    fn = _stub_status(18.0, 5.5, 12.0)
    watch = CommitWatch(min_run_headroom_go=4.0, every_steps=1, status_fn=fn,
                        log=lambda m: None)
    for step in (1, 2, 3):
        watch.maybe_sample(step)
    assert watch.samples == 3
    assert abs(watch.min_avail_gb - 5.5) < 0.01, watch.min_avail_gb


def test_watch_aborts_below_floor():
    fn = _stub_status(9.0, 3.2)
    messages = []
    watch = CommitWatch(min_run_headroom_go=4.0, every_steps=1, status_fn=fn,
                        log=messages.append)
    watch.maybe_sample(1)
    leve = False
    try:
        watch.maybe_sample(2)
    except CommitGuardAbort as exc:
        leve = True
        texte = str(exc)
    assert leve, "la garde n'a pas leve sous le plancher"
    assert "3.2 Go" in texte and "4.0 Go" in texte, texte
    assert watch.abort_reason is not None
    assert watch.summary()["aborted"] is True
    assert any("ARRET DE LA GARDE" in m for m in messages), messages


def test_watch_does_not_abort_at_exact_floor():
    fn = _stub_status(4.0)
    watch = CommitWatch(min_run_headroom_go=4.0, every_steps=1, status_fn=fn,
                        log=lambda m: None)
    statut = watch.maybe_sample(1)
    assert statut is not None, "la garde a coupe a la valeur exacte du plancher"
    assert watch.summary()["aborted"] is False


def test_watch_unmeasurable_warns_once_and_never_aborts():
    fn = _stub_status(None, None, None)
    messages = []
    watch = CommitWatch(min_run_headroom_go=4.0, every_steps=1, status_fn=fn,
                        log=messages.append)
    for step in (1, 2, 3):
        assert watch.maybe_sample(step) is None
    assert watch.samples == 0
    assert watch.min_avail_gb is None
    avertissements = [m for m in messages if "non mesurable" in m]
    assert len(avertissements) == 1, messages
    assert watch.summary()["aborted"] is False


def test_summary_shape():
    watch = CommitWatch(min_run_headroom_go=6.0, every_steps=10,
                        status_fn=_stub_status(7.0), log=lambda m: None)
    watch.maybe_sample(10)
    resume = watch.summary()
    for cle in ("samples", "min_avail_go", "min_run_headroom_go", "every_steps",
                "aborted", "abort_reason"):
        assert cle in resume, f"cle manquante dans le resume : {cle}"
    assert resume["samples"] == 1
    assert resume["min_run_headroom_go"] == 6.0
    assert resume["every_steps"] == 10


def test_every_steps_must_be_positive():
    leve = False
    try:
        CommitWatch(every_steps=0)
    except ValueError:
        leve = True
    assert leve, "une periode nulle doit etre refusee"


def test_run_floor_below_start_threshold():
    assert 0 < DEFAULT_MIN_RUN_HEADROOM_GO < DEFAULT_MIN_START_HEADROOM_GO, (
        f"plancher de run {DEFAULT_MIN_RUN_HEADROOM_GO} Go vs seuil de "
        f"demarrage {DEFAULT_MIN_START_HEADROOM_GO} Go"
    )


def test_linux_status_reads_commit_accounting():
    # En mode strict (vm.overcommit_memory=2), la grandeur du contrat est le
    # COMMIT (CommitLimit / Committed_AS), que le noyau applique : la meme que
    # sous Windows (review #24711, point 1).
    from ict25_commit_guard import _linux_status_from_text

    meminfo_commit = (
        "MemTotal:       32613564 kB\n"
        "MemFree:        12000000 kB\n"
        "MemAvailable:   20000000 kB\n"
        "SwapTotal:       8388604 kB\n"
        "SwapFree:        8000000 kB\n"
        "CommitLimit:    41000772 kB\n"
        "Committed_AS:   33423360 kB\n"
    )
    statut = _linux_status_from_text(meminfo_commit, overcommit_mode=2)
    assert statut is not None
    attendu_avail = (41000772 - 33423360) * 1024
    assert statut.avail_bytes == attendu_avail, (
        f"avail {statut.avail_bytes} != CommitLimit - Committed_AS ({attendu_avail})"
    )
    assert statut.limit_bytes == 41000772 * 1024

    # Noyau sans comptabilite de commit : repli par memoire disponible,
    # grandeur differente, assumee.
    meminfo_sans_commit = (
        "MemTotal:       32613564 kB\n"
        "MemAvailable:   20000000 kB\n"
        "SwapTotal:       8388604 kB\n"
        "SwapFree:        8000000 kB\n"
    )
    statut = _linux_status_from_text(meminfo_sans_commit, overcommit_mode=2)
    assert statut is not None
    assert statut.avail_bytes == (20000000 + 8000000) * 1024
    assert statut.limit_bytes == (32613564 + 8388604) * 1024

    assert _linux_status_from_text("MemTotal: 1 kB\n") is None


def test_linux_status_ignores_unenforced_commit_limit():
    # Hors mode strict, CommitLimit n'est applique par personne : Committed_AS
    # le depasse sans qu'aucune allocation n'echoue. Valeurs mesurees le 05/11
    # sur la VM WSL des runners d'ai-01 (vm.overcommit_memory=1) : la lecture
    # par le commit rendait 0 octet de marge et rougissait main (#24800), alors
    # que 64,8 Gio de memoire restaient disponibles.
    from ict25_commit_guard import _linux_status_from_text

    meminfo_ai01 = (
        "MemTotal:       131901476 kB\n"
        "MemAvailable:   67974788 kB\n"
        "SwapTotal:      33554432 kB\n"
        "SwapFree:       17893596 kB\n"
        "CommitLimit:    99505168 kB\n"
        "Committed_AS:   112841676 kB\n"
    )
    attendu = (67974788 + 17893596) * 1024
    plafond = (131901476 + 33554432) * 1024
    for mode in (0, 1, None):
        statut = _linux_status_from_text(meminfo_ai01, overcommit_mode=mode)
        assert statut is not None, f"mode {mode} : aucune mesure"
        assert statut.avail_bytes == attendu, (
            f"mode {mode} : avail {statut.avail_bytes} != MemAvailable + "
            f"SwapFree ({attendu})"
        )
        assert statut.limit_bytes == plafond, f"mode {mode} : plafond"
    # Temoin : le meme texte en mode strict rend bien la marge de commit nulle.
    strict = _linux_status_from_text(meminfo_ai01, overcommit_mode=2)
    assert strict is not None and strict.avail_bytes == 0, strict


def test_ict25_arms_wires_the_guard():
    source = (SCRIPTS / "ict25_arms.py").read_text(encoding="utf-8")
    preuves = {
        "import du module pur": "from ict25_commit_guard import",
        "callback passe au trainer": "callbacks=[_CommitGuardCallback(watch)]",
        "option de plancher de run": "--min-run-headroom-go",
        "option de periode": "--guard-every-steps",
        "telemetrie de run dans l'artefact": '"commit_guard":',
        "plafond dans l'artefact": '"commit_limit_go":',
        "marge minimale par graine": '"commit_headroom_min_go":',
        "sortie explicite sur arret": "except CommitGuardAbort as exc:",
        "refus de planchers incoherents": "min_run_headroom_go >= args.min_commit_headroom_go",
        "trace d'arret ecrite sur abort": "_write_abort_trace(seed_path, seed, exc)",
        "portee du bloc commit_guard dite": '"scope": "derniere graine du lot"',
    }
    manquants = [nom for nom, motif in preuves.items() if motif not in source]
    assert not manquants, f"branchement absent de ict25_arms.py : {manquants}"


def main():
    echecs = 0
    for nom, fonction in sorted(globals().items()):
        if nom.startswith("test_") and callable(fonction):
            try:
                fonction()
            except Exception as exc:  # noqa: BLE001
                echecs += 1
                print(f"ECHEC {nom}: {type(exc).__name__}: {exc}")
            else:
                print(f"ok    {nom}")
    print(f"\n{len([n for n in globals() if n.startswith('test_')]) - echecs} "
          f"test(s) vert(s), {echecs} echec(s)")
    return 1 if echecs else 0


if __name__ == "__main__":
    sys.exit(main())
