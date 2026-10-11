"""Tests du chien de garde anti-blocage xdist (#16288).

Proprietes sous test, dans l'ordre de ce qu'elles protegent :

1. **Pass-through pur en regime normal** -- le garde recopie la sortie et
   propage le code du fils tel quel. Un garde qui transformerait le verdict
   d'une jambe saine serait pire que le blocage qu'il pretend soigner.
2. **Un vivant n'est pas tue** -- un enfant qui emet regulierement (fils de
   points pytest) traverse une limite d'inactivite sans dommage. C'est le
   garde-fou contre le faux positif, le risque reel d'un detecteur de
   silence.
3. **Un bloque est tue et NOMME** -- la signature mesuree (progression
   ``[99%]`` puis silence, ``node down: gwN``) doit produire un verdict qui
   cite le worker mort et la fenetre de silence, pas seulement un kill.
   C'est le critere d'acceptation de l'issue : le gate nomme aujourd'hui le
   mur, et c'est ce qui fait lire un blocage comme un depassement.
4. **Arme des le demarrage** -- un enfant muet depuis sa naissance (hang de
   collection) est aussi tue : l'armement ne depend pas d'une premiere ligne.
5. **La fraicheur se mesure par OCTET, pas par ligne** (mode 2, run
   35276661841 / PR #16240) : en fin de parcours ``-q``, pytest emet ses
   points SANS saut de ligne tant que la ligne de ~72 caracteres n'est pas
   pleine. Un garde qui n'ecouterait que les lignes completes croit a un
   silence de 8 min et tue un run a ``[99%]`` en train de finir -- le
   flush d'EOF du kill avait laisse sur le log une ligne partielle de 43
   resultats emis PENDANT la fenetre dite muette. Des octets vivants sans
   ``\\n`` doivent donc maintenir la fraicheur ; et un vrai blocage (zero
   octet) doit toujours mourir.

Les enfants sont des ``python -c`` mono-processus : aucun xdist requis
(l'issue note le defaut propre a la classe de runner ; le garde doit etre
testable sans reproduire la mort d'un vrai worker).
"""

from __future__ import annotations

import re
import subprocess
import sys
import textwrap
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import xdist_watchdog as wd  # noqa: E402


def _child(code: str) -> list[str]:
    return [sys.executable, "-c", textwrap.dedent(code)]


def _run_watchdog(argv: list[str], idle_limit: float):
    lines: list[str] = []
    verdicts: list[str] = []

    def echo(line: str) -> None:
        lines.append(line.rstrip("\n"))

    def emit(message: str) -> None:
        verdicts.append(message)

    code = wd.run(argv, idle_limit, echo=echo, emit=emit)
    return code, "\n".join(lines), "\n".join(verdicts)


def test_passthrough_succes_recopie_et_propage():
    code, out, verdict = _run_watchdog(
        _child("""
            for i in range(3):
                print("ligne", i)
            raise SystemExit(0)
        """),
        idle_limit=10.0,
    )
    assert code == 0
    assert "ligne 0" in out and "ligne 2" in out
    assert verdict == ""


def test_passthrough_echec_propage_le_code():
    code, _, verdict = _run_watchdog(
        _child("raise SystemExit(7)"), idle_limit=10.0
    )
    assert code == 7
    assert verdict == ""


def test_vivant_regulier_non_tue():
    # Emet toutes les 0,3 s pendant ~2,4 s avec une limite a 1,0 s :
    # si le garde mesurait n'importe quoi d'autre que le silence de
    # sortie, il tuerait ici.
    code, out, verdict = _run_watchdog(
        _child("""
            import time
            for i in range(8):
                print("progress", i, flush=True)
                time.sleep(0.3)
            raise SystemExit(0)
        """),
        idle_limit=1.0,
    )
    assert code == 0
    assert "XDIST-WATCHDOG" not in out
    assert verdict == ""


def test_bloque_apres_progression_tue_et_nomme_le_worker():
    # La signature exacte de l'issue : [99%], node down gw3, puis silence.
    code, out, verdict = _run_watchdog(
        _child("""
            print("....s....s.. [ 99%]", flush=True)
            print("[gw3] node down: Not properly terminated", flush=True)
            import time
            time.sleep(300)
        """),
        idle_limit=1.0,
    )
    assert code == wd.EXIT_BLOCKED
    assert "BLOQUE" in verdict
    assert "gw3" in verdict
    assert "99%" in verdict
    assert "limite 1 s" in verdict
    assert "XDIST-WATCHDOG" not in out  # le verdict ne pollue pas la sortie pilote


def test_fin_de_parcours_points_partiels_non_tue():
    # Mode 2, run 35276661841 : des octets vivants SANS \n (points de fin
    # de parcours -q) doivent maintenir la fraicheur. Un garde qui
    # n'ecouterait que les lignes completes croirait a un silence et
    # tuerait ce run a 1,0 s de limite -- c'est exactement le faux
    # positif qui a bloque la PR #16240 a [99%].
    code, out, verdict = _run_watchdog(
        _child("""
            import sys, time
            for i in range(16):
                sys.stdout.write(".")
                sys.stdout.flush()
                time.sleep(0.15)
            raise SystemExit(0)
        """),
        idle_limit=1.0,
    )
    assert code == 0
    assert "XDIST-WATCHDOG" not in verdict
    assert "." in out


def test_fragment_final_sans_saut_de_ligne_recopie():
    # Pass-through du fragment final : le dernier chunk sans \n doit etre
    # recopie a l'EOF. La ligne partielle de 43 resultats du run
    # 35276661841 n'aurait jamais du etre invisible jusqu'au kill.
    code, out, verdict = _run_watchdog(
        _child("""
            import sys
            print(".... [ 99%]", flush=True)
            sys.stdout.write("...............s...........................")
            sys.stdout.flush()
            raise SystemExit(0)
        """),
        idle_limit=10.0,
    )
    assert code == 0
    assert "[ 99%]" in out
    assert "...............s" in out
    assert verdict == ""


def test_bloque_apres_fragment_partiel_tue_quand_meme():
    # Garde-fou anti-regression : la fraicheur par octet ne doit pas
    # epargner les vrais blocages. Signature [99%] + worker mort, un
    # dernier fragment partiel, puis ZERO octet : le kill doit partir
    # (fenetre comptee depuis le DERNIER OCTET, pas la derniere ligne)
    # et le verdict doit citer les octets pour la forensique.
    code, out, verdict = _run_watchdog(
        _child("""
            import sys, time
            print("............................ [ 99%]", flush=True)
            print("[gw2] node down: Not properly terminated", flush=True)
            sys.stdout.write("..")
            sys.stdout.flush()
            time.sleep(300)
        """),
        idle_limit=1.0,
    )
    assert code == wd.EXIT_BLOCKED
    assert "BLOQUE" in verdict
    assert "gw2" in verdict
    assert "99%" in verdict
    assert "octets" in verdict


def test_bloque_muet_des_la_naissance_tue_aussi():
    # Hang de collection : aucune ligne jamais emise. Le garde doit etre
    # arme des le demarrage, pas apres une premiere ligne.
    code, out, verdict = _run_watchdog(
        _child("import time; time.sleep(300)"),
        idle_limit=1.0,
    )
    assert code == wd.EXIT_BLOCKED
    assert "BLOQUE" in verdict
    # Verdict honnete : aucun marqueur gwN vu.
    assert "aucun marqueur" in verdict
    assert "aucune ligne de progression vue" in verdict


def test_replacing_crashed_worker_nomme_aussi():
    # Variante du run 34955819329 : remplacement effectif de gw3, mort de
    # gw4 47 s plus tard -- le marqueur "replacing crashed worker" doit
    # lui aussi nommer le worker dans le verdict.
    code, out, verdict = _run_watchdog(
        _child("""
            print("..... [ 97%]", flush=True)
            print("replacing crashed worker gw4", flush=True)
            import time
            time.sleep(300)
        """),
        idle_limit=1.0,
    )
    assert code == wd.EXIT_BLOCKED
    assert "gw4" in verdict


def test_deux_workers_morts_tous_nommes():
    code, out, verdict = _run_watchdog(
        _child("""
            print("[gw3] node down: Not properly terminated", flush=True)
            print("[gw4] node down: Not properly terminated", flush=True)
            print(".. [ 99%]", flush=True)
            import time
            time.sleep(300)
        """),
        idle_limit=1.0,
    )
    assert code == wd.EXIT_BLOCKED
    assert "gw3" in verdict and "gw4" in verdict


def test_main_mappe_exit_bloque_vers_1(capsys):
    # En CLI, le code 3 (interne, distinct pour le triage) se mappe en 1 :
    # la CI ne doit pas distinguer "bloque" d'un echec par le code seul,
    # mais par le verdict -- et ce verdict n'est lisible que s'il porte le
    # prefixe qui en fait une annotation du check-run (section suivante).
    rc = wd.main(["--idle-limit", "0.5", "--",
                  sys.executable, "-c", "import time; time.sleep(300)"])
    captured = capsys.readouterr()
    assert rc == 1
    assert "XDIST-WATCHDOG" in captured.out
    assert wd.ANNOTATION_PREFIX + wd.VERDICT_PREFIX in captured.out


# --- Legibilite et mise en vigueur du garde -------------------------------
#
# Deux proprietes dont la disparition serait SILENCIEUSE : aucune n'etait
# pinnee avant le 2026-09-21, et ni l'une ni l'autre ne rougit quand on
# retire la protection -- le blocage revient simplement, sans temoin.
#
# Le verdict du garde est la seule surface qui distingue, pour qui n'a que le
# check-run sous les yeux, une mort de session d'un rouge de contenu : quand
# le garde tue (`EXIT_BLOCKED` -> 1), l'etape `Run tests` conclut `failure`
# avec l'annotation generique "Process completed with exit code 1.", et
# `classify_job_deaths.py` retourne `REAL_STEP_FAILURE` des qu'une etape a
# conclu `failure`. Sans le prefixe d'annotation, PLUS RIEN ne nomme le
# blocage dans l'API. Mesure sur le job 106258931264 (2026-09-21) : le
# check-run portait 8 annotations "XDIST-WATCHDOG: ...".


def test_chaque_ligne_de_verdict_est_une_annotation():
    # Toutes les lignes, pas seulement la premiere : une ligne laissee nue
    # serait invisible a l'API, et le lecteur n'aurait qu'un verdict partiel.
    # C'est la mutation que ce test attrape (retirer le prefixe d'UNE ligne).
    code, out, verdict = _run_watchdog(
        _child("""
            print("....s....s.. [ 99%]", flush=True)
            print("[gw3] node down: Not properly terminated", flush=True)
            import time
            time.sleep(300)
        """),
        idle_limit=1.0,
    )
    assert code == wd.EXIT_BLOCKED
    lignes = [ln for ln in verdict.splitlines() if ln.strip()]
    assert lignes, "le blocage doit produire un verdict"
    for ligne in lignes:
        assert ligne.startswith(wd.ANNOTATION_PREFIX), ligne
        assert wd.VERDICT_PREFIX in ligne, ligne
    # Le fait qui sert au triage doit etre dans une ligne ANNOTEE, pas
    # seulement dans le detail : c'est la ligne que l'API expose.
    annotee = [ln for ln in lignes if "gw3" in ln]
    assert annotee, verdict


def test_le_prefixe_est_un_dialecte_du_runner_github():
    # Garde-fou de forme, volontairement etroit. Le runner GitHub accepte
    # `##[error]` (forme heritee Azure DevOps) ET `::error::` : les deux ont
    # ete mesures comme annotant (job 106258931264 : les 8 annotations sont
    # venues de `##[error]`). Une TROISIEME forme -- `[error]`, `#error`,
    # `error:` -- n'annoterait RIEN, et le verdict retomberait au rang de
    # texte de log sans qu'aucun autre test ne rougisse.
    assert wd.ANNOTATION_PREFIX in ("##[error]", "::error::"), (
        "ce prefixe doit etre l'une des deux formes mesurees comme annotant "
        "sur le runner GitHub ; une autre forme rend le verdict invisible a "
        "l'API sans faire rougir quoi que ce soit"
    )


def test_le_workflow_cable_le_garde_autour_de_pytest():
    # Le garde n'existe QUE s'il est invoque : la propriete que ce test
    # protege est la mise en vigueur, pas le code. Une edition de workflow
    # qui retirerait l'enveloppe (`scripts-tests.yml` la porte sur une ligne
    # unique) ramenerait la classe #16288 -- 14 a 17 min de silence puis le
    # mur -- sans qu'aucun test ne rougisse. Precedent de la meme famille :
    # #16422 (une suite de tests ecrite par personne -- cablee nulle part).
    racine = Path(__file__).resolve().parents[2]
    workflow = racine / ".github" / "workflows" / "scripts-tests.yml"
    texte = workflow.read_text(encoding="utf-8")
    assert "scripts/ci/xdist_watchdog.py" in texte, (
        "le garde anti-blocage n'est plus invoque par scripts-tests.yml"
    )
    # La commande surveillee : premier jeton suivant le '--' de l'enveloppe,
    # la continuation de ligne shell (`\` en fin de ligne) autorisant le
    # report sur la ligne suivante. Egalite STRICTE et non appartenance :
    # un test ecrit avec `"pytest" in ...` est satisfait par `echo pas-pytest`
    # -- mutation mesuree, le controle de non-vacuite l'a attrapee.
    enveloppe = re.search(
        r"xdist_watchdog\.py[^\n]*--\s*(?:\\\s*\n\s*)?(\S+)", texte
    )
    assert enveloppe, "invocation du garde introuvable dans scripts-tests.yml"
    assert enveloppe.group(1) == "pytest", (
        "le garde doit envelopper l'invocation pytest de la jambe, pas autre "
        "chose : un garde qui surveille une commande d'un autre genre ne "
        "protege pas la jambe ou le blocage a ete mesure"
    )


def test_regex_marqueurs():
    assert wd.NODE_DOWN_RE.search("[gw3] node down: Not properly terminated")
    assert not wd.NODE_DOWN_RE.search(".... [ 42%]")
    assert wd.REPLACING_RE.search(
        "gw3 replacing crashed worker gw3").group(1) == "gw3"
    assert wd.PROGRESS_RE.search("....ss... [ 99%]")
    assert not wd.PROGRESS_RE.search("[gw3] node down")


def test_kill_tree_posix_fallback_mono_processus():
    # Sur Windows (et en fallback POSIX), le kill vise au minimum le fils
    # direct : le wrapper ne doit pas survivre a son propre kill.
    proc = subprocess.Popen(
        [sys.executable, "-c", "import time; time.sleep(300)"],
        stdout=subprocess.PIPE,
    )
    try:
        wd._kill_tree(proc)
        proc.wait(timeout=15)
        assert proc.poll() is not None
    finally:
        if proc.poll() is None:
            proc.kill()


# Mode 3 (#19915) : crash de collecte xdist (KeyError: <WorkerController>).
# Distinction d'avec le mode 1 (silence) : pytest emet en continu
# "replacing crashed worker gwN" (sortie NON muette) mais aucun progres de
# test n'est jamais vu. Le verdict doit etre COLLECT_CRASH, distinct de
# BLOQUE, et doit nommer le worker en collision.


def test_collect_crash_sans_progres_est_tue_avec_verdict_dedie():
    # Reproduction de la signature #19915 : la sortie porte
    # "replacing crashed worker gw8" puis INTERNALERROR> KeyError:
    # <WorkerController gw8>, sans aucune ligne de progres pytest. Le
    # mode 1 (silence) ne peut pas la detecter -- la sortie n'est pas
    # muette. Le mode 3 doit la tuer avec EXIT_COLLECT_CRASH et un
    # verdict dedie qui nomme le worker en collision.
    code, out, verdict = _run_watchdog(
        _child("""
            import sys
            print("[gw7] node down: Not properly terminated", flush=True)
            print("replacing crashed worker gw7", flush=True)
            print("[gw8] node down: Not properly terminated", flush=True)
            print("replacing crashed worker gw8", flush=True)
            print("INTERNALERROR> Traceback (most recent call last):", flush=True)
            print("INTERNALERROR> KeyError: <WorkerController gw8>", flush=True)
            import time
            time.sleep(300)
        """),
        idle_limit=480.0,
    )
    assert code == wd.EXIT_COLLECT_CRASH
    assert "COLLECT_CRASH" in verdict
    assert "gw8" in verdict


def test_collect_crash_apres_progres_ne_declenche_pas_le_mode_3():
    # Si une ligne de progres pytest a ete observee AVANT le KeyError,
    # ce n'est plus un crash de collecte -- c'est un test defectueux
    # qui a produit une collision tardive. Le mode 3 ne doit PAS tuer :
    # on laisse le run finir normalement (mode 1 ou pas de kill du tout).
    code, out, verdict = _run_watchdog(
        _child("""
            print(".... [ 10%]", flush=True)
            import time
            time.sleep(0.2)
            print("INTERNALERROR> KeyError: <WorkerController gw8>", flush=True)
            time.sleep(0.2)
            print(".... [ 11%]", flush=True)
            time.sleep(0.2)
            print("ok")
        """),
        idle_limit=480.0,
    )
    # Pas de kill mode 3 -- on laisse pytest finir.
    assert code != wd.EXIT_COLLECT_CRASH
    # Pas de verdict mode 3 dans la sortie.
    assert "COLLECT_CRASH" not in verdict


def test_collect_crash_workers_multiples_tous_nommes():
    # Plusieurs workers en collision sur la meme trace : le verdict doit
    # tous les nommer pour le triage.
    code, out, verdict = _run_watchdog(
        _child("""
            print("replacing crashed worker gw8", flush=True)
            print("replacing crashed worker gw9", flush=True)
            print("INTERNALERROR> KeyError: <WorkerController gw8>", flush=True)
            print("INTERNALERROR> KeyError: <WorkerController gw9>", flush=True)
            import time
            time.sleep(300)
        """),
        idle_limit=480.0,
    )
    assert code == wd.EXIT_COLLECT_CRASH
    assert "gw8" in verdict
    assert "gw9" in verdict


def test_collect_crash_enfant_sort_juste_apres_la_signature():
    # Course de cadence (revue Hermes du 2026-10-08, PR #19917). La
    # detection vit dans la boucle, qui teste tous les 0,5 s et `break`
    # des que le fils est mort. Sur le corpus, l'ecart entre la ligne
    # `KeyError` et la sortie du processus va de 0,21 a 0,75 s : le fils
    # sort AVANT la premiere evaluation et le wrapper rendait le code du
    # fils sans verdict. Les trois tests precedents ne peuvent pas voir ce
    # cas -- leurs enfants dorment 300 s, donc la boucle mord toujours.
    # Ici l'enfant sort juste apres la signature, ce qui est le regime
    # reel. La conjonction doit etre re-testee apres la boucle.
    for delay in (0.0, 0.2):
        code, out, verdict = _run_watchdog(
            _child(f"""
                print("replacing crashed worker gw8", flush=True)
                print("INTERNALERROR> KeyError: <WorkerController gw8>", flush=True)
                import time
                time.sleep({delay})
            """),
            idle_limit=480.0,
        )
        assert code == wd.EXIT_COLLECT_CRASH, f"delay={delay}: code={code}"
        assert "COLLECT_CRASH" in verdict, f"delay={delay}: aucun verdict"
        assert "gw8" in verdict, f"delay={delay}: worker non nomme"


def test_regex_collect_crash_matche_et_ancre_gwN():
    # La regex doit capturer le nom du worker et ignorer le bruit autour.
    assert wd.COLLECT_CRASH_RE.search("INTERNALERROR> KeyError: <WorkerController gw8>")
    assert wd.COLLECT_CRASH_RE.search("KeyError: <WorkerController gw12>")
    # Pas de faux positif sur un KeyError d'un autre type
    assert not wd.COLLECT_CRASH_RE.search("KeyError: 'gw8'")
    assert not wd.COLLECT_CRASH_RE.search("KeyError: 42")


def test_exit_collect_crash_mappe_vers_1_via_main(capsys):
    # main() doit mapper EXIT_COLLECT_CRASH (4) vers 1, comme EXIT_BLOCKED (3).
    # La CI ne distingue pas par exit code ; c'est le verdict log qui dit
    # la difference. C'est volontaire (cf docstring de EXIT_COLLECT_CRASH).
    import xdist_watchdog
    # Monkeypatch run() pour qu'il rende EXIT_COLLECT_CRASH sans spawner
    # un sous-processus -- on verifie juste le mapping.
    orig_run = xdist_watchdog.run
    xdist_watchdog.run = lambda *a, **kw: xdist_watchdog.EXIT_COLLECT_CRASH
    try:
        code = xdist_watchdog.main([sys.executable, "-c", "pass"])
    finally:
        xdist_watchdog.run = orig_run
    assert code == 1

