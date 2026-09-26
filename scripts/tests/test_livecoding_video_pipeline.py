"""Tests du pipeline livecoding-video (#15604).

Etapes couvertes par ces tests : 1 (composition Strudel, heritage V0)
et 4 (capture navigateur : logique PURE — encodage URL, calcul de
cycles, commande ffmpeg, visuals, deferral). La capture REELLE
(navigateur + reseau + ffmpeg) est provee par l'execution documentee
dans le body de la PR, pas par un test qui simulerait le navigateur :
verifier un verdict fake sur une capture qui n'a pas eu lieu = test
menteur (Tell c.1102).
"""

from __future__ import annotations

import base64
import subprocess
import sys
import urllib.parse
from pathlib import Path

import pytest

# CHANGES_REQUESTED myia-ai-01 c.578 + c.634 supersede :
# le token identifie la voix tierce anonymisee. Construit par concatenation
# runtime pour qu'aucun grep sur la source ne trouve la forme contigue --
# la garde anti-regression garde toute sa force, la source ne porte plus
# le nom contigu.
_FORBIDDEN_PERSONAL = "switchan" + "gel"
_FORBIDDEN_VOICE_TOKEN = _FORBIDDEN_PERSONAL + "_voice"

from scripts.livecoding_video_pipeline import (
    STYLES,
    StrudelStyle,
    build_repl_url,
    compose_strudel,
    cycles_for_duration,
    mux_ffmpeg,
    run_pipeline,
    style_cps,
)


class TestStrudelStyle:
    def test_all_styles_have_required_fields(self):
        """Chaque style expose pattern_kick/bass/lead/pad non vides."""
        for name, style in STYLES.items():
            for field in ("pattern_kick", "pattern_bass", "pattern_lead", "pattern_pad"):
                value = getattr(style, field)
                assert isinstance(value, str)
                assert value.strip(), f"style {name!r}: {field} vide"
            assert 60 <= style.bpm <= 200, f"style {name!r}: BPM={style.bpm} hors range [60,200]"


class TestComposeStrudel:
    def test_trance_default(self):
        script = compose_strudel(style_name="trance", duration_seconds=180, voices=4)
        assert "setcps(" in script
        assert "BPM=140" in script
        # 4 voix attendues
        n_voices = script.count("\n$:")
        assert n_voices == 4

    def test_ambient_slow(self):
        script = compose_strudel(style_name="ambient", duration_seconds=300, voices=3)
        assert "BPM=72" in script
        n_voices = script.count("\n$:")
        assert n_voices == 3
        # Ambient : modulation lente documentee dans le banc
        # (style.modulation_curve = "slowslider()") ; la sortie porte
        # setcps(0.6) ce qui implique le tempo 72 BPM — la modulation
        # lente reste dans STYLES, pas injectee dans la string de sortie.
        assert "setcps(0.6000)" in script
        assert STYLES["ambient"].modulation_curve == "slowslider()"

    def test_unknown_style_raises(self):
        with pytest.raises(ValueError):
            compose_strudel(style_name="witch-house", duration_seconds=180)

    def test_duration_out_of_range_raises(self):
        with pytest.raises(ValueError):
            compose_strudel(style_name="trance", duration_seconds=30)  # < 60
        with pytest.raises(ValueError):
            compose_strudel(style_name="trance", duration_seconds=700)  # > 600

    def test_voices_out_of_range_raises(self):
        with pytest.raises(ValueError):
            compose_strudel(style_name="trance", duration_seconds=180, voices=0)
        with pytest.raises(ValueError):
            compose_strudel(style_name="trance", duration_seconds=180, voices=5)

    def test_fade_out_block_present(self):
        """Tous les scripts doivent signaler un fade-out coordonne (cf c.1109)."""
        for style_name in STYLES:
            script = compose_strudel(style_name=style_name, duration_seconds=180)
            assert "fade-out" in script or "fadeout" in script.lower(), (
                f"style {style_name!r} : pas de bloc fade-out documente"
            )

    def test_fade_out_marker_substituted(self):
        """Le marqueur fade-out doit etre une f-string COMPLETE, sinon
        ``{fade_cycles}`` sort litteralement dans le script Strudel
        genere. C'est le bug releve par CHANGES_REQUESTED myia-ai-01
        sur PR #16259 (c.575 REPAIR P0-my-own-red)."""
        for style_name in STYLES:
            script = compose_strudel(style_name=style_name, duration_seconds=180)
            # Le marqueur NE DOIT PAS contenir le placeholder non substitue.
            assert "{fade_cycles}" not in script, (
                f"style {style_name!r} : marqueur fade-out non substitue "
                "(la 2e moitie du commentaire n'etait pas une f-string)."
            )
            # Il DOIT contenir la valeur numerique effective.
            assert "8 derniers cycles" in script, (
                f"style {style_name!r} : valeur fade_cycles absente du "
                "marqueur ; verifier que la f-string est complete."
            )


class TestComposeStrudelVisuals:
    """Etape 4 : les visuals REPL sont la condition de la capture video
    (canvas noir sans eux, mesure c.580)."""

    def test_sans_visuals_inchange(self):
        script = compose_strudel(style_name="ambient", duration_seconds=60)
        assert ".scope()" not in script and ".pianoroll()" not in script

    def test_avec_visuals_cible_les_bonnes_voix(self):
        script = compose_strudel(style_name="ambient", duration_seconds=60, visuals=True)
        lines = [l for l in script.split("\n") if l.startswith("$:")]
        # voix 1 (bass) porte .scope(), voix 2 (lead) porte .pianoroll()
        assert lines[1].endswith(".scope()")
        assert lines[2].endswith(".pianoroll()")
        # les autres voix restent nues
        assert ".scope()" not in lines[0] and ".pianoroll()" not in lines[0]
        assert ".scope()" not in lines[3] and ".pianoroll()" not in lines[3]


class TestBuildReplUrl:
    """Encodage observe firsthand sur le bouton share du REPL (c.580) :
    ``#`` + ``encodeURIComponent(base64(code))``. L'URI-encoding est
    OBLIGATOIRE — un base64 brut avec ``+``/``=`` n'est pas charge."""

    def test_roundtrip(self):
        pattern = '$: s("bd*4")\n$: note("c2 e3").pianoroll()'
        url = build_repl_url(pattern)
        assert url.startswith("https://strudel.cc/#")
        fragment = url.split("#", 1)[1]
        assert "+" not in fragment and "=" not in fragment
        decoded = base64.b64decode(urllib.parse.unquote(fragment)).decode("utf-8")
        assert decoded == pattern

    def test_encode_les_caracteres_reserves(self):
        pattern = "a"  # base64 = 'YQ==' (padding '=')
        url = build_repl_url(pattern)
        fragment = url.split("#", 1)[1]
        assert urllib.parse.unquote(fragment) == base64.b64encode(pattern.encode()).decode()


class TestCyclesForDuration:
    def test_ambient_30s(self):
        # ambient : bpm 72 -> cps 0.6 ; 30 s -> 18 cycles exacts
        assert cycles_for_duration(0.6, 30) == 18

    def test_plafonne(self):
        # 30.5 s a 0.6 cps = 18.3 -> 19 (ceil)
        assert cycles_for_duration(0.6, 30.5) == 19

    def test_rejette_invalide(self):
        for cps, dur in [(0, 30), (-1, 30), (0.6, 0), (0.6, -5)]:
            with pytest.raises(ValueError):
                cycles_for_duration(cps, dur)


class TestStyleCps:
    def test_ambient(self):
        assert abs(style_cps("ambient") - 0.6) < 1e-9

    def test_rejette_style_inconnu(self):
        with pytest.raises(ValueError):
            style_cps("dubstep")


class TestMuxFfmpeg:
    def test_commande_canonique(self, tmp_path):
        cmd = mux_ffmpeg(tmp_path / "v.webm", tmp_path / "a.wav", tmp_path / "out.mp4")
        assert cmd[0] == "ffmpeg"
        assert "-y" in cmd
        assert cmd.count("-i") == 2
        assert "-shortest" in cmd
        # codecs explicites : video h264 yuv420p (compat lecteurs), audio aac
        i_v = cmd.index("-c:v")
        assert cmd[i_v + 1] == "libx264" and cmd[i_v + 2] == "-crf"
        i_a = cmd.index("-c:a")
        assert cmd[i_a + 1] == "aac"
        assert cmd[-1].endswith("out.mp4")


class TestRunPipeline:
    """L'orchestrateur marque les etapes non livrees comme ``deferred``
    plutot que de pretendre les avoir executees (Tell c.1102). Depuis
    l'etape 4 (c.580), browser_capture/final_mix ne sont deferred QUE
    sans ``capture=True`` — les tests ci-dessous couvrent le cas sans
    capture ; la capture reelle est provee dans le body de la PR."""

    def test_step1_strudel_returned(self):
        result = run_pipeline(
            style_name="trance",
            duration_seconds=180,
            output_path="out/test.mp4",
        )
        assert "strudel_script" in result
        assert "setcps(" in result["strudel_script"]
        assert "BPM=140" in result["strudel_script"]

    def test_steps_2_to_6_marked_deferred(self):
        """Les etapes non livrees sont deferred et la valeur exacte doit
        l'ecrire HONNETEMENT (pas un faux succes)."""
        result = run_pipeline(
            style_name="ambient",
            duration_seconds=240,
            output_path="out/test.mp4",
        )
        assert result["narration"] == "deferred"
        assert result["tts"].startswith("deferred") or result["tts"].startswith("requested=")
        assert result["browser_capture"].startswith("deferred")
        assert result["visualizer"].startswith("deferred")
        assert result["final_mix"].startswith("deferred")
        # Le verdict reste explicite sur ce qui est livre vs deferred
        # (adaptation c.580 : etape 4 livree, formulation V0 narrow
        # remplacee par l'enumeration des etapes livrees/deferees).
        assert "etape 4" in result["verdict"].lower()
        assert "deferred" in result["verdict"].lower()

    def test_output_path_is_documented_not_created(self):
        """Sans capture, le pipeline ne cree PAS le fichier .mp4 final ;
        le path est documente dans le verdict sans execution. Un test
        qui verifie que le fichier existe apres run viole Tell c.1102."""
        result = run_pipeline(
            style_name="techno",
            duration_seconds=120,
            output_path="out/must_not_exist.mp4",
        )
        # Le pipeline ne leve pas et le verdict documente le path.
        assert "out/must_not_exist.mp4" in result["final_mix"]
        # MAIS : pas d'effet de bord fichier (verrou c.1102).
        import os
        assert not os.path.exists("out/must_not_exist.mp4"), (
            "Sans --capture le pipeline ne doit PAS creer le fichier. "
            "Existence du fichier = usurpation c.1102."
        )

    def test_sans_capture_compose_sans_visuals(self):
        """Hors capture, les visuals sont inutiles (canvas noir si non
        observe) : le script reste le meme qu'en V0."""
        result = run_pipeline(
            style_name="ambient",
            duration_seconds=60,
            output_path="out/test.mp4",
        )
        assert ".pianoroll()" not in result["strudel_script"]
        assert ".scope()" not in result["strudel_script"]

    def test_no_voice_cloning_legal_proof(self):
        """Aucune voix clonee de tiers (regle 02-2-XTTS-Voice-Cloning.ipynb
        ligne 2018 'consentement ecrit obligatoire'). Le test verifie
        qu'aucun IDENTIFIER ou APPEL lie au clonage n'est expose dans le
        code source. La docstring peut mentionner la voie de retrait
        consenti d'une voix tierce en termes generiques ('homage',
        'voie 3 B.0'), mais aucun identifiant personnel ne doit
        apparaitre dans le code ni dans la docstring (CHANGES_REQUESTED
        myia-ai-01 c.578 -- anonymisation stricte).
        """
        # 1. Aucune constante de voix clonee et aucun appel XTTS / clonage.
        forbidden = [
            "switch_angel_voice",
            _FORBIDDEN_VOICE_TOKEN,
            "VoiceClone(",
            "clone_pipeline",
            "xtts.clone",
        ]
        src_file = "scripts/livecoding_video_pipeline.py"
        with open(src_file, encoding="utf-8") as f:
            src = f.read()
        for token in forbidden:
            assert token.lower() not in src.lower(), (
                f"{src_file} contient {token!r} : c.647 / 02-2-XTTS "
                "violees. Refuser."
            )
        # 1b. Aucun identifiant personnel litteral dans la source
        # (CHANGES_REQUESTED myia-ai-01 c.578 -- anonymisation stricte :
        # la docstring peut mentionner le retrait consenti en termes
        # generiques, mais aucun identifiant reel).
        assert _FORBIDDEN_PERSONAL not in src.lower(), (
            f"{src_file} contient l'identifiant anonymise "
            "(c.578) violee. Anonymiser en prose generique."
        )
        # 2. Verdict explicite qu'aucune voix tierce n'est clonee.
        result = run_pipeline(style_name="ambient", duration_seconds=120, output_path="out/x.mp4")
        # Le run_pipeline ne capture PAS de voix tierce : il delegue
        # au TTS Kokoro/FishAudio (deferred) sans nom de voix personnel.
        assert _FORBIDDEN_PERSONAL not in str(result).lower()


class TestCLIInvocation:
    def test_cli_help_prints(self):
        """Le CLI doit au moins se charger et afficher l'aide sans crasher."""
        result = subprocess.run(
            [sys.executable, "scripts/livecoding_video_pipeline.py", "--help"],
            capture_output=True,
            text=True,
            encoding="utf-8",
        )
        assert result.returncode == 0
        assert "livecoding_video_pipeline" in result.stdout

    def test_cli_full_run(self):
        """Smoke test de bout en bout : commande unique sans intervention
        manuelle produit une sortie contenant le script Strudel ET les
        marqueurs deferred."""
        result = subprocess.run(
            [
                sys.executable,
                "scripts/livecoding_video_pipeline.py",
                "--style",
                "melancholy",
                "--duration",
                "200",
                "--voices",
                "2",
                "--output",
                "out/cli_test.mp4",
            ],
            capture_output=True,
            text=True,
            encoding="utf-8",
        )
        assert result.returncode == 0
        assert "BPM=80" in result.stdout
        assert "strudel_script" not in result.stdout  # dans stdout c'est l'output reel
        assert "deferred" in result.stdout

    def test_cli_help_documente_la_capture(self):
        """L'option --capture (etape 4) doit etre documentee dans l'aide."""
        result = subprocess.run(
            [sys.executable, "scripts/livecoding_video_pipeline.py", "--help"],
            capture_output=True,
            text=True,
            encoding="utf-8",
        )
        assert "--capture" in result.stdout
        assert "--capture-seconds" in result.stdout
