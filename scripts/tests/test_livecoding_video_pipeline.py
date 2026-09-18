"""Tests du pipeline livecoding-video V0 narrow (#15604).

Ces tests verifient UNIQUEMENT l'etape 1 livree (composition Strudel)
et l'orchestrateur scaffold (qui marque les autres etapes comme
``deferred``). Verifier un verdict fake sur les etapes 2-6 = violer
Tell c.1102 anti-stonewall : le test qui pretend qu'une capture
navigateur a eu lieu quand elle n'a pas eu lieu est un test menteur.
"""

from __future__ import annotations

import subprocess
import sys

import pytest

from scripts.livecoding_video_pipeline import (
    STYLES,
    StrudelStyle,
    compose_strudel,
    run_pipeline,
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


class TestRunPipeline:
    """L'orchestrateur marque les etapes non livrees comme ``deferred``
    plutot que de pretendre les avoir executees (Tell c.1102)."""

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
        """Les etapes 2-6 sont deferred et la valeur exacte doit l'ecrire
        HONNETEMENT (pas un faux succes)."""
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
        assert "V0 narrow" in result["verdict"]
        assert "c.574+" in result["verdict"]

    def test_output_path_is_documented_not_created(self):
        """V0 narrow ne cree PAS le fichier .mp4 final ; le path est
        documente dans le verdict sans execution. Un test qui verifie
        que le fichier existe apres run viole Tell c.1102 (pretendre
        une sortie qu'on n'a pas produite)."""
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
            "V0 narrow ne doit PAS creer le fichier : c'est la V1+ qui "
            "integre ffmpeg. Existence du fichier = usurpation c.1102."
        )

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
        # Identifiant personnel construit par concatenation (CHANGES_REQUESTED
        # myia-ai-01 c.634) : le test detecte le nom reel sans le porter
        # en litteral contigu dans la source.
        _FORBIDDEN_PERSONAL = "switchan" + "gel"
        forbidden = [
            "switch_angel_voice",
            _FORBIDDEN_PERSONAL + "_voice",
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
        # (CHANGES_REQUESTED myia-ai-01 c.578 / c.634 -- anonymisation
        # stricte : la docstring peut mentionner le retrait consenti en termes
        # generiques, mais aucun identifiant reel).
        assert _FORBIDDEN_PERSONAL not in src.lower(), (
            f"{src_file} contient l'identifiant anonymise : "
            "CHANGES_REQUESTED myia-ai-01 c.578 violee. "
            "Anonymiser en prose generique."
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
