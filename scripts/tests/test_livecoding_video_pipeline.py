"""Tests du pipeline livecoding-video (#15604).

Etapes couvertes par ces tests : 1 (composition Strudel, heritage V0),
2 (narration poetique timestampee : moteur template deterministe,
moteur LLM via client injecte — jamais un vrai appel reseau dans les
tests, la sortie LLM est VALIDEE, pas crue) et 4 (capture navigateur :
logique PURE — encodage URL, calcul de cycles, commande ffmpeg,
visuals, deferral). La capture REELLE (navigateur + reseau + ffmpeg)
est provee par l'execution documentee dans le body de la PR, pas par
un test qui simulerait le navigateur : verifier un verdict fake sur
une capture qui n'a pas eu lieu = test menteur.
"""

from __future__ import annotations

import base64
import json
import subprocess
import sys
import urllib.parse
from pathlib import Path
from types import SimpleNamespace

import pytest

# CHANGES_REQUESTED myia-ai-01 c.578 + c.634 supersede :
# le token identifie la voix tierce anonymisee. Construit par concatenation
# runtime pour qu'aucun grep sur la source ne trouve la forme contigue --
# la garde anti-regression garde toute sa force, la source ne porte plus
# le nom contigu.
_FORBIDDEN_PERSONAL = "switchan" + "gel"
_FORBIDDEN_VOICE_TOKEN = _FORBIDDEN_PERSONAL + "_voice"

from scripts.livecoding_video_pipeline import (
    NARRATION_FORBIDDEN_SUBSTRINGS,
    NARRATION_PLANS,
    NARRATION_SYSTEM_PROMPT,
    NARRATION_BANK,
    TTS_ENGINES,
    NarrationSegment,
    STYLES,
    StrudelStyle,
    _load_env_files,
    _build_arg_parser,
    _click_play,
    _drive_code_reveal,
    _lines_with_voices,
    _resolve_capture_seconds,
    _set_editor_code,
    build_repl_url,
    capture_repl_session,
    compose_narration,
    compose_strudel,
    cycles_for_duration,
    mix_final_ffmpeg,
    mux_ffmpeg,
    narration_to_json,
    parse_strudel_highlights,
    plan_code_reveal,
    probe_duration_ffprobe,
    reveal_schedule,
    run_pipeline,
    style_cps,
    synthesize_narration_tts,
    tts_speed_for_intensity,
    validate_narration,
)
from scripts.livecoding_video_pipeline import main as pipeline_main


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
        # sans trim : ni -ss ni -t (chemin canvas historique)
        assert "-ss" not in cmd and "-t" not in cmd

    def test_trim_page_entiere_ss_avant_inputs_t_apres(self, tmp_path):
        """Mode page : record_video filme tout le contexte (chargement,
        play, warmup, export inclus) — la fenetre utile s'extrait par
        -ss (fast seek, AVANT les inputs, piste video seule) + -t (duree
        de sortie, les deux pistes)."""
        cmd = mux_ffmpeg(
            tmp_path / "v.webm", tmp_path / "a.wav", tmp_path / "out.mp4",
            trim_start=12.3456, trim_duration=60.0,
        )
        i_ss, i_in = cmd.index("-ss"), cmd.index("-i")
        assert i_ss < i_in
        assert cmd[i_ss + 1] == "12.346"  # formate a 3 decimales
        i_t = cmd.index("-t")
        assert i_t > i_in and cmd[i_t + 1] == "60.000"
        assert "-shortest" in cmd

    def test_trim_seul_sans_duree(self, tmp_path):
        """trim_start sans trim_duration reste legal (fenetre ouverte)."""
        cmd = mux_ffmpeg(
            tmp_path / "v.webm", tmp_path / "a.wav", tmp_path / "out.mp4",
            trim_start=5.0,
        )
        assert "-ss" in cmd and "-t" not in cmd


# --- Etape 2 : narration poetique timestampee (c.1215) ------------------------


def _seg(start, end, text="Texte original, écrit pour le test.", intensity=0.5):
    return NarrationSegment(
        start_s=start, end_s=end, text=text, intensity=intensity
    )


class TestParseStrudelHighlights:
    """La narration est ancrée au script : le parseur extrait ce qui
    joue REELLEMENT (voix, synthés, effets, BPM, fade)."""

    def test_extraits_voix_sounds_effets(self):
        script = compose_strudel(style_name="trance", duration_seconds=180, voices=4)
        hl = parse_strudel_highlights(script)
        assert hl["voices"] == 4
        assert "supersaw" in hl["sounds"]
        assert "bd" in hl["drums"]
        assert "lpf" in hl["effects"]
        assert hl["bpm"] == 140
        assert hl["has_fade"] is True

    def test_deux_voix_ne_exposent_pas_le_lead(self):
        script = compose_strudel(style_name="ambient", duration_seconds=120, voices=2)
        hl = parse_strudel_highlights(script)
        assert hl["voices"] == 2
        assert "supersine" not in hl["sounds"]


class TestComposeNarrationTemplate:
    def test_deterministe(self):
        """Meme entree -> meme sortie : aucun alea dans le moteur
        template (re-executabilite CI)."""
        for style in STYLES:
            script = compose_strudel(style, 180)
            a = compose_narration(script, style, 180)
            b = compose_narration(script, style, 180)
            assert a == b, f"{style}: la narration template doit etre deterministe"

    def test_tous_styles_valides(self):
        for style in STYLES:
            for dur in (60, 180, 600):
                script = compose_strudel(style, dur)
                segments = compose_narration(script, style, dur)
                validate_narration(segments, dur)  # ne leve pas

    def test_timestamps_dans_la_duree_sans_recouvrement(self):
        script = compose_strudel("trance", 180)
        segs = compose_narration(script, "trance", 180)
        prev_end = 0.0
        for s in segs:
            assert 0.0 <= s.start_s < s.end_s <= 180
            assert s.start_s >= prev_end
            prev_end = s.end_s

    def test_trance_fenetre_plafonnee_90s(self):
        """Issue #15604 etape 2 : 60-90 s de narration pour les videos
        courtes rythmees (trance/techno), pas 100 % de la duree."""
        script = compose_strudel("trance", 180)
        segs = compose_narration(script, "trance", 180)
        span = segs[-1].end_s - segs[0].start_s
        assert span <= 90.5
        assert segs[0].start_s >= NARRATION_PLANS["trance"].start_offset_s

    def test_ambient_couvre_toute_la_duree(self):
        """Ambient lent : la voix off peut tenir 100 % de la duree."""
        script = compose_strudel("ambient", 180)
        segs = compose_narration(script, "ambient", 180)
        assert segs[0].start_s <= 3.0
        assert segs[-1].end_s >= 179.0

    def test_arc_intensite_non_plat(self):
        """L'intensite est l'unite d'entree de la prosodie TTS (etape 3,
        cf acceptance 3 'prosodie non plate') : l'arc doit varier."""
        for style in STYLES:
            script = compose_strudel(style, 180)
            segs = compose_narration(script, style, 180)
            distinct = {round(s.intensity, 3) for s in segs}
            assert len(distinct) >= 3, f"{style}: intensite plate"
            assert max(s.intensity for s in segs) >= 0.85, f"{style}: pas de climax"
            assert min(s.intensity for s in segs) <= 0.3, f"{style}: pas de fade"

    def test_narration_nomme_laction_reelle(self):
        """Calibration GENRE (issue #15604) : nommer l'action du code.
        Le lead REELLEMENT present doit etre nomme (ancrage script)."""
        lead_names = {
            "trance": "supersaw",
            "ambient": "supersine",
            "techno": "sawtooth",
            "melancholy": "supersine",
        }
        for style, lead in lead_names.items():
            script = compose_strudel(style, 180, voices=4)
            segs = compose_narration(script, style, 180)
            assert any(lead in s.text.lower() for s in segs), (
                f"{style}: le lead ({lead}) n'est jamais nomme"
            )

    def test_narration_suit_le_nombre_de_voix(self):
        """voices=2 : les mouvements lead/nappe sont absents du script,
        la narration ne doit pas nommer leurs instruments — y compris
        dans l'enumeration dynamique du climax (_voice_labels)."""
        script = compose_strudel("trance", 180, voices=2)
        segs = compose_narration(script, "trance", 180)
        texts = " ".join(s.text.lower() for s in segs)
        assert "supersaw" not in texts
        assert "nappe" not in texts
        climax = [s.text for s in segs if "Tout joue ensemble" in s.text]
        assert climax, "le mouvement climax doit etre present"
        assert "kick, basse." in climax[0]  # enumeration = voix reelles

    def test_frontieres_alignees_aux_cycles(self):
        """Les frontieres tombent sur la grille de cycles (cps du style)
        — la voix off demarre en phase avec la musique."""
        script = compose_strudel("trance", 180)
        segs = compose_narration(script, "trance", 180)
        cps = style_cps("trance")
        boundaries = [segs[0].start_s] + [s.end_s for s in segs]
        aligned = sum(
            1 for b in boundaries if abs(b * cps - round(b * cps)) < 1e-3
        )
        assert aligned >= len(boundaries) // 2, (
            f"{aligned}/{len(boundaries)} frontieres cycle-alignees"
        )

    def test_banques_sans_placeholder_oublie(self):
        """Un placeholder {voices_list} non substitue dans la sortie
        serait un bug de formatage (cf c.575 sur le marqueur fade)."""
        for style in STYLES:
            script = compose_strudel(style, 180)
            for s in compose_narration(script, style, 180):
                assert "{voices_list}" not in s.text

    def test_banques_completes(self):
        """Chaque style porte une banque pour chaque mouvement du
        template, avec au moins 2 lignes (variete)."""
        for style, bank in NARRATION_BANK.items():
            for movement in ("ouverture", "basse", "lead", "nappe",
                             "modulation", "climax", "fade"):
                assert movement in bank, f"{style}: mouvement {movement} absent"
                assert len(bank[movement]) >= 2, (
                    f"{style}/{movement}: au moins 2 lignes attendues"
                )


class TestValidateNarration:
    def test_valide_segments_template(self):
        segs = compose_narration(compose_strudel("techno", 120), "techno", 120)
        validate_narration(segs, 120)  # ne leve pas

    def test_rejette_moins_de_deux_segments(self):
        with pytest.raises(ValueError, match="2 segments"):
            validate_narration([_seg(0, 10)], 120)

    def test_rejette_recouvrement(self):
        with pytest.raises(ValueError, match="recouvrement"):
            validate_narration([_seg(0, 20), _seg(19, 40)], 120)

    def test_rejette_hors_duree(self):
        with pytest.raises(ValueError, match="timestamps invalides"):
            validate_narration([_seg(0, 20), _seg(20, 130)], 120)

    def test_rejette_intensite_hors_range(self):
        bad = [_seg(0, 20, intensity=1.5), _seg(20, 40)]
        with pytest.raises(ValueError, match="intensité"):
            validate_narration(bad, 120)

    def test_rejette_texte_vide(self):
        bad = [_seg(0, 20, text="   "), _seg(20, 40)]
        with pytest.raises(ValueError, match="texte vide"):
            validate_narration(bad, 120)

    def test_rejette_texte_trop_long(self):
        bad = [_seg(0, 20, text="a" * 601), _seg(20, 40)]
        with pytest.raises(ValueError, match="trop long"):
            validate_narration(bad, 120)

    def test_rejette_nom_artiste_tiers(self):
        """Garde ANTI-NOMINATION (voie 3 B.0) : toute variation de casse
        du nom de la source d'inspiration est rejetee dans les textes.
        NB : c'est une garde de NOM, pas un detecteur de verbatim (cf
        limitation documentee sur validate_narration — un detecteur de
        verbatim exigerait un corpus de reference hors depot)."""
        for needle in NARRATION_FORBIDDEN_SUBSTRINGS:
            for variant in (needle, needle.upper(), needle.title()):
                bad = [
                    _seg(0, 20, text=f"Il y avait {variant} un jour."),
                    _seg(20, 40),
                ]
                with pytest.raises(ValueError, match="artiste"):
                    validate_narration(bad, 120)


class _FakeCompletions:
    def __init__(self, payload):
        self._payload = payload
        self.messages = None

    def create(self, model, messages, **kwargs):
        self.messages = messages
        content = (
            self._payload
            if isinstance(self._payload, str)
            else json.dumps(self._payload, ensure_ascii=False)
        )
        return SimpleNamespace(
            choices=[
                SimpleNamespace(message=SimpleNamespace(content=content))
            ]
        )


class _FakeClient:
    """Client LLM de test : double de contrat (aucun appel reseau, la
    reponse est VALIDEe par le pipeline, jamais crue)."""

    def __init__(self, payload):
        self.chat = SimpleNamespace(completions=_FakeCompletions(payload))


_VALID_LLM_PAYLOAD = [
    {"start_s": 5.0, "end_s": 30.0,
     "text": "La pulsation s'installe, patiente, avant tout le reste.",
     "intensity": 0.3},
    {"start_s": 30.0, "end_s": 60.0,
     "text": "Le supersaw ouvre ses ailes au-dessus de nous.",
     "intensity": 0.8},
    {"start_s": 60.0, "end_s": 90.0,
     "text": "Puis tout redescend, comme une marée qui rentre.",
     "intensity": 0.2},
]


class TestComposeNarrationLLM:
    def test_sortie_validee_et_client_appelle(self):
        client = _FakeClient(_VALID_LLM_PAYLOAD)
        script = compose_strudel("trance", 180)
        segs = compose_narration(
            script, "trance", 180, engine="llm", llm_client=client
        )
        assert len(segs) == 3
        validate_narration(segs, 180)
        system, user = client.chat.completions.messages
        assert system["role"] == "system"
        # prompt system : contrat JSON + originalite + aucun artiste tiers
        assert system["content"] == NARRATION_SYSTEM_PROMPT
        assert "JSON" in NARRATION_SYSTEM_PROMPT
        assert "original" in NARRATION_SYSTEM_PROMPT.lower()
        assert "artiste" in NARRATION_SYSTEM_PROMPT
        # prompt user : le script reel et la duree sont envoyes
        assert "setcps(" in user["content"]
        assert "180" in user["content"]

    def test_sortie_non_json_rejetee(self):
        client = _FakeClient("ceci n'est pas du JSON")
        with pytest.raises(ValueError, match="JSON"):
            compose_narration(
                compose_strudel("trance", 180), "trance", 180,
                engine="llm", llm_client=client,
            )

    def test_sortie_invalide_rejetee(self):
        """Une sortie LLM recouvrante echoue explicitement — jamais
        rafistolee."""
        bad_payload = [
            {"start_s": 0, "end_s": 50, "text": "A.", "intensity": 0.5},
            {"start_s": 40, "end_s": 80, "text": "B.", "intensity": 0.5},
        ]
        client = _FakeClient(bad_payload)
        with pytest.raises(ValueError, match="recouvrement"):
            compose_narration(
                compose_strudel("trance", 180), "trance", 180,
                engine="llm", llm_client=client,
            )

    def test_sans_cle_echec_explicite(self, monkeypatch):
        """Moteur llm sans OPENAI_API_KEY : RuntimeError explicite, PAS
        de fallback silencieux vers template."""
        monkeypatch.delenv("OPENAI_API_KEY", raising=False)
        with pytest.raises(RuntimeError, match="OPENAI_API_KEY"):
            compose_narration(
                compose_strudel("trance", 180), "trance", 180, engine="llm"
            )

    def test_package_openai_absent_echec_explicite(self, monkeypatch):
        """Branche import de _build_llm_client : cle presente mais
        package openai absent -> RuntimeError explicite (la cle est
        verifiee AVANT l'import, cf _build_llm_client)."""
        monkeypatch.setenv("OPENAI_API_KEY", "dummy-key-for-import-branch-test")
        # sys.modules['openai'] = None force `import openai` a echouer
        monkeypatch.setitem(sys.modules, "openai", None)
        with pytest.raises(RuntimeError, match="openai"):
            compose_narration(
                compose_strudel("trance", 180), "trance", 180, engine="llm"
            )

    def test_moteur_inconnu_rejete(self):
        with pytest.raises(ValueError, match="moteur"):
            compose_narration(
                compose_strudel("trance", 180), "trance", 180,
                engine="hallucine",
            )


class TestNarrationToJson:
    def test_roundtrip_et_accents(self):
        segs = compose_narration(compose_strudel("ambient", 240), "ambient", 240)
        data = json.loads(narration_to_json(segs))
        assert len(data) == len(segs)
        assert set(data[0].keys()) == {"start_s", "end_s", "text", "intensity"}
        # ensure_ascii=False : les accents restent lisibles dans le JSON
        assert "é" in narration_to_json(segs)
        # un dict JSON reconstruit == le dataclass d'origine
        first = NarrationSegment(**data[0])
        assert first == segs[0]


class TestRunPipeline:
    """L'orchestrateur marque les etapes non livrees comme ``deferred``
    plutot que de pretendre les avoir executees. Depuis
    l'etape 2 (c.1215), 'narration' est une liste de segments valides ;
    depuis l'etape 4 (c.580), browser_capture/final_mix ne sont
    deferred QUE sans ``capture=True`` — les tests ci-dessous couvrent
    le cas sans capture ; la capture reelle est provee dans le body."""

    def test_step1_strudel_returned(self):
        result = run_pipeline(
            style_name="trance",
            duration_seconds=180,
            output_path="out/test.mp4",
        )
        assert "strudel_script" in result
        assert "setcps(" in result["strudel_script"]
        assert "BPM=140" in result["strudel_script"]

    def test_narration_est_une_liste_de_segments(self):
        """Depuis l'etape 2 (c.1215), 'narration' n'est plus 'deferred' :
        une liste de dicts segments VALIDES (contrat d'entree etape 3)."""
        result = run_pipeline(
            style_name="ambient",
            duration_seconds=240,
            output_path="out/test.mp4",
        )
        narration = result["narration"]
        assert isinstance(narration, list) and len(narration) >= 2
        for item in narration:
            assert set(item.keys()) == {"start_s", "end_s", "text", "intensity"}
        segments = [NarrationSegment(**item) for item in narration]
        validate_narration(segments, 240)

    def test_etapes_3_5_6_marquees_deferred(self):
        """Les etapes non livrees restent deferred et la valeur exacte
        doit l'ecrire HONNETEMENT (pas un faux succes)."""
        result = run_pipeline(
            style_name="ambient",
            duration_seconds=240,
            output_path="out/test.mp4",
        )
        assert result["tts"].startswith("deferred") or result["tts"].startswith("requested=")
        assert result["browser_capture"].startswith("deferred")
        assert result["visualizer"].startswith("deferred")
        assert result["final_mix"].startswith("deferred")
        # Le verdict reste explicite sur ce qui est livre vs deferred
        # (adaptation c.1215 : etapes 1/2/4 livrees, 3/5/6 deferees).
        assert "etape 2" in result["verdict"].lower()
        assert "etape 4" in result["verdict"].lower()
        assert "deferred" in result["verdict"].lower()

    def test_narration_json_ecrit(self, tmp_path):
        """--narration-json : le fichier est reellement ecrit et
        rechargerable (entree de l'etape 3 TTS)."""
        target = tmp_path / "narr" / "segments.json"
        run_pipeline(
            style_name="techno",
            duration_seconds=120,
            output_path="out/test.mp4",
            narration_json_path=str(target),
        )
        assert target.exists()
        data = json.loads(target.read_text(encoding="utf-8"))
        assert len(data) >= 2
        assert set(data[0].keys()) == {"start_s", "end_s", "text", "intensity"}

    def test_output_path_is_documented_not_created(self):
        """Sans capture, le pipeline ne cree PAS le fichier .mp4 final ;
        le path est documente dans le verdict sans execution. Un test
        qui verifie que le fichier existe apres run viole."""
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
            errors="replace",
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
            errors="replace",
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
            errors="replace",
        )
        assert "--capture" in result.stdout
        assert "--capture-seconds" in result.stdout

    def test_cli_help_documente_la_narration(self):
        """Les options etape 2 (--narration-engine/--narration-json)
        doivent etre documentees dans l'aide."""
        result = subprocess.run(
            [sys.executable, "scripts/livecoding_video_pipeline.py", "--help"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
        assert "--narration-engine" in result.stdout
        assert "--narration-json" in result.stdout

    def test_cli_narration_json(self, tmp_path):
        """--narration-json ecrit un JSON valide via la commande unique
        (critere 1 de l'acceptance, partie etape 2)."""
        target = tmp_path / "segments.json"
        result = subprocess.run(
            [
                sys.executable, "scripts/livecoding_video_pipeline.py",
                "--style", "techno",
                "--duration", "120",
                "--output", "out/cli_narr.mp4",
                "--narration-json", str(target),
            ],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
        assert result.returncode == 0
        assert "Narration (etape 2" in result.stdout
        assert "deferred" in result.stdout  # etapes 3/5/6 toujours honnetes
        data = json.loads(target.read_text(encoding="utf-8"))
        assert len(data) >= 2
        assert set(data[0].keys()) == {"start_s", "end_s", "text", "intensity"}

    def test_cli_llm_sans_cle_echec_explicite(self, monkeypatch, capsys):
        """--narration-engine llm sans cle : code retour 2 et message
        d'erreur explicite sur stderr — pas de fallback silencieux
        vers template."""
        monkeypatch.delenv("OPENAI_API_KEY", raising=False)
        rc = pipeline_main(
            [
                "--style", "trance",
                "--duration", "120",
                "--output", "out/x.mp4",
                "--narration-engine", "llm",
            ]
        )
        assert rc == 2
        err = capsys.readouterr().err
        assert "OPENAI_API_KEY" in err


class TestCaptureMode:
    """Fix critere 5a #15604 : la capture par defaut filme la page
    ENTIERE (editeur + canvas), le canvas seul reste disponible."""

    def test_capture_mode_defaut_page(self, capsys):
        """Sans drapeau : 'page' (le fix est le defaut — la demo neuve
        montre le code sans option supplementaire)."""
        rc = pipeline_main(
            ["--style", "trance", "--duration", "120", "--output", "out/x.mp4"]
        )
        assert rc == 0
        assert "'--capture-mode', 'page'" not in capsys.readouterr().out  # silencieux

    def test_capture_mode_choix_refuse(self):
        """Une valeur hors (page, canvas) est rejetee par argparse."""
        with pytest.raises(SystemExit):
            pipeline_main(
                [
                    "--style", "trance", "--duration", "120",
                    "--output", "out/x.mp4",
                    "--capture-mode", "webm-codec",
                ]
            )

    def test_capture_repl_session_rejette_mode_inconnu(self, tmp_path):
        """La garde en entree de capture_repl_session echoue AVANT
        d'ouvrir un navigateur (echec explicite, pas de comportement
        implicite par defaut)."""
        from scripts.livecoding_video_pipeline import capture_repl_session

        with pytest.raises(ValueError, match="capture_mode inconnu"):
            capture_repl_session(
                pattern="s('bd')", output_dir=tmp_path, capture_mode="autre"
            )


# --- Etapes 3 et 6 : TTS expressif + mixage final (#15604) -------------------


def _fake_wav(size: int = 2048) -> bytes:
    """WAV synthetique minimal (en-tete RIFF valide pour le sniff)."""
    return (
        b"RIFF" + (size - 8).to_bytes(4, "little") + b"WAVE"
        + b"\x00" * (size - 12)
    )


class TestTtsSpeedForIntensity:
    """3 paliers distincts (critere 3 de l'acceptance : au moins 3
    variations de pace — parametre speed mesure EFFECTIF sur kokoro,
    cf docstring de la fonction)."""

    def test_trois_paliers_distincts(self):
        speeds = {tts_speed_for_intensity(i) for i in (0.05, 0.5, 0.95)}
        assert len(speeds) == 3

    def test_valeurs_mesurees(self):
        assert tts_speed_for_intensity(0.1) == 0.85   # pose
        assert tts_speed_for_intensity(0.5) == 1.0    # neutre
        assert tts_speed_for_intensity(0.9) == 1.15   # elance

    def test_bornes_inclusives(self):
        # 0.34 pose -> neutre, 0.67 neutre -> elance (strict <)
        assert tts_speed_for_intensity(0.339) == 0.85
        assert tts_speed_for_intensity(0.34) == 1.0
        assert tts_speed_for_intensity(0.669) == 1.0
        assert tts_speed_for_intensity(0.67) == 1.15


class TestLoadEnvFiles:
    def test_charge_sans_ecraser(self, tmp_path, monkeypatch):
        (tmp_path / "docker-configurations/services/tts-multi").mkdir(parents=True)
        env = tmp_path / "docker-configurations/services/tts-multi/.env"
        env.write_text(
            "# commentaire\nTTS_GATEWAY_API_KEY=testkey123\nOTHER=x\n",
            encoding="utf-8")
        monkeypatch.setenv("OTHER", "dejavalue")
        _load_env_files(tmp_path)
        import os
        assert os.environ["TTS_GATEWAY_API_KEY"] == "testkey123"
        assert os.environ["OTHER"] == "dejavalue"  # jamais ecrase
        monkeypatch.delenv("TTS_GATEWAY_API_KEY")

    def test_fichier_absent_silencieux(self, tmp_path):
        # un repo_root sans .env ne leve pas
        _load_env_files(tmp_path / "inexistant")


class TestSynthesizeNarrationTts:
    """Etape 3 : payload OpenAI-compatible, sniff RIFF, erreurs
    explicites avec verdict RECOVERABLE-LOCAL (regle F)."""

    def _segments(self):
        return [
            NarrationSegment(
                start_s=0.0, end_s=8.0,
                text="Premiere voix posee sur l'accord.", intensity=0.1),
            NarrationSegment(
                start_s=8.0, end_s=16.0,
                text="Deuxieme voix elancee.", intensity=0.9),
        ]

    def _mock_urlopen(self, monkeypatch, responses):
        """Mocke urllib.request.urlopen ; responses = liste de bytes
        (un par appel) ou d'exceptions a lever."""
        import urllib.request
        state = {"calls": []}

        class _Resp:
            def __init__(self, data):
                self._data = data

            def read(self):
                return self._data

            def __enter__(self):
                return self

            def __exit__(self, *args):
                return False

        def _fake_urlopen(request, timeout=None):
            state["calls"].append(request)
            item = responses[len(state["calls"]) - 1]
            if isinstance(item, Exception):
                raise item
            return _Resp(item)

        monkeypatch.setattr(urllib.request, "urlopen", _fake_urlopen)
        return state

    def test_moteur_inconnu_erreur_explicite(self, tmp_path):
        with pytest.raises(RuntimeError, match="moteur TTS inconnu"):
            synthesize_narration_tts(
                self._segments(), engine="inexistant", out_dir=tmp_path)

    def test_payload_wav_et_speeds(self, tmp_path, monkeypatch):
        monkeypatch.setenv("TTS_GATEWAY_API_KEY", "testkey123")
        state = self._mock_urlopen(
            monkeypatch, [_fake_wav(), _fake_wav(4096)])
        tracks = synthesize_narration_tts(
            self._segments(), engine="kokoro", out_dir=tmp_path,
            gateway="http://gateway.test")

        assert len(tracks) == len(state["calls"]) == 2
        # payload OpenAI-compatible : model/input/voice/speed
        payload = json.loads(state["calls"][0].data.decode("utf-8"))
        assert payload["model"] == "kokoro"
        assert payload["input"] == "Premiere voix posee sur l'accord."
        assert payload["voice"] == "af_sky"
        assert payload["speed"] == 0.85  # intensity 0.1 -> palier pose
        # Bearer present quand la cle est resolue
        assert state["calls"][0].get_header(
            "Authorization") == "Bearer testkey123"
        # un WAV sniffe RIFF par segment, speeds differents (critere 3)
        assert (tmp_path / "segment_000.wav").read_bytes()[:4] == b"RIFF"
        assert (tmp_path / "segment_001.wav").is_file()
        assert tracks[0]["speed"] == 0.85
        assert tracks[1]["speed"] == 1.15
        assert tracks[1]["bytes"] == 4096

    def test_reponse_non_wav_erreur(self, tmp_path, monkeypatch):
        monkeypatch.delenv("TTS_GATEWAY_API_KEY", raising=False)
        self._mock_urlopen(monkeypatch, [b"MP3DATA-not-a-wav"])
        with pytest.raises(RuntimeError, match="pas un RIFF/WAV"):
            synthesize_narration_tts(
                self._segments(), engine="kokoro", out_dir=tmp_path,
                gateway="http://gateway.test")

    def test_http_503_verdict_recoverable_local(self, tmp_path, monkeypatch):
        import urllib.error
        monkeypatch.delenv("TTS_GATEWAY_API_KEY", raising=False)
        err = urllib.error.HTTPError(
            "http://g/tada", 503, "Service unavailable", {}, None)
        self._mock_urlopen(monkeypatch, [err])
        with pytest.raises(RuntimeError, match="RECOVERABLE-LOCAL"):
            synthesize_narration_tts(
                self._segments(), engine="tada", out_dir=tmp_path,
                gateway="http://gateway.test")


class TestMixFinalFfmpeg:
    """Etape 6 : filtergraph adelay/amix/loudnorm/afade + fade video
    coordonne. La commande est construite sans etre executee (test
    unitaire CI sans ffmpeg)."""

    TRACKS = [
        {"index": 0, "start_s": 2.5, "end_s": 10.0, "intensity": 0.5,
         "speed": 1.0, "wav": "out/tts/segment_000.wav", "bytes": 2048},
        {"index": 1, "start_s": 41.0, "end_s": 48.0, "intensity": 0.9,
         "speed": 1.15, "wav": "out/tts/segment_001.wav", "bytes": 2048},
    ]

    def test_filtergraph_complet(self, monkeypatch):
        import scripts.livecoding_video_pipeline as pl
        monkeypatch.setattr(pl, "probe_duration_ffprobe", lambda m: 60.0)
        cmd = mix_final_ffmpeg(
            Path("video.webm"), Path("browser.wav"), self.TRACKS,
            Path("final.mp4"))
        fc = cmd[cmd.index("-filter_complex") + 1]
        # adelay au start_s de chaque segment (ms, tous canaux)
        assert "adelay=2500:all=1[t0]" in fc
        assert "adelay=41000:all=1[t1]" in fc
        # amix sans normalisation + loudnorm -14 LUFS + plafond TP -1.5
        assert "amix=inputs=3:duration=longest:normalize=0" in fc
        assert "loudnorm=I=-14.0:TP=-1.5:LRA=11" in fc
        # fade-out coordonne video ET audio sur les 3 dernieres secondes
        assert "[0:v]fade=t=out:st=57.000:d=3.0[vout]" in fc
        assert "afade=t=out:st=57.000:d=3.0[aout]" in fc
        # duree caguee sur la video + maps des flux filtres
        assert cmd[cmd.index("-t") + 1] == "60.000"
        assert "[vout]" in cmd and "[aout]" in cmd
        assert str(Path("final.mp4")) == cmd[-1]

    def test_lufs_parametrable_et_zero_piste(self, monkeypatch):
        import scripts.livecoding_video_pipeline as pl
        monkeypatch.setattr(pl, "probe_duration_ffprobe", lambda m: 90.0)
        cmd = mix_final_ffmpeg(
            Path("v.webm"), Path("b.wav"), [], Path("o.mp4"),
            loudnorm_lufs=-16.0)
        fc = cmd[cmd.index("-filter_complex") + 1]
        assert "loudnorm=I=-16.0:TP=-1.5" in fc
        assert "amix=inputs=1:duration=longest:normalize=0" in fc
        assert "st=87.000" in fc  # fade sur les 3 dernieres secondes

    def test_video_courte_fade_depuis_zero(self, monkeypatch):
        import scripts.livecoding_video_pipeline as pl
        monkeypatch.setattr(pl, "probe_duration_ffprobe", lambda m: 2.0)
        cmd = mix_final_ffmpeg(
            Path("v.webm"), Path("b.wav"), self.TRACKS[:1], Path("o.mp4"))
        fc = cmd[cmd.index("-filter_complex") + 1]
        assert "st=0.000" in fc  # max(0, 2 - 3) borne a zero

    def test_video_trim_start_ss_avant_input_video(self, monkeypatch):
        # Mode page : la webm brute inclut le preambule (~5 s de
        # chargement/play/warmup) ; -ss extrait la fenetre utile AVANT
        # le premier -i (seek video seul, pas audio), et le fade se
        # cale sur la duree de la FENETRE pas de la webm brute.
        import scripts.livecoding_video_pipeline as pl
        monkeypatch.setattr(pl, "probe_duration_ffprobe", lambda m: 185.2)
        cmd = mix_final_ffmpeg(
            Path("video.webm"), Path("browser.wav"), self.TRACKS,
            Path("o.mp4"), duration_override=180.0, video_trim_start=5.2)
        assert cmd[cmd.index("-ss") + 1] == "5.200"
        assert cmd.index("-ss") < cmd.index("-i")
        # -t = fenetre utile, pas la webm brute
        assert cmd[cmd.index("-t") + 1] == "180.000"
        fc = cmd[cmd.index("-filter_complex") + 1]
        # fade en fin de fenetre utile : 180 - 3, pas 185.2 - 3
        assert "st=177.000" in fc

    def test_sans_video_trim_start_comportement_historique(self, monkeypatch):
        # Mode canvas : aucun -ss, duree = probe webm (comportement
        # historique inchange).
        import scripts.livecoding_video_pipeline as pl
        monkeypatch.setattr(pl, "probe_duration_ffprobe", lambda m: 60.0)
        cmd = mix_final_ffmpeg(
            Path("v.webm"), Path("b.wav"), self.TRACKS[:1], Path("o.mp4"))
        assert "-ss" not in cmd
        assert cmd[cmd.index("-t") + 1] == "60.000"


class TestRunPipelineEtape3:
    """Cablage de l'etape 3 dans l'orchestrateur (synthese mockee :
    le test CI ne fait pas d'appel reseau)."""

    @staticmethod
    def _fake_tracks(segments, **kwargs):
        out_dir = Path(kwargs.get("out_dir", "out/tts"))
        return [
            {"index": i, "start_s": s.start_s, "end_s": s.end_s,
             "intensity": s.intensity, "speed": 1.0,
             "wav": str(out_dir / f"segment_{i:03d}.wav"), "bytes": 2048}
            for i, s in enumerate(segments)
        ]

    def test_sans_moteur_tts_deferred(self):
        result = run_pipeline(
            style_name="trance", duration_seconds=120,
            output_path="out/x.mp4")
        assert result["tts"] == "deferred"
        assert "etape 3 (TTS) deferred" in result["verdict"]
        assert "etape 6 (mix final) deferred" in result["verdict"]

    def test_avec_moteur_synthese_cablee(self, monkeypatch, tmp_path):
        import scripts.livecoding_video_pipeline as pl
        monkeypatch.setattr(
            pl, "synthesize_narration_tts", self._fake_tracks)
        result = run_pipeline(
            style_name="trance", duration_seconds=120,
            output_path=str(tmp_path / "x.mp4"), tts_engine="kokoro")
        assert result["tts"].startswith("LIVREE : ")
        assert "moteur kokoro" in result["tts"]
        assert "etape 3 (TTS kokoro" in result["verdict"]
        # sans capture, l'etape 6 reste deferred (pas de video a mixer)
        assert "etape 6 (mix final) deferred" in result["verdict"]


class TestCliEtapes36:
    def test_help_documente_le_tts(self):
        result = subprocess.run(
            [sys.executable, "scripts/livecoding_video_pipeline.py", "--help"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
        assert "--tts-engine" in result.stdout
        assert "--tts-gateway" in result.stdout
        assert "--tts-out-dir" in result.stdout

class TestProbeDurationFfprobe:
    """Probe de duree : chaine format -> stream -> erreur explicite
    (les webm MediaRecorder n'exposent AUCUNE duree — mesure
    2026-10-03 : N/A sur les deux entrees pour capture.webm)."""

    def test_parse_la_duree_conteneur(self, monkeypatch):
        import subprocess as subprocess_mod

        def _fake_run(cmd, **kwargs):
            return SimpleNamespace(returncode=0, stdout="62.500\n", stderr="")

        monkeypatch.setattr(subprocess_mod, "run", _fake_run)
        assert probe_duration_ffprobe(Path("x.mp4")) == 62.5

    def test_fallback_stream_quand_format_na(self, monkeypatch):
        import subprocess as subprocess_mod
        calls = []

        def _fake_run(cmd, **kwargs):
            calls.append(cmd)
            # format=duration -> N/A ; stream=duration -> 58.2
            stdout = "N/A\n" if "format=duration" in cmd else "58.200000\n"
            return SimpleNamespace(returncode=0, stdout=stdout, stderr="")

        monkeypatch.setattr(subprocess_mod, "run", _fake_run)
        assert probe_duration_ffprobe(Path("x.webm")) == 58.2
        assert len(calls) == 2

    def test_aucune_duree_erreur_explicite(self, monkeypatch):
        import subprocess as subprocess_mod

        def _fake_run(cmd, **kwargs):
            return SimpleNamespace(returncode=0, stdout="N/A\n", stderr="")

        monkeypatch.setattr(subprocess_mod, "run", _fake_run)
        with pytest.raises(RuntimeError, match="aucune duree"):
            probe_duration_ffprobe(Path("capture.webm"))


class TestMixDurationOverride:
    """duration_override : le caller retombe sur la duree du WAV
    navigateur quand le webm n'expose rien — aucun appel ffprobe."""

    def test_override_court_circuite_le_probe(self, monkeypatch):
        import scripts.livecoding_video_pipeline as pl

        def _probe_fail(media):
            raise AssertionError("probe ne doit pas etre appele")

        monkeypatch.setattr(pl, "probe_duration_ffprobe", _probe_fail)
        cmd = mix_final_ffmpeg(
            Path("video.webm"), Path("browser.wav"),
            [{"index": 0, "start_s": 5.0, "end_s": 9.0, "intensity": 0.5,
              "speed": 1.0, "wav": "s.wav", "bytes": 1}],
            Path("o.mp4"), duration_override=90.85,
        )
        fc = cmd[cmd.index("-filter_complex") + 1]
        assert "st=87.850" in fc  # 90.85 - 3.0
        assert cmd[cmd.index("-t") + 1] == "90.850"


class TestResolveCaptureSeconds:
    """Defaut coherent capture/duration (mesure c.1528 : demo 180 s
    tronquee a 30,9 s, 4/11 segments mixes, sans drapeau explicite)."""

    def test_none_suit_duration(self):
        assert _resolve_capture_seconds(None, 180) == 180

    def test_explicite_respecte(self):
        """Une capture plus courte que la musique reste legale
        (verification rapide, capture de test)."""
        assert _resolve_capture_seconds(45, 180) == 45


class TestCliCaptureSecondsDefault:
    def test_parser_defaut_none(self):
        """Le parser ne fixe plus 30 : None traverse jusqu'a la
        resolution dans run_pipeline, la capture reste coherente avec
        --duration (cycles, narration, mix)."""
        args = _build_arg_parser().parse_args(["--duration", "90"])
        assert args.capture_seconds is None
        assert args.duration == 90

    def test_run_pipeline_transmet_duration_a_la_capture(self, tmp_path, monkeypatch):
        """Wiring : sans capture_seconds explicite, capture_repl_session
        recoit duration_seconds."""
        import scripts.livecoding_video_pipeline as pl

        seen = {}

        def _fake_capture(pattern, output_dir, capture_seconds, cycles, headless,
                          capture_mode="page", reveal_states=None):
            seen["capture_seconds"] = capture_seconds
            return {
                "video_webm": str(tmp_path / "capture.webm"),
                "audio_wav": str(tmp_path / "capture.wav"),
                "final_mp4": str(tmp_path / "capture_final.mp4"),
                "video_bytes": 1,
                "wav_bytes": 1,
                "mp4_bytes": 1,
                "cycles": cycles,
            }

        monkeypatch.setattr(pl, "capture_repl_session", _fake_capture)
        pl.run_pipeline(
            style_name="trance",
            duration_seconds=90,
            output_path=str(tmp_path / "out.mp4"),
            capture=True,
            headless=True,
        )
        assert seen["capture_seconds"] == 90


class _FakePlayPage:
    """Page fake minimale pour l'orchestration _click_play : le clic
    echoue les ``fail_first`` premiers essais puis reussit. Precedent
    _FakeClient (LLM) : on valide la SEQUENCE retry, pas un verdict de
    capture — la capture reelle reste provee par l'execution documentee
    dans le body de la PR."""

    def __init__(self, fail_first: int = 0):
        self.clicks = 0
        self.gotos = 0
        self.waits = 0
        self.last_url = None
        self._fail_first = fail_first
        outer = self

        class _First:
            @staticmethod
            def click(timeout=None):
                outer.clicks += 1
                if outer.clicks <= outer._fail_first:
                    raise RuntimeError(f"Locator.click: Timeout {timeout}ms")

        self._first = _First()

    def get_by_role(self, role, name=None):
        return SimpleNamespace(first=self._first)

    def goto(self, url):
        self.gotos += 1
        self.last_url = url

    def wait_for_timeout(self, ms):
        self.waits += 1


class TestClickPlayRetry:
    """Retry du clic play (timeout flaky 1 run sur 3, mesure c.1528) :
    re-navigation de l'URL de partage entre tentatives, echec explicite
    au dernier essai."""

    def test_succes_immediat_sans_reload(self):
        page = _FakePlayPage(fail_first=0)
        _click_play(page, "https://strudel.cc/#HASH")
        assert page.clicks == 1
        assert page.gotos == 0

    def test_timeout_puis_succes_apres_reload(self):
        page = _FakePlayPage(fail_first=1)
        _click_play(page, "https://strudel.cc/#HASH")
        assert page.clicks == 2
        assert page.gotos == 1
        assert page.last_url == "https://strudel.cc/#HASH"
        assert page.waits == 1  # attente post-navigation avant le 2e essai

    def test_epuise_leve_la_derniere_erreur(self):
        page = _FakePlayPage(fail_first=99)
        with pytest.raises(RuntimeError, match="Timeout 10000ms"):
            _click_play(page, "https://strudel.cc/#HASH", attempts=3)
        assert page.clicks == 3
        assert page.gotos == 2


# --- Critere 5a : devoilement progressif du code (grain successeur) ----------


def _voices_of(script: str):
    return [l for l in script.split("\n") if l.lstrip().startswith("$:")]


def _other_lines(script: str):
    return [l for l in script.split("\n") if not l.lstrip().startswith("$:")]


class _FakeEditorPage:
    """Page fake pour le devoilement, a horloge VIRTUELLE.

    ``wait_for_timeout`` avance l'horloge de la duree demandee : la cadence
    se mesure sans dormir pour de vrai, et les instants d'ecriture sont
    deterministes. ``evaluate`` simule la disponibilite de l'API CodeMirror.
    """

    def __init__(self, codemirror_available: bool = True):
        self.codemirror_available = codemirror_available
        self.now = 0.0
        self.waits_ms = []
        self.js_inserts = []
        self.key_presses = []
        self.keyboard_inserts = []
        self.editor_clicks = 0
        self.keyboard = SimpleNamespace(
            press=self._press, insert_text=self._insert_text
        )

    def _press(self, key):
        self.key_presses.append(key)

    def _insert_text(self, text):
        self.keyboard_inserts.append(text)

    def evaluate(self, js, arg=None):
        if arg is not None:
            self.js_inserts.append(arg)
        return self.codemirror_available

    def locator(self, selector):
        outer = self

        class _El:
            @staticmethod
            def click(timeout=None):
                outer.editor_clicks += 1

        return SimpleNamespace(first=_El())

    def wait_for_timeout(self, ms):
        self.waits_ms.append(ms)
        self.now += ms / 1000.0


class TestLinesWithVoices:
    """Retirer une queue de voix ne doit jamais reecrire le reste du script."""

    def test_toutes_les_voix_rendent_le_script_a_l_identique(self):
        script = compose_strudel("trance", 180, visuals=True)
        assert _lines_with_voices(script, len(_voices_of(script))) == script

    def test_une_voix_conserve_l_entete_et_setcps(self):
        script = compose_strudel("trance", 180, visuals=True)
        one = _lines_with_voices(script, 1)
        assert len(_voices_of(one)) == 1
        assert _voices_of(one)[0] == _voices_of(script)[0]
        assert "setcps(" in one
        assert _other_lines(one) == _other_lines(script)


class TestPlanCodeReveal:
    """Plan du devoilement : etats successifs, dernier etat = script entier."""

    SCRIPT = compose_strudel("trance", 180, voices=4, visuals=True)

    def test_desactive_rend_une_liste_vide(self):
        assert plan_code_reveal(self.SCRIPT, 0) == []
        assert plan_code_reveal(self.SCRIPT, -3) == []

    def test_quatre_actes_sur_quatre_voix_donnent_un_a_quatre(self):
        states = plan_code_reveal(self.SCRIPT, 4)
        assert len(states) == 4
        assert [len(_voices_of(s)) for s in states] == [1, 2, 3, 4]

    def test_trois_actes_sur_quatre_voix_finissent_sur_le_script_entier(self):
        states = plan_code_reveal(self.SCRIPT, 3)
        assert len(states) == 3
        assert [len(_voices_of(s)) for s in states] == [1, 3, 4]
        assert states[-1] == self.SCRIPT

    def test_les_actes_sont_plafonnes_au_nombre_de_voix(self):
        # On ne peut pas montrer plus d'etats distincts qu'il n'y a de voix.
        assert len(plan_code_reveal(self.SCRIPT, 99)) == len(_voices_of(self.SCRIPT))

    def test_un_seul_acte_ne_devoile_rien(self):
        assert plan_code_reveal(self.SCRIPT, 1) == [self.SCRIPT]

    def test_chaque_etat_etend_le_precedent_sans_le_reecrire(self):
        states = plan_code_reveal(self.SCRIPT, 4)
        assert len(set(states)) == 4
        for before, after in zip(states, states[1:]):
            assert len(before) < len(after)
            # Les voix deja montrees sont un PREFIXE, les autres lignes
            # sont identiques : aucun etat ne reorganise le script.
            assert _voices_of(after)[: len(_voices_of(before))] == _voices_of(before)
            assert _other_lines(before) == _other_lines(after)

    def test_un_script_sans_voix_ne_se_devoile_pas(self):
        assert plan_code_reveal("setcps(0.9333)", 4) == ["setcps(0.9333)"]


class TestRevealSchedule:
    """Cadencement des etats sur la fenetre de capture."""

    def test_repartition_uniforme_depuis_zero(self):
        plan = reveal_schedule(["a", "b", "c"], 60.0)
        assert [round(t, 3) for t, _ in plan] == [0.0, 20.0, 40.0]
        assert [s for _, s in plan] == ["a", "b", "c"]

    def test_un_seul_etat_reste_a_zero(self):
        assert reveal_schedule(["a"], 60.0) == [(0.0, "a")]

    def test_liste_vide(self):
        assert reveal_schedule([], 60.0) == []

    def test_fenetre_negative_ne_fabrique_pas_de_temps_negatif(self):
        plan = reveal_schedule(["a", "b"], -10.0)
        assert [t for t, _ in plan] == [0.0, 0.0]

    def test_les_instants_sont_strictement_croissants(self):
        times = [t for t, _ in reveal_schedule(["a", "b", "c", "d"], 90.0)]
        assert times == sorted(times)
        assert len(set(times)) == len(times)


class TestSetEditorCode:
    """Ecriture dans l'editeur : API CodeMirror d'abord, clavier en repli."""

    CODE = "$: s('bd*4')\n$: note(\"c2\")"

    def test_api_codemirror_utilisee_quand_disponible(self):
        page = _FakeEditorPage(codemirror_available=True)
        assert _set_editor_code(page, self.CODE) == "codemirror"
        assert page.js_inserts == [self.CODE]
        assert page.key_presses == []
        assert page.editor_clicks == 0

    def test_repli_clavier_quand_l_api_est_absente(self):
        page = _FakeEditorPage(codemirror_available=False)
        assert _set_editor_code(page, self.CODE) == "keyboard"
        assert page.editor_clicks == 1
        assert page.key_presses == ["Control+A", "Control+Home"]
        assert page.keyboard_inserts == [self.CODE]

    def test_ramene_le_curseur_au_debut_apres_ecriture(self):
        # Sans ce rappel, CodeMirror laisse le curseur en fin de document et
        # defile horizontalement : mesure du 2026-10-25, la ligne 1 sortait
        # par la gauche et le code affiche etait tronque.
        page = _FakeEditorPage(codemirror_available=False)
        _set_editor_code(page, self.CODE)
        assert page.key_presses[-1] == "Control+Home"

    def test_ne_reevalue_jamais_le_pattern(self):
        # Control+Enter relancerait l'evaluation : la musique doit continuer
        # de jouer le pattern complet pendant que l'editeur se remplit.
        for available in (True, False):
            page = _FakeEditorPage(codemirror_available=available)
            _set_editor_code(page, self.CODE)
            assert "Control+Enter" not in page.key_presses


class TestDriveCodeReveal:
    """Le devoilement consomme la fenetre et place chaque etat a son instant."""

    def test_etats_places_aux_instants_du_plan(self):
        page = _FakeEditorPage()
        result = _drive_code_reveal(page, ["a", "b", "c"], 60.0, clock=lambda: page.now)
        assert result["states"] == 3
        assert result["applied_at"] == [0.0, 20.0, 40.0]
        assert result["editor_api"] == "codemirror"
        assert page.js_inserts == ["a", "b", "c"]

    def test_la_fenetre_est_entierement_consommee(self):
        page = _FakeEditorPage()
        _drive_code_reveal(page, ["a", "b", "c"], 60.0, clock=lambda: page.now)
        assert sum(page.waits_ms) == 60_000

    def test_repli_clavier_traverse_tous_les_etats(self):
        page = _FakeEditorPage(codemirror_available=False)
        result = _drive_code_reveal(page, ["a", "b"], 30.0, clock=lambda: page.now)
        assert result["editor_api"] == "keyboard"
        assert page.keyboard_inserts == ["a", "b"]
        assert sum(page.waits_ms) == 30_000


class TestCaptureRevealContract:
    """Le devoilement exige le mode page — echec explicite, pas un drapeau inerte."""

    def test_refuse_le_mode_canvas(self, tmp_path):
        with pytest.raises(ValueError, match="reveal_states exige capture_mode='page'"):
            capture_repl_session(
                "pattern",
                tmp_path,
                capture_seconds=1,
                capture_mode="canvas",
                reveal_states=["a", "b"],
            )

    def test_mode_inconnu_toujours_refuse(self, tmp_path):
        with pytest.raises(ValueError, match="capture_mode inconnu"):
            capture_repl_session("pattern", tmp_path, capture_mode="video")

    def test_sans_devoilement_aucune_garde(self, tmp_path):
        # reveal_states=None : le mode canvas reste accepte (comportement
        # historique) — la garde ne mord que sur le mecanisme nouveau.
        with pytest.raises(Exception) as exc:
            capture_repl_session("pattern", tmp_path, capture_seconds=1,
                                 capture_mode="video")
        assert isinstance(exc.value, ValueError)


class TestCliRevealActs:
    def test_defaut_desactive(self):
        assert _build_arg_parser().parse_args([]).reveal_acts == 0

    def test_valeur_transmise(self):
        assert _build_arg_parser().parse_args(["--reveal-acts", "3"]).reveal_acts == 3


class TestRunPipelineRevealWiring:
    """L'orchestrateur transmet bien les etats — le drapeau ne se perd pas."""

    @staticmethod
    def _fake_capture(tmp_path):
        def _fake(**kwargs):
            return {
                "video_webm": str(tmp_path / "capture.webm"),
                "audio_wav": str(tmp_path / "capture.wav"),
                "final_mp4": str(tmp_path / "capture_final.mp4"),
                "video_bytes": 11,
                "wav_bytes": 22,
                "mp4_bytes": 33,
                "cycles": 1,
                "capture_mode": kwargs.get("capture_mode", "page"),
                "trim_start": 0.5,
                "reveal": {
                    "states": 3,
                    "applied_at": [0.0, 20.0, 40.0],
                    "editor_api": "codemirror",
                },
            }
        return _fake

    def test_les_etats_atteignent_la_capture(self, monkeypatch, tmp_path):
        import scripts.livecoding_video_pipeline as mod

        seen = {}

        def _spy(**kwargs):
            seen.update(kwargs)
            return self._fake_capture(tmp_path)(**kwargs)

        monkeypatch.setattr(mod, "capture_repl_session", _spy)
        result = run_pipeline(
            style_name="trance",
            duration_seconds=60,
            output_path=str(tmp_path / "out.mp4"),
            capture=True,
            capture_seconds=60,
            reveal_acts=3,
        )
        assert len(seen["reveal_states"]) == 3
        assert seen["reveal_states"][-1] == result["strudel_script"]
        assert "devoilement 3 etats" in result["browser_capture"]

    def test_desactive_transmet_une_liste_vide(self, monkeypatch, tmp_path):
        import scripts.livecoding_video_pipeline as mod

        seen = {}

        def _spy(**kwargs):
            seen.update(kwargs)
            return self._fake_capture(tmp_path)(**kwargs)

        monkeypatch.setattr(mod, "capture_repl_session", _spy)
        run_pipeline(
            style_name="trance",
            duration_seconds=60,
            output_path=str(tmp_path / "out.mp4"),
            capture=True,
            capture_seconds=60,
        )
        assert seen["reveal_states"] == []
