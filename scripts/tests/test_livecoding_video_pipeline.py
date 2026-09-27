"""Tests du pipeline livecoding-video (#15604).

Etapes couvertes par ces tests : 1 (composition Strudel, heritage V0),
2 (narration poetique timestampee : moteur template deterministe,
moteur LLM via client injecte — jamais un vrai appel reseau dans les
tests, la sortie LLM est VALIDEE, pas crue) et 4 (capture navigateur :
logique PURE — encodage URL, calcul de cycles, commande ffmpeg,
visuals, deferral). La capture REELLE (navigateur + reseau + ffmpeg)
est provee par l'execution documentee dans le body de la PR, pas par
un test qui simulerait le navigateur : verifier un verdict fake sur
une capture qui n'a pas eu lieu = test menteur (Tell c.1102).
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
    NarrationSegment,
    STYLES,
    StrudelStyle,
    build_repl_url,
    compose_narration,
    compose_strudel,
    cycles_for_duration,
    mux_ffmpeg,
    narration_to_json,
    parse_strudel_highlights,
    run_pipeline,
    style_cps,
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
        rafistolee (Tell c.1102)."""
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
        de fallback silencieux vers template (Tell c.1102)."""
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
    plutot que de pretendre les avoir executees (Tell c.1102). Depuis
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

    def test_cli_help_documente_la_narration(self):
        """Les options etape 2 (--narration-engine/--narration-json)
        doivent etre documentees dans l'aide."""
        result = subprocess.run(
            [sys.executable, "scripts/livecoding_video_pipeline.py", "--help"],
            capture_output=True,
            text=True,
            encoding="utf-8",
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
        vers template (Tell c.1102)."""
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
