"""P1 — Voice Cloning + Casting for the v4 audiobook pipeline.

Generates expressive voice samples for 9 distinct voice profiles, synthesizes
them via FishAudio generic presets, then clones each as a permanent reference
via /v1/references/add.

Output: outputs/fishaudio_references/manifest.json
"""
from __future__ import annotations

import json
from pathlib import Path

from dotenv import load_dotenv

from .schemas import VoiceReference, CanonicalSpeaker
from .context_injector import build_context_block
from .llm_client import call_structured
from .fishaudio_client import (
    fishaudio_tts,
    upload_reference,
    list_references,
    thermal_wait,
    OUTPUT_DIR,
)

BASE_DIR = Path(__file__).parent
REF_DIR = BASE_DIR / "outputs" / "fishaudio_references"
REF_DIR.mkdir(exist_ok=True, parents=True)

# ── Speaker-to-voice mapping: 14 canonical speakers -> 13 cloned voices ──

SPEAKER_TO_VOICE: dict[CanonicalSpeaker, str] = {
    "narrateur": "v4_narrator_male_neutral",
    "figurant": "v4_figurant_male_gruff",  # default figurant — overridden per raw speaker below
    "elisabeth_rousset": "v4_boule_warm_distressed",
    "comte": "v4_comte_onctuous",
    "comtesse": "v4_comtesse_cold",
    "madame_carre_lamadon": "v4_comtesse_cold",
    "loiseau": "v4_loiseau_vulgar",
    "follenvie": "v4_loiseau_vulgar",
    "madame_loiseau": "v4_mme_loiseau_shrew",
    "madame_follenvie": "v4_mme_loiseau_shrew",
    "cornudet": "v4_cornudet_mocking",
    "carre_lamadon": "v4_cornudet_mocking",
    "soeurs": "v4_soeurs_pious",
    "officier": "v4_officier_german",
}

# ── Raw speaker name -> voice override for figurants ──
# When p5_tts processes a figurant segment, it checks speaker_raw against this
# map to assign a more appropriate voice than the default gruff male.

FIGURANT_RAW_VOICE_OVERRIDE: dict[str, str] = {
    # Female figurants -> warm or shrew female voice
    "madame_follenvie": "v4_mme_loiseau_shrew",
    "la vieille femme": "v4_figurant_female_warm",
    "miss": "v4_figurant_female_warm",
    "la femme": "v4_figurant_female_warm",
    "une femme": "v4_figurant_female_warm",
    "la bonne": "v4_figurant_female_warm",
    "la servante": "v4_figurant_female_warm",
    "la paysanne": "v4_figurant_female_warm",
    # Authority male figurants -> officier-adjacent
    "le cocher": "v4_figurant_male_gruff",
    "le bedeau": "v4_figurant_male_gruff",
    "le domestique": "v4_figurant_male_gruff",
    "un domestique": "v4_figurant_male_gruff",
    "le soldat": "v4_officier_german",
    "un soldat": "v4_officier_german",
    "un officier": "v4_officier_german",
    "le capitaine": "v4_officier_german",
    "le general": "v4_officier_german",
    # Neutral male figurants -> light male voice
    "l'homme": "v4_figurant_male_light",
    "un homme": "v4_figurant_male_light",
    "le père": "v4_figurant_male_light",
    "Georges": "v4_figurant_male_light",
    "un voyageur": "v4_figurant_male_light",
    "le voyageur": "v4_figurant_male_light",
    "le conducteur": "v4_figurant_male_gruff",
    # Narrator-adjacent (moi = first-person narrator)
    "moi": "v4_narrator_male_neutral",
    "L'Anglais": "v4_figurant_male_light",
}

# ── Voice profile definitions ──

VOICE_PROFILES: dict[str, dict] = {
    "v4_narrator_male_neutral": {
        "speakers": ["narrateur", "figurant"],
        "register": "calm, slightly grave, ironic distance",
        "sample_text": (
            "Les voyageurs se regardaient avec une certaine honte. "
            "La lueur vacillante de la bougie éclairait des visages décomposés, "
            "et l'on entendait au-dehors le pas lourd des soldats prussiens "
            "qui montaient la garde dans la nuit froide de décembre."
        ),
        "preset": "narrator_male",
    },
    "v4_boule_warm_distressed": {
        "speakers": ["elisabeth_rousset"],
        "register": "warm, vulnerable, progressively distressed",
        "sample_text": (
            "Mais, monsieur, je ne peux pas accepter ça ! "
            "Vous ne comprenez donc pas que c'est une humiliation ? "
            "Toute la diligence me juge, et personne ne me défend. "
            "Je suis seule, complètement seule..."
        ),
        "preset": "expressive_female_warm",
    },
    "v4_comte_onctuous": {
        "speakers": ["comte"],
        "register": "smooth, ingratiating, diplomatic",
        "sample_text": (
            "Ma chère enfant, je comprends parfaitement votre scrupule. "
            "C'est noble, c'est délicat, et cela vous honore infiniment. "
            "Mais songez donc à la situation : nous sommes tous prisonniers ici, "
            "et notre salut dépend peut-être d'un geste de générosité."
        ),
        "preset": "expressive_male_neutral",
    },
    "v4_comtesse_cold": {
        "speakers": ["comtesse", "madame_carre_lamadon"],
        "register": "aristocratic, cold, condescending",
        "sample_text": (
            "Il faut bien se rendre à l'évidence, chère amie. "
            "Cette personne ne comprendra jamais les nuances de notre conduite. "
            "Nous avons notre réputation à préserver, et je ne vois pas "
            "pourquoi nous devrions en souffrir davantage."
        ),
        "preset": "expressive_female_cold",
    },
    "v4_loiseau_vulgar": {
        "speakers": ["loiseau", "follenvie"],
        "register": "jovial-vulgar, rough, greedy",
        "sample_text": (
            "Nom d'un chien ! On crève de faim dans cette auberge de malheur ! "
            "Faut voir si on peut pas trouver à manger ailleurs. "
            "Moi je dis qu'on devrait aller voir cet officier boche, "
            "et lui dire deux mots bien choisis !"
        ),
        "preset": "expressive_male_neutral",
    },
    "v4_mme_loiseau_shrew": {
        "speakers": ["madame_loiseau", "madame_follenvie"],
        "register": "sharp, narrow-minded, mean-spirited",
        "sample_text": (
            "Ces gens-là n'ont aucune décence. Se mêler aux honnêtes gens "
            "alors qu'on sait très bien ce qu'elle est. "
            "Je trouve ça scandaleux, et je le dis hautement. "
            "On devrait la mettre à sa place une bonne fois."
        ),
        "preset": "neutral_female",
    },
    "v4_cornudet_mocking": {
        "speakers": ["cornudet", "carre_lamadon"],
        "register": "sardonic, cynical, ironically detached",
        "sample_text": (
            "Eh bien, messieurs, voilà où mènent les grandes phrases sur l'honneur "
            "et la patrie. On demande à une femme de se sacrifier pour qu'ensuite "
            "on la traite comme une moins que rien. C'est magnifique, ce zèle collectif."
        ),
        "preset": "expressive_male_cold",
    },
    "v4_soeurs_pious": {
        "speakers": ["soeurs"],
        "register": "quiet, religious, gently persuasive",
        "sample_text": (
            "Dieu connaît les intentions du cœur, mon enfant. "
            "Parfois le sacrifice est un acte d'amour envers le prochain. "
            "Pensez à tous ces voyageurs qui souffrent, loin de chez eux, "
            "et qui attendent avec tant d'impatience votre décision."
        ),
        "preset": "neutral_female",
    },
    "v4_officier_german": {
        "speakers": ["officier"],
        "register": "clipped, cold, authoritarian",
        "sample_text": (
            "Je ne change pas d'avis. La personne reste ici tant que je le décide. "
            "Vous êtes en pays occupé, messieurs, et vos coutumes françaises "
            "ne m'intéressent pas. Obéissez, c'est tout."
        ),
        "preset": "expressive_male_cold",
    },
    # ── Figurant voices (4 profiles) ──
    "v4_figurant_male_gruff": {
        "speakers": ["figurant_gruff"],
        "register": "rough, working-class, direct, slightly hoarse",
        "sample_text": (
            "Eh ben, on n'est pas rendus avec ce temps de chien. "
            "La route est mauvaise, les chevaux sont fatigues, "
            "et moi j'ai faim comme un loup. "
            "Faut espérer qu'on trouve un gîte avant la nuit."
        ),
        "preset": "expressive_male_neutral",
    },
    "v4_figurant_male_light": {
        "speakers": ["figurant_light"],
        "register": "neutral, younger, lighter voice, everyday speech",
        "sample_text": (
            "Pardon, monsieur, je ne voulais pas vous deranger. "
            "C'est juste que j'ai entendu dire qu'on pourrait partir demain. "
            "Vous savez si c'est vrai ? "
            "Parce que moi, j'aimerais bien rentrer chez moi."
        ),
        "preset": "expressive_male_neutral",
    },
    "v4_figurant_female_warm": {
        "speakers": ["figurant_female"],
        "register": "warm, mature, everyday kindness, slightly worn",
        "sample_text": (
            "Venez donc vous asseoir pres du feu, vous devez avoir froid. "
            "Je vais vous preparer un peu de soupe, ca vous rechauffera. "
            "Avec tout ce qui se passe dehors, on a bien besoin "
            "d'un peu de reconfort."
        ),
        "preset": "neutral_female",
    },
    "v4_figurant_female_sharp": {
        "speakers": ["figurant_sharp"],
        "register": "sharp, provincial, gossip-prone, judgmental",
        "sample_text": (
            "Vous avez vu ca, vous ? Moi je trouve que c'est un scandal. "
            "Et dire qu'elle se permet de regarder les honnetes gens "
            "de haut. Si j'etais a sa place, je rentrerais sous terre. "
            "Quelle absurdite."
        ),
        "preset": "neutral_female",
    },
}

# Generic presets for initial sample synthesis (before cloning)
GENERIC_PRESETS = {
    "narrator_male": "narrator_male",
    "expressive_female_warm": "expressive_female_warm",
    "expressive_female_cold": "expressive_female_cold",
    "expressive_male_neutral": "expressive_male_neutral",
    "expressive_male_cold": "expressive_male_cold",
    "neutral_female": "neutral_female",
    "neutral_male": "neutral_male",
}


def generate_voice_samples(force: bool = False) -> list[VoiceReference]:
    """Generate voice sample MP3s for each profile using FishAudio generic presets."""
    manifest_path = REF_DIR / "manifest.json"
    samples_dir = REF_DIR / "samples"
    samples_dir.mkdir(exist_ok=True)

    if manifest_path.exists() and not force:
        print(f"[P1] Cached: {manifest_path}")
        data = json.loads(manifest_path.read_text(encoding="utf-8"))
        return [VoiceReference(**r) for r in data]

    print("[P1] Generating voice samples...")
    context_block = build_context_block("voice_cloning")

    refs: list[VoiceReference] = []

    for ref_id, profile in VOICE_PROFILES.items():
        sample_path = samples_dir / f"{ref_id}.mp3"

        if sample_path.exists() and not force:
            print(f"  [P1] Cached sample: {sample_path.name}")
            refs.append(VoiceReference(
                reference_id=ref_id,
                speakers=profile["speakers"],
                register=profile["register"],
                sample_text=profile["sample_text"],
                sample_mp3_path=str(sample_path),
                status="generated",
            ))
            continue

        print(f"  [P1] Synthesizing sample: {ref_id}")
        thermal_wait()

        preset = profile["preset"]
        audio_bytes = fishaudio_tts(
            text=profile["sample_text"],
            reference_id=preset if preset in GENERIC_PRESETS else "",
            seed=42,
            temperature=0.7,
            format="mp3",
            timeout=300,
        )

        if audio_bytes:
            sample_path.write_bytes(audio_bytes)
            refs.append(VoiceReference(
                reference_id=ref_id,
                speakers=profile["speakers"],
                register=profile["register"],
                sample_text=profile["sample_text"],
                sample_mp3_path=str(sample_path),
                status="generated",
            ))
            print(f"    Saved: {sample_path} ({len(audio_bytes):,} bytes)")
        else:
            print(f"    FAILED to synthesize {ref_id}")
            refs.append(VoiceReference(
                reference_id=ref_id,
                speakers=profile["speakers"],
                register=profile["register"],
                sample_text=profile["sample_text"],
                sample_mp3_path="",
                status="failed",
            ))

    manifest_path.write_text(
        json.dumps([r.model_dump() for r in refs], indent=2, ensure_ascii=False),
        encoding="utf-8",
    )
    print(f"[P1] Manifest saved: {manifest_path}")
    return refs


def clone_references(refs: list[VoiceReference], force: bool = False) -> list[VoiceReference]:
    """Upload generated samples as FishAudio voice references."""
    existing = {r["id"] for r in list_references()} if not force else set()

    for ref in refs:
        if ref.status != "generated" or not ref.sample_mp3_path:
            continue

        if ref.reference_id in existing and not force:
            print(f"  [P1] Already cloned: {ref.reference_id}")
            ref.status = "cloned"
            continue

        print(f"  [P1] Cloning: {ref.reference_id}")
        success = upload_reference(
            reference_id=ref.reference_id,
            audio_path=ref.sample_mp3_path,
            text=ref.sample_text,
        )
        ref.status = "cloned" if success else "clone_failed"

    return refs


def run(force: bool = False) -> Path:
    """Run P1 — voice cloning + casting. Returns path to manifest.json."""
    manifest_path = REF_DIR / "manifest.json"

    if manifest_path.exists() and not force:
        print(f"[P1] Cached: {manifest_path}")
        return manifest_path

    print("[P1] Running voice cloning + casting...")

    # Step 1: Generate samples
    print("[P1] Step 1: Generating voice samples...")
    refs = generate_voice_samples(force=force)
    gen_ok = sum(1 for r in refs if r.status == "generated")
    print(f"  Generated: {gen_ok}/{len(refs)}")

    # Step 2: Clone references
    print("[P1] Step 2: Cloning voice references...")
    refs = clone_references(refs, force=force)
    cloned = sum(1 for r in refs if r.status == "cloned")
    print(f"  Cloned: {cloned}/{len(refs)}")

    # Save final manifest
    manifest_path.write_text(
        json.dumps([r.model_dump() for r in refs], indent=2, ensure_ascii=False),
        encoding="utf-8",
    )
    print(f"[P1] Done: {manifest_path}")
    print(f"  Voice profiles: {len(VOICE_PROFILES)}")
    print(f"  Speaker mappings: {len(SPEAKER_TO_VOICE)}")

    return manifest_path


if __name__ == "__main__":
    load_dotenv(Path(__file__).resolve().parent.parent.parent.parent / ".env")
    run(force="--force" in " ".join(__import__("sys").argv))
