"""P4 -- Prosodic Annotation for the v4 FishAudio audiobook pipeline.

Takes segments (from P2) and dramatic context (from P3), then produces
annotated segments with inline prosody tags via batched LLM calls.

Steps:
1. Load segments from outputs/segments_v4.json
2. Load dramatic context from outputs/dramatic_context.json
3. Batch 10 segments per LLM call with narrative context
4. Each batch gets context from context_injector.build_context_block
5. Post-process tags into FishAudio-compatible format

Output: outputs/annotated_v4.json
"""
from __future__ import annotations

import json
import re
from pathlib import Path

from dotenv import load_dotenv

from .schemas import (
    Segment,
    SegmentBatch,
    DramaticContext,
    DramaticContextBatch,
    AnnotatedSegment,
    AnnotatedBatch,
    ALL_PROSODY_TAGS,
)
from .llm_client import call_structured
from .context_injector import build_context_block

BASE_DIR = Path(__file__).parent
OUTPUTS = BASE_DIR / "outputs"
OUTPUTS.mkdir(exist_ok=True)

# ── Constants ──

BATCH_SIZE = 10
MAX_TAGS_PER_SEGMENT = 5

INPUT_SEGMENTS = OUTPUTS / "segments_v4.json"
INPUT_DRAMATIC = OUTPUTS / "dramatic_context.json"
OUTPUT_ANNOTATED = OUTPUTS / "annotated_v4.json"

# ── FishAudio S2-Pro tag system ──
# S2-Pro accepts [brackets] with 15,000+ free-form natural language tags.
# The LLM outputs tags directly in S2-Pro format — no intermediate mapping needed.
# Legacy 22-tag mapping kept for backward compatibility with existing JSON outputs.

TAG_TO_FISHAUDIO: dict[str, str] = {
    # Legacy short tags → official S2-Pro [bracket] equivalents (backward compat)
    "whisper": "[whispering]",
    "shout": "[shouting]",
    "cold": "[low voice]",
    "warm": "[soft voice]",
    "onctuous": "[soft voice]",
    "indignant": "[angry]",
    "mocking": "[emphasis]",
    "angry": "[angry]",
    "sad": "[sad]",
    "nervous": "[whispering]",
    "excited": "[excited]",
    "gentle": "[soft voice]",
    "firm": "[emphasis]",
    "timid": "[whispering]",
    "laugh": "[laughing]",
    "sigh": "[sigh]",
    "sob": "[sobbing]",
    "gasp": "[gasp]",
    "breath": "[inhale]",
    "slow": "[pause]",
    "fast": "[emphasis]",
    "pause": "[pause]",
}

# ── LLM prompt templates ──

NARRATOR_SYSTEM_PROMPT = """Tu es un expert en narration audio pour la synthese vocale.
Tu produis des annotations prosodiques pour un narrateur qui lit un texte litteral francais.
Le narrateur est COMPETENT et EXPRESSIF — pas un robot monotone.

## OBJECTIF PRINCIPAL
Chaque segment de narration DOIT avoir une musicalite propre. Le narrateur modifie son
debit, ses pauses, son souffle, et son intonation pour suivre le texte. DEUX segments
consecutifs ne doivent JAMAIS avoir la meme prosodie.

## Systeme de balises — FishAudio S2-Pro

Le modele utilise des balises entre CROCHETS [tag]. S2-Pro supporte des instructions
en langage naturel libre dans les crochets, mais les balises ci-dessous sont les
seules officiellement testees et produisant des resultats consistants.

### Balises officielles (bien testees)

**Respiration et reactions vocales :**
[clears throat] [inhale] [inhalation] [exhale] [sigh] [panting] [breathing] [gasp]

**Sons vocaux non-verbaux :**
[groan] [moaning] [sobbing] [crying] [laughing] [chuckling] [giggle]

**Rythme et pauses :**
[pause] [short pause] [long pause]

**Style vocal :**
[whispering] [whispering voice] [soft voice] [low voice] [loud voice] [shouting]

**Emotion (3 officiellement testees) :**
[excited] [angry] [sad]

**Autre :**
[emphasis] [rustling sound]

### INTERDIT — Pas de langage naturel libre
N'utilise JAMAIS de descriptions libres entre crochets. S2-Pro VOCALISE le texte libre
au lieu de l'interpreter (prouve par validation WER #1277/#1485, 98 segments WER>100%).
Utilise UNIQUEMENT les 29 tags officiels ci-dessus. Pour les emotions non couvertes
par [excited]/[angry]/[sad], combine les tags de style vocal (ex: sarcasme = [emphasis][soft voice]).

## REGLE CRITIQUE DE PLACEMENT

**Les balises affectent ce qui les SUIT, pas ce qui les precede.**
- `[whispering]` au debut d'un segment rend TOUT le segment murmure.
- Pour un changement en milieu de segment, place la balise AU POINT DE TRANSITION :
  `Il regarda la plaine. [pause][soft voice] Au loin, la riviere brillait.`
- Ne JAMAIS empiler des balises au debut du segment pour "tout activer d'un coup".

## REGLES OBLIGATOIRES pour la NARRATION

### Regle 1 — AUCUN segment de narration sans tag
CHAQUE segment narrateur DOIT contenir au minimum 1 tag. Il n'y a PAS de "narration neutre".
Le narrateur a toujours un ton, un rythme, une intention.

### Regle 2 — Varier la prosodie entre segments consecutifs
Si le segment precedent utilise [sad], le suivant ne DOIT PAS commencer par [sad].
Alterner entre differents registres : emotions, tempo, effets sonores.

### Regle 3 — Tags intra-segment pour les segments longs (>30 mots)
Pour les segments de plus de 30 mots, inserer AU MOINS un tag de variation en milieu
de segment : [pause], [short pause], [inhale], ou [long pause] pour casser la monotonie.
Placer ces tags a des points naturels : avant une virgule, apres un point-virgule.

### Regle 4 — Placement des tags
1. Balises de style vocal ([soft voice], [low voice]) AU POINT OU le changement s'applique
2. [pause] / [short pause] / [long pause] inline aux points de respiration naturelle
3. [inhale] / [exhale] aux changements de phrase ou de sujet
4. Sons non-verbaux ([sigh], [gasp]) au point precis du battement emotionnel
5. Maximum {max_tags} tags par segment

### Regle 5 — Adapter la prosodie au type de narration
- **Description visuelle** : [soft voice] ... [pause] — voix qui contemple
- **Action rapide** : [excited] ... [pause] — voix qui s'anime
- **Commentaire ironique** : [emphasis] ... [short pause] — voix qui souligne
- **Description emotionnelle** : [sad] ... [sigh] — voix qui ressent
- **Transition** : [pause] ... [inhale] — voix qui marque le passage
- **Suspense** : [low voice] ... [long pause] — voix qui cree l'attente
- **Bilan / reflexion** : [emphasis] ... [pause] — voix qui pose

## Format de reponse

Pour chaque segment, retourne un objet JSON avec :
- seg_index : int (doit correspondre)
- type : "narration" | "dialogue" | "thought"
- speaker : nom canonique du locuteur
- text : texte original SANS modification
- annotated_text : texte avec balises [tag] inserees
- prosody_tags : liste des tags officiels S2-Pro choisis (max 3, parmi les 29 tags officiels ci-dessus)

IMPORTANT : annotated_text doit contenir le MEME texte que text, avec seulement
des balises [tag] inserees. Ne pas modifier, traduire ou resumer le texte.
Les prosody_tags doivent correspondre aux balises officielles utilisees dans annotated_text.
Les descriptions libres ne vont PAS dans prosody_tags, seulement dans annotated_text.
""".format(max_tags=MAX_TAGS_PER_SEGMENT)

DIALOGUE_SYSTEM_PROMPT = """Tu es un expert en annotation prosodique pour la synthese vocale.
Tu annotes des dialogues et pensees de personnages avec des balises de prosodie inline.

## Systeme de balises — FishAudio S2-Pro

Le modele utilise des balises entre CROCHETS [tag]. S2-Pro supporte des instructions
en langage naturel libre dans les crochets, mais les balises ci-dessous sont les
seules officiellement testees et produisant des resultats consistants.

### Balises officielles (bien testees)

**Respiration et reactions vocales :**
[clears throat] [inhale] [inhalation] [exhale] [sigh] [panting] [breathing] [gasp]

**Sons vocaux non-verbaux :**
[groan] [moaning] [sobbing] [crying] [laughing] [chuckling] [giggle]

**Rythme et pauses :**
[pause] [short pause] [long pause]

**Style vocal :**
[whispering] [whispering voice] [soft voice] [low voice] [loud voice] [shouting]

**Emotion (3 officiellement testees) :**
[excited] [angry] [sad]

**Autre :**
[emphasis] [rustling sound]

### INTERDIT — Pas de langage naturel libre
N'utilise JAMAIS de descriptions libres entre crochets. S2-Pro VOCALISE le texte libre
au lieu de l'interpreter. Utilise UNIQUEMENT les 29 tags officiels ci-dessus.
Pour les emotions non couvertes, combine les tags de style vocal.

## REGLE CRITIQUE DE PLACEMENT

**Les balises affectent ce qui les SUIT, pas ce qui les precede.**
- Place la balise d'emotion JUSTE AVANT le passage concerne, pas systematiquement au debut.
- Exemple correct : `Je ne veux pas [pause][soft voice] mais si tu insistes...`
- Exemple incorrect : `[angry][shouting] Tout le texte est crie sans nuance.`

## Regles pour les dialogues

1. Chaque dialogue DOIT avoir au moins 1 tag correspondant a l'etat du personnage
2. Inserer [pause] ou [short pause] aux hesitations, ruptures de pensee, silences dramatiques
3. [inhale] avant les phrases longues ou apres une emotion forte
4. Maximum {max_tags} tags par segment
5. Les tags doivent refleter le contexte dramatique (acte, tension, etat emotionnel)
6. Combiner emotion + effet physique pour plus d'expressivite : [sad][sigh], [angry][shouting]

## Format de reponse

Pour chaque segment, retourne un objet JSON avec :
- seg_index : int (doit correspondre)
- type : "narration" | "dialogue" | "thought"
- speaker : nom canonique du locuteur
- text : texte original SANS modification
- annotated_text : texte avec balises [tag] inserees
- prosody_tags : liste des tags officiels S2-Pro choisis (max 3, parmi les 29 tags officiels ci-dessus)

IMPORTANT : annotated_text doit contenir le MEME texte que text, avec seulement
des balises [tag] inserees. Ne pas modifier, traduire ou resumer le texte.
Les prosody_tags doivent correspondre aux balises officielles utilisees dans annotated_text.
Les descriptions libres ne vont PAS dans prosody_tags, seulement dans annotated_text.
""".format(max_tags=MAX_TAGS_PER_SEGMENT)

USER_PROMPT_TEMPLATE = """## Segments a annoter (batch {batch_idx})

{segments_block}

Annote chaque segment avec les balises prosodiques appropriees.
Respecte les regles de placement et le maximum de {max_tags} tags par segment.

## Contexte dramatique
Chaque segment est accompagne d'un "prompt dramatique" et de mots-cles emotionnels.
Utilise-les pour choisir les tags les plus adaptes parmi les 29 tags officiels UNIQUEMENT.
N'ecris JAMAIS de texte libre entre crochets — S2-Pro le prononce au lieu de l'interpreter.

Retourne un objet JSON avec la cle "segments" contenant la liste des segments annotes.
Chaque segment doit avoir : seg_index, type, speaker, text, annotated_text,
prosody_tags (liste des tags officiels choisis, max 3)."""


# ── Helper functions ──


def load_inputs() -> tuple[list[Segment], dict[int, DramaticContext]]:
    """Load segments and dramatic context from pipeline outputs.

    Returns:
        Tuple of (segments list, dramatic context dict keyed by seg_index).

    Raises:
        FileNotFoundError: If required input files are missing.
    """
    if not INPUT_SEGMENTS.exists():
        raise FileNotFoundError(
            f"segments_v4.json introuvable : {INPUT_SEGMENTS}\n"
            "Lancez d'abord la phase P2 (segmentation)."
        )
    if not INPUT_DRAMATIC.exists():
        raise FileNotFoundError(
            f"dramatic_context.json introuvable : {INPUT_DRAMATIC}\n"
            "Lancez d'abord la phase P3 (dramatic context)."
        )

    seg_data = json.loads(INPUT_SEGMENTS.read_text(encoding="utf-8"))

    # Handle both list and dict root
    if isinstance(seg_data, list):
        segments = [Segment(**s) for s in seg_data]
    elif "segments" in seg_data:
        segments = [Segment(**s) for s in seg_data["segments"]]
    else:
        segments = []

    ctx_data = json.loads(INPUT_DRAMATIC.read_text(encoding="utf-8"))
    if isinstance(ctx_data, dict) and "contexts" in ctx_data:
        contexts_list = [DramaticContext(**c) for c in ctx_data["contexts"]]
    elif isinstance(ctx_data, list):
        contexts_list = [DramaticContext(**c) for c in ctx_data]
    else:
        contexts_list = []

    contexts_by_idx = {c.seg_index: c for c in contexts_list}

    print(f"  Loaded {len(segments)} segments, {len(contexts_by_idx)} dramatic contexts")
    return segments, contexts_by_idx


def build_segment_block(segments: list[Segment], contexts: dict[int, DramaticContext]) -> str:
    """Format a batch of segments with their dramatic context for the LLM prompt.

    Args:
        segments: The segments in this batch.
        contexts: Dramatic context dict keyed by seg_index.

    Returns:
        Formatted text block for the user prompt.
    """
    lines: list[str] = []
    for seg in segments:
        ctx = contexts.get(seg.seg_index)
        lines.append(f"### Segment {seg.seg_index}")
        lines.append(f"Type: {seg.type} | Locuteur: {seg.speaker}")
        if ctx:
            lines.append(
                f"Contexte: {ctx.scene_label} | Acte: {ctx.act} | "
                f"Tension: {ctx.tension_0_10}/10 | Position: {ctx.narrative_position}"
            )
            if ctx.dramatic_prompt:
                lines.append(f"Prompt dramatique: {ctx.dramatic_prompt}")
            if ctx.emotional_keywords:
                lines.append(f"Mots-cles emotionnels: {', '.join(ctx.emotional_keywords)}")
            if ctx.character_state:
                states = ", ".join(f"{k}: {v}" for k, v in ctx.character_state.items())
                lines.append(f"Etats emotionnels: {states}")
        word_count = len(seg.text.split())
        lines.append(f"Longueur: {word_count} mots")
        lines.append(f"Texte: {seg.text}")
        lines.append("")
    return "\n".join(lines)


def _get_system_prompt(segments: list[Segment]) -> str:
    """Pick the right system prompt based on batch composition."""
    has_narration = any(s.speaker == "narrateur" for s in segments)
    has_dialogue = any(s.speaker != "narrateur" for s in segments)

    if has_narration and not has_dialogue:
        return NARRATOR_SYSTEM_PROMPT
    if has_dialogue and not has_narration:
        return DIALOGUE_SYSTEM_PROMPT
    # Mixed batch — use the narrator prompt which is more comprehensive
    return NARRATOR_SYSTEM_PROMPT


def annotate_batch(
    segments: list[Segment],
    contexts: dict[int, DramaticContext],
    batch_idx: int,
    previous_tags: list[str] | None = None,
) -> list[AnnotatedSegment]:
    """Send a batch of segments to the LLM for prosodic annotation.

    Args:
        segments: Segments to annotate (typically 10).
        contexts: Dramatic context dict keyed by seg_index.
        batch_idx: Batch number (for logging).
        previous_tags: Tags used in the last segment of the previous batch
                       (to avoid repetition).

    Returns:
        List of AnnotatedSegment instances.
    """
    start = segments[0].seg_index
    end = segments[-1].seg_index
    print(f"  [P4] Batch {batch_idx}: annotating segments {start}-{end} ({len(segments)} segments)")

    context_block = build_context_block("annotation", segment_range=(start, end))
    segments_block = build_segment_block(segments, contexts)

    # Add anti-repetition hint if we know the previous batch's last tags
    repetition_hint = ""
    if previous_tags:
        repetition_hint = (
            f"\nATTENTION : le segment precedent se termine avec les tags {previous_tags}. "
            f"Utilise des tags DIFFERENTS pour ce batch afin de garantir la variante."
        )

    user_prompt = USER_PROMPT_TEMPLATE.format(
        batch_idx=batch_idx,
        segments_block=segments_block,
        max_tags=MAX_TAGS_PER_SEGMENT,
    ) + repetition_hint

    system_prompt = _get_system_prompt(segments)

    result = call_structured(
        AnnotatedBatch,
        system_prompt,
        user_prompt,
        context_block=context_block,
    )

    batch = AnnotatedBatch(**result)

    # Attach dramatic context references + propagate speaker_raw from source segments
    seg_raw_map = {s.seg_index: s.speaker_raw for s in segments}
    annotated: list[AnnotatedSegment] = []
    for seg in batch.segments:
        ctx = contexts.get(seg.seg_index)
        # Extract tts_context_prefix from LLM output if provided
        tts_prefix = getattr(seg, "tts_context_prefix", "") or ""
        dramatic_prompt = ctx.dramatic_prompt if ctx else ""
        annotated.append(AnnotatedSegment(
            seg_index=seg.seg_index,
            type=seg.type,
            speaker=seg.speaker,
            speaker_raw=seg_raw_map.get(seg.seg_index, ""),
            text=seg.text,
            annotated_text=seg.annotated_text,
            prosody_tags=seg.prosody_tags,
            tags_used=seg.tags_used,
            fishaudio_text=convert_tags_for_fishaudio(seg.annotated_text),
            dramatic_ref=ctx,
            dramatic_prompt=dramatic_prompt,
            tts_context_prefix=tts_prefix,
        ))

    tag_count = sum(len(s.tags_used) for s in annotated)
    prosody_count = sum(len(s.prosody_tags) for s in annotated)
    tagged_segs = sum(1 for s in annotated if s.tags_used)
    print(f"    Tags: {tag_count} total ({prosody_count} official S2-Pro), "
          f"{tagged_segs}/{len(annotated)} segments tagged")

    return annotated


def convert_tags_for_fishaudio(annotated_text: str) -> str:
    """Convert legacy prosody tags to FishAudio S2-Pro [bracket] format.

    S2-Pro uses [brackets] for voice instructions. Parenthetical text
    is spoken LITERALLY by S2-Pro and must be converted to brackets.

    Three conversions applied in order:
    1. Legacy single-word [tag] → official S2-Pro equivalent
    2. (parenthetical voice instructions) → [bracket] equivalents
    3. (English adverb tags) like (firmly), (mockingly) → [brackets]
    """
    text = annotated_text

    # Step 1: Legacy single-word tags
    def _replace_legacy_tag(match: re.Match) -> str:
        tag = match.group(1)
        return TAG_TO_FISHAUDIO.get(tag, match.group(0))

    text = re.sub(r"\[(\w+)\]", _replace_legacy_tag, text)

    # Step 2: Convert (parenthetical voice instructions) to [brackets].
    # Match (...) that look like voice instructions: start with a lowercase
    # word, contain no nested parens, and are ≤120 chars.
    # Exclude: legitimate French parenthetical content like numbers (1), (a).
    def _paren_to_bracket(match: re.Match) -> str:
        content = match.group(1)
        # Skip very short content: single letters, digits, simple references
        if len(content) <= 2:
            return match.group(0)
        # Skip if it looks like a reference: (1), (a), (cf. ...), (note ...)
        if re.match(r"^\d+[a-z]?$", content):
            return match.group(0)
        if content.lower().startswith(("cf.", "note", "voir", "ref")):
            return match.group(0)
        # This looks like a voice instruction — convert to brackets
        return f"[{content}]"

    text = re.sub(r"\(([^()]{1,120})\)", _paren_to_bracket, text)

    return text


# ── Quality check: tag diversity ──


def _check_tag_diversity(all_annotated: list[AnnotatedSegment]) -> dict:
    """Check tag diversity across narration segments.

    Returns stats for logging.
    """
    narr_segments = [s for s in all_annotated if s.speaker == "narrateur"]
    if not narr_segments:
        return {"narrator_segments": 0}

    untagged = [s for s in narr_segments if not s.tags_used]
    tag_counts = {}
    for seg in narr_segments:
        for tag in seg.tags_used:
            tag_counts[tag] = tag_counts.get(tag, 0) + 1

    # Check consecutive same-tag starts
    same_start = 0
    prev_start_tags: set[str] = set()
    for seg in narr_segments:
        start_tags = set(seg.tags_used[:2]) if seg.tags_used else set()
        if start_tags and start_tags == prev_start_tags:
            same_start += 1
        prev_start_tags = start_tags

    return {
        "narrator_segments": len(narr_segments),
        "untagged": len(untagged),
        "tag_diversity": len(tag_counts),
        "consecutive_same_start": same_start,
        "most_used": sorted(tag_counts.items(), key=lambda x: -x[1])[:5],
    }


# ── Main entry point ──


def run(force: bool = False) -> Path:
    """Run P4 -- prosodic annotation. Returns path to annotated_v4.json.

    Args:
        force: If True, re-run even if output already exists.

    Returns:
        Path to the generated annotated_v4.json file.
    """
    if OUTPUT_ANNOTATED.exists() and not force:
        print(f"[P4] Cached: {OUTPUT_ANNOTATED}")
        return OUTPUT_ANNOTATED

    print("[P4] Running prosodic annotation...")

    # Step 1: Load inputs
    print("[P4] Step 1: Loading segments and dramatic context...")
    segments, contexts = load_inputs()

    # Step 2: Batch annotation
    print(f"[P4] Step 2: Annotating {len(segments)} segments (batch size: {BATCH_SIZE})...")
    all_annotated: list[AnnotatedSegment] = []
    batch_count = 0
    previous_tags: list[str] | None = None

    for i in range(0, len(segments), BATCH_SIZE):
        batch = segments[i : i + BATCH_SIZE]
        batch_count += 1
        try:
            annotated = annotate_batch(batch, contexts, batch_count, previous_tags)
            all_annotated.extend(annotated)
            # Track last segment's tags for anti-repetition
            if annotated:
                last = annotated[-1]
                previous_tags = last.tags_used[:2] if last.tags_used else None
        except Exception as e:
            print(f"  [P4] Batch {batch_count} FAILED: {e}")
            # Fallback: create minimally tagged segments
            for seg in batch:
                # Even fallback gets a basic tag for narrateur
                if seg.speaker == "narrateur":
                    fallback_text = f"[pause] {seg.text}"
                else:
                    fallback_text = seg.text
                all_annotated.append(AnnotatedSegment(
                    seg_index=seg.seg_index,
                    type=seg.type,
                    speaker=seg.speaker,
                    speaker_raw=seg.speaker_raw,
                    text=seg.text,
                    annotated_text=fallback_text,
                    prosody_tags=["pause"] if seg.speaker == "narrateur" else [],
                    tags_used=["pause"] if seg.speaker == "narrateur" else [],
                    fishaudio_text=convert_tags_for_fishaudio(fallback_text),
                    dramatic_ref=contexts.get(seg.seg_index),
                    dramatic_prompt="",
                    tts_context_prefix="",
                ))

    # Step 3: Sort by seg_index and save
    all_annotated.sort(key=lambda s: s.seg_index)
    batch_result = AnnotatedBatch(segments=all_annotated)

    OUTPUT_ANNOTATED.write_text(
        batch_result.model_dump_json(indent=2),
        encoding="utf-8",
    )

    total_tags = sum(len(s.tags_used) for s in all_annotated)
    total_prosody = sum(len(s.prosody_tags) for s in all_annotated)
    tagged_segments = sum(1 for s in all_annotated if s.tags_used)

    # Quality check
    diversity = _check_tag_diversity(all_annotated)

    print(f"[P4] Saved: {OUTPUT_ANNOTATED}")
    print(f"  Segments: {len(all_annotated)}")
    print(f"  Tagged: {tagged_segments}/{len(all_annotated)}")
    print(f"  Total tags: {total_tags} ({total_prosody} official S2-Pro)")
    print(f"  Batches: {batch_count}")
    print(f"  Narrator quality:")
    print(f"    Untagged narrateur: {diversity.get('untagged', '?')}")
    print(f"    Tag diversity: {diversity.get('tag_diversity', '?')} unique tags")
    print(f"    Consecutive same-start: {diversity.get('consecutive_same_start', '?')}")

    if diversity.get("most_used"):
        print(f"    Top tags: {diversity['most_used']}")

    if diversity.get("untagged", 0) > 0:
        print(f"  WARNING: {diversity['untagged']} narrateur segments still untagged!")

    return OUTPUT_ANNOTATED


if __name__ == "__main__":
    load_dotenv(Path(__file__).resolve().parent.parent.parent.parent / ".env")
    run(force="--force" in " ".join(__import__("sys").argv))
