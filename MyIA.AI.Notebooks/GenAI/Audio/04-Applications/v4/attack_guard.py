"""Garde d'attaque par chunk — issue #19739 (phase 2 du pipeline audiobook v4).

Le défaut mesure en phase 1 (PR #19699) : le narrateur peut rendre un chunk en
commençant **au milieu** du texte fourni — l'attaque (les premiers mots) n'est
jamais prononcée. Le défaut est **graine-dépendant** : re-rouler la graine du
chunk fautif suffit à le récupérer, et une graine espacee redonne une attaque
presque toujours presente.

Ce module est la partie **CPU** de la correction : un detecteur d'attaque
manquante (l'extension par chunk de l'organe d'omission p7) et le plan de
re-roll associe. Il ne rend pas lui-meme : il consomme un manifeste de chunks
rendus et rend un verdict par chunk, plus la liste des chunks a re-rouler avec
leur graine suivante.

Organes natifs reutilises (pas de copie de convention)
-------------------------------------------------------
- la normalisation des mots et le calcul des spans d'omission viennent de
  `v4.p7_verify` (`_normalize_words`, `_missing_word_spans`) : la garde
  mesure exactement ce que mesure l'organe d'omission, donc un verdict
  « attaque manquante » et un span d'omission ne peuvent pas diverger ;
- la convention de re-roll vient de `v4.p5_tts` : graine de base
  `42 + seg_index`, pas de re-roll `104_729` (premier), formule
  `seed + i + attempt * 104_729` ou `i` est l'index du chunk dans le segment.

Le critere de decision est **positionnel**
------------------------------------------
Un premier jet de la garde jugeait l'attaque perdue sur la *presence* des
mots de tete dans la transcription (au moins 3 absents sur les 12 premiers
mots). Ce critere est **faux** : mesure sur 10 rendus reels du corpus
(Boule de Suif, moteur Chatterbox, ASR `whisper-large-v3-turbo`), il
signale 9 chunks sur 10 alors que leurs transcriptions commencent bien par
le texte source -- l'ASR se trompe sur quelques mots, et une absence
*quelque part* n'est pas une attaque perdue.

Le critere retenu est la **perte de tete** : le nombre de mots source
perdus *depuis le mot 0*, sans trou. C'est la definition operationnelle de
l'onset-drop (le rendu commence plus loin dans le texte). Mesure sur le
meme corpus : 0 faux positif sur les 10 rendus naturels, 10/10 sur le
controle positif (memmes rendus amputes de leurs 1,5 premieres secondes).

La garde ne se substitue pas a la boucle de rendu de p5 : elle s'y branche.
Le point d'insertion naturel est la boucle de rendu de p5 (qui re-roule deja
sur un plancher de duree), ou le rendu par chunk doit passer par
`evaluate_chunk` avant d'etre accepte.

Deux modes d'ASR
----------------
- `--asr http` : le serveur Whisper local, meme chemin que p7
  (`POST /v1/audio/transcriptions`, modele `large-v3-turbo`). C'est le chemin
  du pipeline sur la machine qui porte les services.
- `--asr local` : transformers en local, modele `openai/whisper-large-v3-turbo`.
  C'est le chemin auto-portant : il permet de mesurer la garde sur une machine
  qui n'a pas le serveur, sans changer d'outil.

Usage
-----
    # sur un manifeste de chunks rendus, avec les transcriptions deja mesurees
    python -m v4.attack_guard --manifest chunks.json \\
        --transcripts transcripts.json --out attack_report.json

    # ou en mesurant l'ASR sur le moment (serveur local du pipeline)
    python -m v4.attack_guard --manifest chunks.json --asr http \\
        --out attack_report.json
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
from typing import Callable

from .p7_verify import _missing_word_spans, _normalize_words

# Seuil de mots perdus pour qualifier une attaque manquante. Meme valeur que
# le `min_words` de l'organe d'omission p7 (3 mots consecutifs absents) : sous
# ce seuil, une faute de prononciation sur un mot n'est pas une attaque.
ATTACK_MIN_WORDS = 3

# Pas de re-roll de la graine. Meme constante que `p5_tts._CV3_RETRY_SEED_STRIDE`
# (premier, sans rapport avec `seed + seg_index`).
RETRY_SEED_STRIDE = 104_729

# Raisons de verdict, dans l'ordre de priorite.
REASON_LEADING_SPAN = "leading_span"
REASON_EMPTY_TRANSCRIPT = "empty_transcript"
REASON_SOURCE_TOO_SHORT = "source_too_short"
REASON_NONE = "none"


def spaced_seed(
    base_seed: int, chunk_index: int, attempt: int, stride: int = RETRY_SEED_STRIDE
) -> int:
    """Graine du re-roll d'un chunk -- formule identique a celle de p5.

    `p5_tts` re-seme le chunk `i` du segment avec
    `seed + i + attempt * _CV3_RETRY_SEED_STRIDE` ; l'`attempt` 0 reproduit
    la graine d'origine, donc un chunk sain ne bouge pas.
    """
    return base_seed + chunk_index + attempt * stride


def head_loss(source_text: str, transcript: str) -> tuple[int, dict | None]:
    """Perte de tete : combien de mots source sont perdus **depuis le mot 0**.

    C'est la definition operationnelle d'un onset-drop : le rendu commence
    plus loin dans le texte source, donc les premiers mots n'ont pas ete
    prononces.

    L'alignement n'est pas reecrit ici : on interroge l'organe d'omission p7
    avec `min_words=1` pour isoler les groupes perdus, puis on mesure la
    perte **contigue depuis le mot 0** (le groupe qui commence au mot 0,
    prolonge par les groupes qui enchainent sans trou). Un groupe qui ne
    commence pas au mot 0 ne compte pas : ce n'est pas l'attaque qui manque,
    c'est un mot d'ailleurs.

    Renvoie `(perte, span_de_tete)`, le span etant celui de p7 (mot 0
    compris) ou `None`.
    """
    spans = _missing_word_spans(source_text, transcript, min_words=1)
    if not spans or int(spans[0]["start"]) != 0:
        return 0, None

    end = int(spans[0]["end"])
    for span in spans[1:]:
        if int(span["start"]) != end:
            break
        end = int(span["end"])
    return end, spans[0]


def detect_missing_attack(
    source_text: str,
    transcript: str,
    min_attack_words: int = ATTACK_MIN_WORDS,
) -> dict:
    """Verdict d'attaque manquante pour un chunk rendu.

    `source_text` est le texte source du chunk, `transcript` ce que l'ASR a
    transcrit du rendu. L'attaque est « manquante » quand les premiers mots
    du texte source n'ont pas ete prononces.

    Le critere est **la perte de tete** (`head_loss`) : le nombre de mots
    source perdus sans trou depuis le mot 0. Il est positionnel, donc il ne
    confond pas une erreur d'ASR sur un mot avec une attaque perdue -- c'est
    le point corrige par la mesure sur rendus reels (voir l'entete du
    module) : un critere de *presence* des mots de tete signalait 9 chunks
    sains sur 10.

    Le seuil est le meme que celui de p7 : une faute de prononciation sur un
    mot ne doit pas etre lue comme une attaque.
    """
    src = _normalize_words(source_text)
    hyp = _normalize_words(transcript)

    if not src:
        return {
            "attack_dropped": False,
            "reason": REASON_SOURCE_TOO_SHORT,
            "n_missing_leading": 0,
            "first_missing_word": None,
            "span": None,
        }

    if not hyp:
        return {
            "attack_dropped": True,
            "reason": REASON_EMPTY_TRANSCRIPT,
            "n_missing_leading": len(src),
            "first_missing_word": src[0],
            "span": None,
        }

    loss, span = head_loss(source_text, transcript)

    if loss >= min_attack_words:
        reason = REASON_LEADING_SPAN
        n_missing = loss
        first_missing = src[0]
    else:
        reason = REASON_NONE
        n_missing = 0
        first_missing = None

    return {
        "attack_dropped": reason != REASON_NONE,
        "reason": reason,
        "n_missing_leading": n_missing,
        "first_missing_word": first_missing,
        "span": span,
    }


def evaluate_chunk(
    chunk: dict,
    transcript: str,
    min_attack_words: int = ATTACK_MIN_WORDS,
) -> dict:
    """Verdict d'un chunk rendu, enrichi de son identite.

    `chunk` porte au minimum `chunk_index` et `text` ; `seed`, `engine` et
    `audio` sont recopies dans le verdict quand ils sont presents.
    """
    verdict = detect_missing_attack(
        chunk.get("text", ""), transcript, min_attack_words=min_attack_words
    )
    out = {
        "chunk_index": chunk.get("chunk_index"),
        "engine": chunk.get("engine"),
        "seed": chunk.get("seed"),
        "audio": chunk.get("audio"),
        "n_words_source": len(_normalize_words(chunk.get("text", ""))),
        "n_words_transcript": len(_normalize_words(transcript)),
        **verdict,
    }
    return out


def plan_reroll(
    chunk: dict,
    base_seed: int,
    attempt: int = 1,
    stride: int = RETRY_SEED_STRIDE,
) -> dict:
    """Re-roll cible d'un chunk fautif : la graine espacee a tenter.

    L'index du chunk est celui **dans le segment** (comme la boucle de rendu
    de p5), pas celui du manifeste : c'est la graine de p5 qu'on reproduit.
    """
    chunk_index = int(chunk.get("chunk_index", 0))
    return {
        "chunk_index": chunk_index,
        "text": chunk.get("text", ""),
        "current_seed": chunk.get("seed"),
        "next_seed": spaced_seed(base_seed, chunk_index, attempt, stride),
        "attempt": attempt,
    }


def evaluate_chunks(
    chunks: list[dict],
    asr_fn: Callable[[dict], str],
    base_seed: int = 42,
    min_attack_words: int = ATTACK_MIN_WORDS,
) -> dict:
    """Verdict par chunk + plan de re-roll, sur un manifeste de chunks rendus.

    `asr_fn` prend un chunk du manifeste et rend sa transcription. Elle est
    injectee : la garde reste testable hors reseau et hors GPU, et le mode
    « en ligne » (chaque chunk verifie juste apres son rendu) est exactement
    cette signature.
    """
    verdicts = []
    for chunk in chunks:
        transcript = asr_fn(chunk)
        verdicts.append(
            evaluate_chunk(chunk, transcript, min_attack_words=min_attack_words)
        )

    faulty = [v for v in verdicts if v["attack_dropped"]]
    rerolls = [
        plan_reroll(
            {
                "chunk_index": v["chunk_index"],
                "text": next(
                    c.get("text", "") for c in chunks if c.get("chunk_index") == v["chunk_index"]
                ),
                "seed": v.get("seed"),
            },
            base_seed,
        )
        for v in faulty
    ]

    return {
        "method": (
            "garde d'attaque par chunk : perte de tete contigue depuis le mot 0 "
            "(organe d'omission p7 interroge a min_words=1) ; re-roll par "
            "graine espacee (pas 104_729)"
        ),
        "n_chunks": len(chunks),
        "n_attack_dropped": len(faulty),
        "min_attack_words": min_attack_words,
        "verdicts": verdicts,
        "reroll_plan": rerolls,
    }


def asr_http(
    chunk: dict,
    model: str = "large-v3-turbo",
    base_url: str = "http://localhost:8190",
    language: str = "fr",
) -> str:
    """Transcription via le serveur Whisper local — meme chemin que p7."""
    import requests as req

    audio = chunk.get("audio")
    if not audio:
        raise ValueError("chunk sans champ 'audio'")
    with open(audio, "rb") as fh:
        resp = req.post(
            f"{base_url.rstrip('/')}/v1/audio/transcriptions",
            files={"file": fh},
            data={"language": language, "model": model},
            headers={"Authorization": f"Bearer {os.getenv('WHISPER_API_KEY', '')}"},
            timeout=120,
        )
    resp.raise_for_status()
    return resp.json().get("text", "")


def asr_local(
    chunk: dict,
    model: str = "openai/whisper-large-v3-turbo",
    device: str = "cuda",
) -> str:
    """Transcription locale (transformers) — chemin auto-portant.

    Le modele est charge une fois par process (cache module) : le garde
    s'appelle en boucle sur les chunks d'un segment.
    """
    audio = chunk.get("audio")
    if not audio:
        raise ValueError("chunk sans champ 'audio'")
    pipe = _local_asr_pipeline(model, device)
    out = pipe(audio, language="fr", generate_kwargs={"task": "transcribe"})
    return out["text"] if isinstance(out, dict) else str(out)


_LOCAL_ASR: dict[tuple[str, str], object] = {}


def _local_asr_pipeline(model: str, device: str):
    key = (model, device)
    if key not in _LOCAL_ASR:
        from transformers import pipeline

        _LOCAL_ASR[key] = pipeline(
            "automatic-speech-recognition", model=model, device=device
        )
    return _LOCAL_ASR[key]


def load_manifest(path: Path) -> dict:
    return json.loads(Path(path).read_text(encoding="utf-8"))


def load_transcripts(path: Path) -> dict[int, str]:
    """Transcriptions indexees par `chunk_index` (produit par le harnais)."""
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    if isinstance(data, dict):
        items = data.get("transcripts", data)
    else:
        items = data
    out: dict[int, str] = {}
    for key, value in items.items():
        if isinstance(value, dict):
            out[int(key)] = value.get("text", "")
        else:
            out[int(key)] = str(value)
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument(
        "--transcripts",
        type=Path,
        help="Transcriptions deja mesurees (JSON {chunk_index: texte}). "
        "Sans cette option, l'ASR est appele sur le moment.",
    )
    parser.add_argument("--asr", choices=("http", "local"), default="http")
    parser.add_argument("--model", default=None, help="Modele ASR (http : large-v3-turbo)")
    parser.add_argument("--device", default="cuda", help="Device ASR local")
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--min-attack-words", type=int, default=ATTACK_MIN_WORDS)
    args = parser.parse_args(argv)

    manifest = load_manifest(args.manifest)
    chunks = manifest["chunks"]
    base_seed = int(manifest.get("base_seed", 42))

    if args.transcripts:
        transcripts = load_transcripts(args.transcripts)

        def asr_fn(chunk: dict) -> str:
            return transcripts.get(int(chunk.get("chunk_index", 0)), "")

    elif args.asr == "http":
        model = args.model or "large-v3-turbo"

        def asr_fn(chunk: dict) -> str:
            return asr_http(chunk, model=model)

    else:
        model = args.model or "openai/whisper-large-v3-turbo"

        def asr_fn(chunk: dict) -> str:
            return asr_local(chunk, model=model, device=args.device)

    report = evaluate_chunks(
        chunks,
        asr_fn,
        base_seed=base_seed,
        min_attack_words=args.min_attack_words,
    )
    report["engine"] = manifest.get("engine")
    report["base_seed"] = base_seed

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(
        json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8"
    )

    n_dropped = report["n_attack_dropped"]
    print(
        "[garde] %d chunk(s) evalue(s), %d attaque(s) manquante(s) -> %s"
        % (report["n_chunks"], n_dropped, args.out)
    )
    for plan in report["reroll_plan"]:
        print(
            "  chunk %s : graine %s -> %s (a re-rouler)"
            % (plan["chunk_index"], plan["current_seed"], plan["next_seed"])
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
