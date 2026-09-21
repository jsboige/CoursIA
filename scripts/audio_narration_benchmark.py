#!/usr/bin/env python3
"""Benchmark expressif des moteurs TTS exposes par tts-multi (#15604, tranche 2).

**Scope tranche 2 (issue #15604 - narration slammée)** :

L'EPIC #15604 (feat(genai-audio): pipeline livecoding-video - narration slammée
+ capture Strudel + TTS expressif) se décompose en 3 étapes. La tranche 1
(#16259, MERGED) a livré la composition Strudel multi-pistes via template.
Cette tranche-ci ouvre la voie TTS expressif et **compare objectivement les 3
moteurs SOTA** exposes par le gateway `tts-multi` (port 8196) :

| Moteur    | Backend            | VRAM  | Voix            | Expressivité                |
|-----------|--------------------|-------|-----------------|-----------------------------|
| Kokoro    | kokoro-v0_19       | ~2GB  | 6 (af_sky...)   | Standard, rapide            |
| TADA 3B   | HumeAI/tada-3b-ml  | ~6GB  | 1 (default)     | Expressive (prosodie/émotion)|
| Qwen3 TTS | Qwen3-TTS-12Hz-1.7B-CustomVoice | ~4GB | multiple (default, female, male, custom1-3) | Custom voice cloning |

Le benchmark envoie le même texte de narration slammée aux 3 moteurs, mesure
latence, taille du WAV généré, et fournit une grille d'évaluation qualitative.
Aucun appel reel n'est fait si `--dry-run` ; les appels reels passent par
les endpoints documentes du gateway `tts-multi`.

**Voie 3 B.0 (retrait consenti)** : aucune voix clonee, aucun verbatim.
Les voix testees sont les voix STANDARD des modeles. Pour SwitchAngel, le
mecanisme est documente dans `narration_slammee_sota_verdict.md` mais
l'implementation necessite un echantillon audio de référence (RECOVERABLE-USER-HAND).

**Pourquoi ce benchmark plutot qu'une narration reelle ?** Le verdict SOTA
de la tranche 2 est : "Qwen3-TTS CustomVoice est le candidat SOTA si on dispose
d'un echantillon de voix, sinon TADA 3B pour l'expressivité pure, sinon Kokoro
pour la latence". Le verdict est pose sur des **metriques mesurees** quand le gateway est
joignable (mode live : `latency_s` = temps observe), ou sur des **metriques
documentees** en mode `--dry-run` (la table "Recommandation" derive alors
`min(results, key=latency_s)` des `expected_latency_s` EngineSpec, le reste
des lignes reste un verdict SOTA pre-benche qui sera renseigne par la
tranche 3). La tranche 3 (TTS expressif couple a la composition Strudel de
la tranche 1) s'appuiera sur ce verdict pour fixer le moteur.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path

# --- Configuration -----------------------------------------------------------

DEFAULT_GATEWAY = "http://localhost:8196"
DEFAULT_OUTPUT_DIR = Path("MyIA.AI.Notebooks/GenAI/Audio/04-Applications/benchmark_output/narration_slammee")

# Texte de reference : un extrait de narration slammée (style "spoken word"
# urbain, rhythmé, exclamations, jeu sur la prosodie). 4 phrases, ~280 chars,
# sous le seuil d'inactivité du gateway (lazy-loading 1200s).
NARRATION_REFERENCE = (
    "Ecoute bien. Le code vit, le code meurt, le code recommence. "
    "Strudel frappe, Kokoro murmure, Qwen3 chante. "
    "Trois moteurs, une seule voix : la tienne. "
    "Pas la mienne. La tienne, brute, enfin."
)

# Voix par défaut — voicis STANDARD des modèles,pas de voix clonée.
DEFAULT_VOICES = {
    "kokoro": "af_sky",
    "tada": "default",
    "qwen3": "default",
}


@dataclass(frozen=True)
class EngineSpec:
    key: str
    label: str
    path: str             # path-prefix du gateway pour ce moteur
    voice_default: str
    expected_latency_s: float   # indicatif, mesuré au benchmark
    expressivity: str           # verdict qualitatif pré-bench


ENGINES: tuple[EngineSpec, ...] = (
    EngineSpec(
        key="kokoro", label="Kokoro v0.19",
        path="/v1/audio/speech", voice_default="af_sky",
        expected_latency_s=0.8,
        expressivity="Standard : prosodie propre mais peu de variation émotionnelle.",
    ),
    EngineSpec(
        key="tada", label="TADA 3B ML (HumeAI)",
        path="/tada/v1/audio/speech", voice_default="default",
        expected_latency_s=2.5,
        expressivity="Expressive : prosodie + émotion, voix unique (limitation connue).",
    ),
    EngineSpec(
        key="qwen3", label="Qwen3-TTS-12Hz-1.7B-CustomVoice",
        path="/qwen/v1/audio/speech", voice_default="default",
        expected_latency_s=1.5,
        expressivity="CustomVoice : voix par défaut + slot custom1-3 (nécessite échantillon).",
    ),
)


@dataclass
class BenchmarkResult:
    engine: str
    label: str
    voice: str
    latency_s: float
    wav_bytes: int
    status: str  # "ok", "dry-run", "error:<message>"
    error: str | None = None
    notes: list[str] = field(default_factory=list)


# --- Core : appel HTTP vers le gateway --------------------------------------

def call_tts_engine(gateway: str, engine: EngineSpec, text: str, voice: str,
                    timeout_s: float = 30.0) -> tuple[bytes, float, str | None]:
    """Appel un moteur TTS via le gateway. Retourne (wav_bytes, latency, error)."""
    import urllib.request
    import urllib.error

    url = f"{gateway}{engine.path}"
    payload = json.dumps({"model": engine.key, "input": text, "voice": voice}).encode("utf-8")
    req = urllib.request.Request(
        url, data=payload,
        headers={"Content-Type": "application/json"}, method="POST",
    )
    t0 = time.perf_counter()
    try:
        with urllib.request.urlopen(req, timeout=timeout_s) as resp:
            data = resp.read()
        return data, time.perf_counter() - t0, None
    except urllib.error.URLError as e:
        return b"", time.perf_counter() - t0, f"URLError: {e.reason}"
    except Exception as e:
        return b"", time.perf_counter() - t0, f"{type(e).__name__}: {e}"


# --- Dry-run : verdict SOTA documente, sans appel reel ----------------------

def dry_run_benchmark(text: str, output_dir: Path) -> list[BenchmarkResult]:
    """Génère un benchmark dry-run : verdict SOTA documenté, pas d'appels réseau."""
    output_dir.mkdir(parents=True, exist_ok=True)
    results: list[BenchmarkResult] = []

    for engine in ENGINES:
        result = BenchmarkResult(
            engine=engine.key,
            label=engine.label,
            voice=DEFAULT_VOICES[engine.key],
            latency_s=engine.expected_latency_s,
            wav_bytes=0,  # dry-run, pas de WAV produit
            status="dry-run",
            notes=[
                f"verdict expressivité pré-bench : {engine.expressivity}",
                f"path gateway : {engine.path}",
                "aucun appel réseau effectué (--dry-run)",
            ],
        )
        results.append(result)
        print(f"[dry-run] {engine.key:6s} latence_attendue={engine.expected_latency_s:>4.1f}s "
              f"voix={result.voice} expressivité={engine.expressivity[:60]}...")

    return results


# --- Live : appel reel -------------------------------------------------------

def live_benchmark(text: str, output_dir: Path, gateway: str) -> list[BenchmarkResult]:
    """Lance le benchmark live : un appel HTTP par moteur, écrit les WAV."""
    output_dir.mkdir(parents=True, exist_ok=True)
    results: list[BenchmarkResult] = []

    for engine in ENGINES:
        voice = DEFAULT_VOICES[engine.key]
        wav, latency, err = call_tts_engine(gateway, engine, text, voice)
        if err is None:
            wav_path = output_dir / f"{engine.key}_benchmark.wav"
            wav_path.write_bytes(wav)
            results.append(BenchmarkResult(
                engine=engine.key, label=engine.label, voice=voice,
                latency_s=latency, wav_bytes=len(wav), status="ok",
                notes=[f"WAV ecrit : {wav_path}"],
            ))
            print(f"[ok]   {engine.key:6s} latence={latency:>5.2f}s wav={len(wav):>6d}o -> {wav_path}")
        else:
            results.append(BenchmarkResult(
                engine=engine.key, label=engine.label, voice=voice,
                latency_s=latency, wav_bytes=0, status=f"error:{err[:60]}",
                error=err,
            ))
            print(f"[err]  {engine.key:6s} latence={latency:>5.2f}s ERREUR: {err}")

    return results


# --- Verdict SOTA ------------------------------------------------------------

def _render_verdict_md(text: str, results: list[BenchmarkResult]) -> str:
    """Génère un verdict SOTA markdown avec verdict par moteur + recommandation."""
    lines = [
        "# Verdict SOTA — benchmark expressivité TTS (#15604 tranche 2)",
        "",
        "**Texte de référence** (extrait narration slammée, ~280 chars) :",
        "",
        f"> {text}",
        "",
        "**Tableau des résultats** :",
        "",
        "| Moteur | Voix | Latence | Taille WAV | Statut |",
        "|--------|------|--------:|-----------:|--------|",
    ]
    for r in results:
        lines.append(
            f"| `{r.engine}` ({r.label}) | `{r.voice}` | "
            f"{r.latency_s:.2f}s | {r.wav_bytes}o | {r.status} |"
        )
    # Table "Recommandation par cas d'usage" :
    # - La ligne "Latence minimale" est DERIVÉE des résultats mesurés (`latency_s`
    #   = observé en live, ou `expected_latency_s` EngineSpec en dry-run).
    # - Les autres lignes sont un verdict SOTA PRÉ-BENCHÉ documenté ; la tranche
    #   3 les renseignera avec les résultats live.
    live_results = [r for r in results if r.status in ("ok", "dry-run")]
    if live_results:
        fastest = min(live_results, key=lambda r: r.latency_s)
        latency_str = f"{fastest.latency_s:.2f}s"
    else:
        fastest = None
        latency_str = "indisponible"
    lines.append("")
    lines.append("## Recommandation par cas d'usage")
    lines.append("")
    lines.append("| Cas d'usage | Moteur recommandé | Justification |")
    lines.append("|-------------|-------------------|---------------|")
    if fastest is not None:
        lines.append(
            f"| Latence minimale | `{fastest.engine}` | {latency_str} (derive des resultats "
            f"{'live' if any(r.status == 'ok' for r in results) else 'dry-run'}) |"
        )
    else:
        lines.append("| Latence minimale | (indisponible) | Aucun resultat exploitable |")
    lines.append("| Expressivité maximale (sans clonage) | `tada` | Prosodie + émotion HumeAI |")
    lines.append("| Clonage de voix (voie SwitchAngel) | `qwen3` (custom1-3) | Slot dédié, échantillon requis |")
    lines.append("| Mix des trois | Pipeline composite | Kokoro narration + TADA emphasis + Qwen3 refrain |")
    lines.append("")
    lines.append("## Notes")
    lines.append("")
    lines.append("- Aucune voix clonée, aucun verbatim testé. Voix STANDARD uniquement (voie 3 B.0).")
    lines.append("- Pour le clonage SwitchAngel, un échantillon audio de référence est requis (RECOVERABLE-USER-HAND).")
    lines.append("- Ce script est un **bénéfice collatéral** de la tranche 2 : il ne ferme pas la tranche mais documente le verdict.")
    return "\n".join(lines) + "\n"


# --- Main --------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(
        description="Benchmark expressif des moteurs TTS (tts-multi) — tranche 2 EPIC #15604",
    )
    parser.add_argument("--gateway", default=DEFAULT_GATEWAY,
                        help=f"URL du gateway tts-multi (defaut: {DEFAULT_GATEWAY})")
    parser.add_argument("--text", default=NARRATION_REFERENCE,
                        help="Texte de référence à synthétiser")
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR,
                        help="Répertoire de sortie pour les WAV + verdict")
    parser.add_argument("--dry-run", action="store_true",
                        help="N'appelle pas le gateway : verdict SOTA documenté, pas de WAV produit")
    parser.add_argument("--json", action="store_true",
                        help="Sortie JSON machine-parseable en plus du verdict MD")
    args = parser.parse_args()

    print(f"[benchmark] gateway={args.gateway} output={args.output_dir} "
          f"dry_run={args.dry_run}")

    if args.dry_run:
        results = dry_run_benchmark(args.text, args.output_dir)
    else:
        results = live_benchmark(args.text, args.output_dir, args.gateway)

    # Le verdict SOTA est concu pour vivre dans le notebook 04-5 (cellules markdown)
    # ou en sortie stdout pour intégration. On ne l'ecrit PAS dans le worktree :
    # un fichier MD sous benchmark_output/ n'est PAS gitignored par défaut et
    # contaminerait la PR (cf git-workflow § Jamais un PR_BODY.md dans le worktree).
    print("\n[verdict SOTA — copier-coller dans le notebook 04-5 ou rediriger stdout]")
    print(_render_verdict_md(args.text, results))

    if args.json:
        json_path = args.output_dir / "benchmark_results.json"
        json_path.write_text(
            json.dumps([asdict(r) for r in results], indent=2, ensure_ascii=False),
            encoding="utf-8",
        )
        print(f"[json] {json_path}")

    # Exit code : 0 si tous ok ou dry-run, 1 si une erreur live.
    return 0 if all(r.status in ("ok", "dry-run") for r in results) else 1


if __name__ == "__main__":
    sys.exit(main())
