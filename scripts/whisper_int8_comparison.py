"""Compare faster-whisper transcription quality: float16 vs int8_float16.

Uses Kokoro TTS to generate reference French phrases, then sends them
to the Whisper API for transcription. Compares word accuracy.
"""

import os
import json
import time
import tempfile
import requests

# Test phrases (French, varied difficulty)
TEST_PHRASES = [
    "Bonjour, comment allez-vous aujourd'hui ?",
    "L'intelligence artificielle transforme de nombreux secteurs industriels.",
    "Le marché boursier a enregistré une hausse significative ce matin.",
    "Les étudiants préparent leurs examens de fin de semestre.",
    "NanoClaw est un assistant vocal conçu pour la maison connectée.",
]

TTS_URL = "http://127.0.0.1:8191/v1/audio/speech"
STT_URL = "http://127.0.0.1:8190/v1/audio/transcriptions"
TTS_API_KEY = os.getenv("TTS_API_KEY", "BwCaesdZuitLAfs6Nr1KX_CVNhX12XavyZThvpT2RD4c1smVrQ00xfZY2PP2pYgK")
STT_API_KEY = os.getenv("WHISPER_API_KEY", "BwCaesdZuitLAfs6Nr1KX_CVNhX12XavyZThvpT2RD4c1smVrQ00xfZY2PP2pYgK")


def generate_audio(text: str, output_path: str) -> bool:
    """Generate audio via Kokoro TTS."""
    resp = requests.post(
        TTS_URL,
        json={"input": text, "voice": "af_bella", "response_format": "wav"},
        headers={"Authorization": f"Bearer {TTS_API_KEY}"},
        timeout=30,
    )
    if resp.status_code == 200:
        with open(output_path, "wb") as f:
            f.write(resp.content)
        return True
    print(f"  TTS error: {resp.status_code} {resp.text[:100]}")
    return False


def transcribe(audio_path: str) -> dict:
    """Send audio to Whisper API."""
    with open(audio_path, "rb") as f:
        resp = requests.post(
            STT_URL,
            files={"file": (os.path.basename(audio_path), f, "audio/wav")},
            data={"language": "fr", "response_format": "verbose_json"},
            headers={"Authorization": f"Bearer {STT_API_KEY}"},
            timeout=60,
        )
    if resp.status_code == 200:
        return resp.json()
    print(f"  STT error: {resp.status_code} {resp.text[:100]}")
    return {"error": resp.status_code, "text": ""}


def normalize(text: str) -> str:
    """Normalize text for comparison."""
    return text.lower().strip().replace(",", "").replace("?", "").replace(".", "").replace("!", "")


def word_accuracy(reference: str, hypothesis: str) -> float:
    """Simple word-level accuracy."""
    ref_words = normalize(reference).split()
    hyp_words = normalize(hypothesis).split()
    if not ref_words:
        return 1.0
    matches = sum(1 for w in ref_words if w in hyp_words)
    return matches / len(ref_words)


def run_test(compute_label: str) -> list:
    """Run full test suite and return results."""
    print(f"\n{'='*60}")
    print(f"Testing with: {compute_label}")
    print(f"{'='*60}")
    results = []

    with tempfile.TemporaryDirectory() as tmpdir:
        for i, phrase in enumerate(TEST_PHRASES):
            audio_path = os.path.join(tmpdir, f"phrase_{i}.wav")

            # Generate audio
            if not generate_audio(phrase, audio_path):
                results.append({"phrase": phrase, "error": "TTS failed"})
                continue

            # Transcribe
            result = transcribe(audio_path)
            if "error" in result:
                results.append({"phrase": phrase, "error": f"STT {result['error']}"})
                continue

            hypothesis = result.get("text", "")
            accuracy = word_accuracy(phrase, hypothesis)
            duration = result.get("duration", 0)

            results.append({
                "phrase": phrase,
                "hypothesis": hypothesis,
                "accuracy": accuracy,
                "duration": duration,
            })

            status = "OK" if accuracy >= 0.8 else "LOW"
            print(f"  [{status}] ({accuracy:.0%}) {hypothesis[:60]}...")
            time.sleep(0.5)  # Rate limit

    return results


def print_summary(label: str, results: list):
    avg_acc = sum(r.get("accuracy", 0) for r in results) / max(len(results), 1)
    ok_count = sum(1 for r in results if r.get("accuracy", 0) >= 0.8)
    print(f"\n{label}: avg accuracy={avg_acc:.1%}, {ok_count}/{len(results)} phrases OK")
    return avg_acc


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("--skip-generate", action="store_true", help="Skip generation, use cached")
    args = parser.parse_args()

    # Run test with current compute type
    compute_type = os.getenv("WHISPER_COMPUTE_TYPE", "unknown")
    print(f"Current compute_type from env: {compute_type}")
    print("Model will lazy-load on first request (may take ~15s)...")

    results = run_test("current-config")

    # Detect actual compute type from API
    try:
        health = requests.get("http://127.0.0.1:8190/health", timeout=5).json()
        gpu_mem = health.get("gpu_memory_gb", "unknown")
        model_loaded = health.get("model_loaded", False)
    except Exception:
        gpu_mem = "unknown"
        model_loaded = False

    avg = print_summary("Current", results)

    # Save results
    output = {
        "compute_type": compute_type,
        "gpu_memory_gb": gpu_mem,
        "model_loaded": model_loaded,
        "avg_accuracy": avg,
        "results": results,
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S"),
    }
    output_path = os.path.join(os.path.dirname(__file__), "whisper_comparison_results.json")
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(output, f, ensure_ascii=False, indent=2)
    print(f"\nResults saved to {output_path}")
    print(f"GPU memory reported: {gpu_mem}GB, model_loaded: {model_loaded}")
