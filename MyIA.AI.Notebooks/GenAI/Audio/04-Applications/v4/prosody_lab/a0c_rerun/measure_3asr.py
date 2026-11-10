"""measure_3asr.py — mesure WER normalise + omissions par alignement mot a mot + prosodie.

Cadrage audio c.1467 + diagnostique c.6115711862 (#19695) :
- WER par distance de Levenshtein sur la normalisation de p7_verify (NFC,
  lower, alnum->space, whitespace squeeze). Le seuil de 0,15 (c.6034723389)
  porte sur ce WER normalise, pas sur le split() brut.
- Omissions = runs de >= 3 mots de reference SUPPRIMES a l'alignement
  (`difflib.SequenceMatcher` opcodes `delete` + excedent `replace` >= 3),
  vote >= 2 ASR sur un recouvrement >= 3 mots. Un mot substitue ne casse
  pas une omission : le verdict tranche sur la disparition du passage.
- Set ASR par defaut : tiny, large-v3, large-v3-turbo (pas small).
- Jambe prosodie : `verify_prosody.py --single <wav>` imprime un rapport
  JSON sur stdout (bakeoff_large/banc_phase_a0.py:117-120). Stocke dans
  `metrics["prosody"]`.

Entree : un fichier .wav + le texte de reference + un metrics.json existant.
Sortie : enrichit le metrics.json en place (champs `wer`, `omissions`,
`prosody`).
"""
from __future__ import annotations

import argparse
import difflib
import json
import re
import subprocess
import sys
import time
import unicodedata
from pathlib import Path

# p7_verify est un voisin du dossier prosody_lab (04-Applications/v4/).
# `_normalize_words` est une fonction pure, mais p7_verify.py utilise un
# import relatif (`from .schemas import QualityReport`) au top-level qui
# casse quand on l'importe en module plat. On reproduit ici la convention
# exacte de p7_verify._normalize_words (cf. c.6034723389) -- l'inline est
# la solution deja employee par A0C-remesure-20261012-method.py du
# coordinateur (cf. diagnostic c.6115711862).
def _normalize_words(text: str) -> list[str]:
    import re
    import unicodedata
    text = unicodedata.normalize("NFC", text).lower()
    text = "".join(c if c.isalnum() else " " for c in text)
    return re.sub(r"\s+", " ", text).strip().split()

ROOT = Path(__file__).resolve().parents[7]  # repo root
VERIFY_PROSODY = ROOT / "scripts" / "tts_verification" / "verify_prosody.py"


def _lev(r: list[str], h: list[str]) -> float:
    """Distance de Levenshtein normalisee par la longueur de la reference."""
    n, m = len(r), len(h)
    dp = list(range(m + 1))
    for i in range(1, n + 1):
        prev, dp[0] = dp[0], i
        for j in range(1, m + 1):
            cur = dp[j]
            dp[j] = prev if r[i - 1] == h[j - 1] else 1 + min(prev, dp[j], dp[j - 1])
            prev = cur
    return dp[m] / max(n, 1)


def _deletion_runs(r: list[str], h: list[str], min_words: int = 3) -> list[tuple[int, int]]:
    """Runs de reference SUPPRIMES a l'alignement, >= min_words.

    Source : methode de remesure du coordinateur (c.6115711862). Les
    `replace` dont la reference est plus longue que l'hypothese de >=
    min_words mots comptent aussi comme suppressions : un ASR qui entend
    la moitie d'un passage declare une omission, meme si les quelques mots
    qu'il rend ne s'alignent pas en `equal`.
    """
    out: list[tuple[int, int]] = []
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, r, h, autojunk=False).get_opcodes():
        if tag == "delete" and i2 - i1 >= min_words:
            out.append((i1, i2))
        elif tag == "replace" and (i2 - i1) - (j2 - j1) >= min_words:
            out.append((i1, i2))
    return out


def _vote_omissions(
    runs_by_asr: dict[str, list[tuple[int, int]]],
    k: int = 2,
    min_overlap: int = 3,
) -> list[tuple[int, int, tuple[str, ...]]]:
    """Vote >= k ASR par recouvrement >= min_overlap mots (c.6115711862)."""
    flat = [(a, b, name) for name, rs in runs_by_asr.items() for a, b in rs]
    raw: list[tuple[int, int, tuple[str, ...]]] = []
    for a, b, name in flat:
        supporters = {
            n2 for a2, b2, n2 in flat if min(b, b2) - max(a, a2) >= min_overlap
        }
        if len(supporters) >= k:
            raw.append((a, b, tuple(sorted(supporters))))
    # dedupe : le plus large gagne quand des runs se chevauchent
    raw.sort(key=lambda x: (x[0], -(x[1] - x[0])))
    merged: list[tuple[int, int, tuple[str, ...]]] = []
    for a, b, s in raw:
        if merged and a < merged[-1][1]:
            if b - a > merged[-1][1] - merged[-1][0]:
                merged[-1] = (a, b, s)
            continue
        merged.append((a, b, s))
    return merged


def _transcribe_with_faster_whisper(wav_path: str, model_size: str, device: str) -> str:
    """Transcrit via faster-whisper, retourne la chaine hyp complete."""
    from faster_whisper import WhisperModel
    wm = WhisperModel(
        model_size,
        device=device if device == "cuda" else "cpu",
        compute_type="float16" if device == "cuda" else "int8",
    )
    segments, _info = wm.transcribe(wav_path, language="fr", beam_size=5)
    return " ".join(seg.text for seg in segments).strip()


def _run_verify_prosody(wav_path: Path) -> dict:
    """Subprocess vers verify_prosody.py --single, retourne le dict JSON parse.

    stdout est un rapport JSON (cf banc_phase_a0.py:117-120). En cas
    d'echec (rc != 0 ou JSON absent), on retourne un dict `{"error": ...}`
    -- la branche metrics['prosody'] reste informative sans bloquer la mesure.
    """
    if not VERIFY_PROSODY.exists():
        return {"error": f"verify_prosody.py introuvable a {VERIFY_PROSODY}"}
    try:
        proc = subprocess.run(
            [sys.executable, str(VERIFY_PROSODY), "--single", str(wav_path)],
            capture_output=True, text=True, encoding="utf-8", timeout=300,
        )
    except subprocess.TimeoutExpired:
        return {"error": "verify_prosody timeout (300s)"}
    if proc.returncode != 0:
        return {
            "error": f"verify_prosody exit={proc.returncode}",
            "stderr_tail": proc.stderr[-400:] if proc.stderr else "",
        }
    # La sortie est un rapport verbatim (table ASCII + dernier bloc JSON)
    out = proc.stdout.strip()
    # Strategy : parser la derniere ligne qui ressemble a {...} sur une seule ligne
    for line in reversed(out.splitlines()):
        s = line.strip()
        if s.startswith("{") and s.endswith("}"):
            try:
                return json.loads(s)
            except json.JSONDecodeError:
                continue
    return {"raw_tail": out[-800:], "parse": "no-json-line"}


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--wav", required=True, type=Path)
    p.add_argument("--ref-text-file", required=True, type=Path)
    p.add_argument("--metrics-json", required=True, type=Path,
                   help="metrics.json a enrichir (le script ecrit en place).")
    p.add_argument("--asr-models", nargs="+",
                   default=["tiny", "large-v3", "large-v3-turbo"],
                   help="Set ASR (defaut : tiny, large-v3, large-v3-turbo).")
    p.add_argument("--device", default="cuda")
    p.add_argument("--skip-prosody", action="store_true",
                   help="Sauter la jambe verify_prosody (debug).")
    args = p.parse_args()

    if not args.wav.exists():
        print(f"WAV introuvable : {args.wav}", file=sys.stderr)
        return 2
    if not args.ref_text_file.exists():
        print(f"Ref texte introuvable : {args.ref_text_file}", file=sys.stderr)
        return 2
    if not args.metrics_json.exists():
        print(f"metrics.json introuvable : {args.metrics_json}", file=sys.stderr)
        return 2

    ref_text = args.ref_text_file.read_text(encoding="utf-8").strip()
    ref_norm = _normalize_words(ref_text)

    print(f"=== Mesure 3-ASR sur {args.wav.name} ===")
    print(f"  Ref : {len(ref_text)} chars, {len(ref_norm)} mots (normalises)")
    print(f"  ASR : {args.asr_models}")
    print()

    metrics = json.loads(args.metrics_json.read_text(encoding="utf-8"))
    hyps: dict[str, str] = {}
    hyps_norm: dict[str, list[str]] = {}
    wer_by_model: dict[str, dict] = {}
    for model_size in args.asr_models:
        t0 = time.time()
        try:
            hyp = _transcribe_with_faster_whisper(str(args.wav), model_size, args.device)
        except Exception as e:
            print(f"  [{model_size}] ECHEC : {e}", file=sys.stderr)
            wer_by_model[model_size] = {"error": str(e)}
            continue
        dt = time.time() - t0
        hyp_n = _normalize_words(hyp)
        wer = _lev(ref_norm, hyp_n)
        hyps[model_size] = hyp
        hyps_norm[model_size] = hyp_n
        wer_by_model[model_size] = {
            "wer": round(float(wer), 4),
            "wer_pct": round(wer * 100, 2),
            "hyp_words": len(hyp_n),
            "wallclock_s": round(dt, 1),
        }
        print(f"  [{model_size}] WER norm = {wer*100:.2f}% ({len(hyp_n)} mots, {dt:.1f}s)")

    # Omissions : runs de reference supprimes a l'alignement, vote >= 2 ASR
    omissions = None
    if len(hyps_norm) >= 2:
        runs_by_asr = {a: _deletion_runs(ref_norm, h, 3) for a, h in hyps_norm.items()}
        voted = _vote_omissions(runs_by_asr, k=2, min_overlap=3)
        print(f"\n  Omissions (>= 3 mots, vote >= 2 ASR) : {len(voted)} span(s)")
        for a, b, supporters in voted:
            txt = " ".join(ref_norm[a:b])
            print(f"    - « {txt[:80]}{'...' if len(txt) > 80 else ''} » "
                  f"({b - a} mots) sous {supporters}")
        omissions = {
            "n_omitted": len(voted),
            "n_omitted_3asr": sum(1 for v in voted if len(v[2]) >= 3),
            "segments": [
                {
                    "ref_slice": " ".join(ref_norm[a:b]),
                    "n_words": b - a,
                    "supporters": list(supporters),
                }
                for a, b, supporters in voted
            ],
            "per_asr_runs": {
                a: [{"ref_slice": " ".join(ref_norm[x:y]), "n_words": y - x}
                    for x, y in rs]
                for a, rs in runs_by_asr.items()
            },
        }

    # Jambe prosodie : verify_prosody --single
    prosody = None
    if not args.skip_prosody:
        print("\n  Prosodie (verify_prosody --single)...")
        t0 = time.time()
        prosody = _run_verify_prosody(args.wav)
        dt = time.time() - t0
        if "error" in prosody:
            print(f"    [WARN] {prosody['error']} ({dt:.1f}s)")
        else:
            gv = prosody.get("g_verdict", "?")
            sv = prosody.get("s_verdict", "?")
            print(f"    global={gv} syll={sv} ({dt:.1f}s)")

    # Mise a jour metrics.json
    metrics["wer"] = {
        "by_model": wer_by_model,
        "ref_text_file": str(args.ref_text_file),
        "hyps_full": hyps,
        "normalization": "p7_verify._normalize_words (NFC, lower, alnum->space, split)",
    }
    metrics["omissions"] = omissions
    if prosody is not None:
        metrics["prosody"] = prosody
    args.metrics_json.write_text(json.dumps(metrics, indent=2, ensure_ascii=False),
                                 encoding="utf-8")
    print(f"\n  metrics.json enrichi : {args.metrics_json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
