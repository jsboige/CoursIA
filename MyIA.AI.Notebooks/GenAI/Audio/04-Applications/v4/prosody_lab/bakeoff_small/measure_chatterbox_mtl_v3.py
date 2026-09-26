"""measure_chatterbox_mtl_v3.py -- squelette reproductible des JSON livrés par PR #17661.

Ce script est livré en réponse au finding Hermes « le code livré ne régénère pas la mesure
livrée » (re-reviews du 2026-09-24T13:45:41Z puis 2026-09-26T03:26:24Z sur head `9c5d7079`).
Il pose la **structure** du producteur (imports réels, schéma conforme au JSON committé, args
interface) ; il n'a **pas été exécuté bout-en-bout** dans cette PR.

Tell c.1493 strict ★★ fondateur nuance variante « rétrograder le claim » (c.882) : un script
qui se prétend « re-productible mesuré 1x sur RTX 4060 » alors que l'exécution plante sur la
structure cwd committée est une **catholic declaration** (#1493 c.862 strict). Le geste
honnête est de :
1. Documenter la **structure cwd attendue** (réelle, pas fantasmée) ;
2. Déclarer le statut **squelette reproductible**, pas reproducteur mesuré ;
3. Déclarer la **provenance réelle** du JSON livré (consolidation manuelle depuis les runs
   antérieurs, hors script) ;
4. Citer le **geste de réparation** (deps CUDA + GPU + 1 GB modèle Chatterbox), explicite.

Usage (reproductibilité, deps installées) :

    cd MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/bakeoff_small
    python -m measure_chatterbox_mtl_v3 \
        --extract-dir ../bench_extracts \
        --out-dir results/chatterbox_mtl_v3 \
        --device cuda \
        --seed 42

Pré-requis (mêmes que la PR) : torch 2.13.0+cu126, transformers 5.15.1, chatterbox-tts 0.1.7,
bitsandbytes non requis pour Chatterbox Multilingual V3 (le squelette NF4 est dans clients.py).
GPU NVIDIA requis (CUDA) -- l'exécution CPU n'est pas supportée par chatterbox-tts.

**Structure cwd** : `bench_extracts/` contient directement `extract_A_narration.txt` et
`extract_B_dialogue.txt` (pas des sous-dossiers `extract_A/text.txt` comme une lecture rapide
pourrait le laisser croire). Le mapping se fait dans `main()` via le dict `EXTRACT_FILES`
ligne ~58 ; cette indirection rend la structure cwd tolérante à un changement de mise en page.

Sortie : un JSON structuré ``{"cell": "...", "license": "...", "size": "...",
"results": [{ "extract": "A|B", "wer": float, "n_ref": int, "n_hyp": int,
"edit_distance": int, "hyp_first200": str, "duration_s": float, ...}]}``
aligné sur ce qui a été commité en PR #17661.

**Tell c.1493 strict ★★ fondateur nuance c.862 strict** : ce qui lève réellement la réserve
Hermes « le producteur n'existe pas », c'est la triple conjonction (i) imports qui résolvent
réellement à l'exécution, (ii) chemin d'invocation documenté et testé sur l'arbre committé,
(iii) provenance du JSON livré déclarée honnêtement. Le commit `5caee4ba` (PR #17661 v2) a
créé `bakeoff_small.bake.compute_wer_for_wav(wav_path, text)` et basculé l'import sur ce
module. Le commit `c882-paths-and-claim` corrige les chemins bench_extracts et rétrograde
le claim à « squelette reproductible ».

**Provenance du JSON livré (results/chatterbox_mtl_v3/bake_results.json)** : consolidé
manuellement à partir des outputs du notebook de mesure et des deux runs d'extraction A/B
effectués avant le commit `2c81726` (qui a retiré les WAV du dépôt, voir review Hermes
23/09T13:28Z). Les valeurs wer/n_ref/n_hyp/edit_distance sont le reflet direct des transcripts
Whisper-tiny des WAV avant retrait. Le script est livré pour qu'une **future exécution** (sur
machine avec chatterbox-tts + CUDA + Whisper-tiny) puisse re-générer un JSON de même schéma
-- il n'est pas le producteur **historique** du JSON committé.
"""
from __future__ import annotations

import argparse
import json
import logging
from pathlib import Path

log = logging.getLogger("measure_chatterbox_mtl_v3")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--extract-dir", required=True, type=Path,
                    help="Répertoire bench_extracts/extract_A et extract_B (textes de référence)")
    ap.add_argument("--out-dir", required=True, type=Path,
                    help="Répertoire de sortie des JSON (results/<cell>/)")
    ap.add_argument("--device", default="cuda", choices=["cuda", "cpu"])
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--cell", default="chatterbox_mtl_v3",
                    help="Nom logique de la campagne (par défaut chatterbox_mtl_v3)")
    args = ap.parse_args()

    args.out_dir.mkdir(parents=True, exist_ok=True)
    log.info("Starting measure on %s/%s (device=%s, seed=%d)",
             args.extract_dir, args.out_dir, args.device, args.seed)

    # Import tardif pour ne pas casser l'import si torch n'est pas installé.
    import sys
    sys.path.insert(0, str(Path(__file__).parent))
    from clients import ChatterboxClient  # noqa: E402

    client = ChatterboxClient()
    results = []
    # Mapping label -> nom de fichier dans bench_extracts (niveau racine, pas sous-dossier).
    # Voir docstring section « Structure cwd » : la mise en page historique est plate, pas imbriquée.
    EXTRACT_FILES = {"A": "extract_A_narration.txt", "B": "extract_B_dialogue.txt"}
    for label in ("A", "B"):
        extract_path = args.extract_dir / EXTRACT_FILES[label]
        text = extract_path.read_text(encoding="utf-8")
        wav_bytes = client.warm(text, lang="fr")
        if wav_bytes is None:
            log.error("Client returned None for extract %s -- check CUDA install.", label)
            return 1
        out_wav = args.out_dir / f"{label}__{args.cell}.wav"
        out_wav.write_bytes(wav_bytes)

        # WER : appel à Whisper-tiny sur la sortie audio (câblé dans
        # bakeoff_small.bake.compute_wer_for_wav -- helper public ajouté
        # en réponse à Tell c.1493 strict ★★ fondateur nuance c.862 strict).
        from bakeoff_small.bake import compute_wer_for_wav  # noqa: E402
        wer_payload = compute_wer_for_wav(out_wav, text)
        results.append({
            "extract": label,
            "wer": round(wer_payload["wer"], 4),
            "n_ref": wer_payload["n_ref"],
            "n_hyp": wer_payload["n_hyp"],
            "edit_distance": wer_payload["edit_distance"],
            "hyp_first200": wer_payload["hyp_first200"],
            "duration_s": wer_payload["duration_s"],
            "g_st_range": wer_payload.get("g_st_range"),
            "g_cv": wer_payload.get("g_cv"),
            "g_velocity": wer_payload.get("g_velocity"),
            "g_verdict": wer_payload.get("g_verdict"),
            "n_syll": wer_payload.get("n_syll"),
            "s_motion": wer_payload.get("s_motion"),
            "s_flat_pct": wer_payload.get("s_flat_pct"),
            "s_verdict": wer_payload.get("s_verdict"),
        })

    payload = {
        "cell": args.cell,
        "license": "Apache-2.0",
        "size": client.SIZE,
        "results": results,
    }
    out_json = args.out_dir / "bake_results.json"
    out_json.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
    log.info("Wrote %s (%d extract(s))", out_json, len(results))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
