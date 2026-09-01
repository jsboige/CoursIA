#!/usr/bin/env python3
"""P6 -- Orchestrateur end-to-end du pipeline audiobook agentique (EPIC #1028).

Chainage des passes v4 (p0..p7) de `MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/`
sur un livre arbitraire. Chaque passe est un module v4 existant avec son
point d'entree `run()` ; cet orchestrateur les execute dans l'ordre, avec :

- `--book PATH`      : texte source arbitraire (defaut : boule_de_suif_full.txt),
                       plombe dans toute passe lisant SOURCE_TEXT (p0, p1_5, p2)
- `--dry-run`        : n'appelle AUCUN service externe -- les passes gatees
                       (LLM, TTS, SearXNG) sont planifiees avec leur gate
                       documentee, la segmentation deterministe (p2) s'execute
                       reellement en local sur le livre fourni
- `--list-passes`    : affiche le registre des passes et sort
- `--from-pass/--to-pass` : restreint la fenetre d'execution (p.ex. reprendre
                       apres une panne sans rejouer les passes amont)

Exit codes : 0 = toutes les passes executees/planiees sans erreur ; 1 = erreur
d'execution ; 2 = arguments invalides.

Tranche 1 (ce script) : chainage + dry-run. Les passes non-gatees en dry-run
ecrivent deja leurs artefacts reels dans `v4/outputs/` quand elles tournent.
"""
from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
V4_DIR = REPO_ROOT / "MyIA.AI.Notebooks" / "GenAI" / "Audio" / "04-Applications"
DEFAULT_BOOK = V4_DIR / "boule_de_suif_full.txt"

if str(V4_DIR) not in sys.path:
    sys.path.insert(0, str(V4_DIR))


@dataclass(frozen=True)
class Pass:
    key: str
    label: str
    module: str
    gate: str  # dependance externe ; vide = deterministe/local


PASSES: tuple[Pass, ...] = (
    Pass("p0", "Recherche narrative (sources secondaires)", "v4.p0_narrative_research",
         "SearXNG (recherche web)"),
    Pass("p1_5", "Catalogue des personnages", "v4.p1_5_speaker_catalog",
         "LLM structurant (.env du repo)"),
    Pass("p2", "Segmentation dialogue/narration", "v4.p2_segmentation", ""),
    Pass("p3", "Contexte dramatique par scene", "v4.p3_dramatic_context",
         "LLM structurant (.env du repo)"),
    Pass("p4", "Annotation prosodique", "v4.p4_annotation",
         "LLM structurant (.env du repo)"),
    Pass("p5", "Generation TTS", "v4.p5_tts",
         "FishAudio S2-Pro (cle API + service)"),
    Pass("p6c", "Compilation audio (ffmpeg)", "v4.p6_compile",
         "ffmpeg + artefacts p5 (gated par p5)"),
    Pass("p7", "Verification WER", "v4.p7_verify",
         "Whisper + artefacts p5/p6c (gated par p5)"),
)


def select_window(argv_from: str | None, argv_to: str | None) -> list[Pass]:
    keys = [p.key for p in PASSES]
    lo = keys.index(argv_from) if argv_from else 0
    hi = keys.index(argv_to) if argv_to else len(keys) - 1
    if lo > hi:
        raise SystemExit("--from-pass apres --to-pass dans l'ordre du pipeline")
    return list(PASSES)[lo : hi + 1]


def dry_run_p2(book: Path) -> dict:
    """Segmentation deterministe : paragraphes + chunks, sans aucun appel LLM.

    Les fonctions amont de p2 (decoupage, chunking) sont pures ; seul
    `segment_chunk` appelle le LLM et n'est PAS utilise ici.
    """
    import v4.p2_segmentation as p2

    text = book.read_text(encoding="utf-8")
    paragraphs = p2.split_into_paragraphs(text)
    chunks = p2.build_chunks(paragraphs)
    chars = sum(len(p.get("text", "")) for p in paragraphs)
    return {
        "paragraphs": len(paragraphs),
        "chunks": len(chunks),
        "caracteres": chars,
        "chunk_size": p2.CHUNK_SIZE,
        "overlap": p2.OVERLAP,
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Pipeline audiobook agentique EPIC #1028 (chainage p0..p7)")
    parser.add_argument("--book", type=Path, default=DEFAULT_BOOK,
                        help="texte source arbitraire (.txt)")
    parser.add_argument("--dry-run", action="store_true",
                        help="aucun appel service : passes gatees planifiees, p2 reel")
    parser.add_argument("--list-passes", action="store_true",
                        help="afficher le registre des passes et sortir")
    parser.add_argument("--from-pass", choices=[p.key for p in PASSES])
    parser.add_argument("--to-pass", choices=[p.key for p in PASSES])
    args = parser.parse_args()

    if args.list_passes:
        for p in PASSES:
            gate = p.gate if p.gate else "deterministe (local)"
            print(f"{p.key:5s} {p.label}  [{gate}]")
        return 0

    if not args.book.is_file():
        print(f"Livre introuvable : {args.book}", file=sys.stderr)
        return 2

    window = select_window(args.from_pass, args.to_pass)
    print(f"Livre    : {args.book}")
    print(f"Mode     : {'DRY-RUN (aucun service)' if args.dry_run else 'COMPLET'}")
    print(f"Fenetre  : {window[0].key}..{window[-1].key} "
          f"({len(window)}/{len(PASSES)} passes)")
    print()

    failures = 0
    for p in window:
        if args.dry_run:
            if p.key == "p2":
                stats = dry_run_p2(args.book)
                print(f"[REEL ] {p.key:5s} {p.label} : {stats['paragraphs']} "
                      f"paragraphes, {stats['chunks']} chunks "
                      f"(taille {stats['chunk_size']}, recouvrement {stats['overlap']})")
            elif p.gate:
                print(f"[PLAN ] {p.key:5s} {p.label} -- gate : {p.gate}")
            else:
                print(f"[PLAN ] {p.key:5s} {p.label}")
            continue
        try:
            mod = __import__(p.module, fromlist=["run"])
            if hasattr(mod, "SOURCE_TEXT"):
                mod.SOURCE_TEXT = args.book
            out = mod.run()
            print(f"[ OK  ] {p.key:5s} {p.label} -> {getattr(out, 'name', out)}")
        except Exception as exc:  # gate absente (cle, service) ou artefact amont manquant
            failures += 1
            print(f"[FAIL ] {p.key:5s} {p.label} -- {type(exc).__name__}: {exc}")

    print()
    if args.dry_run:
        print("Dry-run termine : plan etabli, aucune passe gatee n'a ete appelee.")
        return 0
    if failures:
        print(f"{failures} passe(s) en echec -- voir ci-dessus.")
        return 1
    print("Pipeline complet termine.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
