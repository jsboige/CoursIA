#!/usr/bin/env python3
"""Phase A — séparation voix/musique pour analyse SwitchAngel (#15604).

Ce script orchestre `demucs htdemucs` sur un corpus audio local pour
isoler la voix de la musique, en préparation d'une re-transcription
faster-whisper (Phase B). L'entrée et la sortie restent **hors du dépôt** :
le script prend un dossier d'entrée (typiquement un miroir local sous
`G:\\Mon Drive\\MyIA\\IA\\Bibliographie IA\\SwitchAngel-livecoding-strudel\\`)
et écrit les stems `vocals.wav` / `accompaniment.wav` dans un dossier
d'artifacts également hors dépôt (jamais commit).

L'orchestrateur est volontairement narrow :
- accepte une liste explicite de fichiers en argument (pas de glob
  magique) ;
- journalise chaque étape en JSONL append-only pour audit ;
- expose `--dry-run` pour vérifier la commande avant exécution ;
- ne **jamais** committer d'archive SwitchAngel — la règle
  `bibliography-hygiene.md` §2 reste première.

Conçu pour RTX 3070 Laptop (8 GiB) — `htdemucs` consomme ~2-3 GB VRAM.
Pour RTX 3090 et au-delà, on peut passer `-d htdemucs_ft` (fine-tuned).

Voir issue #15604 (Phase A narrow) et le report myia-po-2023 c.446.
"""
from __future__ import annotations

import argparse
import json
import shlex
import subprocess
import sys
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path


@dataclass(frozen=True)
class SplitRequest:
    input_path: Path
    output_dir: Path
    model: str
    device: str
    shifts: int
    overlap: float


def _now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _log_journal(journal: Path, event: dict) -> None:
    """Append a JSONL line. Fail-CLOSED: refuse si le journal n'est pas
    accessible, c'est l'unique trace d'audit."""
    journal.parent.mkdir(parents=True, exist_ok=True)
    with journal.open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(event, ensure_ascii=False) + "\n")


def _build_command(req: SplitRequest, segments: list[Path]) -> list[str]:
    """Construit la commande `demucs` subprocess pour N fichiers en série.

    `demucs` accepte plusieurs fichiers en une passe (`--files` n'existe
    pas ; on appelle l'API en série pour mieux journaliser).
    """
    cmds: list[list[str]] = []
    for src in segments:
        cmd = [
            "demucs",
            "-n", req.model,
            "--device", req.device,
            "--shifts", str(req.shifts),
            "--overlap", str(req.overlap),
            "--out", str(req.output_dir),
            str(src),
        ]
        cmds.append(cmd)
    return cmds  # type: ignore[return-value]


def _check_paths(segments: list[Path], output_dir: Path) -> list[str]:
    """Vérifications fail-CLOSED avant subprocess :
    - les inputs existent et sont des .wav ;
    - l'output n'est **pas** sous le dépôt (jamais commit d'artifacts).
    """
    errors: list[str] = []
    for src in segments:
        if not src.is_file():
            errors.append(f"input manquant : {src}")
            continue
        if src.suffix.lower() != ".wav":
            errors.append(f"input non-.wav : {src}")
        if src.stat().st_size < 1024:
            errors.append(f"input trop petit (<1 KiB) : {src}")

    output_resolved = output_dir.resolve()
    cwd = Path.cwd().resolve()
    try:
        output_resolved.relative_to(cwd)
        errors.append(
            f"output_dir {output_resolved} est sous le cwd {cwd} — "
            "refuse (pas de commit d'artifacts)"
        )
    except ValueError:
        pass  # output hors cwd : OK
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Phase A — séparation voix/musique via demucs (narrow #15604)"
    )
    parser.add_argument(
        "--input",
        type=Path,
        action="append",
        required=True,
        help="Chemin d'un .wav à traiter (peut être répété ; PAS de glob)",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        required=True,
        help="Dossier d'output (vocals.wav/accompaniment.wav par fichier) — "
        "DOIT être hors dépôt",
    )
    parser.add_argument(
        "--journal",
        type=Path,
        default=Path("./artifacts/switchangel-demucs/journal.jsonl"),
        help="Journal JSONL append-only (défaut hors dépôt)",
    )
    parser.add_argument(
        "--model",
        default="htdemucs",
        choices=["htdemucs", "htdemucs_ft", "mdx", "mdx_extra"],
        help="Modèle demucs (défaut htdemucs, ~2-3 GiB VRAM)",
    )
    parser.add_argument(
        "--device",
        default="cuda",
        choices=["cuda", "cpu"],
        help="Device (défaut cuda — RTX 3070 Laptop OK)",
    )
    parser.add_argument(
        "--shifts",
        type=int,
        default=1,
        help="Nombre de shifts pour la séparation (défaut 1 ; 5 = mieux mais +lent)",
    )
    parser.add_argument(
        "--overlap",
        type=float,
        default=0.25,
        help="Overlap entre segments (défaut 0.25)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Affiche les commandes sans les exécuter",
    )
    args = parser.parse_args(argv)

    req = SplitRequest(
        input_path=Path(),  # placeholder, multiple inputs via _build_command
        output_dir=args.output_dir,
        model=args.model,
        device=args.device,
        shifts=args.shifts,
        overlap=args.overlap,
    )

    segments = [Path(p).resolve() for p in args.input]
    errors = _check_paths(segments, args.output_dir)
    if errors:
        for err in errors:
            print(f"REFUSE : {err}", file=sys.stderr)
        return 2

    cmds = _build_command(req, segments)
    if args.dry_run:
        for cmd in cmds:
            print(" ".join(shlex.quote(c) for c in cmd))
        return 0

    args.output_dir.mkdir(parents=True, exist_ok=True)
    print(
        f"[switchangel-demucs] {len(cmds)} fichier(s) → {args.output_dir} "
        f"(model={args.model}, device={args.device}, shifts={args.shifts})"
    )

    failed: list[tuple[int, list[str], str]] = []
    for idx, cmd in enumerate(cmds, start=1):
        started = _now()
        print(f"[{idx}/{len(cmds)}] {' '.join(shlex.quote(c) for c in cmd)}")
        try:
            proc = subprocess.run(cmd, check=False, capture_output=True, text=True)
        except FileNotFoundError as exc:
            print(f"ERREUR : binaire manquant : {exc}", file=sys.stderr)
            _log_journal(
                args.journal,
                {
                    "ts": started,
                    "event": "binary_missing",
                    "cmd": cmd,
                    "error": str(exc),
                },
            )
            return 3

        ended = _now()
        event = {
            "ts_start": started,
            "ts_end": ended,
            "event": "demucs_run",
            "cmd": cmd,
            "rc": proc.returncode,
            "stdout_tail": proc.stdout[-2000:] if proc.stdout else "",
            "stderr_tail": proc.stderr[-2000:] if proc.stderr else "",
        }
        _log_journal(args.journal, event)

        if proc.returncode != 0:
            failed.append((idx, cmd, proc.stderr[-500:] if proc.stderr else ""))
            print(f"  → rc={proc.returncode} (voir journal {args.journal})")
        else:
            print(f"  → OK ({ended})")

    if failed:
        print(
            f"\n[switchangel-demucs] {len(failed)}/{len(cmds)} échec(s) — "
            f"voir {args.journal}",
            file=sys.stderr,
        )
        return 1
    print(
        f"\n[switchangel-demucs] {len(cmds)}/{len(cmds)} OK — "
        f"stems dans {args.output_dir}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
