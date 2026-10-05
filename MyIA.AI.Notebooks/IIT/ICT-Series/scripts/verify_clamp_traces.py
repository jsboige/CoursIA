#!/usr/bin/env python3
"""verify_clamp_traces.py -- le clamp est-il visible dans la trace ?

## Le defaut que ce script attrape

``ResidCapture`` (extract_sae_traces.py) capturait le residu AVANT d'appliquer
le clamp de la meme couche : les traces "clampees" sortaient byte-identiques
aux intactes (mesure #5635 / #19184 : 0 / 134 950 valeurs differentes). Un
clamp invisible ne plante pas et n'avertit pas -- le fichier existe, il est
lisible, et la seule chose qui manque est l'intervention qu'il est cense
porter. Les Gates 22-23 ont mesure le modele intact pendant ce temps.

Ce script rejoue le controle sur un repertoire de traces, en lisant les
metadonnees ``__meta__`` que chaque trace embarque deja :

* ``clamp_ids`` non vide et ``clamp_scale != 0`` -> la trace DOIT differer de
  sa reference intacte ;
* ``clamp_ids`` non vide et ``clamp_scale == 0`` -> no-op par construction
  (``ClampHook`` sort avant de modifier quoi que ce soit) -> la trace doit
  etre IDENTIQUE, au bruit flottant pres.

## La reference d'un bras

La trace non clampee de MEME identite : ``model``, ``sae_repo``, ``layer``,
``variant``, ``seed``, ``prompt_sets``, ``n_tokens_total``. Aucune
heuristique sur le nom de fichier -- les metadonnees sont la seule autorite,
et elles seules distinguent ``inoc_qwen35-2b-base_layer23of24_*`` (reference
``inocref_*``) de ``ict24_g24*_layer16_*`` (reference
``ict21_sae_layer16_trained``), dont les prefixes ne disent rien.

Zero candidate ou plusieurs : erreur NOMMEE, jamais un choix silencieux. Un
bras qu'on ne sait pas juger n'est pas un bras qui passe.

## Usage

    python verify_clamp_traces.py                    # traces/ de la serie
    python verify_clamp_traces.py --traces-dir DIR
    python verify_clamp_traces.py --json

Sortie : 0 si chaque bras clampe porte bien ce que sa metadonnee annonce,
1 si un bras est muet (ou non jugeable), 2 si le repertoire est inutilisable.
Depuis #19216.
"""
from __future__ import annotations

import argparse
import json
import sys
import zipfile
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np

# Cles qui identifient une extraction. Deux traces qui les partagent toutes
# sont le meme modele, a la meme couche, sur les memes prompts : l'une peut
# donc servir de reference a l'autre. `n_tokens_total` separe notamment
# `ict21_sae_layer16_*` de `ict24_jlens_layer16_*` (meme modele et meme
# couche, corpus different).
IDENTITY_KEYS = (
    "model", "sae_repo", "layer", "variant", "seed", "prompt_sets",
    "n_tokens_total",
)

# Part de valeurs qui peuvent differer sans que le clamp soit en cause : la
# somme flottante en float16 sur des millions de valeurs laisse passer
# quelques unites (mesure #19216 : 1 / 272 600 pour un bras alpha=0). Le
# plancher est pose 3 ordres au-dessus de ce bruit mesure et 2 ordres
# au-dessous du plus petit effet de clamp reel observe (2,7 %), de sorte
# qu'il ne peut ni absoudre un clamp muet ni condamner un controleur inerte.
NOISE_FLOOR_FRAC = 1e-3

DEFAULT_TRACES_DIR = Path(__file__).resolve().parent.parent / "traces"


@dataclass
class Trace:
    """Une trace et sa metadonnee."""

    path: Path
    meta: dict | None

    @property
    def name(self) -> str:
        return self.path.name

    @property
    def clamped(self) -> bool:
        return bool(self.meta and self.meta.get("clamp_ids"))

    @property
    def scale(self) -> float:
        """Intensite annoncee. Absente -> 1.0 (clamp plein, comportement du
        script d'extraction)."""
        if not self.meta:
            return 1.0
        return float(self.meta.get("clamp_scale", 1.0))

    def identity(self) -> tuple:
        if not self.meta:
            return ()
        return tuple(_frozen(self.meta.get(k)) for k in IDENTITY_KEYS)


def _frozen(value):
    """Rend une valeur de metadonnee comparable (les dict ne le sont pas)."""
    if isinstance(value, dict):
        return tuple(sorted((k, _frozen(v)) for k, v in value.items()))
    if isinstance(value, list):
        return tuple(_frozen(v) for v in value)
    return value


@dataclass
class Verdict:
    """Ce qu'on peut dire d'un bras, et pourquoi."""

    trace: Trace
    reference: Trace | None
    differing: int = 0
    total: int = 0
    status: str = "ok"
    detail: str = ""

    @property
    def frac(self) -> float:
        return (self.differing / self.total) if self.total else 0.0

    @property
    def failed(self) -> bool:
        return self.status in {"MUET", "NO-OP-ACTIF", "SANS-REFERENCE",
                               "AMBIGU", "ILLISIBLE"}

    def line(self) -> str:
        ref = self.reference.name if self.reference else "-"
        pct = f"{100.0 * self.frac:.1f} %" if self.total else "-"
        return (f"| `{self.trace.name}` | {self.trace.scale:g} | `{ref}` | "
                f"{self.differing}/{self.total} | {pct} | {self.status} |")


@dataclass
class Report:
    verdicts: list[Verdict] = field(default_factory=list)
    skipped: list[str] = field(default_factory=list)

    @property
    def failures(self) -> list[Verdict]:
        return [v for v in self.verdicts if v.failed]

    def as_json(self) -> str:
        return json.dumps({
            "verdicts": [{
                "trace": v.trace.name,
                "scale": v.trace.scale,
                "reference": v.reference.name if v.reference else None,
                "differing": v.differing,
                "total": v.total,
                "status": v.status,
                "detail": v.detail,
            } for v in self.verdicts],
            "skipped": self.skipped,
        }, ensure_ascii=False, indent=2)

    def as_markdown(self) -> str:
        out = ["| trace | scale | reference | valeurs differentes | % | verdict |",
               "|---|---|---|---|---|---|"]
        out += [v.line() for v in self.verdicts]
        if self.skipped:
            out.append("")
            out.append(f"Sans metadonnee (non jugeables, {len(self.skipped)}) : "
                       + ", ".join(f"`{n}`" for n in self.skipped))
        return "\n".join(out)

    def summary(self) -> str:
        n_muet = sum(1 for v in self.verdicts if v.status == "MUET")
        n_noop = sum(1 for v in self.verdicts if v.status == "NO-OP-ACTIF")
        n_bad = sum(1 for v in self.verdicts
                    if v.status in {"SANS-REFERENCE", "AMBIGU", "ILLISIBLE"})
        return (f"{len(self.verdicts)} bras juges : "
                f"{len(self.verdicts) - len(self.failures)} conformes, "
                f"{n_muet} muets (clamp invisible), {n_noop} actifs a alpha=0, "
                f"{n_bad} non jugeables, {len(self.skipped)} sans metadonnee.")


def read_meta(path: Path) -> dict | None:
    """La metadonnee ``__meta__`` d'une trace, ou None si elle n'en porte pas."""
    try:
        with np.load(path, allow_pickle=False) as z:
            if "__meta__" not in z.files:
                return None
            return json.loads(str(z["__meta__"]))
    # Un .npz corrompu ou tronque leve zipfile.BadZipFile ou EOFError, qui ne
    # derivent d'aucune des quatre premieres : sans elles, un seul fichier
    # abime ferait avorter l'audit entier au lieu d'etre declare sans
    # metadonnee et de laisser les autres bras juges.
    except (OSError, ValueError, KeyError, json.JSONDecodeError,
            zipfile.BadZipFile, EOFError):
        return None


def differing_values(a: Path, b: Path) -> tuple[int, int]:
    """(valeurs qui different, valeurs comparees) entre deux traces.

    Les tableaux communs de meme forme sont compares valeur a valeur ; un
    tableau present d'un seul cote, ou de forme differente, compte comme une
    divergence entiere -- c'est une difference, pas une absence de mesure.
    La metadonnee ``__meta__`` ne participe pas au compte (elle porte la date
    de generation, qui differe toujours).
    """
    with np.load(a, allow_pickle=False) as za, np.load(b, allow_pickle=False) as zb:
        keys = [k for k in za.files if k != "__meta__"]
        diff = total = 0
        for key in keys:
            x = za[key]
            if not isinstance(x, np.ndarray):
                # Un membre pourri arrive en bytes bruts sous numpy 2.x (sans
                # lever a l'acces) : ce ne sont pas des valeurs comparables.
                raise ValueError(f"membre {key!r} illisible dans {a.name}")
            total += int(x.size)
            if key not in zb.files:
                # Tableau present seulement dans la reference : il manque au bras.
                diff += int(x.size)
                continue
            y = zb[key]
            if not isinstance(y, np.ndarray):
                raise ValueError(f"membre {key!r} illisible dans {b.name}")
            if x.shape != y.shape:
                diff += int(x.size)
                continue
            diff += int(np.count_nonzero(x != y))
        # Tableaux presents seulement dans le bras : ils manquent a la reference.
        for key in zb.files:
            if key == "__meta__" or key in za.files:
                continue
            y = zb[key]
            if not isinstance(y, np.ndarray):
                # Meme garde que la premiere boucle : un membre pourri arrive en
                # bytes bruts sous numpy 2.x (sans lever a l'acces), et ``.size``
                # y leverait un AttributeError que le tuple du juge n'attrape
                # pas -- un traceback qui tuerait l'audit des autres bras
                # (#19249, reproduction independante de l'adjoint 2026-10-05 :
                # membre extra corrompu present dans le bras seul).
                raise ValueError(f"membre {key!r} illisible dans {b.name}")
            diff += int(y.size)
            total += int(y.size)
    return diff, total


def references_for(trace: Trace, corpus: list[Trace]) -> list[Trace]:
    """Les traces intactes de meme identite que ``trace``."""
    ident = trace.identity()
    return [t for t in corpus
            if t is not trace and not t.clamped and t.meta is not None
            and t.identity() == ident]


def judge(trace: Trace, corpus: list[Trace],
          noise_floor: float = NOISE_FLOOR_FRAC) -> Verdict:
    """Le verdict d'un bras clampe : muet, conforme, ou non jugeable."""
    candidates = references_for(trace, corpus)
    if len(candidates) > 1:
        return Verdict(trace, None, status="AMBIGU",
                       detail=f"{len(candidates)} references de meme identite : "
                              + ", ".join(t.name for t in candidates))
    if not candidates:
        return Verdict(trace, None, status="SANS-REFERENCE",
                       detail="aucune trace intacte de meme identite "
                              "(model/sae_repo/layer/variant/seed/prompt_sets/"
                              "n_tokens_total)")
    ref = candidates[0]
    try:
        diff, total = differing_values(ref.path, trace.path)
    except (OSError, ValueError, zipfile.BadZipFile, EOFError) as exc:
        # Archive presente mais membre illisible : le bras n'est pas jugeable,
        # et c'est un echec declare -- jamais un traceback qui tuerait l'audit
        # des autres bras.
        return Verdict(trace, ref, status="ILLISIBLE",
                       detail=f"archive illisible : {type(exc).__name__}")
    frac = (diff / total) if total else 0.0
    if trace.scale == 0.0:
        # No-op annonce : le hook sort avant de modifier le residual stream.
        # S'il agit quand meme, la metadonnee ne decrit plus le fichier.
        if frac > noise_floor:
            return Verdict(trace, ref, diff, total, "NO-OP-ACTIF",
                           f"alpha=0 annonce, mais {100.0 * frac:.1f} % des "
                           "valeurs different")
        return Verdict(trace, ref, diff, total, "ok-noop")
    if frac <= noise_floor:
        return Verdict(trace, ref, diff, total, "MUET",
                       f"clamp annonce (alpha={trace.scale:g}) mais la trace "
                       f"est identique a sa reference au bruit pres "
                       f"({100.0 * frac:.4f} % <= {100.0 * noise_floor:.2f} %)")
    return Verdict(trace, ref, diff, total, "ok")


def audit(traces_dir: Path, noise_floor: float = NOISE_FLOOR_FRAC) -> Report:
    """Juge tous les bras clampes d'un repertoire de traces."""
    corpus = [Trace(p, None) for p in sorted(traces_dir.glob("*.npz"))]
    for t in corpus:
        t.meta = read_meta(t.path)
    report = Report()
    for t in corpus:
        if t.meta is None:
            report.skipped.append(t.name)
        elif t.clamped:
            report.verdicts.append(judge(t, corpus, noise_floor))
    return report


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--traces-dir", type=Path, default=DEFAULT_TRACES_DIR,
                   help=f"repertoire des traces (defaut : {DEFAULT_TRACES_DIR})")
    p.add_argument("--json", action="store_true", help="sortie JSON")
    p.add_argument("--noise-floor-frac", type=float, default=NOISE_FLOOR_FRAC,
                   help="part de valeurs toleree comme bruit flottant "
                        f"(defaut {NOISE_FLOOR_FRAC})")
    args = p.parse_args(argv)

    if not args.traces_dir.is_dir():
        print(f"verify_clamp_traces: {args.traces_dir} n'est pas un repertoire",
              file=sys.stderr)
        return 2
    report = audit(args.traces_dir, args.noise_floor_frac)
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")

    if args.json:
        print(report.as_json())
    else:
        print(report.as_markdown())
        print()
        print(report.summary())
        for v in report.failures:
            print(f"  ECHEC {v.trace.name} : {v.status} -- {v.detail}", file=sys.stderr)
    return 1 if report.failures else 0


if __name__ == "__main__":
    sys.exit(main())
