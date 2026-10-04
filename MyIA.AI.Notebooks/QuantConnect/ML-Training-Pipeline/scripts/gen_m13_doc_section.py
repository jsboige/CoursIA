"""Splice the M13 cluster-revalidation section into docs/M13_MS_HAR.md.

The section's numbers come from the committed manifest, never from a hand-typed
table (the doctrine of #17029: aggregates belong to the automation; a re-run must
reproduce the prose, not require editing it). Re-running this after a new cluster
run rewrites the section in place.

The prose that states WHAT the port changed is static here -- it is a statement
about the harness, verified against the source, not a measurement. Everything
that is a measurement (per-horizon verdicts, per-cell counts, alignment
diagnostics, artifact digests) is derived from the manifest.

Usage:
    python gen_m13_doc_section.py                 # splice into docs/M13_MS_HAR.md
    python gen_m13_doc_section.py --dry-run       # print the section only
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
DOC_PATH = SCRIPTS_DIR.parent / "docs" / "M13_MS_HAR.md"
MANIFEST_PATH = SCRIPTS_DIR / "results" / "m13_ms_har_cluster_aligned.json"

VERDICT_ORDER = ["BEATS", "NO BEATS", "refuted-de-biased", "INCONCLUSIVE"]

PROSE_HEAD = """## Revalidation cluster appariée par origine (2026-10-04)

Le protocole #18190 (appariement par origine, porté depuis M4/#18650 puis M15/#18664) a été
appliqué au run cluster 7 actifs x 3 horizons x 4 seeds (84 combos, `mse`). Les jambes DM joignent
les deux walk-forwards sur leurs dates d'origine communes et **refusent** sur mismatch de cible
partagée — jamais de troncature positionnelle.

### Ce que le port change sur M13

Contrairement à M15 — où le garde a refusé deux fois avant toute mesure valide et a mis au jour un
défaut de convention réel — M13 produit ses deux jambes depuis la **même série `rv`** sur le
**même découpage** : l'appariement y est attendu **l'identité**, et le garde est ici la **preuve**
que la comparaison porte bien sur les mêmes jours, pas un correctif.

Ce que le port ajoute est ailleurs, et il porte sur le **verdict publié** :

1. **Le verdict publié est un sign-test binomial** (`_binomial_pvalue_one_sided` ; l'original
   n'importe ni DM ni `bias_metrics`, vérifié à la source) sur **84 combos traités comme
   indépendants** (`NO BEATS`, 39/84, p=0,7774), et il porte sur le **Sharpe** — pas sur le MSE.
   Deux réserves distinctes : (a) quatre graines d'un EM déterministe sur la même fenêtre ne sont
   pas quatre réplications indépendantes (même constat que la ligne REGISTRY M17 : « les 4 graines
   OLS sont bit-identiques, pas des réplications indépendantes »), donc le dénominateur 84
   sur-déclare la puissance ; (b) aucune jambe DM, aucune jambe dé-biaisée, aucun rapport de biais
   par modèle. Le port **ajoute** donc une lecture §C sur le **MSE** ; il ne réfute pas le verdict
   Sharpe publié, qui porte sur une autre métrique.
2. **La cible de la jambe HAR servait aux DEUX prévisions** — `target = har_out["targets"]...`
   puis `ms_pred = ms_fc.reindex(target.index)` (`origin/main` lignes 441-443, vérifié) : toute
   divergence entre les cibles réalisées des deux jambes était silencieusement ignorée. Le port
   donne à chaque jambe **sa propre cible** et fait refuser le join si les deux divergent
   (`target_tol=1e-8`). Le défaut était **latent** — les deux jambes partageant la même série `rv`
   et le même découpage, les cibles coïncident — et le garde le **prouve** au lieu de le supposer.
"""


def _fmt(v, nd=2):
    if v is None:
        return "n/a"
    if isinstance(v, float):
        return f"{v:.{nd}f}".replace(".", ",")
    return str(v)


def _pct(v, nd=1):
    if v is None:
        return "n/a"
    return f"{v:+.{nd}f} %".replace(".", ",")


def _gap(v):
    """A shared-target gap is either exactly 0, an ULP-sized float residue, or a real divergence.

    Printing an ULP residue as `0,000000000000` reads like a precision claim the
    manifest does not make; the scientific form says what it is.
    """
    if v is None:
        return "n/a"
    if v == 0:
        return "0,0"
    if abs(v) < 1e-6:
        return f"{v:.1e}".replace(".", ",")
    return f"{v:.6f}".replace(".", ",")


def build_section(manifest: dict) -> str:
    alignment = {a["cell"]: a for a in manifest["alignment"]}
    horizons = manifest["config"]["horizons"]

    # --- alignment diagnostics, read off the manifest, not assumed ----------
    gaps = [a["dm_target_gap_max"] for a in manifest["alignment"] if a["dm_target_gap_max"] is not None]
    n_mismatch = sum(a["n_target_mismatch"] for a in manifest["alignment"])
    n_min = min((a["dm_n_aligned_min"] for a in manifest["alignment"]
                 if a["dm_n_aligned_min"] is not None), default=None)
    n_max = max((a["dm_n_aligned_max"] for a in manifest["alignment"]
                 if a["dm_n_aligned_max"] is not None), default=None)
    gap_max = max(gaps) if gaps else None

    # --- per-horizon aggregate (28 combos each) -----------------------------
    rows = []
    for h in horizons:
        cells = [a for a in manifest["alignment"] if a["cell"].endswith(f"|h={h}")]
        raw = Counter(a["aggregate_verdict"] for a in cells)
        deb = Counter(a["aggregate_verdict_debiased"] for a in cells)
        mean_red = sum(a["mean_reduction_pct"] or 0.0 for a in cells) / max(len(cells), 1)
        mean_red_d = sum((a["mean_reduction_pct_vs_debiased_classic"] or 0.0) for a in cells) / max(len(cells), 1)
        p_med = sorted(a["dm_p_median"] for a in cells if a["dm_p_median"] is not None)
        p_mid = p_med[len(p_med) // 2] if p_med else None
        # raw verdict string, most frequent first
        def _verdict_str(c: Counter) -> str:
            parts = [f"{k} {v}/7" for k, v in sorted(c.items(), key=lambda kv: -kv[1])]
            return " ; ".join(parts)
        rows.append((h, mean_red, mean_red_d, p_mid, _verdict_str(raw), _verdict_str(deb)))

    # --- per-cell counts ----------------------------------------------------
    cell_counts = {k: 0 for k in VERDICT_ORDER}
    for a in manifest["alignment"]:
        cell_counts[a["aggregate_verdict"]] = cell_counts.get(a["aggregate_verdict"], 0) + 1
    n_cells = len(manifest["alignment"])

    lines = [PROSE_HEAD]
    lines.append("### Diagnostic d'alignement\n")
    lines.append(
        f"Le garde shared-target a refusé **{n_mismatch}** fois sur les {n_cells} agrégats "
        f"coin x horizon ; gap max sur les cibles partagées **{_gap(gap_max)}** ; "
        f"longueurs appariées {n_min}–{n_max}. "
        + ("L'appariement est donc l'identité, mesurée et non supposée."
           if not n_mismatch else "Des cellules ont été refusées -- voir `alignment` du manifeste.")
    )
    lines.append("")
    lines.append("### Verdicts cluster (jambe brute / jambe dé-biaisée)\n")
    lines.append("Agrégé par horizon (7 actifs chacun), et par cellule (21 couples coin x horizon) :\n")
    lines.append("| Horizon | edge MSE moyen | edge MSE hors biais | dm_p_median | verdicts par actif (brut) | verdicts par actif (dé-biaisé) |")
    lines.append("|---|---|---|---|---|---|")
    for h, mr, mrd, pm, raw, deb in rows:
        lines.append(f"| h={h} | {_pct(mr)} | {_pct(mrd)} | {_fmt(pm, 4)} | {raw} | {deb} |")
    lines.append("")
    counts = " ; ".join(f"**{k}** {cell_counts.get(k, 0)}/{n_cells}" for k in VERDICT_ORDER)
    lines.append(f"Par cellule : {counts}.\n")

    art = manifest["artifact"]
    lines.append(
        f"Manifeste compact committé : `scripts/results/{MANIFEST_PATH.name}` "
        f"(politique #15890, {MANIFEST_PATH.stat().st_size if MANIFEST_PATH.exists() else '?'} octets). "
        f"Artefact complet (hors dépôt) : `{art['path']}`, {art['bytes']} octets, "
        f"sha256 `{art['sha256'][:12]}…` ; runtime mesuré {_fmt(manifest['elapsed_s'], 0)} s "
        f"pour {manifest['total_rows']} lignes. Le champ `elapsed_s` mesure le groupe le plus long, "
        f"pas la somme des trois groupes parallèles."
    )
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--dry-run", action="store_true", help="print the section instead of splicing it")
    args = p.parse_args(argv)

    manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    section = build_section(manifest)

    if args.dry_run:
        print(section)
        return

    doc = DOC_PATH.read_text(encoding="utf-8")
    marker = "## Revalidation cluster appariée par origine"
    if marker in doc:  # idempotent: replace a previous splice
        doc = doc[: doc.index(marker)]
    if not doc.endswith("\n"):
        doc += "\n"
    DOC_PATH.write_text(doc + "\n" + section, encoding="utf-8")
    print(f"Spliced cluster section into {DOC_PATH} ({len(section)} chars)")
    print(f"manifest sha256: {hashlib.sha256(MANIFEST_PATH.read_bytes()).hexdigest()[:16]}")


if __name__ == "__main__":
    main()
