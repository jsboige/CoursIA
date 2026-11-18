"""Contraste géométrique des lentilles sur des traces de mêmes tokens (#17740).

La paire SAE/J-Lens est mesurée sur les vingt prompts 9B de la couche 16.
Quand une capture dense des mêmes résidus est disponible (``--dense`` ou
``traces/ict25_dense_layer16_trained.npz``, produite par
``scripts/extract_dense_traces.py``), F-Lens (géométrie factorisée) et S-Lens
(probe de self-location positionnelle) sont mesurés **sur ce même substrat**,
sous le même contrat d'alignement (model/layer/seed/variant + tokens égaux).
Sans capture dense, F-Lens et S-Lens restent des absences explicites : une
absence n'est jamais un accord nul. Les quatre instruments sont rapportés
**séparément** — jamais fusionnés en un score unique.
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from . import flens_traces, jlens_traces, sae_traces, slens_traces
from .lens_agreement import colocalize_lenses


TRACE_NAMES = {
    "sae": "ict21_sae_layer16_trained.npz",
    "jlens": "ict24_jlens_layer16_trained.npz",
    "dense": "ict25_dense_layer16_trained.npz",
}


def _aligned_dense(dense_path: Path, sae: dict) -> dict:
    """Charge la capture dense et fait respecter le contrat d'alignement.

    Mêmes garde-fous que la paire SAE/J-Lens : model/layer/seed/variant
    égaux, mêmes prompts, tokens strictement égaux. Refuse plutôt que de
    présenter un substrat différent comme le même run.
    """
    dense = flens_traces.load_dense(dense_path)
    for key in ("model", "layer", "seed", "variant"):
        if (dense["meta"].get(key) is None or
                dense["meta"][key] != sae["meta"].get(key)):
            raise ValueError(f"traces désalignées : {key}")
    if set(dense["prompts"]) != set(sae["prompts"]):
        raise ValueError("traces désalignées : prompts différents")
    for prompt in sae["prompts"]:
        left = sae["prompts"][prompt]["tokens"]
        right = dense["prompts"][prompt]["tokens"]
        if not np.array_equal(left, right):
            raise ValueError(f"traces désalignées : tokens du prompt {prompt}")
    return dense


def _per_set_summary(measured: dict, flens: dict, slens: dict) -> list[dict]:
    """Agrégats par jeu de prompts — lecture croisée, pas fusion.

    Chaque ligne rappelle ce que chaque instrument dit du MÊME jeu : comptes
    de verdicts SAE/J-Lens, NC@90 moyen (F-Lens), R² pooled restreint au jeu
    (S-Lens). C'est une table de lecture, jamais un score composite.
    """
    rows = []
    flens_by_set: dict[str, list[int]] = {}
    for item in flens["per_prompt"]:
        flens_by_set.setdefault(item["prompt"][0], []).append(
            item["nc_at"]["90"])
    slens_by_set: dict[str, list[float]] = {}
    for item in slens["per_prompt"]:
        slens_by_set.setdefault(item["prompt"][0], []).append(item["r2"])
    verdict_by_set: dict[str, dict[str, int]] = {}
    for item in measured["per_prompt"]:
        verdicts = verdict_by_set.setdefault(item["prompt"][0], {})
        verdicts[item["verdict"]] = verdicts.get(item["verdict"], 0) + 1
    for set_name in sorted(verdict_by_set):
        nc = flens_by_set.get(set_name, [])
        r2 = slens_by_set.get(set_name, [])
        rows.append({
            "set": set_name,
            "sae_jlens_verdicts": verdict_by_set[set_name],
            "flens_nc90_mean": (float(np.mean(nc)) if nc else None),
            "slens_r2_mean": (None if not r2 or any(
                v is None or np.isnan(v) for v in r2)
                else float(np.mean(r2))),
        })
    return rows


def contrast(traces_dir: str | Path, *, n_null: int = 200,
             dense: str | Path | None = None) -> dict:
    """Rapporte séparément accord temporel, dissociation et absences de mesure.

    Les indices de prompt et les longueurs seuls ne garantissent pas le même
    texte. Vérifier les tokens avant de calculer une co-localisation ; refuser
    une paire partielle plutôt que la présenter comme le même substrat.
    """
    if n_null < 2:
        raise ValueError("n_null doit être >= 2 pour estimer le contrôle par rotation")
    root = Path(traces_dir)
    sae = sae_traces.load_traces(root / TRACE_NAMES["sae"])
    jlens = jlens_traces.load_traces(root / TRACE_NAMES["jlens"])
    for key in ("model", "layer", "seed", "variant"):
        if (sae["meta"].get(key) is None or
                sae["meta"][key] != jlens["meta"].get(key)):
            raise ValueError(f"traces désalignées : {key}")
    if set(sae["prompts"]) != set(jlens["prompts"]):
        raise ValueError("traces désalignées : prompts différents")
    for prompt in sae["prompts"]:
        left = sae["prompts"][prompt]["tokens"]
        right = jlens["prompts"][prompt]["tokens"]
        if not np.array_equal(left, right):
            raise ValueError(f"traces désalignées : tokens du prompt {prompt}")

    measured = colocalize_lenses(
        sae, jlens, n_null=n_null, rng=np.random.default_rng(0)
    )
    if measured["n_skipped"] or measured["n_prompts"] != len(sae["prompts"]):
        raise ValueError("traces désalignées : prompts non comparés")
    counts = {name: measured[f"n_{name}"] for name in
              ("colocalized", "dissociated", "chance", "undefined")}
    result = {
        "substrate": {"model": sae["meta"]["model"],
                      "layer": sae["meta"]["layer"],
                      "seed": sae["meta"]["seed"],
                      "prompts": measured["n_prompts"]},
        "sae_jlens": {
            "counts": counts,
            "per_prompt": [
                {"prompt": list(item["prompt"]), "verdict": item["verdict"],
                 "sae_ignitions": item["n_ign_a"],
                 "jlens_ignitions": item["n_ign_b"]}
                for item in measured["per_prompt"]
            ],
            "interpretation": (
                "Le verdict chance ne démontre pas une dissociation : les prompts "
                "où au moins une lentille n'allume rien restent indéfinis. SAE top-k exact, "
                "J-Lens top-k partiel (directions non observées)."
            ),
        },
    }

    dense_path = Path(dense) if dense is not None else root / TRACE_NAMES["dense"]
    if dense_path.exists():
        loaded = _aligned_dense(dense_path, sae)
        # top_k borne par la dimension : une capture de test de petite dim
        # reste mesurable, une nulle non appariee serait muette.
        top_k = min(16, int(loaded["meta"]["d_model"]))
        flens = flens_traces.measure_flens(loaded, top_k=top_k, n_null=n_null)
        slens = slens_traces.measure_slens(loaded)
        result["f_lens"] = flens
        result["s_lens"] = slens
        result["per_set_summary"] = _per_set_summary(measured, flens, slens)
        result["cross_instrument_reading"] = (
            "Quatre instruments, quatre lectures distinctes du même substrat "
            "(co-localisation temporelle SAE/J-Lens, géométrie factorisée "
            "F-Lens, décodabilité positionnelle S-Lens) : les lignes de "
            "per_set_summary se lisent ensemble, jamais sommées. Une ligne où "
            "un instrument voit de la structure et l'autre pas est le signal, "
            "pas un bruit à lisser."
        )
    else:
        result["f_lens"] = {"status": "not_comparable",
                            "reason": "Aucune trace dense sur ces mêmes prompts/run 9B."}
        result["s_lens"] = {"status": "not_comparable",
                            "reason": "Le pilote S-Lens mesure copy_offset/variable_binding, "
                                      "pas ces prompts/run 9B."}
    return result


def main() -> None:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--traces-dir", type=Path,
                        default=Path(__file__).resolve().parent.parent / "traces")
    parser.add_argument("--dense", type=Path, default=None,
                        help="capture dense (défaut : traces/"
                             + TRACE_NAMES["dense"] + " si présente)")
    args = parser.parse_args()
    print(json.dumps(contrast(args.traces_dir, dense=args.dense),
                     ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
