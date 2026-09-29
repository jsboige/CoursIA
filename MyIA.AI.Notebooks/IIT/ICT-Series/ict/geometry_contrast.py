"""Contraste géométrique des lentilles sur des traces de mêmes tokens (#17740).

La paire SAE/J-Lens est mesurée sur les vingt prompts 9B de la couche 16.
F-Lens et S-Lens ne sont pas des traces alignées de ce run : leurs pilotes
portent des substrats distincts. Une absence n'est jamais un accord nul.
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from . import jlens_traces, sae_traces
from .lens_agreement import colocalize_lenses


TRACE_NAMES = {
    "sae": "ict21_sae_layer16_trained.npz",
    "jlens": "ict24_jlens_layer16_trained.npz",
}


def contrast(traces_dir: str | Path, *, n_null: int = 200) -> dict:
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
    return {
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
        "f_lens": {"status": "not_comparable",
                   "reason": "Aucune trace F-Lens sur ces mêmes prompts/run 9B."},
        "s_lens": {"status": "not_comparable",
                   "reason": "Le pilote S-Lens mesure copy_offset/variable_binding, "
                             "pas ces prompts/run 9B."},
    }


def main() -> None:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--traces-dir", type=Path,
                        default=Path(__file__).resolve().parent.parent / "traces")
    args = parser.parse_args()
    print(json.dumps(contrast(args.traces_dir), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
