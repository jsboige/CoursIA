"""Extraction de traces J-Lens pour ICT-24 (strate 5, #5681 Track P) — Qwen3.5-4B persona.

CONTRAT de répartition (honoré) : po-2025 prépare le code CPU-side (ce script, sans
GPU requis pour le prep), ai-01 lance l'extraction GPU2 (``CUDA_VISIBLE_DEVICES=2``
STRICT) et la valide. Drafted CPU po-2025 2026-07-11 ; GPU2 run = ai-01.

Track P = piste **persona** du tête-à-tête #5681, DISTINCTE de Track S (structure).
Là où Track S confronte SAE <-> J-lens sur le MÊME substrat (Qwen3.5-9B-Base, prompts
de structure : code/prose/dialogue/math) pour mesurer la co-location cross-appareil,
Track P demande si le **workspace global se réorganise selon le persona** elicité :
des conditionnements persona contrastés (prudent ↔ enthousiaste, formel ↔ casual,
avocat du diable) produisent-ils des ignitions/workspace candidates DISTINCTES au
même layer ? C'est la lecture "persona" du *Global Workspace in Claude* (Anthropic,
2026) : le workspace est censé encoder la stance active du modèle.

Substrat réel (G.1 — vérifié firsthand po-2025 2026-07-11, ne pas propager la note
stale "4B-instruct/Subtext" de la matrice #5681)
-------------------------------------------------------------------------------------------------
La matrice de disponibilité #5681 (note 2026-07-07) listait Track P comme
"4B-instruct, J-lens via Subtext". Vérification ``list_repo_files`` sur le Hub HF le
2026-07-11 (po-2025, GPU-free) établit que :

* ``Qwen/Qwen3.5-4B-Instruct`` **n'existe pas** sur HF (``RepositoryNotFoundError``).
  Seul ``Qwen/Qwen3.5-4B-Base`` est publié (downloads=206540).
* Aucune source de lens dite "Subtext" n'est publique (recherche ``list_models``
  "subtext" → uniquement des modèles de sentiment/intent sans rapport).
* Le SEUL lens 4B publié est ``neuronpedia/jacobian-lens`` au chemin
  ``qwen3.5-4b/jlens/Salesforce-wikitext/Qwen3.5-4B_jacobian_lens.pt``, fitté par
  Neuronpedia sur ``Qwen/Qwen3.5-4B`` (base, n=1000, config.yaml confirmé).

Le substrate réellement exécutable est donc **Qwen3.5-4B base + persona via prompts
de conditionnement** (le persona est elicité par le prompt, pas par un
instruction-tuning — c'est exactement le paradigme du workspace-on-persona
d'Anthropic, et c'est méthodologiquement plus propre pour isoler l'effet persona du
post-training). Ce script encode cette interprétation. ``--model`` et
``--lens-filename`` restent CLI-overridables : si ai-01 dispose d'un lens "Subtext"
privé/gated sur un autre substrat, il le branche par UN seul flag sans toucher au
code. Le discrepancy vs la note de matrice est reporté dans ``__meta__`` (champ
``substrate_g1_note``) pour la traçabilité du tete-a-tete.

Fidélité du miroir Track S (exigence #5681 "miroir extract_jlens_traces.py")
---------------------------------------------------------------------------
* MEME architecture 3 couches que Track S : couche #1 = ce runner, couche #2 =
  :mod:`ict.jlens_trackP_traces` (adaptateur numpy, garde-fou anti-mélange Track S
  ↔ Track P), couche #3 = notebook (à livrer APRES fixtures 4B, follow-on séparé).
* MEME readout J-lens : :func:`jlens_readout_topk` réutilisée DRY depuis
  :mod:`extract_jlens_traces` (top-k token logits par position, base unembedding).
* MEME output ``.npz`` : cles ``<set>__<idx>__{topk_ids,topk_vals,tokens}`` +
  ``__meta__`` au schema :mod:`ict.sae_traces` (pour que :mod:`ict.workspace` tourne
  INCHANGÉ). SEUL CHANGE le nom de fixture (``ict_trackP_jlens_*`` vs ``ict24_jlens_*``)
  et le ``meta["track"]`` ("P" vs "S").
* Garde-fous GPU (:func:`guard_single_gpu`, :func:`find_decoder_layers`) et controle
  (:func:`apply_control_permutation`) réutilisés DRY depuis :mod:`extract_sae_traces`.
* CE QUI EST TRACK-P-SPÉCIFIQUE (pas importé) : :data:`PERSONA_PROMPT_SETS` (le
  substrat persona contrasté, distinct des :data:`PROMPT_SETS` de structure).

Usage GPU2-strict (ai-01)
-------------------------
::

    CUDA_VISIBLE_DEVICES=2 PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True \\
        python extract_jlens_trackP_traces.py --stage smoke
    # puis full trained + control :
    CUDA_VISIBLE_DEVICES=2 python extract_jlens_trackP_traces.py --stage full --variant trained
    CUDA_VISIBLE_DEVICES=2 python extract_jlens_trackP_traces.py --stage full --variant control

References
----------
* Anthropic, *Global Workspace in Claude* (transformer-circuits.pub, 2026).
* :mod:`extract_jlens_traces` -- le miroir Track S (structure, 9B-Base), dont
  :func:`jlens_readout_topk` / :func:`load_jlens` / :func:`probe_lens_fit_n` sont
  réutilisées ici DRY.
* :mod:`ict.jlens_trackP_traces` -- adaptateur numpy couche #2 (garde-fou anti-mélange
  Track S ↔ Track P : on refuse une fixture Track S chargée comme Track P, modèles
  distincts = substrats non comparables directement).
* github.com/anthropics/jacobian-lens -- package ``jlens`` officiel (dépendance).
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import sys
import time
from pathlib import Path

import numpy as np
import torch

# Reutilisation DRY des garde-fous GPU + controle depuis le miroir SAE Track S.
# (On n'importe PAS PROMPT_SETS : Track P a son propre substrat persona, distinct.)
from extract_sae_traces import (
    guard_single_gpu,
    find_decoder_layers,
    apply_control_permutation,
)
# Reutilisation DRY du readout J-lens + chargement lens depuis le miroir Track S :
# le readout top-k token logits est IDENTIQUE (seul le model/prompt change).
from extract_jlens_traces import (
    jlens_readout_topk,
    load_jlens,
    probe_lens_fit_n,
)

DEFAULT_MODEL = "Qwen/Qwen3.5-4B"   # G.1 : BASE (pas d'instruct publié). Voir docstring.
# Hub neuronpedia publie des lens pré-ajustés. Le 4B (base) est fitté n=1000
# (config.yaml confirmé). Le fichier ``_n1000.pt`` (fit complet Anthropic) est une
# alternative --lens-filename pour un fit de qualité maximale si le défaut (auto-
# stoppé à stop_at_delta=0.002) s'avérait trop court pour le tete-a-tete persona.
DEFAULT_LENS_REPO = "neuronpedia/jacobian-lens"
DEFAULT_LENS_FILENAME = "qwen3.5-4b/jlens/Salesforce-wikitext/Qwen3.5-4B_jacobian_lens.pt"


# --------------------------------------------------------------------------- #
# Substrat persona contrasté (Track-P-spécifique)
# --------------------------------------------------------------------------- #
# Cinq personas contrastés. Chaque prompt = un conditionnement persona (préfixe de
# stance) + une continuation de sujet. L'objectif du tete-a-tete persona est de
# mesurer si la batterie ict.workspace détecte une réorganisation du workspace
# (candidates / ignitions différentes) ENTRE personas au même layer -- l'analogue
# persona de la gate de co-location cross-appareil de Track S.
#
# Les personas sont conçus DIFFÉRENTIELS (chacun ancre une stance distinctive sur
# des sujets voisins) pour que differential_features (ict.sae_traces) ait une chance
# de faire ressortir des tokens persona-distinctifs. Mélange FR/EN comme PROMPT_SETS
# (Track S) pour la cohérence de série.
PERSONA_PROMPT_SETS: dict[str, list[str]] = {
    "persona_cautious": [
        # Prudent, mesuré, hypothèse à chaque pas.
        "You are a careful, risk-averse analyst. Before recommending anything, you "
        "weigh every downside. On the question of whether to adopt a new technology, "
        "you begin: 'We must be cautious. The potential benefits are real, but so "
        "are the failure modes. Consider first the worst case —'\n",
        "En tant que conseiller prudent, je ne m'engage jamais à la légère. Face à "
        "un investissement incertain, la règle est de préserver le capital avant "
        "de viser le gain. Ma première recommandation serait donc d'abord de —\n",
        "A cautious doctor hedges every diagnosis. 'It could be benign, but we "
        "cannot yet rule out complications. I would order further tests before "
        "concluding.' The disciplined stance is to —\n",
        "As a conservative engineer, you triple-check load tolerances. 'Redundancy "
        "is not waste; it is insurance. A single point of failure is, by "
        "definition, a failure waiting to happen. Therefore we'\n",
    ],
    "persona_enthusiastic": [
        # Enthousiaste, confiant, bullish.
        "You are an energetic, optimistic champion of bold ideas. Where others see "
        "risk, you see opportunity. On adopting a new technology, you begin: 'This "
        "is a moment to move fast and lead! The upside dwarfs the cost, and the "
        "future belongs to those who —'\n",
        "En tant qu'entrepreneur enthousiaste, je vois chaque défi comme une "
        "chance. Un investissement incertain ? C'est exactement là que se forge "
        "l'avantage ! Ma recommandation est de foncer, car —\n",
        "An enthusiastic coach fires up the team. 'We've got this! Every setback "
        "is a setup for a comeback. Leave it all on the field, because winners "
        "are made in the moments nobody is watching. Let's go out there and'\n",
        "As a bullish founder pitching investors, you radiate conviction. 'The "
        "market is ours to take. The numbers compound, the moat deepens, and the "
        "only real risk is moving too slowly. Join us now before —'\n",
    ],
    "persona_formal": [
        # Académique, troisième personne, précis.
        "It is the position of the present author that the matter admits of "
        "careful analysis. One observes, upon inspection of the relevant "
        "literature, that the phenomenon in question exhibits three principal "
        "features, which may be enumerated as follows. First, it is notable that —\n",
        "Dans un registre formel, on conviendra que la question mérite un "
        "traitement rigoureux. L'examen des données disponibles permet de dégager, "
        "sans précipitation, plusieurs constats dont le premier, et non le moindre, "
        "est que —\n",
        "The committee, having deliberated at length, hereby records its finding "
        "that the proposal, while not without merit, requires amendment. The "
        "grounds for this determination are threefold and shall be set out "
        "presently. In the first instance —\n",
        "From a standpoint of analytical rigor, one must distinguish between the "
        "nominal and the effective quantities. The discrepancy, though small, is "
        "systematic and bears on the conclusion. It is therefore incumbent upon "
        "the investigator to —\n",
    ],
    "persona_casual": [
        # Colloquial, première personne, chaleureux.
        "Honestly? I'd just go for it. Life's too short to overthink every little "
        "thing. You wanna try the new thing? Try it! Worst case you learn "
        "something, right? Look, here's how I see it —\n",
        "Bah, te casse pas la tête avec ça ! Franchement, tu te prends trop le "
        "chou. Essaie, point. Si ça marche, génial, et si ça foire, bah tu "
        "feras autre chose. Moi je te dis, écoute ton instinct et —\n",
        "So like, here's the deal — I've been there, done that, and honestly the "
        "best stuff happens when you just wing it a little. Don't get me wrong, a "
        "little planning is fine, but at some point you gotta just —\n",
        "Look, I'm no expert, but from what I've seen, you just gotta trust your "
        "gut, you know? People overcomplicate this stuff. Take it from me, the "
        "simple way is usually the right way, so just —\n",
    ],
    "persona_devil": [
        # Avocat du diable, contrarien, teste les faiblesses.
        "Let me play devil's advocate, because someone has to. Everyone here is "
        "quick to celebrate, but has anyone seriously considered what could go "
        "wrong? I'd argue the strongest case is actually AGAINST the proposal, "
        "and here is why. Suppose, for a moment, that —\n",
        "Pour le bien du débat, permettez-moi d'attaquer notre propre conclusion. "
        "Je soutiendrai la thèse inverse, non par conviction, mais pour en éprouver "
        "la robustesse. Si l'on adopte délibérément le contre-argument, on constate "
        "que —\n",
        "As a committed contrarian, I have to push back. The consensus feels too "
        "tidy, too convenient — and that is exactly what should make us suspicious. "
        "What is the steel-man of the opposing view? Charitably stated, the other "
        "side would say that —\n",
        "Let's stress-test this. You've all convinced yourselves, which is precisely "
        "when smart people make bad calls. So I'll be the annoying one: name the "
        "single weakest link in the plan. My own nominee for that weak link is —\n",
    ],
}


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--stage", choices=["smoke", "full"], default="smoke")
    p.add_argument("--variant", choices=["trained", "control"], default="trained",
                   help="control = permutation seedee des lignes d'input embeddings "
                        "(même sanction que #5101, appliquee sur le HF model avant "
                        "le wrap jlens)")
    p.add_argument("--layer", type=int, default=16,
                   help="couche du lens jacobien lue (defaut 16 = mi-reseau, miroir Track S)")
    p.add_argument("--model", default=DEFAULT_MODEL,
                   help=f"défaut = {DEFAULT_MODEL} (base). Si ai-01 dispose d'un "
                        f"substrat alternatif (ex: lens privé sur un 4B fine-tuné), "
                        f"l'overrider ici + --lens-filename.")
    p.add_argument("--lens-repo", default=DEFAULT_LENS_REPO)
    p.add_argument("--lens-filename", default=DEFAULT_LENS_FILENAME,
                   help=f"défaut = lens 4B-base vérifié (n=1000). Alternative "
                        f"qualité-max : '.../Qwen3.5-4B_jacobian_lens_n1000.pt'.")
    p.add_argument("--k", type=int, default=50,
                   help="top-k token logits gardes par position (analogue du k=50 SAE)")
    p.add_argument("--out-dir",
                   default=str(Path(__file__).resolve().parent.parent / "traces"))
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--attn", default=None,
                   help="attn_implementation a forcer (ex: eager) si le defaut echoue")
    return p.parse_args()


def main() -> None:
    args = parse_args()
    t0 = time.time()
    torch.manual_seed(args.seed)
    device = guard_single_gpu()

    import transformers
    import jlens  # dépendance officielle Anthropic, jamais copiée (garde-fou #4 #5681)

    print(f"[load] {args.model} (bf16, forward-only) ...")
    cfg_kwargs: dict = {"dtype": torch.bfloat16}
    if args.attn:
        cfg_kwargs["attn_implementation"] = args.attn
    hf = transformers.AutoModelForCausalLM.from_pretrained(args.model, **cfg_kwargs).to(device)
    hf.eval()
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model)
    d_model = getattr(hf.config, "hidden_size", None)
    n_layers = getattr(hf.config, "num_hidden_layers", None)
    vocab_size = hf.config.vocab_size
    print(f"[model] classe={type(hf).__name__} n_layers={n_layers} "
          f"d_model={d_model} vocab={vocab_size} "
          f"vram={torch.cuda.memory_allocated() / 2**30:.1f} GiB")

    # Contrairement à Track S (qui REJETTE instruct), Track P est la piste persona :
    # on accepte tout substrat. On signale juste si le modèle est un base model
    # (persona alors elicité par prompt, voir docstring + G.1 note).
    is_instruct = "instruct" in args.model.lower() or "-it" in args.model.lower()
    if is_instruct:
        print("[persona] modèle instruct détecté : persona double (prompt + post-training).")
    else:
        print("[persona] base model : persona elicité PAR le prompt (paradigme workspace-"
              "on-persona d'Anthropic, G.1 note : pas d'instruct 4B publié).")

    # Controle : permutation seedee des input embeddings (#5101), APPLIQUEE sur le
    # HF model AVANT le wrap jlens (etre refletée dans le lens), miroir Track S.
    if args.variant == "control":
        apply_control_permutation(hf, args.seed)

    # Wrap jlens (apres permutation eventuelle).
    model = jlens.from_hf(hf, tokenizer)
    print(f"[jlens] HF model wrappé via jlens.from_hf.")

    lens = load_jlens(args.lens_repo, args.lens_filename)
    lens_fit_n = probe_lens_fit_n(args.lens_repo, args.lens_filename)
    print(f"[lens] fit n={lens_fit_n} (garde-fou #2 #5681)")

    sets = PERSONA_PROMPT_SETS
    if args.stage == "smoke":
        # Smoke = 1 prompt par persona sur 2 personas (cauchemar delicence), pour
        # valider l'API + le decode. miroir Track S (1 par set, 2 sets).
        sets = {"persona_cautious": PERSONA_PROMPT_SETS["persona_cautious"][:1],
                "persona_enthusiastic": PERSONA_PROMPT_SETS["persona_enthusiastic"][:1]}

    arrays: dict[str, np.ndarray] = {}
    pos_total = 0
    for set_name, prompts in sets.items():
        for i, text in enumerate(prompts):
            ids, vals, tokens, T_eff = jlens_readout_topk(
                lens, model, tokenizer, text, args.layer, args.k)
            pos_total += T_eff
            key = f"{set_name}__{i}"
            arrays[f"{key}__topk_ids"] = ids.cpu().numpy()
            arrays[f"{key}__topk_vals"] = vals.cpu().numpy()
            arrays[f"{key}__tokens"] = np.array(tokens, dtype=str)
            print(f"[trace] {key}: T={T_eff} k={args.k} "
                  f"top-logit max={vals.max().item():.2f} "
                  f"min={vals.min().item():.2f}")
            if args.stage == "smoke":
                top5 = [tokenizer.decode([int(t)]) for t in ids[-1, :5]]
                print(f"        top-5 token logits (dernier token) : {top5}")

    # Sanity greedy (miroir Track S) : attrape un chargement de poids errone.
    if args.stage == "smoke" and args.variant == "trained":
        probe = tokenizer("La capitale de la France est", return_tensors="pt").to(device)
        with torch.no_grad():
            gen = hf.generate(**probe, max_new_tokens=12, do_sample=False)
        print(f"[sanity] greedy: {tokenizer.decode(gen[0], skip_special_tokens=True)!r}")

    print(f"\n[sanity] {pos_total} positions, top-k={args.k} par position "
          f"(base unembedding, ~vocab={vocab_size})")
    print(f"[sanity] vram pic={torch.cuda.max_memory_allocated() / 2**30:.1f} GiB")

    if args.stage == "full":
        out_dir = Path(args.out_dir)
        out_dir.mkdir(parents=True, exist_ok=True)
        out = out_dir / f"ict_trackP_jlens_layer{args.layer}_{args.variant}.npz"
        meta = {
            # --- schema commun sae_traces (consommé par ict.workspace inchangé) ---
            "model": args.model, "layer": args.layer, "k": args.k,
            "d_model": int(d_model) if d_model else None,
            "variant": args.variant, "seed": args.seed,
            # --- identification de l'appareil (EXIGÉ par ict.jlens_trackP_traces) ---
            "lens": "jacobian",
            "readout": "topk_token_logits (jlens.apply -> logits base unembedding "
                       "-> topk k=K par position)",
            # --- dimension de l'espace de readout (CLE d_sae pour compat sae_traces) ---
            "d_sae": int(vocab_size),
            "d_sae_semantics": "vocab_size (topk_ids = token ids, base unembedding)",
            "lens_repo": args.lens_repo, "lens_filename": args.lens_filename,
            "lens_fit_n": lens_fit_n,            # garde-fou #2 de #5681
            # --- IDENTIFICATION TRACK P (cle du garde-fou anti-mélange Track S/P) ---
            "track": "P (persona via conditioning prompts, base model)",
            "is_instruct_model": is_instruct,
            "persona_sets": list(sets.keys()),
            # --- G.1 note : discrepancy vs matrice #5681 (ne pas propager la note stale) ---
            "substrate_g1_note": (
                "Matrice #5681 (2026-07-07) listait Track P = '4B-instruct, J-lens "
                "via Subtext'. Verifie firsthand po-2025 2026-07-11 (list_repo_files "
                "HF) : Qwen3.5-4B-Instruct n'est PAS publié (seul 4B-Base), et aucune "
                "source de lens 'Subtext' n'est publique. Substrate réel = Qwen3.5-4B "
                "base + persona par prompts de conditionnement. ai-01 peut redirect "
                "via --model/--lens-filename si un lens privé/gated existe."),
            # --- garde-fous d'honnêteté #5681 (reportés côté notebook) ---
            "lens_is_dependency": "jlens = git+https://github.com/anthropics/jacobian-lens "
                                  "(officiel Anthropic, dépendance, jamais copié)",
            "mono_token_vocab_restricted": ("J-lens = mono-token, vocabulaire-restreint "
                                            "(limitation déclarée Anthropic)"),
            "persona_methodology": ("Persona elicité par conditionnement du prompt "
                                    "(prudent/enthousiaste/formel/casuel/contrarien). "
                                    "Non instruction-tuned : l'effet persona est isolé "
                                    "du post-training, paradigme workspace-on-persona."),
            "semantic_divergence_vs_sae": ("SAE top-k : hors top-k = 0 EXACT. "
                                           "J-lens top-k token logits : hors top-k ~ petit "
                                           "mais NON nul (densify = approximation rang-k)."),
            "prompt_sets": {kk: len(vv) for kk, vv in sets.items()},
            "n_positions_total": pos_total,
            "date": _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds"),
            "cpu_drafted_untested": ("Drafted CPU po-2025 (torch+cpu) 2026-07-11, "
                                     "extraction GPU2 ai-01 (contrat de répartition #5681). "
                                     "Cf DM msg-20260711T132815-0unnkf."),
        }
        arrays["__meta__"] = np.array(json.dumps(meta, ensure_ascii=False))
        np.savez_compressed(out, **arrays)
        print(f"[out] {out} ({out.stat().st_size / 2**20:.2f} MiB)")

    print(f"[done] stage={args.stage} variant={args.variant} "
          f"en {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
