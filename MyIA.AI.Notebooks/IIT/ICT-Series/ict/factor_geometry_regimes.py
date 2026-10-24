"""Campagnes des regimes generatifs (suivi #20071) : resoudre les deux falsifiables.

Les constructions sont livrees depuis #20091 (``NoisedChannel`` dans
``bench_factorise``, ``ConditionalBench``, ``conditional_child_floor``) et le
carnet ICT-36 en a rendu une premiere lecture a 400 pas. Deux falsifiables
sont restes OUVERTS, et ce module porte les corrections de protocole qui
les tranchent :

1. **Bruit du canal -- la lecture doit exister aussi la ou le gate echoue.**
   La premiere passe ne rendait la geometrie qu'aux niveaux ou la perte
   jointe passait sous l'uniforme : or la question du critere est la
   LISIBILITE DU FACTEUR, pas la reussite du modele. La falsifiable
   (« overlap_coef_max retombe dans la bande du temoin au-dela d'un seuil,
   ou n'en sort jamais ») se joue precisement aux niveaux ou le modele
   n'apprend plus rien -- c'est la que la geometrie d'un modele qui n'a rien
   appris doit se confondre avec celle des initialisations non entrainees.
   :func:`sweep_channel_noise` entraîne PAR NIVEAU, rejoue le temoin a
   CHAQUE niveau et rend la lecture a TOUS les niveaux, gate reussi ou
   echoue (tagge).

2. **Structure conditionnelle -- de-saturer le discriminant.**
   L'``additivity_gap`` est un entier vivant au rang pres : sur les bancs
   Mess3 x Mess3, le temoin rendait la meme valeur aux six initialisations
   (bande de largeur NULLE, une bande qui ne discrimine aucun modele -- le
   controle independant mesurait deja -2.000 partout). La correction est
   double : la metrique continue ``overlap_energy`` (ajoutee au rapport par
   ce suivi, bandes de temoin de largeur non nulle) ET un budget plus fort
   (kappa eleve vers sa borne de stochasticite, 1200 pas, trois graines
   modele). :func:`conditional_campaign` mesure le banc conditionnel contre
   le controle INDEPENDANT aux memes marginales, meme enfant, memes seeds.

Les campagnes sont deterministes (seeds explicites), bornees (minutes CPU),
et se persistent en JSON sous ``ict/results/`` (convention des artefacts
committes de la serie) : le carnet ICT-36 lit les
artefacts, il ne rejoue pas la campagne (pattern artefacts-commits du banc
ICT-25).
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Dict, List, Sequence

import numpy as np

from ict import factor_geometry_trained as fgt
from ict.bench_factorise import (
    ConditionalBench,
    FactoredBench,
    Mess3Canonical,
    NoisedChannel,
    RRXOR,
    conditional_child_floor,
)

__all__ = [
    "position_contre_bande",
    "sweep_channel_noise",
    "conditional_campaign",
    "main",
]


def _jsonable(obj):
    """NaN/inf -> None : le JSON strict refuse NaN, l'artefact doit rester portable."""
    if isinstance(obj, dict):
        return {k: _jsonable(v) for k, v in obj.items()}
    if isinstance(obj, (list, tuple)):
        return [_jsonable(v) for v in obj]
    if isinstance(obj, bool):
        return obj
    if isinstance(obj, (np.bool_,)):
        return bool(obj)
    if isinstance(obj, (np.integer, int)):
        return int(obj)
    if isinstance(obj, (np.floating, float)):
        v = float(obj)
        return v if math.isfinite(v) else None
    return obj


def position_contre_bande(valeur: float, bande: Dict[str, float]) -> str:
    """Position d'une metrique contre la bande p05-p95 de son temoin du MEME niveau.

    ``n/a`` si la metrique ou la bande est degenerree (cible constante ->
    sonde de rang nul a gamma = 1, bande sans valeur finie) : un niveau
    degenerere se RAPPORTE, il ne se supprime pas.
    """
    v = float(valeur)
    p05, p95 = float(bande.get("p05", float("nan"))), float(bande.get("p95", float("nan")))
    if not (np.isfinite(v) and np.isfinite(p05) and np.isfinite(p95)):
        return "n/a"
    if v < p05:
        return "sous_bande"
    if v > p95:
        return "dessus_bande"
    return "dans_bande"


def sweep_channel_noise(
    gammas: Sequence[float] = (0.0, 0.25, 0.5, 0.65, 0.75, 0.9, 1.0),
    *,
    length: int = 100,
    n_train: int = 300,
    n_val: int = 40,
    steps: int = 1200,
    eval_every: int = 100,
    data_seed: int = 1,
    model_seed: int = 0,
    n_init: int = 6,
) -> List[Dict[str, object]]:
    """Critere 1 : entrainement complet PAR niveau de bruit du canal, temoin rejoue
    a CHAQUE niveau, lecture rendue a TOUS les niveaux (gate reussi OU echoue).

    Le bruit porte sur les emissions des DEUX facteurs (matrice ``E`` du
    Mess3, tenseur d'aretes ``W`` du RRXOR), transitions intactes. La
    lecture rendue au niveau a gate echoue est taggee : la falsifiable du
    critere -- la courbe overlap(gamma) retombe-t-elle dans la bande ? --
    se joue exactement la, ou un modele qui n'a rien appris doit se confondre
    avec le temoin de SON niveau.
    """
    if not fgt.HAS_TORCH:
        raise RuntimeError("sweep_channel_noise exige torch (pip install torch)")
    import torch

    uniforme_joint = float(np.log(3.0) + np.log(2.0))
    n_total = length * (n_train + n_val) + length
    n_tranche = n_train * length
    lignes: List[Dict[str, object]] = []
    for g in gammas:
        bench_g = FactoredBench(NoisedChannel(Mess3Canonical(), g), NoisedChannel(RRXOR(), g))
        ech_g = bench_g.sample(n_total, seed_a=data_seed, seed_b=data_seed)
        xj = np.stack([ech_g["obs_a"], ech_g["obs_b"]], axis=1).astype(np.int64)
        pl_a = fgt.bayes_floor(bench_g.factor_a, ech_g["obs_a"][:n_tranche])
        pl_b = fgt.bayes_floor(bench_g.factor_b, ech_g["obs_b"][:n_tranche])
        xtr = torch.from_numpy(xj[:n_tranche].reshape(n_train, length, 2))
        xva = torch.from_numpy(
            xj[n_tranche : n_tranche + n_val * length].reshape(n_val, length, 2)
        )
        modele_g = fgt.FactoredRNN(seed=model_seed)
        res_g = fgt.train_model(modele_g, xtr, xva, steps=steps, eval_every=eval_every, seed=model_seed)
        bel_a = bench_g.factor_a.beliefs(ech_g["obs_a"][:n_tranche])
        bel_b = bench_g.factor_b.beliefs(ech_g["obs_b"][:n_tranche])
        rapport = fgt.factor_geometry_report(
            fgt.collect_activations(modele_g, xtr), bel_a, bel_b
        )
        temoin = fgt.untrained_null(
            lambda sd: fgt.FactoredRNN(seed=sd), xtr, bel_a, bel_b, n_init=n_init
        )
        lignes.append(
            {
                "gamma": float(g),
                "plancher_a": pl_a,
                "plancher_b": pl_b,
                "plancher_joint": pl_a + pl_b,
                "best_val_nll": float(res_g["best_val_nll"]),
                "best_step": int(res_g["best_step"]),
                "gate": bool(res_g["best_val_nll"] < uniforme_joint),
                "rapport": rapport,
                "temoin": temoin,
            }
        )
    return lignes


def conditional_campaign(
    kappa: float = 0.28,
    child_emission_diag: float = 0.4,
    *,
    length: int = 100,
    n_train: int = 300,
    n_val: int = 40,
    steps: int = 1200,
    eval_every: int = 100,
    data_seed: int = 1,
    model_seeds: Sequence[int] = (0, 1, 7),
    n_init: int = 6,
) -> Dict[str, object]:
    """Critere 2 : banc conditionnel contre controle independant, memes marginales.

    Corrections de protocole par rapport a la premiere passe (#20091, 400
    pas, kappa = 0.2, une graine) :

    - ``kappa`` pousse vers la borne de stochasticite de l'enfant (enfant a
      emission plus plate : ``emission_diag = 0.4`` -> hors-diagonale 0.30,
      kappa <= 0.30) : la dependance posee par les donnees est plus forte,
      l'appariement des marginales reste EXACT (les rotations s'annulent) ;
    - trois graines modele (le verdict n'est plus celui d'une seule graine) ;
    - le discriminant rendu est ``overlap_energy`` (continu) A COTE du gap
      entier imprime -- c'est la de-saturation mesuree : les bandes du temoin
      en gap entier etaient de largeur nulle sur les deux bancs.

    Le controle independant utilise le MEME enfant (meme ``emission_diag``),
    les memes seeds de donnees : tout ecart entre les deux bancs ne peut
    venir que de la loi jointe.
    """
    if not fgt.HAS_TORCH:
        raise RuntimeError("conditional_campaign exige torch (pip install torch)")
    import torch

    parent = Mess3Canonical()
    enfant = Mess3Canonical(emission_diag=child_emission_diag)
    bench_cond = ConditionalBench(parent, enfant, kappa=kappa)
    bench_ind = FactoredBench(parent, enfant)
    n_total = length * (n_train + n_val) + length
    n_tranche = n_train * length
    ech_c = bench_cond.sample(n_total, seed_parent=data_seed, seed_child=data_seed)
    ech_i = bench_ind.sample(n_total, seed_a=data_seed, seed_b=data_seed)
    bels_c = bench_cond.beliefs(ech_c["obs_a"], ech_c["obs_b"])
    bels_i = bench_ind.beliefs(ech_i["obs_a"], ech_i["obs_b"])

    # appariement des marginales, verifie sur les MATRICES puis sur l'echantillon
    e_marg = np.asarray(enfant.emission_matrix(), dtype=np.float64)
    apparie_mat = bool(np.allclose(bench_cond.marginal_child(), e_marg, atol=1e-12))
    emp_c = np.bincount(ech_c["obs_b"], minlength=e_marg.shape[1]) / len(ech_c["obs_b"])
    emp_i = np.bincount(ech_i["obs_b"], minlength=e_marg.shape[1]) / len(ech_i["obs_b"])
    apparie_emp = float(np.abs(emp_c - emp_i).max())

    t_e, pi_e = enfant.transition_matrix(), enfant.stationary()
    variants = bench_cond.emission_variants()
    pl_genie = conditional_child_floor(ech_c["obs_b"], ech_c["obs_a"], t_e, variants, pi_e, burn=32)
    pl_aveugle = conditional_child_floor(
        ech_c["obs_b"], ech_c["obs_a"], t_e, (e_marg,) * len(variants), pi_e, burn=32
    )
    pl_parent = fgt.bayes_floor(parent, ech_c["obs_a"][:n_tranche])
    uniforme = float(2.0 * np.log(3.0))

    resultats: Dict[str, object] = {}
    for nom, ech_x, bels in (
        ("conditionnel", ech_c, bels_c),
        ("independant", ech_i, bels_i),
    ):
        xj = np.stack([ech_x["obs_a"], ech_x["obs_b"]], axis=1).astype(np.int64)
        xtr = torch.from_numpy(xj[:n_tranche].reshape(n_train, length, 2))
        xva = torch.from_numpy(
            xj[n_tranche : n_tranche + n_val * length].reshape(n_val, length, 2)
        )
        bel_a = bels["belief_a"][:n_tranche]
        bel_b = bels["belief_b"][:n_tranche]
        par_seed: Dict[int, Dict[str, object]] = {}
        for sd in model_seeds:
            modele_x = fgt.FactoredRNN(n_a=3, n_b=3, seed=sd)
            res_x = fgt.train_model(modele_x, xtr, xva, steps=steps, eval_every=eval_every, seed=sd)
            rapport = fgt.factor_geometry_report(
                fgt.collect_activations(modele_x, xtr), bel_a, bel_b
            )
            par_seed[int(sd)] = {
                "best_val_nll": float(res_x["best_val_nll"]),
                "gate": bool(res_x["best_val_nll"] < uniforme),
                "rapport": rapport,
            }
        temoin = fgt.untrained_null(
            lambda s: fgt.FactoredRNN(n_a=3, n_b=3, seed=s), xtr, bel_a, bel_b, n_init=n_init
        )
        resultats[nom] = {"par_seed": par_seed, "temoin": temoin}

    return {
        "kappa": float(kappa),
        "child_emission_diag": float(child_emission_diag),
        "steps": int(steps),
        "model_seeds": [int(s) for s in model_seeds],
        "n_init": int(n_init),
        "appariement": {
            "matrices_exact": apparie_mat,
            "ecart_empirique_max": apparie_emp,
        },
        "planchers": {
            "genie": pl_genie,
            "aveugle": pl_aveugle,
            "prime_conditionnelle": pl_aveugle - pl_genie,
            "parent": pl_parent,
            "uniforme_joint": uniforme,
        },
        "resultats": resultats,
    }


def _print_sweep(lignes: List[Dict[str, object]]) -> None:
    print("gamma  plancher   val     gate    r2a (bande)          r2b (bande)          ovl (bande)          energie (bande)")
    for l in lignes:
        r, t = l["rapport"], l["temoin"]
        def _b(m):  # bande p05-p95 d'une metrique du temoin
            b = t[m]
            return f"{b['p05']:.3f}-{b['p95']:.3f}" if b.get("n") else "degeneree"
        gate = "PASS  " if l["gate"] else "ECHEC "
        def _v(m):
            v = r[m]
            return f"{v:.3f}" if np.isfinite(v) else "nan"
        print(f"{l['gamma']:.2f}  {l['plancher_joint']:.5f}  {l['best_val_nll']:.4f}  {gate}  "
              f"{_v('probe_r2_a')} [{_b('probe_r2_a')}]  {_v('probe_r2_b')} [{_b('probe_r2_b')}]  "
              f"{_v('overlap_coef_max')} [{_b('overlap_coef_max')}]  {_v('overlap_energy')} [{_b('overlap_energy')}]")
        for m in ("probe_r2_a", "probe_r2_b", "overlap_coef_max", "overlap_energy"):
            pos = position_contre_bande(r[m], t[m])
            if pos != "n/a":
                print(f"       {m}: {pos}")


def main(argv: Sequence[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        description="Campagnes des regimes generatifs #20071 (critere 1 : bruit du canal ; critere 2 : conditionnel)."
    )
    p.add_argument("--out-dir", default=None, help="dossier des artefacts (defaut : ict/results/)")
    p.add_argument("--steps", type=int, default=1200)
    p.add_argument("--quick", action="store_true", help="passe fumeee mini (tests CI)")
    args = p.parse_args(argv)

    out = Path(args.out_dir) if args.out_dir else Path(__file__).resolve().parent / "results"
    out.mkdir(parents=True, exist_ok=True)
    commun = {"steps": args.steps, "length": 100, "n_train": 300, "n_val": 40, "n_init": 6}
    gammas: Sequence[float] = (0.0, 0.25, 0.5, 0.65, 0.75, 0.9, 1.0)
    if args.quick:
        commun.update({"steps": 20, "length": 20, "n_train": 8, "n_val": 4, "n_init": 5})
        gammas = (0.0, 1.0)

    print("[regime 1] sweep bruit du canal -- entraînement PAR niveau, temoin PAR niveau")
    lignes = sweep_channel_noise(gammas=gammas, steps=commun["steps"], length=commun["length"],
                                 n_train=commun["n_train"], n_val=commun["n_val"],
                                 n_init=commun["n_init"])
    _print_sweep(lignes)
    art1 = out / "ict36_regime1_sweep_bruit_canal.json"
    art1.write_text(
        json.dumps(_jsonable({"protocole": commun, "niveaux": lignes}), indent=1, ensure_ascii=False),
        encoding="utf-8",
    )
    print(f"[regime 1] artefact -> {art1}")

    print("[regime 2] conditionnel vs independant -- memes marginales, kappa fort, 3 graines")
    camp = conditional_campaign(steps=commun["steps"], length=commun["length"],
                                n_train=commun["n_train"], n_val=commun["n_val"],
                                n_init=commun["n_init"])
    pl = camp["planchers"]
    print(f"appariement matrices exact : {camp['appariement']['matrices_exact']}  "
          f"ecart empirique max : {camp['appariement']['ecart_empirique_max']:.4f}")
    print(f"planchers enfant : genie {pl['genie']:.4f} / aveugle {pl['aveugle']:.4f}  "
          f"prime {pl['prime_conditionnelle']:+.4f} nats")
    for nom, ent in camp["resultats"].items():
        t_gap, t_enr = ent["temoin"]["additivity_gap"], ent["temoin"]["overlap_energy"]
        print(f"{nom:12s} temoin gap [{t_gap['p05']:+.3f},{t_gap['p95']:+.3f}]  "
              f"energie [{t_enr['p05']:.3f},{t_enr['p95']:.3f}]")
        for sd, e in ent["par_seed"].items():
            r = e["rapport"]
            print(f"  seed {sd}: val={e['best_val_nll']:.4f} gate={'PASS' if e['gate'] else 'ECHEC'}  "
                  f"gap={r['additivity_gap']:+.3f} [{position_contre_bande(r['additivity_gap'], t_gap)}]  "
                  f"energie={r['overlap_energy']:.3f} [{position_contre_bande(r['overlap_energy'], t_enr)}]  "
                  f"ovl={r['overlap_coef_max']:.3f}  r2=({r['probe_r2_a']:.3f},{r['probe_r2_b']:.3f})")
    art2 = out / "ict36_regime2_conditionnel.json"
    art2.write_text(json.dumps(_jsonable(camp), indent=1, ensure_ascii=False), encoding="utf-8")
    print(f"[regime 2] artefact -> {art2}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
