# Adaptateur PyMC du contrat JSON VoI (tranche 3/3 #13569).
# Extraction fidele de DecPyMC-5 cellule 33, alimentee par PyMC :
# le modele generatif (etat -> signal) est echantillonne par
# pm.sample_prior_predictive (seed fixe), les posterieurs P(etat|signal=j)
# et marginales P(signal=j) sont les frequences conditionnelles empiriques
# du modele PyMC -- pas de Bayes ecrit a la main.
#
# usage: python pymc_voi.py <problem.json> <output.json> [draws]

import json
import sys

import numpy as np
import pymc as pm
import pytensor.tensor as pt

DEFAULT_DRAWS = 200_000


def main(argv):
    if len(argv) < 3:
        print("usage: pymc_voi.py <problem.json> <output.json> [draws]", file=sys.stderr)
        return 2
    with open(argv[1], encoding="utf-8") as fh:
        spec = json.load(fh)
    draws = int(argv[3]) if len(argv) > 3 else DEFAULT_DRAWS

    if len(spec["states"]) != 2 or len(spec["signals"]) != 2:
        print("contrat binaire : 2 etats x 2 signaux", file=sys.stderr)
        return 2

    s1, s0 = spec["states"]
    sig1, sig0 = spec["signals"]
    p1 = spec["priors"][s1]
    lik11 = spec["likelihood"][sig1][s1]
    lik10 = spec["likelihood"][sig1][s0]

    # Modele generatif PyMC : etat ~ Bernoulli(prior), signal | etat ~ Bernoulli(lik)
    with pm.Model() as model:
        etat = pm.Bernoulli("etat", p=p1)
        p_signal = pt.switch(etat, lik11, lik10)
        signal = pm.Bernoulli("signal", p=p_signal)
        idata = pm.sample_prior_predictive(draws=draws, random_seed=42)

    etat_draws = idata.prior["etat"].values.ravel()
    signal_draws = idata.prior["signal"].values.ravel()

    signal_marginals = {
        sig1: float(np.mean(signal_draws == 1)),
        sig0: float(np.mean(signal_draws == 0)),
    }
    posteriors = {}
    for name, obs in ((sig1, 1), (sig0, 0)):
        mask = signal_draws == obs
        n = int(mask.sum())
        if n == 0:
            print(f"signal {name} jamais tire en {draws} draws", file=sys.stderr)
            return 2
        post1 = float(np.mean(etat_draws[mask] == 1))
        posteriors[name] = {s1: post1, s0: 1.0 - post1}

    # Combinateur VoI (cellule 33), alimente par les quantites PyMC
    states, actions = spec["states"], spec["actions"]
    utils = spec["utilities"]

    def eu_action(action, belief):
        return sum(belief[st] * utils[action][st] for st in states)

    eu_per_action = {a: eu_action(a, spec["priors"]) for a in actions}
    action_no_info = max(eu_per_action, key=eu_per_action.get)
    eu_no_info = eu_per_action[action_no_info]

    eu_perfect = sum(
        spec["priors"][st] * max(utils[a][st] for a in actions) for st in states
    )
    evpi = eu_perfect - eu_no_info

    eu_avec_info = sum(
        signal_marginals[sig] * max(eu_action(a, posteriors[sig]) for a in actions)
        for sig in (sig1, sig0)
    )
    evsi_brute = eu_avec_info - eu_no_info
    evsi_nette = evsi_brute - spec["test_cost"]

    output = {
        "engine": "pymc",
        "problem": spec["problem"],
        "draws": draws,
        "eu_no_info": eu_no_info,
        "action_no_info": action_no_info,
        "evpi": evpi,
        "evsi_brute": evsi_brute,
        "evsi_nette": evsi_nette,
        "decision": "observer" if evsi_nette > 0 else "agir_sans_test",
        "signal_marginals": signal_marginals,
        "posteriors": posteriors,
    }
    with open(argv[2], "w", encoding="utf-8") as fh:
        json.dump(output, fh, indent=2)
    print(
        f"pymc | {spec['problem']} | EU={eu_no_info:.0f} ({action_no_info}) "
        f"EVPI={evpi:.0f} EVSI_brute={evsi_brute:.0f} EVSI_nette={evsi_nette:.0f} "
        f"decision={output['decision']}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
