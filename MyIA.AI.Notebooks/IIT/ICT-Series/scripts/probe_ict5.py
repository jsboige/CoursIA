"""Probe de grounding ICT-5 : calcule avec le VRAI PyPhi tous les chiffres
narres dans le notebook sur l'emergence causale (effective information et Phi
aux echelles micro/macro, recherche de coarse-graining a la Hoel/Jansma).

Lancer avec le python de l'env `pyphi`. Sortie sur stdout, a relire avant ecriture.
"""
import numpy as np
import pyphi

pyphi.config.WELCOME_OFF = True
pyphi.config.PROGRESS_BARS = False
pyphi.config.VALIDATE_SUBSYSTEM_STATES = False
for _attr in ("PARALLEL_CONCEPT_EVALUATION", "PARALLEL_CUT_EVALUATION",
              "PARALLEL_COMPLEX_EVALUATION", "PARALLEL"):
    if hasattr(pyphi.config, _attr):
        setattr(pyphi.config, _attr, False)

import pyphi.macro as M

print("=== versions ===")
print("pyphi", pyphi.__version__, "numpy", np.__version__)


def report(net, state, name):
    micro_phi = float(pyphi.compute.phi(pyphi.Subsystem(net, state, range(net.size))))
    micro_ei = float(M.effective_info(net))
    mn = M.emergence(net, state, do_coarse_grain=True, do_blackbox=False)
    macro_phi = float(mn.phi)
    delta = float(mn.emergence)
    print(f"\n##### {name} (micro n={net.size}, etat={state}) #####")
    print(f"  micro : Phi={micro_phi:.4f}  EI={micro_ei:.4f}")
    print(f"  macro : Phi={macro_phi:.4f}  emergence (dPhi)={delta:+.4f}")
    print(f"  meilleur coarse-grain : partition={mn.coarse_grain.partition}")
    return dict(name=name, micro_phi=micro_phi, micro_ei=micro_ei,
                macro_phi=macro_phi, emergence=delta,
                partition=mn.coarse_grain.partition)


# 1) exemple canonique d'emergence livre avec PyPhi (Hoel) : micro degenere -> macro net
report(pyphi.examples.macro_network(), (0, 0, 0, 0),
       "Hoel macro_network (micro bruite -> macro emergent)")

# 2) contre-exemple : XOR, micro deja maximalement integre -> coarse-graining detruit
report(pyphi.examples.xor_network(), (0, 0, 0),
       "XOR (micro integre -> pas d'emergence)")

# 3) contre-exemple : basic_network, micro le plus integre
report(pyphi.examples.basic_network(), (1, 0, 0),
       "basic_network (micro integre -> pas d'emergence)")
