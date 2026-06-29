"""Probe de grounding ICT-1 : calcule avec le VRAI PyPhi tous les chiffres
narres dans le notebook (paysages de Phi, trajectoires, perturbation/recuperation).
Lancer avec le python de l'env `pyphi`. Sortie sur stdout, a relire avant ecriture.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import numpy as np
import pyphi
pyphi.config.PROGRESS_BARS = False
pyphi.config.WELCOME_OFF = True
pyphi.config.VALIDATE_SUBSYSTEM_STATES = False
for attr in ("PARALLEL_CONCEPT_EVALUATION", "PARALLEL_CUT_EVALUATION",
             "PARALLEL_COMPLEX_EVALUATION", "PARALLEL"):
    if hasattr(pyphi.config, attr):
        setattr(pyphi.config, attr, False)

from ict import trajectories as T

print("=== versions ===")
print("pyphi", pyphi.__version__, "numpy", np.__version__)


def phi_landscape(network, n):
    nodes = tuple(range(n))
    out = {}
    for s in T.all_states(n):
        sub = pyphi.Subsystem(network, s, nodes)
        out[s] = float(pyphi.compute.phi(sub))
    return out


# --- reseau integre AND/OR (verifie : Phi(1,0,0)=2.31) -------------------
andor_tpm = np.array([
    [0, 0, 0], [0, 0, 1], [1, 0, 1], [1, 0, 0],
    [1, 1, 0], [1, 1, 1], [1, 1, 1], [1, 1, 0],
])
andor = pyphi.Network(andor_tpm, node_labels=['A', 'B', 'C'])

# --- reseau XOR (exemple canonique pyphi) -------------------------------
xor = pyphi.examples.xor_network()

print("\n=== paysage de Phi : AND/OR ===")
land_andor = phi_landscape(andor, 3)
for s, p in land_andor.items():
    print(f"  etat {s} -> Phi = {p:.4f}")
vals = list(land_andor.values())
print(f"  min={min(vals):.4f} max={max(vals):.4f} moyenne={sum(vals)/len(vals):.4f} amplitude={max(vals)-min(vals):.4f}")

print("\n=== paysage de Phi : XOR ===")
land_xor = phi_landscape(xor, 3)
for s, p in land_xor.items():
    print(f"  etat {s} -> Phi = {p:.4f}")
vx = list(land_xor.values())
print(f"  min={min(vx):.4f} max={max(vx):.4f} moyenne={sum(vx)/len(vx):.4f} amplitude={max(vx)-min(vx):.4f}")

print("\n=== trajectoires deterministes AND/OR ===")
for start in [(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 1)]:
    path, cyc = T.state_trajectory(andor.tpm, start)
    attr = T.attractor_of(andor.tpm, start)
    phis = T.phi_trajectory(land_andor, path)
    print(f"  depart {start}: chemin={path} attracteur={attr}")
    print(f"     Phi le long = {[round(p,3) for p in phis]}  events={T.detect_events(phis)}")

print("\n=== trajectoires deterministes XOR ===")
for start in [(0, 0, 0), (1, 0, 0), (1, 1, 1), (0, 1, 1)]:
    path, cyc = T.state_trajectory(xor.tpm, start)
    attr = T.attractor_of(xor.tpm, start)
    phis = T.phi_trajectory(land_xor, path)
    print(f"  depart {start}: chemin={path} attracteur={attr}")
    print(f"     Phi le long = {[round(p,3) for p in phis]}")

print("\n=== bassins d'attraction ===")
print("  AND/OR:", T.basin_sizes(andor.tpm, 3))
print("  XOR   :", T.basin_sizes(xor.tpm, 3))

print("\n=== perturbation / recuperation de Phi (AND/OR) ===")
# on part d'un etat, on rejoint l'attracteur, on bascule 1 bit, on re-evolue
start = (1, 1, 1)
attr = T.attractor_of(andor.tpm, start)
base_state = attr[0]
print(f"  attracteur depuis {start} = {attr}, on perturbe a partir de {base_state}")
for bit in range(3):
    pert = T.flip_bit(base_state, bit)
    path, cyc = T.state_trajectory(andor.tpm, pert)
    phis = T.phi_trajectory(land_andor, [base_state] + path)
    new_attr = T.attractor_of(andor.tpm, pert)
    same = tuple(sorted(new_attr)) == tuple(sorted(attr))
    print(f"  flip noeud {bit}: {base_state}->{pert}  Phi={[round(p,3) for p in phis]}  retour_meme_attracteur={same}")
