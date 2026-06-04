"""Quick API test for PyPhi 1.2.0 - verify notebook code works."""
import os
os.environ['PYPHI_WELCOME_OFF'] = 'yes'
import pyphi
import numpy as np

print("PyPhi version:", pyphi.__version__)

# Test 1: XOR network + CES
network = pyphi.examples.xor_network()
state = (0, 0, 0)
subsystem = pyphi.Subsystem(network, state)
print("Subsystem nodes:", subsystem.node_indices)

pyphi.config.VALIDATE_SUBSYSTEM_STATES = False
ces = pyphi.compute.ces(subsystem)
print("CES length:", len(ces))
for c in ces:
    print(f"  Concept: mech={c.mechanism}, phi={c.phi}")

# Test 2: SIA (big Phi)
sia = pyphi.compute.sia(subsystem)
print(f"Big Phi (SIA): {sia.phi}")
print(f"SIA cut: {sia.cut}")

# Test 3: MICE for a mechanism
mechanism = (0, 1)
try:
    mice_cause = subsystem.find_mice(pyphi.Direction.CAUSE, mechanism)
    print(f"MICE cause for {mechanism}: phi={mice_cause.phi}, purview={mice_cause.purview}")
    mice_effect = subsystem.find_mice(pyphi.Direction.EFFECT, mechanism)
    print(f"MICE effect for {mechanism}: phi={mice_effect.phi}, purview={mice_effect.purview}")
except Exception as e:
    print(f"MICE error: {e}")

# Test 4: Cause/effect repertoire
try:
    rep_cause = subsystem.cause_repertoire(mechanism, (0,))
    print(f"Cause repertoire shape: {rep_cause.shape}")
    print(f"Cause repertoire:\n{rep_cause}")
    rep_effect = subsystem.effect_repertoire(mechanism, (0,))
    print(f"Effect repertoire shape: {rep_effect.shape}")
except Exception as e:
    print(f"Repertoire error: {e}")

# Test 5: Larger network (4 nodes)
tpm = np.array([
    [0, 0, 0, 0],
    [0, 0, 1, 1],
    [0, 1, 0, 1],
    [1, 1, 1, 0],
    [0, 0, 1, 1],
    [1, 0, 0, 1],
    [1, 1, 0, 0],
    [1, 1, 1, 1],
    [0, 1, 0, 0],
    [1, 0, 1, 1],
    [0, 0, 1, 0],
    [1, 1, 0, 1],
    [0, 1, 1, 0],
    [1, 0, 0, 0],
    [1, 0, 1, 0],
    [1, 1, 0, 1],
])
cm = np.array([[0,1,1,0],[1,0,0,1],[1,0,0,1],[0,1,1,0]])
labels = ('A','B','C','D')
net4 = pyphi.Network(tpm, cm, labels=labels)
print("4-node network created, nodes:", list(net4.node_indices))

# Test 6: Concept style (IIT 3.0 vs concept-style)
try:
    cs = pyphi.compute.sia_concept_style(subsystem)
    print(f"Concept-style Phi: {cs.phi}")
except Exception as e:
    print(f"Concept-style error: {e}")

# Test 7: effective_info
try:
    ei = pyphi.subsystem.effective_info(subsystem)
    print(f"Effective info: {ei}")
except Exception as e:
    print(f"EI error: {e}")

# Test 8: All partitions of a mechanism
try:
    cuts = list(pyphi.partition.mip_bipartitions(subsystem.node_indices, subsystem.node_indices))
    print(f"MIP bipartitions count: {len(cuts)}")
except Exception as e:
    print(f"Partitions error: {e}")

print("\nAll API tests completed!")
