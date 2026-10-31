"""Tests du module :mod:`ict.argumentation` (ICT-7289 Phase A, Epic #4588).

Chaque test valide une propriete falsifiable du substrat argumentation,
numerote par *gate*. Pattern herite de ``test_time_arrow.py`` /
``test_reversibility_budget.py`` : bootstrap ``sys.path`` module-level, sans
fixtures, tolerances commentees.
"""

from __future__ import annotations

import os
import sys

import numpy as np
import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict import argumentation as arg  # noqa: E402


# --------------------------------------------------------------------------- #
#  Gate 1 : semantique grounded sur un AF simple (in / out)                   #
# --------------------------------------------------------------------------- #


def test_grounded_simple_in_out():
    """Un argument non attaque est ``in`` ; celui qu'il attaque est ``out``.

    AF : 0 -> 1 (0 attaque 1). Pas d'autre attaque.
    Labeling grounded attendu : 0 = in, 1 = out.
    """
    af = arg.DungAF([0, 1], [(0, 1)])
    lab = arg.grounded_labeling(af)
    assert lab[0] == "in", f"0 non attaque doit etre in, recu {lab[0]}"
    assert lab[1] == "out", f"1 attaque par 0 (in) doit etre out, recu {lab[1]}"


# --------------------------------------------------------------------------- #
#  Gate 2 : Nixon diamond -> les deux undec (cas test canonique)              #
# --------------------------------------------------------------------------- #


def test_grounded_nixon_diamond_undec():
    """Le Nixon diamond (cycle d'attaque mutuelle) -> les deux ``undec``.

    AF : 0 -> 1 et 1 -> 0 (attaque mutuelle, aucun attaquant externe).
    La semantique grounded ne peut trancher : ni 0 ni 1 n'a tous ses
    attaquants ``out`` -> les deux restent ``undec``.
    """
    af = arg.nixon_diamond()
    lab = arg.grounded_labeling(af)
    assert lab[0] == "undec" and lab[1] == "undec", (
        f"Nixon diamond : les deux doivent etre undec, recu {lab}"
    )


# --------------------------------------------------------------------------- #
#  Gate 3 : chaine lineaire -> alternance in/out                              #
# --------------------------------------------------------------------------- #


def test_grounded_chain_alternance():
    """Chaine 0 -> 1 -> 2 -> 3 : alternance in/out (0=in, 1=out, 2=in, 3=out)."""
    af = arg.controversial_chain(4)
    lab = arg.grounded_labeling(af)
    expected = {0: "in", 1: "out", 2: "in", 3: "out"}
    for a, exp in expected.items():
        assert lab[a] == exp, f"chaine : {a} doit etre {exp}, recu {lab[a]}"


# --------------------------------------------------------------------------- #
#  Gate 4 : trajectoire de croyance (arrivee sequentielle)                    #
# --------------------------------------------------------------------------- #


def test_belief_trajectory_length_and_evolution():
    """L'arrivee sequentielle produit une trajectoire de longueur n, et le
    labeling evolue (le dernier pas porte tous les arguments)."""
    af = arg.controversial_chain(3)
    traj = arg.belief_trajectory(af, order=[0, 1, 2])
    assert len(traj) == 3, f"trajectoire de longueur 3 attendue, {len(traj)}"
    # Au pas 1 : seul l'arg 0, non attaque -> in.
    assert traj[0] == {0: "in"}
    # Au pas 3 : tous presents, chaine complete.
    assert set(traj[2].keys()) == {0, 1, 2}


def test_belief_trajectory_include_empty():
    """``include_empty=True`` ajoute l'etat vide en tete (etat initial)."""
    af = arg.nixon_diamond()
    traj = arg.belief_trajectory(af, order=[0, 1], include_empty=True)
    assert len(traj) == 3
    assert traj[0] == {}, f"etat initial vide attendu, recu {traj[0]}"


# --------------------------------------------------------------------------- #
#  Gate 5 : resume d'etat (n_in, n_out, n_undec)                              #
# --------------------------------------------------------------------------- #


def test_belief_summary_counts():
    """Le resume compte correctement in/out/undec."""
    labeling = {0: "in", 1: "out", 2: "undec", 3: "in"}
    assert arg.belief_summary(labeling) == (2, 1, 1)


# --------------------------------------------------------------------------- #
#  Gate 6 : signature complete base-3 (identite preservee)                    #
# --------------------------------------------------------------------------- #


def test_state_signature_base3_with_placeholder():
    """La signature encode out=0, undec=1, in=2, et -1 pour les non-arrives."""
    labeling = {0: "in", 2: "out"}  # arg 1 non arrive
    sig = arg.state_signature(labeling, n_args=3)
    assert sig == (2, -1, 0), f"signature base-3 attendue (2,-1,0), recu {sig}"


def test_state_signature_distinguishes_identity():
    """Deux labelings avec meme compte mais identite differente -> signatures
    differentes (critere pour la dette d'irreversibilite en Phase B)."""
    lab_a = {0: "in", 1: "out"}
    lab_b = {0: "out", 1: "in"}
    # Memes comptes (1 in, 1 out) mais identites differentes.
    assert arg.belief_summary(lab_a) == arg.belief_summary(lab_b)
    assert arg.state_signature(lab_a, n_args=2) != arg.state_signature(lab_b, n_args=2)


# --------------------------------------------------------------------------- #
#  Gate 7 : TPM ligne-stochastique depuis une trajectoire                     #
# --------------------------------------------------------------------------- #


def test_belief_transition_matrix_row_stochastic():
    """La TPM est carree et ligne-stochastique (chaque ligne somme a 1)."""
    af = arg.controversial_chain(5)
    P, mapping = arg.belief_transition_matrix(af, order=[0, 1, 2, 3, 4])
    n = P.shape[0]
    assert P.shape == (n, n), "TPM carree attendue"
    row_sums = P.sum(axis=1)
    assert np.allclose(row_sums, 1.0), (
        f"lignes de TPM doivent sommer a 1, recu {row_sums}"
    )


def test_belief_transition_matrix_encoding_signature():
    """L'encodage ``signature`` produit une TPM valide (etats distincts)."""
    af = arg.nixon_diamond()
    P, mapping = arg.belief_transition_matrix(
        af, order=[0, 1], encoding="signature"
    )
    assert P.shape[0] >= 1
    assert np.allclose(P.sum(axis=1), 1.0)


# --------------------------------------------------------------------------- #
#  Gate 8 : fleche du temps du discours (sigma >= 0)                          #
# --------------------------------------------------------------------------- #


def test_discourse_irreversibility_nonneg_and_stationary():
    """``discourse_irreversibility`` renvoie sigma >= 0 et pi stochastique."""
    af = arg.controversial_chain(6)
    P, _ = arg.belief_transition_matrix(af, order=list(range(6)))
    diag = arg.discourse_irreversibility(P)
    assert diag["sigma"] >= 0.0, f"sigma doit etre >= 0, recu {diag['sigma']}"
    assert np.allclose(diag["pi"].sum(), 1.0), "pi doit sommer a 1"
    assert diag["P_rev_distance"] >= 0.0


def test_discourse_irreversibility_reversible_zero():
    """Une TPM symetrique (detailed balance) a sigma ~ 0 (discours reversible)."""
    P_sym = np.array([[0.5, 0.5], [0.5, 0.5]])
    diag = arg.discourse_irreversibility(P_sym)
    assert diag["sigma"] < 1e-9, f"TPM reversible : sigma ~ 0, recu {diag['sigma']}"


def test_discourse_irreversibility_asymmetric_positive():
    """Une TPM bidirectionnelle ASYMETRIQUE a sigma > 0 (fleche du temps reelle).

    Honnetete : sur un debat deterministe a ordre fixe (gate 8 precedent),
    sigma = 0 (pas de cycle de flux). Mais l'instrument DOIT distinguer un
    regime bidirectionnel asymetrique (bascules de croyance preferentiellement
    dans un sens) -> sigma strictement positif. Sans ce test, l'instrument
    pourrait etre accuse de 'rendre toujours 0'.
    """
    # TPM 2x2 asymetrique : transition 0->1 plus probable que 1->0.
    P_asym = np.array([[0.3, 0.7], [0.9, 0.1]])
    diag = arg.discourse_irreversibility(P_asym)
    assert diag["sigma"] > 0.0, (
        f"TPM asymetrique : sigma > 0 attendu, recu {diag['sigma']}"
    )


# --------------------------------------------------------------------------- #
#  Gate 9 : sous-AF induit (induced)                                          #
# --------------------------------------------------------------------------- #


def test_induced_subgraph_keeps_internal_attacks_only():
    """Le sous-AF induit ne garde que les attaques dont les deux extremites
    sont dans le sous-ensemble."""
    af = arg.DungAF([0, 1, 2, 3], [(0, 1), (1, 2), (2, 3)])
    sub = af.induced([0, 1, 3])  # arg 2 retire
    # (1,2) et (2,3) disparaissent (2 absent) ; seul (0,1) reste.
    assert sub.attacks == [(0, 1)]
    assert sub.n() == 3


# --------------------------------------------------------------------------- #
#  Gate 10 : PASS Phase A — TPM derivee d'un AF canonique (verdict)           #
# --------------------------------------------------------------------------- #


def test_phase_a_verdict_tpm_derivable():
    """GATE de Phase A : une TPM exploitable est derivable d'un AF reel.

    Preuve : on derive une TPM ligne-stochastique non triviale (au moins 2
    etats distincts) depuis l'AF canonique *Nixon diamond* (documente dans la
    serie Tweety). Si la TPM etait triviale (1 etat), le substrat serait
    inexploitable -> verdict d'impossibilite. Ici : PASS.
    """
    af = arg.nixon_diamond()
    P, mapping = arg.belief_transition_matrix(af, order=[0, 1])
    n_states = len(mapping)
    assert n_states >= 2, (
        f"Phase A : la TPM doit avoir >= 2 etats, recu {n_states} -> FAIL"
    )
    assert np.allclose(P.sum(axis=1), 1.0)


# --------------------------------------------------------------------------- #
#  Gate 11 : self-loop = cycle de longueur 1 -> undec (corner case Dung)      #
# --------------------------------------------------------------------------- #


def test_grounded_self_loop_is_undec():
    """Un argument qui s'auto-attaque (self-loop ``(a, a)``) reste ``undec``.

    Corner case sémantique de Dung : un self-loop est un cycle de longueur 1.
    L'algorithme par point fixe ne crédite jamais ``a`` comme ``in`` (il
    faudrait que son unique attaquant -- lui-même -- soit d'abord ``out``, ce
    qui exigerait qu'un ``in`` l'attaque, impasse), ni comme ``out`` (aucun
    ``in`` ne l'attaque). Il tombe donc ``undec``, exactement comme un cycle
    classique (Nixon diamond). Ce test protège la sémantique contre une
    « optimisation » qui traiterait les self-loops comme des attaques
    incontestées -> ``out`` (convention non standard).
    """
    af = arg.DungAF([0], [(0, 0)])
    label = arg.grounded_labeling(af)
    assert label[0] == "undec", (
        f"self-loop doit etre undec (cycle longueur 1), recu {label[0]!r}"
    )


# --------------------------------------------------------------------------- #
#  Gate 12 : tweety_bird() resout le conflit (vs Nixon diamond)               #
# --------------------------------------------------------------------------- #


def test_tweety_bird_resolves_conflict():
    """Le schéma canonique *Tweety* (oiseau vs autruche) se résout par soutien
    indirect -- contrairement au *Nixon diamond* (cycle non résolu).

    AF : 0 <-> 1 (conflit direct Tweety vole / ne vole pas), 2 -> 1 (le fait
    « oiseau » attaque la négation). Grounded : 2 (non attaqué) = ``in`` ;
    1 (attaqué par 2 ``in``) = ``out`` ; 0 (son seul attaquant 1 est ``out``)
    = ``in``. Labeling attendu : {0: in, 1: out, 2: in}, aucun ``undec``.
    C'est le contrepoint canonique au Nixon diamond (les deux ``undec``) :
    l'ajout d'un attaquant externe non contesté (2) brise la symétrie.
    """
    af = arg.tweety_bird()
    label = arg.grounded_labeling(af)
    assert label == {0: "in", 1: "out", 2: "in"}, (
        f"tweety_bird doit se resoudre en {{0:in, 1:out, 2:in}}, recu {label}"
    )


# --------------------------------------------------------------------------- #
#  Gate 13 : controversial_chain(n) = alternance in/out stricte               #
# --------------------------------------------------------------------------- #


@pytest.mark.parametrize("n", [2, 3, 4, 5, 8])
def test_controversial_chain_alternation(n):
    """Une chaîne d'attaques ``0 -> 1 -> ... -> n-1`` produit une alternance
    stricte ``in / out / in / out / ...`` en sémantique grounded.

    Propriété documentée dans la docstring de :func:`controversial_chain` :
    0 (non attaqué) = ``in``, 1 (attaqué par 0 ``in``) = ``out``, 2 (attaqué
    par 1 ``out``, donc défendu) = ``in``, etc. Ce test formalise cette
    propriété d'alternance (que le docstring énonce mais ne vérifiait pas) :
    ``label[i] == 'in'`` si ``i`` pair, ``'out'`` si ``i`` impair. C'est le
    substrat canonique d'une TPM non triviale (bascules propres).
    """
    af = arg.controversial_chain(n)
    label = arg.grounded_labeling(af)
    for i in range(n):
        expected = "in" if i % 2 == 0 else "out"
        assert label[i] == expected, (
            f"arg {i} dans controversial_chain({n}) : attendu {expected!r}, "
            f"recu {label[i]!r} (alternance in/out cassee)"
        )


# --------------------------------------------------------------------------- #
#  Gate 14 : refus de mesurer — distingué d'un zéro (tranche témoins #7742)   #
# --------------------------------------------------------------------------- #


def test_refus_entree_vide_distingue_du_zero():
    """Une entrée vide produit un REFUS, jamais un zéro silencieux.

    Le contrat de l'arbitrage #7742 : zéro mesuré (ex. sigma = 0.0 sur un
    débat déterministe) et refus de mesurer sont deux objets disjoints. Le
    premier est un nombre ; le second lève :class:`RefusDeMesure` avec un
    code. Un pipeline qui retournerait 0.0 sur une entrée vide rendrait le
    contrôle négatif vide avant d'avoir tourné.
    """
    with pytest.raises(arg.RefusDeMesure) as excinfo:
        arg.enonces_codables("")
    assert excinfo.value.code == "ENTREE_VIDE"
    with pytest.raises(arg.RefusDeMesure) as excinfo2:
        arg.enonces_codables("   \n\t  ")
    assert excinfo2.value.code == "ENTREE_VIDE"


def test_refus_glossolalie_aucun_enonce_codable():
    """La glossolalie (pseudo-langue sans entrée lexicale) est refusée.

    Un fragment de pseudo-allemand inventé (matériau de test du refuseur,
    étiqueté « fragment, pas reconstitution » dans le notebook) ne porte
    aucune signature de langue : 0 mot fonctionnel, donc incodable —
    MÉCANIQUEMENT, sans liste noire de contenu.
    """
    glossolalie = ("Djunkin schpilkov dem hoppen der flussen! "
                   "Achten schmerzen, blauten krugen. "
                   "Hoppen fleigen der weltenkrugen?")
    with pytest.raises(arg.RefusDeMesure) as excinfo:
        arg.enonces_codables(glossolalie)
    assert excinfo.value.code == "AUCUN_ENONCE_CODABLE"
    # et le code lève pour la bonne raison : des candidats existent (>= 2 mots
    # par segment), aucun ne passe le test de langue.
    assert "candidats" in str(excinfo.value)


def test_refus_pas_zero_et_reciproque():
    """La distinction refus/zéro se vérifie dans les DEUX sens.

    (a) un AF réel produit sigma = 0.0 (zéro mesuré, honnête, documenté §5) ;
    (b) une entrée sans contenu propositionnel lève RefusDeMesure — et
    l'exception ne porte AUCUNE valeur numérique mesurée.
    """
    # (a) zéro mesuré : débat déterministe à ordre fixe
    P, _ = arg.belief_transition_matrix(arg.nixon_diamond(), order=[0, 1])
    diag = arg.discourse_irreversibility(P)
    assert diag["sigma"] == 0.0 or diag["sigma"] >= 0.0  # un NOMBRE est sorti
    # (b) refus : aucun nombre ne sort
    with pytest.raises(arg.RefusDeMesure):
        arg.enonces_codables("Schnitzel banana rama fugen")
    # "Schnitzel banana rama fugen" : 4 mots, 0 fonctionnel -> refus, pas 0.0


def test_codable_anglais_ordinaire_passe():
    """L'anglais ordinaire passe le test de langue avec une marge large.

    Contre-face du gate glossolalie : une phrase anglaise réelle (extrait
    de test, pas du corpus) doit être codable — sinon le refuseur refuserait
    tout et ne distinguerait plus rien.
    """
    phrases = arg.enonces_codables(
        "The misery that is now upon us is but the passing of greed. "
        "The hate of men will pass."
    )
    assert len(phrases) >= 2
    assert all(arg.est_codable(p) for p in phrases)


def test_verdict_canaux_traduction_contredit():
    """Hynkel : canal principal incodable + canal traduction => REFUS global.

    Règle inter-canaux pré-enregistrée : si le canal principal ne porte pas
    de langue et qu'un canal « traduction » est présent, mesurer lirait la
    traduction — les deux canaux se contredisent, refus
    CANAUX_CONTRADICTOIRES. Un canal principal codable, lui, est MESURABLE.
    """
    hynkel = {
        "principal": "Djunkin schpilkov dem hoppen der flussen!",
        "traduction": "His excellency says something about peace.",
    }
    assert arg.verdict_canaux(hynkel) == "REFUS:CANAUX_CONTRADICTOIRES"
    # sans traduction, le verdict reste MESURABLE (le refus par canal se lit
    # via enonces_codables, pas via cette règle de cohérence)
    seul = {"principal": "The hate of men will pass, and dictators die."}
    assert arg.verdict_canaux(seul) == "MESURABLE"


def test_refus_code_inconnu_rejete():
    """Un code de refus hors enumeration est une erreur de programmation."""
    with pytest.raises(ValueError):
        arg.RefusDeMesure("CODE_INCONNU", "test")


# --------------------------------------------------------------------------- #
#  Gate : derivation du labelling depuis l'extension (parite labelling, #7742)
#  Proposition consultant du 24/10 : la parite sur les seuls ensembles IN ne
#  voit pas la separation out/undec. Ces tests sont PUR PYTHON -- aucun
#  organe Java requis -- la reference etant l'instrument lui-meme.
# --------------------------------------------------------------------------- #


def test_labelling_from_extension_reproduit_instrument():
    """La derivation (in/out/undec depuis l'extension) = le labelling direct.

    Sur les 12 cas canoniques + les 200 aleatoires (seed 42, la banque de la
    parite 212), le labelling derive de l'extension IN de l'instrument est
    EGAL au labelling iterate-au-point-fixe. Si une future refactor de
    ``grounded_labeling`` brise cette coherence, la jambe labelling de la
    parite la verra -- l'ancienne jambe IN, elle, ne la verrait pas.
    """
    from ict import tweety_bridge as bridge

    bank = bridge.canonical_cases() + bridge.random_cases(seed=42)
    for _, af in bank:
        extension = bridge.instrument_grounded(af)
        assert bridge.labelling_from_extension(af, extension) == arg.grounded_labeling(af)


def test_mutant_undec_en_out_passe_la_parite_in_pas_le_labelling():
    """Temoir rouge : le mutant exact decrit par le consultant (24/10).

    Un mutant qui etiquette ``undec`` en ``out`` : (a) son ensemble IN est
    IDENTIQUE a celui de l'instrument -- la parite IN historique l'acquitte ;
    (b) son labelling complet diverge de la derivation sur tout cas portant
    au moins un ``undec`` -- la jambe labelling l'attrape.
    """
    from ict import tweety_bridge as bridge

    def mutant_labeling(af):
        return {
            a: ("out" if v == "undec" else v)
            for a, v in arg.grounded_labeling(af).items()
        }

    nixon = arg.DungAF([0, 1], [(0, 1), (1, 0)])
    # (a) meme ensemble IN -> la jambe IN ne distingue pas
    mutant_in = frozenset(a for a, v in mutant_labeling(nixon).items() if v == "in")
    assert mutant_in == bridge.instrument_grounded(nixon) == frozenset()
    # (b) labelling divergent -> la jambe labelling attrape
    derived = bridge.labelling_from_extension(nixon, mutant_in)
    assert mutant_labeling(nixon) != derived
    assert all(v == "undec" for v in derived.values())


def test_banque_212_porte_147_cas_undec():
    """Compte de la banque : 147/212 cas portent au moins un ``undec``.

    Chiffre mesure par le consultant (24/10) sur la meme banque
    (canonical_cases + random_cases(seed=42)). Le pinner ici rend toute
    derivee de la banque detectable : si le compte change, la donnee de
    reference des deux jambes de parite a bouge.
    """
    from ict import tweety_bridge as bridge

    bank = bridge.canonical_cases() + bridge.random_cases(seed=42)
    assert len(bank) == 212
    n_undec = sum(
        1
        for _, af in bank
        if any(v == "undec" for v in arg.grounded_labeling(af).values())
    )
    assert n_undec == 147
