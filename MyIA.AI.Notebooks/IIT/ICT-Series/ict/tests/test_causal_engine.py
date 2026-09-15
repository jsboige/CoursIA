"""Tests du module :mod:`ict.causal_engine` (Epic #15475, grain #15479).

Couvre les six acceptances de l'issue #15479 sur des panneaux synthetiques
deterministes (CPU, numpy-only, aucune capture GPU) :

  1. (Gate contrat commun) les CINQ operations appliquees a un panneau
     synthetique produisent l'exact changement attendu, calcule a la main ;
     une operation hors enum echoue proprement.
  2. (Gate controles) la cible aleatoire est appariee en norme ET frequence,
     liee a la cible ; le sham passe par la meme voie de code (dose 0 =
     identite) ; les doses symetriques s'inversent en signe.
  3. (Gate canaux separes) un meme run remplit les trois canaux
     etat/readout/comportement en slots separes, jamais fusionnes.
  4. (Gate format Gate 24) :func:`build_gate24_family` represente exactement
     les trois bras de #5635 (cible / aleatoire apparie / intact), le bras
     intact etant l'identite PAR LA MEME VOIE de code.
  5. (Gate dommage general) un collapse global du panneau rend le verdict
     ``global_damage`` meme si l'effet cible est grand ; une intervention
     propre et concentree rend ``selective``.
  6. (Gate rejouabilite/contrat) determinisme seed (appariement
     byte-stable), enregistrement sidecar JSON serialisable, empreintes
     avant/apres distinctes, desalignement nomme le champ fautif.

Pattern herite de ``test_lens_agreement.py`` (bootstrap ``sys.path``
module-level, fixtures synthetiques placees a la main, tolerances commentees).
"""

from __future__ import annotations

import math
import sys
import unittest
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from ict.causal_engine import (  # noqa: E402
    ALIGNMENT_KEYS,
    EffectChannels,
    InterventionRecord,
    InterventionSpec,
    apply_intervention,
    assert_alignment,
    artifact_sha256,
    build_gate24_family,
    damage_metrics,
    dose_response_specs,
    holm_adjust,
    interchange_panels,
    random_target_matched,
    selectivity_verdict,
    sham_of,
    symmetric_doses,
)


def _panel(seed: int = 7, T: int = 6, d: int = 10) -> np.ndarray:
    """Panneau synthetique deterministe, valeurs placees (pas de structure cachee)."""
    rng = np.random.default_rng(seed)
    return rng.normal(size=(T, d)).astype(np.float64)


def _clamp_spec(dose: float = 2.0) -> InterventionSpec:
    return InterventionSpec(
        operation="clamp",
        instrument="sae",
        layer=3,
        positions=(1, 2),
        features=(4, 5),
        dose=dose,
        direction=(1.0, 0.0),
        run="synthetic-run-a",
        seed=11,
    )


class TestGate1ContratCommun(unittest.TestCase):
    """Acceptance 1 : cinq operations, contrat commun, changement exact attendu."""

    def test_ablate_met_exactement_la_cible_a_zero(self) -> None:
        x = _panel()
        spec = InterventionSpec(
            operation="ablate", instrument="synthetic", layer=0,
            positions=(0, 3), features=(2, 7), run="r", seed=1,
        )
        out = apply_intervention(x, spec)
        self.assertTrue(np.all(out[[0, 3]][:, [2, 7]] == 0.0))
        # hors cible : inchanged byte a byte
        mask = np.ones(x.shape, bool)
        mask[np.ix_([0, 3], [2, 7])] = False
        self.assertTrue(np.array_equal(out[mask], x[mask]))
        # l'entree n'est jamais mutee
        self.assertFalse(np.array_equal(out, x))

    def test_clamp_ecrit_dose_fois_direction(self) -> None:
        x = _panel()
        spec = InterventionSpec(
            operation="clamp", instrument="sae", layer=1,
            positions=(2,), features=(0, 1, 2), dose=3.0,
            direction=(0.0, 1.0, 0.0), run="r", seed=2,
        )
        out = apply_intervention(x, spec)
        self.assertTrue(np.all(out[2, [0, 1, 2]] == np.array([0.0, 3.0, 0.0])))

    def test_steer_ajoute_dose_fois_direction_unitaire(self) -> None:
        x = _panel()
        direction = (3.0, 4.0)  # norme 5 -> direction unitaire (0.6, 0.8)
        spec = InterventionSpec(
            operation="steer", instrument="flens", layer=2,
            positions=(0, 1), features=(8, 9), dose=1.0,
            direction=direction, run="r", seed=3,
        )
        out = apply_intervention(x, spec)
        self.assertTrue(np.allclose(out[[0, 1]][:, [8, 9]] - x[[0, 1]][:, [8, 9]],
                                    np.array([[0.6, 0.8], [0.6, 0.8]])))

    def test_patch_ecrit_le_donneur_empirique(self) -> None:
        x = _panel()
        donor = ((1.5, -2.5), (-3.5, 4.5))
        spec = InterventionSpec(
            operation="patch", instrument="jlens", layer=4,
            positions=(0, 5), features=(3, 6), donor=donor, run="r", seed=4,
        )
        out = apply_intervention(x, spec)
        self.assertTrue(np.array_equal(out[np.ix_([0, 5], [3, 6])],
                                       np.array(donor)))

    def test_interchange_est_bilateral_et_symetrique(self) -> None:
        a, b = _panel(seed=1), _panel(seed=2)
        spec = InterventionSpec(
            operation="interchange", instrument="synthetic", layer=0,
            positions=(1,), features=(4,), run="ra", paired_run="rb", seed=5,
        )
        a2, b2 = interchange_panels(a, b, spec)
        self.assertEqual(a2[1, 4], b[1, 4])
        self.assertEqual(b2[1, 4], a[1, 4])
        # hors cible intact des deux cotes
        self.assertEqual(a2[0, 0], a[0, 0])
        self.assertEqual(b2[0, 0], b[0, 0])

    def test_operation_hors_enum_echoue_proprement(self) -> None:
        with self.assertRaises(ValueError):
            InterventionSpec(
                operation="lesion", instrument="sae", layer=0,
                positions=(0,), features=(0,), run="r", seed=0,
            )

    def test_direction_de_mauvaise_dimension_echoue(self) -> None:
        with self.assertRaises(ValueError):
            InterventionSpec(
                operation="clamp", instrument="sae", layer=0,
                positions=(0,), features=(0, 1), dose=1.0,
                direction=(1.0,), run="r", seed=0,
            )


class TestGate2Controles(unittest.TestCase):
    """Acceptance 2 : controles random/sham/dose generes et relies a la cible."""

    def test_random_target_apparie_norme_et_frequence(self) -> None:
        x = _panel(seed=9, T=8, d=24)
        norms = np.abs(np.random.default_rng(3).normal(1.0, 0.05, size=24))
        freqs = np.full(24, 0.5)
        spec = InterventionSpec(
            operation="ablate", instrument="sae", layer=1,
            positions=(0, 1), features=(2, 3), run="r", seed=42,
        )
        control = random_target_matched(x, spec, feature_norms=norms,
                                        feature_freqs=freqs, rel_tol=0.5)
        # meme NOMBRE de features, toutes distinctes de la cible
        self.assertEqual(len(control.features), len(spec.features))
        self.assertNotEqual(set(control.features), set(spec.features))
        # chaque candidate respecte la bande de norme (appariement, pas strawman)
        for c, t in zip(control.features, spec.features):
            self.assertLessEqual(abs(norms[c] - norms[t]) / norms[t], 0.5)

    def test_random_target_sans_candidate_dans_la_bande_echoue_avec_diagnostic(self) -> None:
        x = _panel(seed=9, T=4, d=4)
        norms = np.array([1.0, 100.0, 100.0, 100.0])  # cible isolee : bande vide
        spec = InterventionSpec(
            operation="ablate", instrument="sae", layer=0,
            positions=(0,), features=(0,), run="r", seed=0,
        )
        with self.assertRaises(ValueError) as ctx:
            random_target_matched(x, spec, feature_norms=norms,
                                  feature_freqs=np.full(4, 0.5), rel_tol=0.1)
        self.assertIn("appari", str(ctx.exception))  # diagnostic nomme, pas un echo muet

    def test_sham_reecrit_les_valeurs_propres_par_la_meme_voie(self) -> None:
        spec = _clamp_spec(dose=2.0)
        x = _panel()
        sham = sham_of(spec, x)
        out = apply_intervention(x, sham)
        # le sham de clamp REECRIT la tranche originale via la voie d'ecriture
        # absolue partagee clamp/patch — meme code path, contenu identique
        self.assertTrue(np.array_equal(out, x))
        self.assertEqual(sham.control_ref, "sham-of-clamp(write-back)")
        # sans panneau, le sham de clamp echoue explicitement (pas de degradation)
        with self.assertRaises(ValueError):
            sham_of(spec)

    def test_sham_steer_dose_zero_et_sham_interchange_soit_meme(self) -> None:
        steer = InterventionSpec(
            operation="steer", instrument="flens", layer=0,
            positions=(0,), features=(1, 2), dose=1.0, direction=(1.0, 1.0),
            run="r", seed=6,
        )
        sham = sham_of(steer)
        out = apply_intervention(_panel(), sham)
        self.assertTrue(np.array_equal(out, _panel()))  # dose 0 additive
        inter = InterventionSpec(
            operation="interchange", instrument="synthetic", layer=0,
            positions=(1,), features=(2,), run="ra", paired_run="rb", seed=6,
        )
        x = _panel()
        a2, b2 = interchange_panels(x, x, sham_of(inter))
        self.assertTrue(np.array_equal(a2, x) and np.array_equal(b2, x))

    def test_doses_symetriques_et_courbe_dose_reponse(self) -> None:
        doses = symmetric_doses(4.0, n_pairs=3)
        self.assertEqual(doses, (1.0, -1.0, 2.0, -2.0, 4.0, -4.0))
        specs = dose_response_specs(_clamp_spec(), doses)
        self.assertEqual([s.dose for s in specs], list(doses))
        # toutes les autres coordonnees de spec invariantes
        for s in specs:
            self.assertEqual(s.features, (4, 5))
            self.assertEqual(s.positions, (1, 2))

    def test_determinisme_de_l_appariement_par_seed(self) -> None:
        x = _panel(seed=9, T=8, d=30)
        norms = np.abs(np.random.default_rng(5).normal(1.0, 0.3, size=30))
        freqs = np.full(30, 0.5)
        spec = InterventionSpec(
            operation="ablate", instrument="sae", layer=0,
            positions=(0,), features=(7, 8, 9), run="r", seed=123,
        )
        c1 = random_target_matched(x, spec, feature_norms=norms, feature_freqs=freqs)
        c2 = random_target_matched(x, spec, feature_norms=norms, feature_freqs=freqs)
        self.assertEqual(c1.features, c2.features)  # byte-stable, RNG spec-seed


class TestGate3CanauxSepares(unittest.TestCase):
    """Acceptance 3 : etat/readout/comportement en slots separes, jamais ecrases."""

    def test_un_run_remplit_les_trois_canaux(self) -> None:
        x = _panel()
        spec = _clamp_spec()
        out = apply_intervention(x, spec)
        channels = EffectChannels()
        channels.record(
            "state",
            {"norm": lambda p: float(np.linalg.norm(p))},
            x, out,
        )
        channels.record(
            "readout",
            {"top_logit": lambda p: float(p[:, 0].max())},
            x, out,
        )
        channels.record(
            "behavior",
            {"copy_acc": lambda p: float((p > 0).mean())},
            x, out,
        )
        for slot in ("state", "readout", "behavior"):
            data = getattr(channels, slot)
            self.assertIn("norm_before", data) if slot == "state" else None
            self.assertTrue(any(k.endswith("_delta") for k in data))
        # les trois canaux sont distincts et peuples independamment
        self.assertIn("top_logit_delta", channels.readout)
        self.assertIn("copy_acc_delta", channels.behavior)
        self.assertNotIn("top_logit_delta", channels.state)  # pas d'ecrasement croise

    def test_canal_inconnu_echoue(self) -> None:
        channels = EffectChannels()
        with self.assertRaises(ValueError):
            channels.record("meta", {}, _panel(), _panel())


class TestGate4FormatGate24(unittest.TestCase):
    """Acceptance 4 : le format represente exactement le Gate 24 de #5635."""

    def test_famille_trois_bras_exacte(self) -> None:
        spec = _clamp_spec()
        x = _panel()
        norms = np.abs(np.random.default_rng(1).normal(1.0, 0.01, size=x.shape[1]))
        control = random_target_matched(
            x, spec, feature_norms=norms,
            feature_freqs=np.full(x.shape[1], 0.5), rel_tol=1.5,
        )
        family = build_gate24_family(spec, control)
        self.assertEqual(set(family), {"target", "random", "intact"})
        # bras cible et aleatoire : meme nombre de features (exigence Gate 24)
        self.assertEqual(len(family["random"].features), len(family["target"].features))
        self.assertNotEqual(family["random"].features, family["target"].features)
        # bras intact : cible vide, identite PAR LA MEME VOIE
        intact_out = apply_intervention(x, family["intact"])
        self.assertTrue(np.array_equal(intact_out, x))


class TestGate5DommageGeneral(unittest.TestCase):
    """Acceptance 5 : un collapse global n'est pas de la causalite selective."""

    def test_intervention_propre_et_concentree_est_selective(self) -> None:
        x = _panel()
        spec = _clamp_spec()
        out = apply_intervention(x, spec)
        damage = damage_metrics(x, out, spec)
        self.assertEqual(selectivity_verdict(damage), "selective")
        self.assertGreater(damage["selectivity_ratio"], 5.0)
        self.assertLess(damage["off_target_rel"], 1e-12)  # hors cible intact

    def test_collapse_global_rend_global_damage_malgre_un_effet_cible_grand(self) -> None:
        x = _panel()
        spec = _clamp_spec()
        out = apply_intervention(x, spec)
        out = out + 5.0  # dommage global : TOUT le panneau deplace
        damage = damage_metrics(x, out, spec)
        verdict = selectivity_verdict(damage)
        self.assertEqual(verdict, "global_damage")  # l'effet cible existe mais le
        # dommage hors cible disqualifie la lecture selective

    def test_ratio_sature_a_inf_sous_le_plancher_de_mesure(self) -> None:
        """Hors cible au plancher = rapport NON BORNE, pas un grand nombre.

        ``on_rel / eps`` publiait une magnitude qui dependait de la constante
        interne (462774272000.00 mesure sur le banc copy_offset pour une
        intervention parfaitement propre) : lisible comme une mesure alors
        qu'elle n'en est pas une. Et une intervention sans AUCUN effet ne doit
        pas ressortir selective -- son rapport vaut 0.0.
        """
        x = _panel()
        spec = _clamp_spec()
        out = apply_intervention(x, spec)
        damage = damage_metrics(x, out, spec)
        self.assertLessEqual(damage["off_target_rel"], 1e-12)  # sous le plancher
        self.assertTrue(math.isinf(damage["selectivity_ratio"]))
        self.assertGreater(damage["selectivity_ratio"], 0.0)  # inf passe le seuil
        self.assertEqual(selectivity_verdict(damage), "selective")

        # rien ne bouge : aucun rapport mesurable, et surtout pas "selective"
        neutre = damage_metrics(x, x, spec)
        self.assertEqual(neutre["selectivity_ratio"], 0.0)
        self.assertEqual(selectivity_verdict(neutre), "not_selective")


class TestGate6RejouabiliteEtContrat(unittest.TestCase):
    """Acceptance 6 : sidecar conforme, empreintes, alignement nomme, Holm."""

    def test_enregistrement_sidecar_json_serialisable_et_alignable(self) -> None:
        x = _panel()
        spec = _clamp_spec()
        out = apply_intervention(x, spec)
        rec = InterventionRecord(
            spec=spec,
            alignment=spec.alignment(model="toy", prompt_set="synthetic"),
            sha_before=artifact_sha256(x),
            sha_after=artifact_sha256(out),
            damage=damage_metrics(x, out, spec),
            verdict="selective",
        )
        payload = rec.to_json()
        self.assertIn('"clamp"', payload)
        self.assertNotEqual(rec.sha_before, rec.sha_after)
        for key in ("instrument", "layer", "run", "seed"):  # cles d'alignement embarquees
            self.assertIn(key, payload)
        # deux enregistrements alignes se comparent sans erreur
        rec2 = InterventionRecord(
            spec=spec, alignment=dict(rec.alignment),
            sha_before=rec.sha_before, sha_after=rec.sha_after,
        )
        assert_alignment(rec, rec2)  # pas d'exception

    def test_desalignement_nomme_le_champ_fautif(self) -> None:
        spec = _clamp_spec()
        rec_a = InterventionRecord(
            spec=spec, alignment=spec.alignment(model="toy-a"),
            sha_before="x", sha_after="y",
        )
        rec_b = InterventionRecord(
            spec=spec, alignment=spec.alignment(model="toy-b"),
            sha_before="x", sha_after="y",
        )
        with self.assertRaises(ValueError) as ctx:
            assert_alignment(rec_a, rec_b)
        self.assertIn("model", str(ctx.exception))  # champ fautif + deux valeurs

    def test_holm_bonferroni_famille_de_controles(self) -> None:
        # famille {cible vs aleatoire (p petit), cible vs sham (p grand)}
        adjusted = holm_adjust([0.01, 0.40])
        self.assertLessEqual(adjusted[0], 2 * 0.01)  # le plus petit est penalise par m
        self.assertGreaterEqual(adjusted[1], 0.40)
        self.assertLessEqual(max(adjusted), 1.0)

    def test_alignment_keys_couvre_le_litteral_v1(self) -> None:
        for key in ("contract_version", "instrument", "layer", "model",
                    "run", "seed", "prompt_set"):
            self.assertIn(key, ALIGNMENT_KEYS)


if __name__ == "__main__":
    unittest.main()
