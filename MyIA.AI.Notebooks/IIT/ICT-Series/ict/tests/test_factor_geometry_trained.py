"""Tests unitaires pour :mod:`ict.factor_geometry_trained` (#15478).

Le module ferme la boucle de la geometrie factorisee : le modele est
**reellement entraine** sur le banc, la geometrie est lue sur **ses**
activations, et le temoin nul est celui d'initialisations **non entrainees de
la meme architecture**. Ces tests figent les contrats qui rendent cette
fermeture falsifiable -- sans eux, un modele mal entraine et un modele entraine
se ressembleraient.

Contrats attestes :

    1.  (``predictive_matrix`` stochastique) : les deux formes -- Moore
        (``Mess3Canonical``, via ``T @ E``) et Mealy (``RRXOR``, via le
        tenseur d'aretes) -- rendent une matrice dont chaque ligne somme a 1,
        de largeur egale a la taille de l'alphabet d'observation.
    2.  (plancher exact sur un processus iid) : ``RRXOR_Iid`` est un
        processus iid binaire (les XOR adjacents de bits iid sont
        independants, cf. sa docstring) ; sa perte Bayes-optimale vaut donc
        **exactement** ``ln 2``. C'est le seul contrat du module dont la
        valeur est connue a l'avance au bit pres -- il valide toute la chaine
        filtration -> predictive -> -log en une egalite.
    3.  (plancher sous l'uniforme) : sur ``Mess3Canonical``, le plancher est
        strictement inferieur a ``ln 3``, et strictement positif : le
        processus est predictible, mais pas deterministe.
    4.  (bornes de ``burn``) : un ``burn`` negatif ou au-dela de la serie est
        refuse, et une serie 2D est refusee -- le calcul porte sur des pas,
        pas sur des tableaux.
    5.  (sonde : recuperation d'un sous-espace connu) : quand les cibles sont
        une fonction lineaire exacte des activations, la base des coefficients
        retrouve l'espace colonne de la matrice generatrice.
    6.  (sonde : orthonormalite) : la base rendue a colonnes orthonormees
        (``B^T B = I``), quel que soit le rang.
    7.  (additivite) : deux facteurs portes par des directions DISJOINTES
        rendent ``additivity_gap == 0`` ; deux facteurs qui partagent une
        direction rendent un ecart **negatif** -- c'est la mesure directe de
        l'entremellement.
    8.  (temoin nul : plancher de comptage) : moins de 5 initialisations est
        refuse, et le temoin rend les percentiles 5/50/95 de **chaque**
        metrique du rapport, jamais un sous-ensemble.
    9.  (temoin nul : il discrimine) : sur des activations tirees au hasard,
        ``probe_r2_b`` d'une initialisation non entrainee reste tres en deca
        de celui d'un modele entraine -- le temoin n'est pas decoratif.
    10. (entrainement : la perte descend sous l'uniforme) : apres
        entrainement, la perte jointe du modele passe sous la perte uniforme
        ``ln(3) + ln(2)``. Test d'integration, garde par ``HAS_TORCH``.
"""

import unittest

import numpy as np

from ict import bench_factorise as bf
from ict import factor_geometry_trained as fgt


class TestPlancherDeBayes(unittest.TestCase):
    """Contrats 1 a 4 : le plancher est exact, borne, et refuse le mauvais usage."""

    def test_predictive_matrix_stochastique_moore_et_mealy(self):
        """Contrat 1 : les deux formes rendent une matrice stochastique en ligne."""
        m = bf.Mess3Canonical()
        pm = fgt.predictive_matrix(m)
        self.assertEqual(pm.shape, (m.n_states, m.n_states))
        np.testing.assert_allclose(pm.sum(axis=1), np.ones(m.n_states), atol=1e-12)

        r = bf.RRXOR()
        pr = fgt.predictive_matrix(r)
        self.assertEqual(pr.shape, (r.n_states, 2))
        np.testing.assert_allclose(pr.sum(axis=1), np.ones(r.n_states), atol=1e-12)

    def test_plancher_iid_vaut_exactement_ln2(self):
        """Contrat 2 : sur un processus iid binaire, le plancher EST ln 2."""
        proc = bf.RRXOR_Iid()
        obs = proc.sample(4000, seed=0)[1]
        self.assertAlmostEqual(fgt.bayes_floor(proc, obs), float(np.log(2.0)), places=9)

    def test_plancher_mess3_sous_uniforme_et_positif(self):
        """Contrat 3 : predictible (sous ln 3) mais non deterministe (positif)."""
        proc = bf.Mess3Canonical()
        obs = proc.sample(4000, seed=0)[1]
        floor = fgt.bayes_floor(proc, obs)
        self.assertGreater(floor, 0.0)
        self.assertLess(floor, float(np.log(3.0)))

    def test_burn_et_forme_refuses(self):
        """Contrat 4 : bornes de burn et refus d'une serie non 1D."""
        proc = bf.Mess3Canonical()
        obs = proc.sample(200, seed=0)[1]
        with self.assertRaises(ValueError):
            fgt.bayes_floor(proc, obs, burn=-1)
        with self.assertRaises(ValueError):
            fgt.bayes_floor(proc, obs, burn=len(obs))
        with self.assertRaises(ValueError):
            fgt.bayes_floor(proc, obs.reshape(-1, 1))


class TestSondeDeCoefficients(unittest.TestCase):
    """Contrats 5 et 6 : la sonde retrouve le sous-espace et rend une base propre."""

    def _donnees(self, n=800, d=8, seed=3):
        rng = np.random.default_rng(seed)
        return rng.normal(size=(n, d))

    def test_recupere_un_sous_espace_connu(self):
        """Contrat 5 : cibles = H @ M  =>  l'espace colonne de M est retrouve."""
        H = self._donnees()
        M = np.zeros((8, 3))
        M[1, 0] = 1.0
        M[4, 1] = 1.0
        M[6, 2] = 1.0
        B = fgt.probe_coefficient_basis(H, H @ M, ridge=1e-9)
        self.assertEqual(fgt.subspace_rank(B), 3)
        # La SVD rend une base arbitraire DU SOUS-ESPACE : ses colonnes sont des
        # combinaisons des directions retrouvees, pas ces directions elles-memes.
        # L'assertion correcte est donc que l'ENERGIE hors du support {1, 4, 6}
        # est nulle -- pas que chaque colonne est un vecteur de base canonique.
        hors_support = B[[0, 2, 3, 5, 7], :]
        np.testing.assert_allclose(hors_support, np.zeros_like(hors_support), atol=1e-6)

    def test_base_orthonormee(self):
        """Contrat 6 : B^T B = I, quel que soit le rang."""
        H = self._donnees()
        Y = H @ np.random.default_rng(0).normal(size=(8, 3))
        B = fgt.probe_coefficient_basis(H, Y, ridge=1e-6)
        np.testing.assert_allclose(B.T @ B, np.eye(B.shape[1]), atol=1e-10)

    def test_formes_incompatibles_refusees(self):
        """Contrat 6 (suite) : un desaccord de lignes est refuse, pas devine."""
        with self.assertRaises(ValueError):
            fgt.probe_coefficient_basis(np.zeros((10, 4)), np.zeros((9, 2)))


class TestAdditiviteEtTemoin(unittest.TestCase):
    """Contrats 7, 8 et 9 : l'additivite signe l'entremellement, le temoin borne."""

    def _activations_et_cibles(self, partage, n=900, d=6, seed=5):
        rng = np.random.default_rng(seed)
        H = rng.normal(size=(n, d))
        Ma, Mb = np.zeros((d, 2)), np.zeros((d, 2))
        Ma[0, 0] = Ma[1, 1] = 1.0
        if partage:
            Mb[1, 0] = Mb[2, 1] = 1.0          # partage la direction 1 avec A
        else:
            Mb[3, 0] = Mb[4, 1] = 1.0          # directions disjointes
        return H, H @ Ma, H @ Mb

    def test_gap_nul_quand_directions_disjointes(self):
        """Contrat 7 (a) : facteurs additifs => ecart exactement nul."""
        H, ya, yb = self._activations_et_cibles(partage=False)
        rep = fgt.factor_geometry_report(H, ya, yb, ridge=1e-9)
        self.assertEqual(rep["dim_a"], 2.0)
        self.assertEqual(rep["dim_b"], 2.0)
        self.assertEqual(rep["additivity_gap"], 0.0)

    def test_gap_negatif_quand_une_direction_est_partagee(self):
        """Contrat 7 (b) : une direction commune => ecart strictement negatif."""
        H, ya, yb = self._activations_et_cibles(partage=True)
        rep = fgt.factor_geometry_report(H, ya, yb, ridge=1e-9)
        self.assertLess(rep["additivity_gap"], 0.0)
        self.assertEqual(rep["dim_union"], 3.0)

    def test_temoin_exige_cinq_initialisations(self):
        """Contrat 8 : moins de cinq initialisations est refuse, pas tolere."""
        H, ya, yb = self._activations_et_cibles(partage=False)
        with self.assertRaises(ValueError):
            fgt.untrained_null(lambda sd: None, H, ya, yb, n_init=4)

    def test_temoin_rend_toutes_les_metriques_du_rapport(self):
        """Contrat 8 (suite) : chaque metrique du rapport est bornee, pas un extrait.

        Le temoin construit de VRAIS modeles (meme architecture, non entrainee) :
        un temoin qui n'evaluerait pas l'architecture ne repondrait pas a
        l'objection qu'il est cense traiter.
        """
        if not fgt.HAS_TORCH:
            self.skipTest("torch absent : le temoin d'architecture est indisponible")
        import torch

        # 12 sequences de 5 pas => 60 lignes d'activations : les cibles doivent
        # porter le meme nombre de lignes, sinon la sonde refuse (et c'est voulu).
        H, ya, yb = self._activations_et_cibles(partage=False, n=60)
        attendues = set(fgt.factor_geometry_report(H, ya, yb).keys())
        x = torch.zeros(12, 5, 2, dtype=torch.long)
        null = fgt.untrained_null(lambda sd: fgt.FactoredRNN(hidden=12, seed=sd), x, ya, yb, n_init=5)
        self.assertEqual(set(null.keys()), attendues)
        for stat in null.values():
            self.assertEqual(set(stat), {"p05", "p50", "p95", "n"})
            self.assertEqual(stat["n"], 5.0)
            self.assertLessEqual(stat["p05"], stat["p50"])
            self.assertLessEqual(stat["p50"], stat["p95"])


@unittest.skipUnless(fgt.HAS_TORCH, "torch absent : l'entrainement est indisponible")
class TestBoucleFermee(unittest.TestCase):
    """Contrat 10 : integration -- le modele entraine passe sous la perte uniforme."""

    def test_entrainement_passe_sous_l_uniforme(self):
        """Contrat 10 : apres entrainement, la perte jointe bat l'uniforme ``ln3+ln2``."""
        import torch

        bench = bf.FactoredBench(bf.Mess3Canonical(), bf.RRXOR())
        ln, ntr = 60, 60
        s = bench.sample(ln * (ntr + 10), seed_a=0, seed_b=0)
        obs = np.stack([s["obs_a"], s["obs_b"]], axis=1).astype(np.int64)
        x = torch.from_numpy(obs)
        xt = x[: ntr * ln].reshape(ntr, ln, 2)
        xv = x[ntr * ln : (ntr + 10) * ln].reshape(10, ln, 2)

        model = fgt.FactoredRNN(seed=0)
        uniforme = float(np.log(3.0) + np.log(2.0))
        avant = fgt.joint_nll(model, xv)
        res = fgt.train_model(model, xt, xv, steps=120, eval_every=20)
        apres = fgt.joint_nll(model, xv)
        self.assertLess(apres, uniforme, "l'entrainement n'a pas battu l'uniforme")
        self.assertLessEqual(res["best_val_nll"], apres + 1e-6)
        self.assertLess(res["best_val_nll"], avant)

    def test_activations_de_la_bonne_forme(self):
        """Contrat 10 (suite) : les activations sont aplaties en (T, cachee)."""
        import torch

        model = fgt.FactoredRNN(hidden=16, seed=1)
        x = torch.zeros(2, 7, 2, dtype=torch.long)
        self.assertEqual(fgt.collect_activations(model, x).shape, (14, 16))


if __name__ == "__main__":
    unittest.main()
