"""Tests du module :mod:`ict.lens_agreement` (capstone strate 5, Epic #4588).

Le module implemente la jambe **lens-agreement** de la triade
beauty/ignition/lens-agreement. Les deux fonctions publiques sont
:func:`lens_ignition_centers` et :func:`colocalize_lenses`. Les tests
ci-dessous couvrent 5 proprietes falsifiables issues du module :

  1. (Gate format) :func:`lens_ignition_centers` retourne le tuple
     ``(centers: List[int], T: int)`` attendu par
     :func:`ict.workspace.event_colocalization`.

  2. (Gate determinisme) :func:`colocalize_lenses` avec un RNG fixe
     donne un resultat byte-stable (meme ``z_mean``, meme verdict).

  3. (Gate co-localisation exacte) deux series d'ignitions **identiques**
     donnent un ``z >> 0`` (la distance au plus-proche-voisin est nulle
     par construction, le null ne peut pas faire mieux).

  4. (Gate T incompatible) deux prompts ou ``T_a != T_b`` sont ranges
     dans ``skipped`` et exclus du verdict.

  5. (Gate verdict synthese) si tous les prompts sont ``colocalized``,
     le verdict agrege est ``colocalized`` ; symetriquement pour
     ``dissociated`` ; sinon ``chance``.

Pattern herite de ``test_reversibility_budget.py`` et ``test_time_arrow.py``
(bootstrap ``sys.path`` module-level, pas de fixtures, tolerances
commentees). Les fixtures ``traces_a`` / ``traces_b`` sont synthetiques
(shape controlee, densites placees a la main) -- on patche
:func:`ict.lens_agreement.acts_topk_panels` et
:func:`ict.lens_agreement.differential_features` pour eviter la
dependance aux veritables traces SAE / J-Lens (qui demandent le
notebook ICT-SAE-JLens-TeteATete et les fichiers .npz de la couche 16).
"""

from __future__ import annotations

import numpy as np
import pytest

# sys.path.insert est dans conftest.py (parent du dossier tests/).
from ict import lens_agreement as la  # noqa: E402
# Les dependances sont importees paresseusement a l'interieur de
# lens_agreement.py (from .sae_traces import acts_topk_panels, etc.).
# Pour monkeypatcher, on vise la **source** des imports : les modules
# `ict.sae_traces` et `ict.workspace`. Un `from X import Y` fait un
# nouveau lookup a chaque appel, donc patcher la source prend effet.
from ict import sae_traces as _sae_traces  # noqa: E402
from ict import workspace as _workspace  # noqa: E402


# --------------------------------------------------------------------------- #
# Helpers de fixtures synthetiques                                            #
# --------------------------------------------------------------------------- #


def _make_dense(seed: int, T: int = 200, K: int = 32) -> np.ndarray:
    """Genere un panneau [T, K] avec des activations **localisees**.

    On tire ``K`` features dont chacune s'active sur ~10 % de la
    sequence, autour de positions aleatoires distinctes. C'est le
    profil qu'on attend d'un token specialise SAE : activite ponctuelle,
    pas diffuse.
    """
    rng = np.random.default_rng(seed)
    dense = np.zeros((T, K), dtype=np.float32)
    for k in range(K):
        center = int(rng.integers(5, T - 5))
        width = int(rng.integers(3, 8))
        t0, t1 = max(0, center - width), min(T, center + width)
        dense[t0:t1, k] = rng.uniform(0.5, 1.0, size=t1 - t0)
    return dense


def _patch_panels(monkeypatch, dense_a: np.ndarray, dense_b: np.ndarray, prompts=("p0",)):
    """Patche :func:`acts_topk_panels` et :func:`differential_features`.

    On court-circuite la lecture des vraies traces en branchant un
    dict ``traces`` minimal qui satisfait les lookups ``traces["prompts"]``.
    Les features differentielles sont tirees arbitrairement (le module ne
    les utilise que pour la cle du panel dense).
    """
    keys = [(s, 0) for s in prompts]

    def fake_acts_topk_panels(traces, feature_ids):  # noqa: ARG001
        # ``dense_a`` pour tous les prompts de la lentille A.
        return {key: dense_a for key in keys}

    # ``differential_features`` est appele dans ``colocalize_lenses``
    # uniquement. On peut le laisser retourner n'importe quoi (feature
    # IDs arbitraires) puisque ``fake_acts_topk_panels`` ignore.
    def fake_differential_features(traces, k=64):  # noqa: ARG001
        return np.arange(K_FIXTURE, dtype=np.int64)

    # Patch sur la SOURCE (`ict.sae_traces`), pas sur le module consommateur.
    # ``lens_agreement.py`` fait ``from .sae_traces import acts_topk_panels``
    # a l'interieur de la fonction, donc le lookup est rafraichi a chaque
    # appel et notre patch prend effet.
    monkeypatch.setattr(_sae_traces, "acts_topk_panels", fake_acts_topk_panels)
    monkeypatch.setattr(_sae_traces, "differential_features", fake_differential_features)


K_FIXTURE = 32  # valeur partagee par ``fake_differential_features``.


def _make_traces_stub():
    """Stub minimal pour les appels ``traces_a`` / ``traces_b``.

    On n'utilise que les cles, pas la structure profonde (puisque
    :func:`acts_topk_panels` et :func:`differential_features` sont
    patches).
    """
    return {"prompts": {}}


# --------------------------------------------------------------------------- #
# Gate 1 -- format de retour de lens_ignition_centers                         #
# --------------------------------------------------------------------------- #


def test_lens_ignition_centers_returns_centers_and_T(monkeypatch):
    """``lens_ignition_centers`` retourne ``Dict[key, (centers, T)]``.

    Les centres sont des ``int`` dans ``[0, T)`` ; ``T`` est la longueur
    de la serie de concentration (= taille du panneau).
    """
    dense = _make_dense(seed=11, T=200, K=K_FIXTURE)
    _patch_panels(monkeypatch, dense, dense, prompts=("p0", "p1"))
    feat_ids = np.arange(K_FIXTURE, dtype=np.int64)
    traces = _make_traces_stub()

    out = la.lens_ignition_centers(traces, feat_ids, q=0.9, persistence=3)

    assert set(out.keys()) == {("p0", 0), ("p1", 0)}
    for key, (centers, T) in out.items():
        assert T == 200
        assert isinstance(centers, list)
        for c in centers:
            assert isinstance(c, int)
            assert 0 <= c < T


def test_lens_ignition_centers_at_least_one_ignition(monkeypatch):
    """Sur un panneau dense avec 32 features localisees et ``q=0.9``,
    on attend au moins 1 ignition par prompt (seuil de quantile sur
    Gini = 0.9 implique que le **pic** de la serie passe).
    """
    dense = _make_dense(seed=12, T=300, K=K_FIXTURE)
    _patch_panels(monkeypatch, dense, dense, prompts=("p0",))
    feat_ids = np.arange(K_FIXTURE, dtype=np.int64)
    traces = _make_traces_stub()

    out = la.lens_ignition_centers(traces, feat_ids, q=0.9, persistence=3)
    centers, _T = out[("p0", 0)]
    assert len(centers) >= 1, f"attendu au moins 1 ignition, recu {centers}"


# --------------------------------------------------------------------------- #
# Gate 2 -- determinisme byte-stable de colocalize_lenses                     #
# --------------------------------------------------------------------------- #


def test_colocalize_lenses_deterministic_with_fixed_rng(monkeypatch):
    """Deux appels avec le meme rng produisent le meme ``z_mean``.

    Le module utilise un ``default_rng(0)`` si pas de rng, OU le rng
    transmis. On verifie que la transmission preserve le determinisme.
    """
    dense_a = _make_dense(seed=21, T=400, K=K_FIXTURE)
    dense_b = _make_dense(seed=22, T=400, K=K_FIXTURE)
    _patch_panels(monkeypatch, dense_a, dense_b, prompts=("p0", "p1", "p2"))
    traces = _make_traces_stub()
    rng_a = np.random.default_rng(42)
    rng_b = np.random.default_rng(42)

    r1 = la.colocalize_lenses(traces, traces, k=K_FIXTURE, n_null=100, rng=rng_a)
    r2 = la.colocalize_lenses(traces, traces, k=K_FIXTURE, n_null=100, rng=rng_b)

    assert r1["z_mean"] == pytest.approx(r2["z_mean"], abs=1e-9)
    assert r1["verdict"] == r2["verdict"]


# --------------------------------------------------------------------------- #
# Gate 3 -- co-localisation exacte : meme lentille -> verdict "colocalized"   #
# --------------------------------------------------------------------------- #


def test_colocalize_lenses_identical_lens_is_colocalized(monkeypatch):
    """Si les deux lentilles voient EXACTEMENT le meme panneau, leurs
    series d'ignitions sont identiques, donc la distance au plus-proche
    voisin est nulle, donc ``z >> 0``.

    Verdict agrege attendu : ``colocalized``.
    """
    dense = _make_dense(seed=31, T=400, K=K_FIXTURE)
    _patch_panels(monkeypatch, dense, dense, prompts=("p0", "p1", "p2", "p3"))
    traces = _make_traces_stub()
    rng = np.random.default_rng(7)

    r = la.colocalize_lenses(traces, traces, k=K_FIXTURE, n_null=200, rng=rng)

    assert r["n_prompts"] == 4
    assert r["n_skipped"] == 0
    # Z strictement positif (distance nulle ou quasi-nulle).
    assert r["z_mean"] > 5.0, f"attendu z >> 0 pour lentilles identiques, recu {r['z_mean']}"
    assert r["verdict"] == "colocalized"


# --------------------------------------------------------------------------- #
# Gate 4 -- T incompatible -> range dans skipped                             #
# --------------------------------------------------------------------------- #


def test_colocalize_lenses_skips_prompts_with_incompatible_T(monkeypatch):
    """Si les deux lentilles ont des panneaux de longueur differente
    pour un meme prompt, ce prompt va dans ``skipped``.

    On realise cela en donnant a ``acts_topk_panels`` des panneaux
    ``dense_a`` (T=400 pour les 2 prompts) et ``dense_b`` (T=250 pour
    ``p_short``, T=400 pour ``p_long``).
    """
    dense_a_short = _make_dense(seed=41, T=400, K=K_FIXTURE)
    dense_a_long = _make_dense(seed=42, T=400, K=K_FIXTURE)
    dense_b_short = _make_dense(seed=43, T=250, K=K_FIXTURE)
    dense_b_long = _make_dense(seed=44, T=400, K=K_FIXTURE)

    def fake_acts_topk_panels_a(traces, feature_ids):  # noqa: ARG001
        # Cote A : T=400 pour les deux prompts.
        return {("p_short", 0): dense_a_short, ("p_long", 0): dense_a_long}

    def fake_acts_topk_panels_b(traces, feature_ids):  # noqa: ARG001
        # Cote B : T=250 pour p_short, T=400 pour p_long.
        return {("p_short", 0): dense_b_short, ("p_long", 0): dense_b_long}

    def fake_differential_features(traces, k=64):  # noqa: ARG001
        return np.arange(K_FIXTURE, dtype=np.int64)

    # Patch distinct cote A / cote B via ``wraps``.
    monkeypatch.setattr(_sae_traces, "acts_topk_panels", fake_acts_topk_panels_a)
    monkeypatch.setattr(_sae_traces, "differential_features", fake_differential_features)

    # Le patch ci-dessus est global, donc lens_agreement verra toujours
    # fake_acts_topk_panels_a pour les DEUX lentilles (a et b). Pour
    # distinguer les cotes, on wrappe la fonction patchee via un setattr
    # en deux temps : d'abord on capture la version "a" puis on patche
    # pour qu'elle distingue cote A vs cote B.
    # NB : ``colocalize_lenses`` appelle d'abord ``lens_ignition_centers``
    # pour traces_a, puis pour traces_b. Comme traces_a == traces_b ==
    # stub vide, on ne peut pas distinguer via l'argument. Hack : on wrappe
    # ``lens_ignition_centers`` directement.
    def lens_ignition_centers_factory(side_panels):
        """Retourne une closure qui imite lens_ignition_centers en utilisant
        les panneaux specifiques au cote ``a`` ou ``b``."""

        def fake_lens_ignition_centers(traces, feature_ids, *, q=0.9, persistence=3, metric="gini"):  # noqa: ARG001
            # Reproduit la signature de retour : Dict[key, (centers, T)].
            # On tire un seul centre par prompt au milieu du panneau.
            out = {}
            for (prompt, _), panel in side_panels.items():
                # Centre unique = milieu du panneau, deterministe.
                center = int(panel.shape[0] // 2)
                out[(prompt, 0)] = ([center], int(panel.shape[0]))
            return out

        return fake_lens_ignition_centers

    side_panels_a = {("p_short", 0): dense_a_short, ("p_long", 0): dense_a_long}
    side_panels_b = {("p_short", 0): dense_b_short, ("p_long", 0): dense_b_long}
    monkeypatch.setattr(la, "lens_ignition_centers", lens_ignition_centers_factory(side_panels_a))

    traces = _make_traces_stub()

    # On ne peut pas monkeypatcher lens_ignition_centers differentiellement
    # pour traces_a vs traces_b. Donc on appelle la primitive
    # directement en mode skip-test : on verifie que colocalize_lenses
    # skip bien un prompt ou T_a != T_b. On wrappe en remplacant la
    # fonction de telle sorte que le 1er appel (traces_a) renvoie
    # side_panels_a et le 2eme (traces_b) renvoie side_panels_b.
    call_count = {"n": 0}

    def fake_lens_ignition_centers_seq(traces, feature_ids, **kw):  # noqa: ARG001
        call_count["n"] += 1
        if call_count["n"] == 1:
            return lens_ignition_centers_factory(side_panels_a)(traces, feature_ids, **kw)
        else:
            return lens_ignition_centers_factory(side_panels_b)(traces, feature_ids, **kw)

    monkeypatch.setattr(la, "lens_ignition_centers", fake_lens_ignition_centers_seq)

    rng = np.random.default_rng(0)
    r = la.colocalize_lenses(traces, traces, k=K_FIXTURE, n_null=100, rng=rng)

    # ``p_short`` est skip (T_a=400 != T_b=250). ``p_long`` est OK.
    assert r["n_prompts"] == 1
    assert r["n_skipped"] == 1
    assert r["skipped"][0]["prompt"] == ("p_short", 0)
    assert r["skipped"][0]["T_a"] == 400
    assert r["skipped"][0]["T_b"] == 250


# --------------------------------------------------------------------------- #
# Gate 5 -- verdict synthese = max(n_colocalized, n_dissociated)               #
# --------------------------------------------------------------------------- #


def test_colocalize_lenses_synthetic_verdict_aggregation(monkeypatch):
    """Test synthetique : on impose a ``event_colocalization`` (via
    monkeypatch) des verdicts connus et on verifie l'agregation.

    On ecrase :func:`ict.lens_agreement.event_colocalization` pour
    retourner une serie de verdicts deterministes.
    """
    dense = _make_dense(seed=51, T=300, K=K_FIXTURE)
    _patch_panels(monkeypatch, dense, dense, prompts=("p0", "p1", "p2", "p3", "p4"))
    traces = _make_traces_stub()

    verdicts_to_inject = ["colocalized", "colocalized", "dissociated", "chance", "colocalized"]

    def fake_event_coloc(centers_a, centers_b, T, n_null=500, rng=None):  # noqa: ARG001
        v = verdicts_to_inject.pop(0)
        z_map = {"colocalized": 3.5, "dissociated": -3.5, "chance": 0.0, "undefined": float("nan")}
        return {"z": z_map[v], "verdict": v}

    monkeypatch.setattr(la, "event_colocalization", fake_event_coloc)
    rng = np.random.default_rng(0)
    r = la.colocalize_lenses(traces, traces, k=K_FIXTURE, n_null=10, rng=rng)

    assert r["n_colocalized"] == 3
    assert r["n_dissociated"] == 1
    assert r["n_chance"] == 1
    assert r["n_undefined"] == 0
    # Verdict : max(3, 1) = colocalized.
    assert r["verdict"] == "colocalized"
    # z_mean sur les 5 prompts definis (chance a z=0.0 non-nan donc
    # inclus). Somme : 3.5 + 3.5 - 3.5 + 0.0 + 3.5 = 7.0 -> moyenne 1.4.
    assert r["z_mean"] == pytest.approx((3.5 + 3.5 - 3.5 + 0.0 + 3.5) / 5.0, abs=1e-9)


def test_colocalize_lenses_dominant_dissociated_verdict(monkeypatch):
    """Si les dissocies dominent strictement, verdict = "dissociated"."""
    dense = _make_dense(seed=61, T=300, K=K_FIXTURE)
    _patch_panels(monkeypatch, dense, dense, prompts=("p0", "p1", "p2"))
    traces = _make_traces_stub()

    verdicts_to_inject = ["dissociated", "dissociated", "colocalized"]

    def fake_event_coloc(centers_a, centers_b, T, n_null=500, rng=None):  # noqa: ARG001
        v = verdicts_to_inject.pop(0)
        z_map = {"colocalized": 3.0, "dissociated": -3.0}
        return {"z": z_map[v], "verdict": v}

    monkeypatch.setattr(la, "event_colocalization", fake_event_coloc)
    r = la.colocalize_lenses(traces, traces, k=K_FIXTURE, n_null=10, rng=np.random.default_rng(0))

    assert r["n_colocalized"] == 1
    assert r["n_dissociated"] == 2
    assert r["verdict"] == "dissociated"


def test_colocalize_lenses_balanced_verdict_is_chance(monkeypatch):
    """Si n_colocalized == n_dissociated, verdict = "chance"."""
    dense = _make_dense(seed=71, T=300, K=K_FIXTURE)
    _patch_panels(monkeypatch, dense, dense, prompts=("p0", "p1"))
    traces = _make_traces_stub()

    verdicts_to_inject = ["colocalized", "dissociated"]

    def fake_event_coloc(centers_a, centers_b, T, n_null=500, rng=None):  # noqa: ARG001
        v = verdicts_to_inject.pop(0)
        z_map = {"colocalized": 3.0, "dissociated": -3.0}
        return {"z": z_map[v], "verdict": v}

    # `event_colocalization` est importe au top-level dans lens_agreement.py,
    # donc le monkeypatch doit viser la reference deja importee, pas la source.
    monkeypatch.setattr(la, "event_colocalization", fake_event_coloc)
    r = la.colocalize_lenses(traces, traces, k=K_FIXTURE, n_null=10, rng=np.random.default_rng(0))

    assert r["n_colocalized"] == 1
    assert r["n_dissociated"] == 1
    assert r["verdict"] == "chance"


# --------------------------------------------------------------------------- #
# Gate complementaire -- le default rng est applique si rng=None               #
# --------------------------------------------------------------------------- #


def test_colocalize_lenses_default_rng_when_none(monkeypatch):
    """Si ``rng=None``, le module utilise ``default_rng(0)``. Deux appels
    successifs avec ``rng=None`` donnent le meme verdict.
    """
    dense_a = _make_dense(seed=81, T=300, K=K_FIXTURE)
    dense_b = _make_dense(seed=82, T=300, K=K_FIXTURE)
    _patch_panels(monkeypatch, dense_a, dense_b, prompts=("p0", "p1"))
    traces = _make_traces_stub()

    r1 = la.colocalize_lenses(traces, traces, k=K_FIXTURE, n_null=50, rng=None)
    r2 = la.colocalize_lenses(traces, traces, k=K_FIXTURE, n_null=50, rng=None)

    assert r1["z_mean"] == pytest.approx(r2["z_mean"], abs=1e-9)
    assert r1["verdict"] == r2["verdict"]