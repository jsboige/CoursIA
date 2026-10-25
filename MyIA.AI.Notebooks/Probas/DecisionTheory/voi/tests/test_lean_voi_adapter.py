# Tests de l'adaptateur exact JSON -> Lean (items 5 et 6 de #22374).
#
# Trois familles :
#   1. conversion exacte et valeurs du banc (controle discriminant + negatif) ;
#   2. refus explicites (poids invalide, normalisation, cle manquante) ;
#   3. parite avec le module Lean committe : le bloc genere et les nombres des
#      theoremes doivent coincider avec la sortie courante de l'adaptateur.

import copy
import json
import sys
from fractions import Fraction
from pathlib import Path

import pytest

VOI = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(VOI))
from lean_voi_adapter import (  # noqa: E402
    AdapterError,
    BLOCK_BEGIN,
    BLOCK_END,
    bench_instances,
    build_instance,
    emit_block,
    evaluate,
    load_problem,
)

LEAN_MODULE = (
    VOI.parents[2] / "GameTheory" / "lean_game_defs_ext" / "Bayesian" / "VoiBench.lean"
)


def problem(name):
    return load_problem(VOI / "problems" / name)


# --- 1. conversion exacte -------------------------------------------------


def test_petrolier_conversion_exacte():
    inst = build_instance(problem("forage-petrolier.json"))
    # prior x vraisemblance, ramene a des entiers : 0.3*0.9 = 27/100, etc.
    assert inst.p == ((27, 3), (14, 56))
    assert inst.u == ((1500000, 200000), (-500000, 200000))
    assert (inst.scale_p, inst.scale_u) == (100, 1)
    assert inst.value_scale == 100
    assert inst.cost == 60000 * 100


def test_petrolier_valeurs_exactes():
    values = evaluate(build_instance(problem("forage-petrolier.json")))
    assert values["eu_no_info"] == 200000
    assert values["evsi_raw"] == 253000
    assert values["evsi_net"] == 193000
    assert values["evpi"] == 390000
    assert values["factored"] is None, "le forage informatif n'est pas factorise"


def test_non_informatif_est_factorise_et_de_gain_nul():
    inst = build_instance(problem("forage-non-informatif.json"))
    values = evaluate(inst)
    assert inst.factored == ((3, 7), (1, 1))
    assert values["evsi_raw"] == 0
    assert values["evsi_net"] == Fraction(-60000)
    # meme decision sans test que le probleme informatif : vendre
    assert values["eu_no_info"] == 200000


def test_aucune_valeur_lean_n_est_une_fraction():
    for inst in bench_instances():
        values = evaluate(inst)
        for key, value in values.items():
            if key.startswith("lean_") and isinstance(value, (int, Fraction)):
                assert isinstance(value, int), f"{key} doit etre entier"


def test_masse_totale_vaut_exactement_un():
    for inst in bench_instances():
        # somme des poids joints = Lp * 1, exactement, sans tolerance
        assert sum(sum(row) for row in inst.p) == inst.scale_p


# --- 2. refus explicites ---------------------------------------------------


def _mutate(name, path, value):
    spec = copy.deepcopy(problem(name))
    node = spec
    for key in path[:-1]:
        node = node[key]
    node[path[-1]] = value
    return spec


@pytest.mark.parametrize(
    "name,path,value,motif",
    [
        ("forage-petrolier.json", ("priors", "petrole"), Fraction(1, 2), "priors != 1"),
        ("forage-petrolier.json", ("priors", "petrole"), Fraction(-1, 10), "prior negatif"),
        (
            "forage-petrolier.json",
            ("likelihood", "positif", "petrole"),
            Fraction(1, 2),
            "vraisemblance != 1",
        ),
        (
            "forage-petrolier.json",
            ("likelihood", "positif", "petrole"),
            Fraction(-1, 10),
            "vraisemblance negative",
        ),
        ("forage-petrolier.json", ("test_cost",), Fraction(-1), "cout negatif"),
        ("forage-petrolier.json", ("test_cost",), "60000", "valeur non numerique"),
    ],
)
def test_refus_explicites(name, path, value, motif):
    spec = _mutate(name, path, value)
    with pytest.raises(AdapterError):
        build_instance(spec)


def test_refus_cle_manquante():
    spec = copy.deepcopy(problem("forage-petrolier.json"))
    del spec["likelihood"]
    with pytest.raises(AdapterError, match="likelihood"):
        build_instance(spec)


def test_refus_utilite_manquante_pour_un_etat():
    spec = copy.deepcopy(problem("forage-petrolier.json"))
    del spec["utilities"]["forer"]["pas_petrole"]
    with pytest.raises(AdapterError, match="utilite manquante"):
        build_instance(spec)


def test_signal_impossible_contribue_zero_et_reste_factorise():
    # signal "positif" de masse nulle : legal (ce n'est pas un poids invalide),
    # sa colonne jointe est nulle et sa contribution vaut exactement zero.
    spec = copy.deepcopy(problem("forage-non-informatif.json"))
    spec["likelihood"] = {
        "positif": {"petrole": 0, "pas_petrole": 0},
        "negatif": {"petrole": 1, "pas_petrole": 1},
    }
    inst = build_instance(spec)
    assert inst.p == ((0, 3), (0, 7))
    assert inst.factored == ((3, 7), (0, 1))
    assert evaluate(inst)["evsi_raw"] == 0


def test_corruption_de_la_table_divergence_de_la_reference():
    # Une corruption infime doit changer la valeur, jamais etre blanchie par un
    # arrondi : la conversion est exacte, donc 0.01 de vraisemblance se voit.
    spec = _mutate(
        "forage-petrolier.json", ("likelihood", "positif", "petrole"), Fraction(89, 100)
    )
    # la colonne ne somme plus a 1 : refus explicite plutot qu'acceptation muette
    with pytest.raises(AdapterError, match="ne somme pas exactement a 1"):
        build_instance(spec)


def test_corruption_normalisee_change_la_valeur():
    # corruption qui reste normalisee : 0.9/0.1 -> 0.89/0.11 cote petrole
    spec = copy.deepcopy(problem("forage-petrolier.json"))
    spec["likelihood"]["positif"]["petrole"] = Fraction(89, 100)
    spec["likelihood"]["negatif"]["petrole"] = Fraction(11, 100)
    values = evaluate(build_instance(spec))
    assert values["evsi_raw"] != 253000
    assert values["evsi_raw"] < 253000


# --- 3. parite avec le module Lean committe --------------------------------


def test_le_module_lean_existe():
    assert LEAN_MODULE.is_file(), f"module Lean absent : {LEAN_MODULE}"


def test_bloc_genere_identique_au_module_committe():
    texte = LEAN_MODULE.read_text(encoding="utf-8")
    debut = texte.index(BLOCK_BEGIN)
    fin = texte.index(BLOCK_END) + len(BLOCK_END)
    attendu = emit_block(bench_instances())
    assert texte[debut:fin].strip() == attendu.strip(), (
        "le bloc d'instances du module Lean diverge de l'adaptateur : "
        "regenerer avec `python lean_voi_adapter.py problems/*.json --emit`"
    )


@pytest.mark.parametrize(
    "theoreme,attendu",
    [
        ("valueNoisyNoInfo benchForagePetrolier", "20000000"),
        ("valueNoisySignal benchForagePetrolier", "45300000"),
        ("valueNoisyPerfect benchForagePetrolier", "59000000"),
        ("evsiRaw benchForagePetrolier", "25300000"),
        ("evsiNet benchForagePetrolier 6000000", "19300000"),
        ("valueNoisyPerfect benchForageNonInformatif", "11800000"),
        ("evsiNet benchForageNonInformatif 1200000", "-1200000"),
    ],
)
def test_nombres_des_theoremes_lean_coincident_avec_l_adaptateur(theoreme, attendu):
    texte = LEAN_MODULE.read_text(encoding="utf-8")
    assert f"{theoreme} = {attendu}" in texte, (
        f"le module Lean n'annonce pas `{theoreme} = {attendu}`"
    )


def test_le_module_lean_certifie_le_zero_par_le_theoreme():
    # la preuve du zero doit invoquer le critere d'Evans, pas seulement `decide`
    texte = LEAN_MODULE.read_text(encoding="utf-8")
    assert "valueNoisySignal_eq_valueNoisyNoInfo_of_factored" in texte
    assert "Factored benchForageNonInformatif" in texte


def test_les_deux_moteurs_du_banc_confirment_la_valeur_exacte():
    comparaison = json.loads((VOI / "comparison.json").read_text(encoding="utf-8"))
    tolerance = comparaison["tolerance"]["utility_abs"]
    exact = evaluate(build_instance(problem("forage-petrolier.json")))["evsi_raw"]
    lignes = {
        row["field"]: row
        for row in comparaison["problems"]["forage-petrolier"]["rows"]
    }
    infer_net = float(lignes["evsi_brute"]["infer_net"])
    pymc = float(lignes["evsi_brute"]["pymc"])
    assert infer_net == float(exact), "Infer.NET doit rendre la valeur exacte"
    assert abs(pymc - float(exact)) <= tolerance, "PyMC doit rester dans la tolerance"
