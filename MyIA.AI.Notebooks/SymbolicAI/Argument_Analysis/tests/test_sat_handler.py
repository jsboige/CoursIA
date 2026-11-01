"""Tests de l'organe SAT de l'argumentation propositionnelle (#23120).

`argumentation_lib/sat_handler.py` est l'organe natif que `_pl_handler.py`
appelle deja (`from .sat_handler import SATHandler`) mais qui manquait dans
l'arbre : le chemin SAT etait donc du code mort, et toute requete PL
retombait sur l'enumeration de modeles de Tweety (2^n) — d'ou
`java.lang.OutOfMemoryError: Java heap space` sur le contenu reel du carnet
08b.

Ces tests verifient le **comportement** de l'organe, pas sa presence :
  - un entailment **vrai** produit un verdict `ACCEPTED` ;
  - un entailment **faux** produit un verdict `REJECTED` ;
  - une base **non propositionnelle** (phrases en langage naturel) est
    **refusee** a la frontiere (`PLFormulaError`) au lieu d'etre atomisee en
    silence (le mecanisme 2^n) ;
  - une base large reste **decisive** (cout lineaire, pas exponentiel) ;
  - le moteur de resolution est celui du depot (`ext_tools/sat_solver.py`).

Run with: pytest tests/test_sat_handler.py -v
"""

import sys
import time
from pathlib import Path

import pytest

# Ajoute Argument_Analysis/ au path pour importer le package argumentation_lib.
sys.path.insert(0, str(Path(__file__).parent.parent))

from argumentation_lib.sat_handler import (  # noqa: E402
    PLFormulaError,
    SATHandler,
    SATPLEngine,
    entails,
    parse_pl_formula,
    verdict,
)
from argumentation_lib.sat_handler import _Atom, _BinOp, _Not  # noqa: E402

#: Extrait reel du texte d'analyse du carnet 08b (transition energetique).
#: Ce sont des phrases en langage naturel : c'est exactement la forme que la
#: normalisation mot a mot transformait en dizaines d'atomes.
PHRASES_NATURELLES = [
    "Les energies renouvelables sont essentielles pour lutter contre le changement climatique.",
    "La France s'est engagee a reduire ses emissions de CO2 de 40% d'ici 2030.",
    "L'Allemagne produit 46% de son electricite a partir de sources renouvelables en 2023.",
    "Les energies renouvelables creent des emplois locaux non delocalisables.",
    "Le secteur emploie deja plus de 150 000 personnes en France.",
    "Quiconque s'oppose a cette transition est contre la creation d'emplois.",
    "Les ecologistes veulent nous ramener a l'age de pierre en supprimant le nucleaire.",
    "Le nucleaire fournit 70% de notre electricite.",
    "Le cout de la transition est exorbitant.",
    "Tout le monde sait que les eoliennes sont inefficaces car elles ne tournent que 25% du temps.",
    "Les panneaux solaires sont fabriques en Chine avec du charbon.",
    "Investir dans le solaire revient donc a financer la pollution chinoise.",
    "Des milliers de scientifiques ont signe une petition pour le climat.",
    "Les climatosceptiques sont finances par les lobbies petroliers.",
]


# ---------------------------------------------------------------------------
# Verdicts reels
# ---------------------------------------------------------------------------


def test_entailment_acceptee():
    """Une proposition presente dans la base est entailee -> ACCEPTED."""
    base = ["climat_urgence", "renouvelables_essentielles"]

    assert entails(base, "climat_urgence") is True
    assert verdict(base, "climat_urgence") == "ACCEPTED"


def test_entailment_acceptee_par_chaine_implicative():
    """L'enchainement d'implications est entail : p -> q -> r entraine r."""
    base = ["p", "p -> q", "q -> r"]

    assert entails(base, "r") is True
    assert verdict(base, "r") == "ACCEPTED"


def test_entailment_rejetee():
    """Une proposition absente de la base n'est pas entailee -> REJECTED."""
    base = ["climat_urgence", "renouvelables_essentielles"]

    assert entails(base, "nucleaire_solution") is False
    assert verdict(base, "nucleaire_solution") == "REJECTED"


def test_entailment_rejetee_meme_si_la_base_implique_autre_chose():
    """Une implication vraie dans la base n'entraine pas son consequent isole."""
    base = ["p -> q"]

    # q n'est entail que si p l'est ; la base ne fixe pas p.
    assert entails(base, "q") is False


def test_conclusion_par_contradiction_detectee():
    """Une base contradictoire entraine tout (ex falso) : le comportement est
    correct, et `solve_formulas` signale l'incoherence."""
    handler = SATHandler()
    is_sat, _model, stats = handler.solve_formulas(["a", "!a"])

    assert is_sat is False
    assert stats["status"] == "UNSAT"


def test_solve_formulas_modele_nomme():
    """Une base satisfiable renvoie un modele nomme (proposition -> booleen)."""
    handler = SATHandler()
    is_sat, model, stats = handler.solve_formulas(["a", "b", "!c"])

    assert is_sat is True
    assert model is not None
    assert model["a"] is True
    assert model["b"] is True
    assert model["c"] is False
    assert stats["num_atoms"] == 3


# ---------------------------------------------------------------------------
# Refus a la frontiere : pas d'atomisation silencieuse
# ---------------------------------------------------------------------------


def test_refus_phrase_en_langage_naturel():
    """Une phrase n'est pas une formule propositionnelle : elle est refusee."""
    with pytest.raises(PLFormulaError):
        parse_pl_formula(PHRASES_NATURELLES[0])


def test_refus_du_belief_set_naturel_entier():
    """Le cas mesure sur le carnet 08b : les 14 phrases ne sont pas
    propositionnelles. Le refus est instantane et borne (pas de 2^n)."""
    handler = SATHandler()
    debut = time.perf_counter()

    with pytest.raises(PLFormulaError):
        handler.query(PHRASES_NATURELLES, "climat_urgence")

    ecoule = time.perf_counter() - debut
    # Une atomisation mot a mot suivie d'une enumeration de modeles est
    # exponentielle : le refus doit rester instantane.
    assert ecoule < 1.0, f"refus trop lent : {ecoule:.3f}s"


def test_refus_formule_vide_ou_tronquee():
    """Une formule vide ou malformee est refusee, jamais devinee."""
    with pytest.raises(PLFormulaError):
        parse_pl_formula("")
    with pytest.raises(PLFormulaError):
        parse_pl_formula("a &")
    with pytest.raises(PLFormulaError):
        parse_pl_formula("(a | b")


def test_refus_des_caracteres_hors_langage():
    """Un litteral markdown ou une ponctuation n'est pas une proposition."""
    with pytest.raises(PLFormulaError):
        parse_pl_formula("Le climat, urgent !")
    with pytest.raises(PLFormulaError):
        parse_pl_formula("**climat**")


# ---------------------------------------------------------------------------
# Mise a l'echelle : cout lineaire, verdict decisif
# ---------------------------------------------------------------------------


def test_verdict_decisif_sur_base_large():
    """Une base large reste decisive : la chaine d'implications est entailee
    sans que le cout croisse exponentiellement (le defaut 2^n du chemin
    Tweety)."""
    taille = 200
    base = ["p0"]
    base += [f"p{i} -> p{i + 1}" for i in range(taille)]
    base += [f"p{i}" for i in range(taille)]

    handler = SATHandler()
    debut = time.perf_counter()
    resultat = handler.query(base, f"p{taille}")
    ecoule = time.perf_counter() - debut

    assert resultat is True
    assert ecoule < 10.0, f"resolution trop lente sur {taille} propositions : {ecoule:.3f}s"


def test_verdict_decisif_sur_base_large_non_impliquante():
    """Meme base large, proposition hors chaine : le verdict reste REJECTED."""
    taille = 120
    base = ["p0"]
    base += [f"p{i} -> p{i + 1}" for i in range(taille)]

    handler = SATHandler()
    assert handler.query(base, "p_absente") is False


# ---------------------------------------------------------------------------
# Organe natif du depot (regle "organ-first")
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Verification independante : table de verite exhaustive
# ---------------------------------------------------------------------------


def _atoms(node, collect):
    """Recueille les propositions d'un arbre de formule."""
    if isinstance(node, _Atom):
        collect.add(node.name)
    elif isinstance(node, _Not):
        _atoms(node.child, collect)
    elif isinstance(node, _BinOp):
        _atoms(node.left, collect)
        _atoms(node.right, collect)


def _evaluate(node, env):
    """Evalue l'arbre de formule sous une valuation (dictionnaire proposition -> bool)."""
    if isinstance(node, _Atom):
        return bool(env.get(node.name, False))
    if isinstance(node, _Not):
        return not _evaluate(node.child, env)
    if isinstance(node, _BinOp):
        left = _evaluate(node.left, env)
        right = _evaluate(node.right, env)
        if node.op == "&":
            return left and right
        if node.op == "|":
            return left or right
        if node.op == "->":
            return (not left) or right
        if node.op == "<->":
            return left == right
        if node.op == "^":
            return left != right
    raise AssertionError(f"noeud inconnu : {node!r}")


def _entailment_par_table_de_verite(base, query):
    """Entailment par enumeration exhaustive (témoin independant du solveur)."""
    collect = set()
    for formule in list(base) + [query]:
        _atoms(parse_pl_formula(formule), collect)
    noms = sorted(collect)
    for masque in range(2 ** len(noms)):
        env = {nom: bool((masque >> i) & 1) for i, nom in enumerate(noms)}
        if all(_evaluate(parse_pl_formula(f), env) for f in base):
            if not _evaluate(parse_pl_formula(query), env):
                return False
    return True


def test_verdict_conforme_a_la_table_de_verite_exhaustive():
    """Le verdict SAT est verifie contre une enumeration exhaustive des
    valuations : les deux methodes (solveur CNF / table de verite) sont
    independantes, donc leur accord vaut temoin de l'encodeur."""
    cas = [
        (["a"], "a", True),
        (["a"], "b", False),
        (["a", "b"], "a & b", True),
        (["a & b"], "a", True),
        (["a | b"], "a", False),
        (["a", "b"], "a | b", True),
        (["a -> b", "a"], "b", True),
        (["a -> b"], "b", False),
        (["a <-> b", "a"], "b", True),
        (["a <-> b"], "a", False),
        (["!a"], "a", False),
        (["a ^ b", "a"], "b", False),
        (["a ^ b", "a"], "!b", True),
        (["(a | b) -> c", "a"], "c", True),
        (["(a | b) -> c", "a"], "!c", False),
        # implication niee dans la requete (polarite du defaut encodeur #1) :
        ([], "a -> a", True),
        (["!a"], "a -> b", True),
        (["a"], "a <-> a", True),
        (["!(a -> b)"], "!b", True),
    ]

    handler = SATHandler()
    for base, query, attendu in cas:
        obtenu = handler.query(list(base), query)
        attendu_table = _entailment_par_table_de_verite(list(base), query)
        assert obtenu == attendu, f"{base} entail {query} : {obtenu} != {attendu}"
        assert obtenu == attendu_table, (
            f"{base} entail {query} : solveur={obtenu}, table de verite={attendu_table}"
        )


def test_organ_sat_du_depot_present_et_utilise():
    """Le moteur de resolution est celui du depot (`ext_tools/sat_solver.py`),
    pas une reimplementation locale."""
    from argumentation_lib import sat_handler

    chemin = Path(sat_handler._REPO_SAT_ORGAN).resolve()
    assert chemin.is_file(), f"organe SAT du depot introuvable : {chemin}"

    handler = SATHandler()
    assert handler._organ is not None
    assert getattr(handler._organ, "PYSAT_AVAILABLE", False) is True
    assert "cadical195" in [name for name, _ in handler._organ.RECOMMENDED_SOLVERS]


def test_module_expose_le_drapeau_pysat_available():
    """Le module expose `PYSAT_AVAILABLE` en tant que bool : c'est le symbole
    que `_pl_handler._sat_available` lit pour decider du chemin SAT. Sans lui,
    `sat_handler.PYSAT_AVAILABLE` levait AttributeError, avalie par le `except`
    du caller, et le chemin SAT restait du code mort (reserve #23449)."""
    from argumentation_lib import sat_handler

    assert "PYSAT_AVAILABLE" in sat_handler.__all__
    assert isinstance(sat_handler.PYSAT_AVAILABLE, bool)


# ---------------------------------------------------------------------------
# Couture moteur : le contrat `entails(formules, query)` de #23040
# ---------------------------------------------------------------------------


def test_moteur_sat_expose_le_contrat_du_moteur_de_reference():
    """`SATPLEngine.entails(formulas, query)` est le contrat que
    `PLReasonerPlugin` appelle sur son moteur injectable (#23040)."""
    engine = SATPLEngine()

    assert engine.entails(["p", "p => q"], "q") is True
    assert engine.entails(["p", "p => q"], "r") is False


def test_moteur_sat_accepte_la_syntaxe_du_formalisme_utilise():
    """Les variantes d'operateurs usuelles sont acceptees."""
    engine = SATPLEngine()

    assert engine.entails(["a & b"], "a") is True
    assert engine.entails(["a", "b"], "a | b") is True
    # Une disjonction n'entraine aucune de ses branches.
    assert engine.entails(["a | b"], "a") is False
    assert engine.entails(["!a"], "a") is False
    assert engine.entails(["a -> b", "a"], "b") is True
    assert engine.entails(["a <-> b", "a"], "b") is True


def test_moteur_sat_refuse_un_belief_set_non_propositionnel():
    """Le moteur refuse l'entree non propositionnelle au lieu de la
    degrader : c'est le remede au `OutOfMemoryError` mesure sur #23120."""
    engine = SATPLEngine()

    with pytest.raises(PLFormulaError):
        engine.entails(PHRASES_NATURELLES, "climat_urgence")
