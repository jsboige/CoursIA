"""Tests unitaires pour les helpers FP-class du detect_solution_leaks.

Couvre les classes de faux positifs isoles par le sub-grain c.8104c du
EPIC #8053 :

- ``exercise_with_none_stub_or_marker`` : def/class avec `= None` stubs
  + print trailer (Lab4-DataWrangling, SW-12-GraphRAG, Planners-1, Arrow).
- ``exercise_with_a_completer_minizinc`` : model-text avec `% A COMPLETER`
  + `display_model` (App-8-MiniZinc).
- ``exercise_with_attente_implementation`` : C# `Console.WriteLine("...
  en attente de votre implementation")` (CSP-3-Advanced, CSP-7-Soft,
  App-1b-NQueens).
- ``exercise_with_exercice_indice_skeleton`` : Python `# Exercice` /
  `# Indice` headers, no substantive call/return (Arrow-33 pattern).

Run: python scripts/notebook_tools/test_detect_solution_leaks_skeleton_instructions.py
"""
import sys
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

from detect_solution_leaks import (  # noqa: E02
    exercise_with_none_stub_or_marker,
    exercise_with_a_completer_minizinc,
    exercise_with_attente_implementation,
    exercise_with_exercice_indice_skeleton,
)


class TestExerciseWithNoneStubOrMarker(unittest.TestCase):
    """`def` with `= None` stub assignments + print trailer = exercise."""

    def test_lab4_datawrangling_pattern(self):
        """Lab4 cell 25: def detecter_anomalies_iqr with None stubs."""
        src = """\
def detecter_anomalies_iqr(serie, facteur=1.5):
    \"\"\"Detection d'anomalies par la methode IQR.\"\"\"
    Q1 = None
    Q3 = None
    IQR = None
    borne_inf = None
    borne_sup = None
    nb_doublons = None
    return nb_doublons

print("detecter_anomalies_iqr OK")
"""
        self.assertTrue(exercise_with_none_stub_or_marker(src))

    def test_arrow_cell_33_pattern(self):
        """Arrow cell 33: def with None stubs + trailing announce."""
        src = """\
def generer_profil_extremal_4alt(cible, alternatives):
    \"\"\"Genere un profil extremal pour 4 alternatives.\"\"\"
    profil = None
    position = None
    nb_profils = None
    return profil

print("generer_profil_extremal_4alt defini")
"""
        self.assertTrue(exercise_with_none_stub_or_marker(src))

    def test_single_none_is_not_enough(self):
        """A single `= None` assignment is too lenient — must have 2+."""
        src = """\
def foo():
    x = None
    return x

print("foo OK")
"""
        self.assertFalse(exercise_with_none_stub_or_marker(src))

    def test_no_print_trailer(self):
        """Missing `print(...)` trailer — not the exercise-with-None pattern."""
        src = """\
def foo():
    Q1 = None
    Q3 = None
    return None
"""
        self.assertFalse(exercise_with_none_stub_or_marker(src))

    def test_real_solution_with_substantive_body(self):
        """A real solution has substantive body lines, not None stubs."""
        src = """\
def fibonacci(n):
    if n <= 1:
        return n
    a, b = 0, 1
    for _ in range(2, n + 1):
        a, b = b, a + b
    return b

print(fibonacci(10))
"""
        self.assertFalse(exercise_with_none_stub_or_marker(src))


class TestExerciseWithACompleterMinizinc(unittest.TestCase):
    """MiniZinc model text with `% A COMPLETER` + display_model = exercise."""

    def test_app8_magic_square_pattern(self):
        """App-8 cell 41: carre magique with `% A COMPLETER` + `???` placeholders."""
        src = """\
model_magic_square = \"\"\"
int: n = 3;
int: magic_sum = n * (n * n + 1) div 2;

array[1..n, 1..n] of var 1..n*n: grid;

% A COMPLETER :
% constraint alldifferent(???);
% constraint forall(i in 1..n)(???);

solve satisfy;
\"\"\"

display_model(model_magic_square, "Carre magique (a completer)")
"""
        self.assertTrue(exercise_with_a_completer_minizinc(src))

    def test_app8_coloring_pattern(self):
        """App-8 cell 43: coloration with `# A COMPLETER :` + `% A COMPLETER...`."""
        src = """\
# A COMPLETER : ecrire le modele MiniZinc
model_coloring = \"\"\"
% A COMPLETER...
% solve minimize ???;
\"\"\"

display_model(model_coloring, "Coloration (a completer)")
"""
        self.assertTrue(exercise_with_a_completer_minizinc(src))

    def test_minizinc_placeholder_alone(self):
        """`???` MiniZinc placeholder + solve satisfy = exercise even without `A COMPLETER` text."""
        src = """\
model_x = \"\"\"
int: n = 5;
array[1..n] of var 1..10: x;
constraint forall(i in 1..n-1)(x[i] < x[i+1] ???);
solve satisfy;
\"\"\"

display_model(model_x, "test")
"""
        self.assertTrue(exercise_with_a_completer_minizinc(src))

    def test_no_marker_no_model(self):
        """No `% A COMPLETER` marker, no `???`, no model = not a MiniZinc exercise."""
        src = """\
x = 1 + 2
print(x)
"""
        self.assertFalse(exercise_with_a_completer_minizinc(src))


class TestExerciseWithAttenteImplementation(unittest.TestCase):
    """C# `Console.WriteLine("... en attente de votre implementation")` = exercise."""

    def test_csp3_advanced_nreines_pattern(self):
        """CSP-3-Advanced cell 22: N-Reines with model constructor + attente announce."""
        src = """\
// === EXERCICE 2 : N-Reines avec cassage de symmétries ===
int n8 = 8;
var model8 = new Model($"N-Reines {n8}");

Console.WriteLine($"Exercice 2 - N-Reines n={n8} : en attente de votre implementation");
Console.WriteLine("Nombre de solutions N=8 sans cassage = 92");
"""
        self.assertTrue(exercise_with_attente_implementation(src))

    def test_csp3_advanced_minivrp_pattern(self):
        """CSP-3-Advanced cell 24: Mini-VRP placeholder with dist matrix."""
        src = """\
// === EXERCICE 3 : Mini-VRP via subCircuit ===
var dist9 = new[,] { {0, 3, 1, 5, 8}, {3, 0, 6, 2, 7} };
int n9 = 5;

var model9 = new Model("Mini-VRP — subCircuit");

Console.WriteLine("Exercice 3 - Mini-VRP subCircuit : en attente de votre implementation");
"""
        self.assertTrue(exercise_with_attente_implementation(src))

    def test_csp7_soft_emploisdutemps_pattern(self):
        """CSP-7-Soft cell 22: emploi du temps with prefs + attente."""
        src = """\
// === EXERCICE 3 : Emploi du temps enseignant ===
string[] prefLabels = { "A", "A", "B", "B", "C" };
int[] prefCosts = { 0, 0, 1, 1, 5 };
int nCours8 = 4;
int nJours8 = 5;
Console.WriteLine($"Exercice 3 - {nCours8} cours sur {nJours8} jours");
Console.WriteLine("En attente de votre implementation");
"""
        self.assertTrue(exercise_with_attente_implementation(src))

    def test_real_solver_call_not_exercise(self):
        """A real solver call is a real solution, not a placeholder."""
        src = """\
// Exercice 1
var model = new Model("test");
var x = model.NewIntVar("x", 0, 10);
model.Add(x == 5);
var solver = new CpSolver();
solver.Solve(model);
Console.WriteLine(solver.Value(x));
"""
        self.assertFalse(exercise_with_attente_implementation(src))

    def test_no_attente_marker(self):
        """Without `en attente` / `à compléter` text, not flagged."""
        src = """\
int n = 5;
Console.WriteLine($"n = {n}");
"""
        self.assertFalse(exercise_with_attente_implementation(src))


class TestExerciseWithExerciceIndiceSkeleton(unittest.TestCase):
    """Python with `# Exercice` / `# Indice` headers, no substantive call/return."""

    def test_arrow_cell_33_skeleton(self):
        """Arrow cell 33: # Exercice + # Indice guidance, variable setup."""
        src = """\
# Exercice 1 : Lemme Extremal avec 4 alternatives
# ================================================

# Exercice: adaptez generate_extremal_profiles pour 4 alternatives
# Indice : avec ['A', 'B', 'C', 'D'], la cible 'B' peut etre en premiere
# ou derniere position.

alternatives_4 = ['A', 'B', 'C', 'D']

# Exercice: generez 100 profils ou B est toujours en position extreme
# Indice : utilisez une boucle similaire au test systematique

# Votre code ici
"""
        self.assertTrue(exercise_with_exercice_indice_skeleton(src))

    def test_real_solution_with_function_call(self):
        """A real solution has a substantive assignment-to-call expression."""
        src = """\
# Exercice 1
# Indice : utilisez la formule de Bernoulli

from math import comb
result = comb(10, 3) * (0.5 ** 10)
print(result)
"""
        self.assertFalse(exercise_with_exercice_indice_skeleton(src))

    def test_single_marker_not_enough(self):
        """Single `# Exercice` marker is too lenient — need 2+."""
        src = """\
# Exercice 1
x = 42
print(x)
"""
        self.assertFalse(exercise_with_exercice_indice_skeleton(src))


if __name__ == "__main__":
    unittest.main(verbosity=2)
