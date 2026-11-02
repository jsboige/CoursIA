#!/usr/bin/env python3
r"""Tests de l'organe de mesure lanyonai (#19741, etape 3).

Pinent le contrat qui a rendu la mesure du 2026-10-26 concluante, et qui ne doit
pas regresser silencieusement :

1. `parse_primitive` distingue un **pilote** d'un **stub**. Le C de
   `lanyonai/BurgersEquation` compile et s'execute, mais son `main` ne contient
   que `// Insert simulation drivers here.` + `return 0;` — sans ce predicat,
   l'organe laisserait croire que le depot livre des simulations.
2. `parse_primitive` rend `main_is_stub = None` quand il n'y a pas de `main` du
   tout (bibliotheque de noyaux) : « absent » et « stub » ne se confondent pas.
3. Les commentaires sont retires avant l'analyse du corps : un `return 0;`
   present dans un commentaire ne fabrique pas un stub, et un `main(` cite en
   commentaire ne fabrique pas un pilote.
4. `parse_proof` compte `sorry`, `native_decide` et `axiom` — les trois classes
   que le gate Lean du depot interdit, et dont un `grep -c sorry` ne voit qu'une.
5. `parse_proof` releve les jetons de **correspondance code <-> modele**. Le
   fichier amont n'en porte aucun : la preuve etablit les proprietes du schema,
   pas la correspondance C <-> Lean.
6. `render_text` nomme le verdict (`STUB`/`PILOTE`/`SANS OBJET`) et la ligne
   d'integrite, pour qu'une lecture rapide ne puisse pas sur-vendre le depot.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "research"))

import measure_lanyonai as mlo  # noqa: E402


# Forme reelle du C amont (lanyonai/BurgersEquation, implementations/
# inviscid_burgers_1d.c, lignes 437-441) — le `main` y est un stub.
STUB_C = """\
#include <math.h>
#include <stdlib.h>

static inline bool
inviscid_burgers_1d_state_valid(const inviscid_burgers_1d_state *U)
{
  double f = U->f;
  return isfinite(f);
}

static inline void
inviscid_burgers_1d_x_flux(const inviscid_burgers_1d_coordinates *C, double out)
{
  double x = C->x;
  out = ((1 / 2) * x * x);
}

int
main(int argc, char *argv[])
{
  // Insert simulation drivers here.

  return 0;
}
"""

# Un vrai pilote : du travail entre l'ouverture et le retour.
DRIVEN_C = """\
#include <stdio.h>

int main(int argc, char *argv[])
{
  for (int i = 0; i < 10; i++) {
    printf("%d\\n", i);
  }
  return 0;
}
"""

# Une bibliotheque de noyaux, sans point d'entree.
LIBRARY_C = """\
static inline double flux(double f)
{
  return 0.5 * f * f;
}
"""

# Forme reelle de la preuve amont : import unique, defs, theoremes, aucune
# mention du code C.
PROOF = """\
import Mathlib

set_option maxHeartbeats 1000000

namespace inviscid_burgers_1d

noncomputable def xFluxExprs (C : Coordinates) (P : Parameters) (U : State) : Flux :=
  { flux_f := ((1 / 2 : Real) * U.f * U.f) }

theorem xHyperbolicity (C : Coordinates) (P : Parameters) (U : State) :
    (xFluxJacobianEigenExprs C P U).lambda1 = U.f := by
  refine ⟨(xFluxJacobianEigenExprs C P U).lambda1, rfl⟩

theorem xFluxConservative (CL : Coordinates) (CR : Coordinates)
    (U : State) :
    True := by
  trivial

end inviscid_burgers_1d
"""


def test_stub_main_is_detected():
    """Le cas fondateur : le depot compile, s'execute, et ne calcule rien."""
    pm = mlo.parse_primitive(STUB_C, "BurgersEquation", "inviscid_burgers_1d")
    assert pm.has_main is True
    assert pm.main_is_stub is True
    assert pm.static_inline_count == 2
    assert pm.lines == len(STUB_C.splitlines())


def test_real_driver_is_not_a_stub():
    pm = mlo.parse_primitive(DRIVEN_C, "X", "y")
    assert pm.has_main is True
    assert pm.main_is_stub is False


def test_library_without_main_is_sans_objet():
    """Absent != stub : une bibliotheque de noyaux ne s'accuse pas d'etre vide."""
    pm = mlo.parse_primitive(LIBRARY_C, "X", "y")
    assert pm.has_main is False
    assert pm.main_is_stub is None


def test_comments_ne_fabriquent_pas_de_pilote():
    """Un `main(` en commentaire ne cree pas de point d'entree."""
    code = "// main(int argc, char **argv)\nstatic inline double f(double x) { return x; }\n"
    pm = mlo.parse_primitive(code, "X", "y")
    assert pm.has_main is False


def test_return_zero_in_comment_ne_fabrique_pas_un_stub():
    """Symetrique du precedent : un `return 0;` commente ne rend pas un pilote vide."""
    code = (
        "int main(void)\n{\n"
        "  // return 0;\n"
        "  int s = 0;\n"
        "  for (int i = 0; i < 3; i++) { s += i; }\n"
        "  return s;\n"
        "}\n"
    )
    pm = mlo.parse_primitive(code, "X", "y")
    assert pm.has_main is True
    assert pm.main_is_stub is False


def test_proof_counts_and_shape():
    pm = mlo.parse_proof(PROOF, "BurgersEquation", "inviscid_burgers_1d")
    assert pm.imports == ["Mathlib"]
    assert pm.defs == 1
    assert pm.theorems == 2
    assert pm.theorem_names == ["xHyperbolicity", "xFluxConservative"]
    assert pm.sorry_count == 0
    assert pm.native_decide_count == 0
    assert pm.axiom_count == 0


def test_proof_counts_the_three_forbidden_classes():
    """`grep -c sorry` ne voit qu'une des trois classes interdites par le gate."""
    text = PROOF + (
        "\ntheorem trou (n : Nat) : n = n := by sorry\n"
        "theorem natif : (2 : Nat) = 2 := by native_decide\n"
        "axiom magique : False\n"
    )
    pm = mlo.parse_proof(text, "X", "y")
    assert pm.sorry_count == 1
    assert pm.native_decide_count == 1
    assert pm.axiom_count == 1


def test_upstream_proof_claims_no_code_correspondence():
    """Le coeur de la mesure : aucune mention du code dans la preuve amont."""
    pm = mlo.parse_proof(PROOF, "BurgersEquation", "inviscid_burgers_1d")
    assert pm.implementation_mentions == []


def test_code_correspondence_markers_are_reported():
    pm = mlo.parse_proof(PROOF + "\n-- code_matches Float\ntheorem t : True := trivial\n", "X", "y")
    assert "code_matches" in pm.implementation_mentions
    assert "Float" in pm.implementation_mentions


def test_render_text_names_the_verdict():
    report = {
        "org": "lanyonai",
        "measured_by": "scripts/research/measure_lanyonai.py",
        "repos": [
            {
                "repo": "BurgersEquation",
                "license": "MIT",
                "license_file": True,
                "default_branch": "main",
                "language": "Lean",
                "size_kb": 1,
                "has_lean_toolchain": False,
                "has_lakefile": False,
                "root_entries": ["LICENSE"],
            }
        ],
        "proof": mlo.parse_proof(PROOF, "BurgersEquation", "inviscid_burgers_1d").to_dict(),
        "primitive": mlo.parse_primitive(
            STUB_C, "BurgersEquation", "inviscid_burgers_1d"
        ).to_dict(),
    }
    text = mlo.render_text(report)
    assert "toolchain=ABSENT" in text
    assert "lakefile=ABSENT" in text
    assert "sorry=0" in text
    assert "implementation_mentions) : AUCUNE" in text
    assert "STUB" in text
    assert "PILOTE" not in text
