"""Algèbre affine exacte du plan (arithmétique rationnelle).

Fondement des groupes de symétrie du plan : toute isométrie ou symétrie
cristallographique s'écrit ``x -> A x + t`` avec ``A`` une matrice 2x2 et ``t``
un vecteur. Travailler en `fractions.Fraction` evite tout arrondi : les
invariants des groupes (ordre du groupe ponctuel, réseau de translation,
directions de miroir) doivent etre **exacts**, sinon un classement faux
remplace une classification.

Aucune dependance externe : la bibliotheque standard suffit.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from fractions import Fraction

__all__ = [
    "Affine",
    "Matrix",
    "Vector",
    "identity_matrix",
    "mat_det",
    "mat_inv",
    "mat_mul",
    "mat_vec",
    "vec_add",
    "vec_neg",
    "vec_sub",
]

Matrix = tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]
Vector = tuple[Fraction, Fraction]

F = Fraction

IDENTITY: Matrix = ((F(1), F(0)), (F(0), F(1)))


def identity_matrix() -> Matrix:
    """Matrice identite (une instance neuve a chaque appel)."""
    return (IDENTITY[0], IDENTITY[1])


def mat_mul(a: Matrix, b: Matrix) -> Matrix:
    """Produit matriciel ``a @ b``."""
    return (
        (
            a[0][0] * b[0][0] + a[0][1] * b[1][0],
            a[0][0] * b[0][1] + a[0][1] * b[1][1],
        ),
        (
            a[1][0] * b[0][0] + a[1][1] * b[1][0],
            a[1][0] * b[0][1] + a[1][1] * b[1][1],
        ),
    )


def mat_vec(a: Matrix, v: Vector) -> Vector:
    """Produit matrice-vecteur ``a @ v``."""
    return (
        a[0][0] * v[0] + a[0][1] * v[1],
        a[1][0] * v[0] + a[1][1] * v[1],
    )


def mat_det(a: Matrix) -> Fraction:
    """Determinant d'une matrice 2x2."""
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def mat_inv(a: Matrix) -> Matrix:
    """Inverse d'une matrice 2x2 invertible (det != 0)."""
    det = mat_det(a)
    if det == 0:
        raise ValueError("matrice singuliere : inverse impossible")
    return (
        (a[1][1] / det, -a[0][1] / det),
        (-a[1][0] / det, a[0][0] / det),
    )


def vec_add(u: Vector, v: Vector) -> Vector:
    return (u[0] + v[0], u[1] + v[1])


def vec_sub(u: Vector, v: Vector) -> Vector:
    return (u[0] - v[0], u[1] - v[1])


def vec_neg(u: Vector) -> Vector:
    return (-u[0], -u[1])


def mat_is_identity(a: Matrix) -> bool:
    return a == IDENTITY


@dataclass(frozen=True)
class Affine:
    """Transformation affine ``x -> A x + t``.

    ``matrix`` est la partie lineaire, ``translation`` la partie affine.
    """

    matrix: Matrix
    translation: Vector

    @classmethod
    def identity(cls) -> Affine:
        return cls(identity_matrix(), (F(0), F(0)))

    @classmethod
    def translation(cls, tx: Fraction | int, ty: Fraction | int) -> Affine:
        return cls(identity_matrix(), (F(tx), F(ty)))

    @classmethod
    def linear(cls, a: Matrix) -> Affine:
        return cls(a, (F(0), F(0)))

    def compose(self, other: Affine) -> Affine:
        """``self.compose(other)`` applique ``other`` **puis** ``self``."""
        return Affine(
            mat_mul(self.matrix, other.matrix),
            vec_add(mat_vec(self.matrix, other.translation), self.translation),
        )

    def __mul__(self, other: Affine) -> Affine:
        return self.compose(other)

    def apply(self, point: Vector) -> Vector:
        """Image d'un point."""
        return vec_add(mat_vec(self.matrix, point), self.translation)

    def apply_vector(self, vector: Vector) -> Vector:
        """Image d'un vecteur (partie lineaire seule)."""
        return mat_vec(self.matrix, vector)

    def inverse(self) -> Affine:
        inv = mat_inv(self.matrix)
        return Affine(inv, vec_neg(mat_vec(inv, self.translation)))

    @property
    def determinant(self) -> Fraction:
        return mat_det(self.matrix)

    @property
    def is_identity(self) -> bool:
        return self.matrix == IDENTITY and self.translation == (F(0), F(0))

    @property
    def is_pure_translation(self) -> bool:
        return self.matrix == IDENTITY

    @property
    def is_orientation_preserving(self) -> bool:
        return self.determinant > 0

    def linear_equals(self, other: Affine) -> bool:
        return self.matrix == other.matrix


def compose_all(elements: Iterable[Affine]) -> Affine:
    """Compose une iterable d'elements (le premier applique en premier)."""
    result = Affine.identity()
    for element in elements:
        result = result.compose(element)
    return result
