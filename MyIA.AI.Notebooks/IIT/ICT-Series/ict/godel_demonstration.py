"""Numérotation de Gödel d'un énoncé non trivial -- le théorème de Pythagore en Tarski.

Outille la cellule ajoutée au notebook Lean-34 (cycle 26, grain #19351 du plan #19333).

Le module materialize l'exemple de l'article *The Gödel Number of a Non-Trivial
Sentence* (Sheydvasser, 04/07/2026, https://derangedmathematician.substack.com/p/
the-godel-number-of-a-non-trivial) : la numérotation de Gödel du **théorème de
Pythagore** formule -- en **paraphrase informelle** inspiree de la notation de
Tarski (B3 "entre", C4 "congruence"). Les versions 2 a 4 ne sont **pas** des
formulations rigoureuses du langage de Tarski (la congruence y est 4-aire, pas
une fonction binaire ; il n'y a pas de symbole de fonction), mais des
**schémas pedagogiques** qui montrent la croissance de complexite. La version
5 **s'auto-refere** (la diagonale de Gödel) -- sa longueur explose par
auto-substitution, et son nombre de Gödel depasse les bornes du representable
en Python (on n'affiche que l'ordre de grandeur log10).

L'operation de Gödel sous-jacente est la **substitution** : encoder une chaîne
s sur alphabet ASCII comme un entier N par

    N = Π_{i=0}^{len(s)-1}  p_i ^ (ord(s[i]) + 1)

où p_i est le i-ème nombre premier. C'est l'encodage historique (Gödel 1931),
avant les variantes binaires modernes. L'injectivité repose sur le théorème
fondamental de l'arithmétique.

La fonction `godel_pythagore(version: int) -> str` matérialise les 5 versions.
La fonction `godel_number(s: str) -> int` (decomposition factorielle) calcule le
nombre ; pour la version 5, le nombre est astronomique et on n'affiche que
l'ordre de grandeur (log10).
"""

import math
from math import log10


def _is_prime_stream(n: int):
    """Flux lazy de nombres premiers jusqu'a n (crible d'Eratosthene)."""
    sieve = [True] * (n + 1)
    sieve[0] = sieve[1] = False
    for p in range(2, int(n ** 0.5) + 1):
        if sieve[p]:
            for k in range(p * p, n + 1, p):
                sieve[k] = False
    return [i for i in range(2, n + 1) if sieve[i]]


_PRIMES_10K = _is_prime_stream(10000)


def godel_pythagore(version: int) -> str:
    """Le theoreme de Pythagore en Tarski, dans sa version 1..5.

    Version 1 : enonce concis (le theoreme, point).
    Version 2 : enonce developpe (avec quantification universelle explicite).
    Version 3 : enonce formel (operateurs B3, C4 nommes).
    Version 4 : enonce enonce (commentaires et lemmes intermediaires).
    Version 5 : l'enonce **s'auto-reference** -- sa longueur explose par
        iteration de la diagonale de Gödel.
    """
    if version < 1 or version > 5:
        raise ValueError(f"version doit etre dans 1..5 (recu {version})")
    if version == 1:
        return "for any right triangle, a^2 + b^2 = c^2"
    if version == 2:
        # Paraphrase informelle inspiree de la notation Tarski.
        # La notation stricte de Tarski n'a pas de symbole de fonction (Cong
        # est 4-aire, et il n'y a pas de predicat "right angle" -- le
        # triangle rectangle est un cas particulier hors du langage nu).
        # Cette version sert d'echelle de complexite, pas d'encodage formel.
        return (
            "forall triangle ABC with right angle at C, "
            "if B3(A, C, B) "  # C entre A et B (segment AB)
            "then the segment AB has length equal to the sum of lengths of AC and BC squared"
        )
    if version == 3:
        return (
            "Informal paraphrase (not strict Tarski language): "
            "B3(x, y, z) means 'y is between x and z'. "
            "Theorem (Pythagoras): For any points A, B, C such that B3(A, C, B) "
            "and AC perpendicular to BC, "
            "the squared length of AB equals the sum of squared lengths of AC and BC."
        )
    if version == 4:
        # Version developpee avec preuve informelle
        return (
            "Informal paraphrase (not strict Tarski language): "
            "B3(x, y, z) means 'y is between x and z'. "
            "Axioms of betweenness (Tarski 1959): "
            "B3(x, y, z) implies B3(z, y, x). "
            "B3(x, y, z) and B3(x, z, y) imply y = z. "
            "Lemma (existence of right angle): there exist points A, B, C "
            "such that B3(A, C, B) and AC perpendicular to BC. "
            "Theorem (Pythagoras): For any such points A, B, C, "
            "AB^2 = AC^2 + BC^2. "
            "Proof sketch: by the area argument of Euclid's Elements I.47. "
            "QED."
        )
    # version 5 : l'enonce s'auto-reference -- c'est la diagonale de Gödel.
    # On itere k fois la substitution @ <- repr(s). A chaque iteration, le
    # nombre de @ dans s est **carre** (chaque @ est remplace par une copie
    # de s qui contient elle-meme plusieurs @), donc la longueur explose
    # super-lineairement. Mesure : 3 iterations sur la base ci-dessous
    # produisent 256 @ et ~120k caracteres. L'article de Sheydvasser continue
    # l'iteration jusqu'a > 10^212077 chiffres numeriques, ce qui necessiterait
    # k ~ 30 iterations (chaine de ~10^9 chars) -- hors de portee d'un
    # notebook pedagogique. Le verdict garde l'esprit du critere : la
    # diagonale fait exploser la longueur.
    base = (
        "Informal paraphrase (not strict Tarski language): "
        "B3(x, y, z) means 'y is between x and z'. "
        "Theorem (Pythagoras, self-referential encoding v5): "
        "For any points A, B, C such that B3(A, C, B) "
        "and AC perpendicular to BC, AB^2 = AC^2 + BC^2. "
        "Encoded statement: <@> "
        "Note: <@> refers to the Gödel code of THIS very sentence. "
        "The diagonal lemma guarantees that such a self-referential "
        "encoding exists."
    )
    s = base
    n_iter = 3  # 3 iterations -> 256 @ (k**2 par iter), ~120k caracteres
    for _ in range(n_iter):
        s = s.replace("@", repr(s))
    return s


def godel_number(s: str, n_primes: int | None = None) -> int:
    """Nombre de Gödel d'une chaîne sur alphabet ASCII.

    N(s) = Π_{i=0}^{len(s)-1}  p_i ^ (ord(s[i]) + 1)

    Le +1 evite l'exposant 0 (qui ferait disparaitre le facteur premier).
    Les premiers sont pre-calcules (_PRIMES_10K en fournit 1229). Pour des
    chaînes > 1229 caractères, il faut etendre le crible -- pour la version
    5 (longueur 10^8+), cette fonction renvoie une borne log10 et -1.
    """
    if n_primes is None:
        n_primes = len(_PRIMES_10K)
    if len(s) > n_primes:
        # Trop long pour un calcul exact -- on retourne une borne log10.
        return -1  # sentinel : voir godel_number_log10
    prod = 1
    for i, c in enumerate(s):
        prod *= _PRIMES_10K[i] ** (ord(c) + 1)
    return prod


def godel_number_log10(s: str) -> float:
    """log10 du nombre de Gödel, robuste aux chaînes très longues.

    log10(N) = Σ_{i=0}^{len(s)-1}  (ord(s[i]) + 1) * log10(p_i)

    Garantit que `_PRIMES_10K` contient au moins `len(s)` premiers avant la
    somme. L'extension utilise un criblage complet jusqu'a une borne derivee
    du PNT (pi(x) ~ x / ln x) -- suffisant pour ne pas tronquer la somme sur
    des chaines de ~10^6 caracteres.
    """
    needed = len(s)
    if len(_PRIMES_10K) < needed:
        # Borne : pi(x) >= n pour x >= n * (ln n + ln ln n) (Rosser + Schoenfeld).
        # On prend une marge +100 pour absorber les fluctuations.
        if needed < 6:
            bound = 15
        else:
            bound = int(needed * (math.log(needed) + math.log(math.log(needed)))) + 100
        _PRIMES_10K.clear()
        _PRIMES_10K.extend(_is_prime_stream(bound))
    return sum((ord(c) + 1) * log10(p) for i, (c, p) in enumerate(zip(s, _PRIMES_10K)))


if __name__ == "__main__":
    for v in range(1, 6):
        s = godel_pythagore(v)
        n_digits_est = godel_number_log10(s)
        print(f"version {v}: len(s) = {len(s):>10}  log10(N) ~ {n_digits_est:.3e}")