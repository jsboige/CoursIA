"""Adaptateur de fixtures : le codec natif du carnet 02, sans recopie.

Le carnet `Compression-02-HuffmanCanonique-Python.ipynb` definit son codec en
cellules de code melees a du code de demonstration (comptages, affichages,
assertions). Ce module extrait **les fonctions elles-memes** du notebook par
analyse AST — aucune longueur, aucun mot de code, aucune table n'est recopie
ici. Les tests confrontent ensuite ces fonctions au module Lean
`Compression_lean/SymbolCodec.lean` sur les memes tables.

Ce que l'adaptateur garantit, et ce qu'il ne garantit pas :

- il selectionne les cellules **par nom de fonction** (pas par index), donc une
  renumerotation du carnet ne le casse pas ;
- il n'execute que les `import` et les `def` de chaque cellule : le code de
  demonstration (variables `comptages`, `EXTRAIT_OCTETS`, impressions) n'est
  jamais evalue ;
- il n'invente rien : si une fonction attendue disparait du carnet, le module
  echoue explicitement au chargement au lieu de fournir un substitut.
"""

from __future__ import annotations

import ast
import json
import re
from pathlib import Path
from typing import Any, Callable

NOTEBOOK = Path(__file__).with_name("Compression-02-HuffmanCanonique-Python.ipynb")


def _cell_functions(source: str) -> set[str]:
    """Les noms de fonctions definies au premier niveau d'une cellule."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return set()
    return {
        node.name
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    }


def _definitions_only(source: str) -> str:
    """Le source d'une cellule, reduit a ses imports et definitions.

    Le code de demonstration d'une cellule peut referencer des variables
    definies ailleurs (`comptages`, `EXTRAIT_OCTETS`) : il ne doit pas etre
    execute. Les definitions, elles, ne sont executees que pour etre liees ;
    leurs corps ne tournent qu'a l'appel.
    """
    tree = ast.parse(source)
    kept = [
        node
        for node in tree.body
        if isinstance(node, (ast.Import, ast.ImportFrom, ast.FunctionDef,
                             ast.AsyncFunctionDef, ast.ClassDef))
    ]
    module = ast.Module(body=kept, type_ignores=[])
    return ast.unparse(module)


def _notebook_cells(path: Path) -> list[str]:
    data = json.loads(path.read_text(encoding="utf-8"))
    return [
        "".join(cell["source"])
        for cell in data["cells"]
        if cell["cell_type"] == "code"
    ]


def _load(names: set[str], path: Path = NOTEBOOK) -> dict[str, Any]:
    """Charge les fonctions nommees depuis les cellules qui les definissent.

    Toutes les cellules sont traversees : une cellule peut ne definir aucune
    fonction utile mais fournir l'`import heapq` dont le codec depend.
    """
    namespace: dict[str, Any] = {}
    for source in _notebook_cells(path):
        exec(_definitions_only(source), namespace)  # noqa: S102 - code du carnet, filtre
    missing = set(names) - set(namespace)
    if missing:
        raise RuntimeError(
            f"fonctions introuvables dans {path.name}: {sorted(missing)}"
        )
    return {name: namespace[name] for name in names}


_FUNCTIONS = _load({"huffman", "code_canonique", "table_decodage",
                    "encoder", "decoder"})

huffman: Callable[[dict[int, int]], tuple[dict[int, int], dict[int, str]]] = _FUNCTIONS["huffman"]
code_canonique: Callable[[dict[int, int]], dict[int, str]] = _FUNCTIONS["code_canonique"]
table_decodage: Callable[[dict[int, str], int], tuple[bytearray, bytearray]] = _FUNCTIONS["table_decodage"]
encoder: Callable[[bytes, dict[int, str]], str] = _FUNCTIONS["encoder"]
decoder: Callable[[str, bytearray, bytearray, int], bytes] = _FUNCTIONS["decoder"]


def canonical_lengths(weights: dict[int, int]) -> dict[int, int]:
    """Les longueurs de code que le carnet attribue a ces poids."""
    lengths, _ = huffman(weights)
    return lengths


def canonical_code(lengths: dict[int, int]) -> dict[int, str]:
    """Le code canonique du carnet pour ces longueurs."""
    return code_canonique(lengths)


def symbol_order(lengths: dict[int, int]) -> list[int]:
    """L'ordre total `(longueur, symbole)` que la canonisation applique.

    C'est la propriete que le module Lean nomme `canonPairs` : la longueur
    d'abord, l'indice de symbole pour departager les egalites.
    """
    return sorted(lengths, key=lambda s: (lengths[s], s))


def is_prefix_free(code: dict[int, str]) -> bool:
    """Vrai si aucun mot du code n'est prefixe d'un autre.

    Propriete verifiee par les tests, ecrite ici parce qu'elle porte sur le
    code produit et non sur une facon de le produire.
    """
    words = list(code.values())
    return not any(
        a != b and b.startswith(a) for a in words for b in words
    )


def is_injective(code: dict[int, str]) -> bool:
    """Vrai si deux symboles distincts n'ont jamais le meme mot."""
    words = list(code.values())
    return len(set(words)) == len(words)


def lean_demo_lengths(path: Path | None = None) -> list[int]:
    """Les longueurs de `demoLengths` lues dans le module Lean.

    Le fixture n'est pas recopie : il est lu a la source Lean, pour que les
    deux implementations soient confrontees au *meme* litteral.
    """
    lean = path or (Path(__file__).parent / "Compression_lean" / "SymbolCodec.lean")
    for line in lean.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if stripped.startswith("def demoLengths"):
            literal = stripped.split("![", 1)[1].split("]", 1)[0]
            return [int(part) for part in literal.split(",")]
    raise RuntimeError(f"demoLengths introuvable dans {lean}")


def _parse_ltree(tokens: list[str]) -> tuple:
    """Prefixe `.node`/`.leaf` -> arbre imbrique (les parentheses ne portent rien)."""
    head = tokens.pop(0)
    if head == ".leaf":
        return ("leaf", int(tokens.pop(0)))
    if head == ".node":
        return ("node", _parse_ltree(tokens), _parse_ltree(tokens))
    raise RuntimeError(f"jeton Lean inattendu : {head}")


def _tree_words(tree: tuple, prefix: tuple[bool, ...] = ()) -> dict[int, list[bool]]:
    """Le mapping symbole -> mot, avec `true` a gauche — la convention de `pairs`."""
    if tree[0] == "leaf":
        return {tree[1]: list(prefix)}
    words = _tree_words(tree[1], prefix + (True,))
    words.update(_tree_words(tree[2], prefix + (False,)))
    return words


def lean_demo_canon_words(path: Path | None = None) -> dict[int, list[bool]]:
    """Le code que l'arbre Lean `demoCanonTree` realise, symbole par symbole.

    L'arbre est **lu dans le module Lean** (sa definition est un terme clos) :
    le test compare donc la table du carnet au code que la preuve Lean fige,
    au lieu de comparer deux copies d'une meme constante.
    """
    lean = path or (Path(__file__).parent / "Compression_lean" / "SymbolCodec.lean")
    lines = lean.read_text(encoding="utf-8").splitlines()
    for index, line in enumerate(lines):
        if not line.strip().startswith("def demoCanonTree"):
            continue
        body = [line]
        cursor = index + 1
        while cursor < len(lines) and lines[cursor].strip():
            body.append(lines[cursor])
            cursor += 1
        joined = " ".join(body)
        if ":=" not in joined:
            raise RuntimeError(f"demoCanonTree sans ':= ' dans {lean}")
        tokens = re.findall(r"\.node|\.leaf|\d+", joined.split(":=", 1)[1])
        if not tokens:
            raise RuntimeError(f"demoCanonTree sans terme dans {lean}")
        return _tree_words(_parse_ltree(tokens))
    raise RuntimeError(f"demoCanonTree introuvable dans {lean}")


__all__ = [
    "canonical_code",
    "canonical_lengths",
    "code_canonique",
    "decoder",
    "encoder",
    "huffman",
    "is_injective",
    "is_prefix_free",
    "lean_demo_canon_words",
    "lean_demo_lengths",
    "symbol_order",
    "table_decodage",
]
