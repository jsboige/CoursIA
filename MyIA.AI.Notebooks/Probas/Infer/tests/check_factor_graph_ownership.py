"""Controle d'appartenance des factor graphs entre carnets Infer (AC2 de #25276).

Reproduit la mesure de la fuite mesuree le 2026-11-08 (issue #25276, PR #25263) :
un nom de variable distinctif d'un carnet — present dans le source d'UN SEUL des
carnets verses — ne doit apparaitre dans AUCUN label de noeud SVG d'un autre
carnet. Un graphe rendu par un autre carnet porte des identifiants etrangers au
carnet qui l'affiche : c'est ce signal que le detecteur nomme.

Ne sont des signaux NI les attributs XML du SVG (class, id...), NI les labels
framework Infer.NET (Gaussian, precision, scale...), NI les noms generes par le
compilateur (vdouble..., absents de tout source) : ils proviennent du moteur,
pas du modele d'un voisin.

Sortie 0 = aucune fuite croisee ; sortie 1 = au moins une fuite, listee avec
carnet victime, cellule, identifiant et carnet d'origine ; sortie 2 = erreur
d'entree.

Usage :
    python check_factor_graph_ownership.py [carnet.ipynb ...]

Sans argument, la famille Infer a factor graph est verifiee par defaut
(les cinq carnets touches par #25276, voisins du repertoire du script).
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

TEXT_LABEL_RE = re.compile(r"<text[^>]*>(.*?)</text>", re.DOTALL)
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
MIN_TOKEN_LEN = 5

# Labels et port names emis par Infer.NET/Graphviz pour TOUT modele, independants
# du source du carnet : ils ne prouvent aucune appartenance.
FRAMEWORK_LABELS = frozenset(
    {
        "Gaussian", "Gamma", "Sample", "Sum", "Product", "Multiply", "Max", "Min",
        "Bernoulli", "Discrete", "Dirichlet", "Vector", "VectorGaussian", "Beta",
        "Random", "Poisson", "Uniform", "Wishart", "And", "Not",
        "mean", "variance", "precision", "scale", "shape", "array", "Model",
        "condition", "value", "Value", "observed", "Observed", "evidence",
        "Evidence", "marginal", "Marginal",
        "innerProduct", "InnerProduct", "GetItems", "GetItem", "Subarray",
        "Concat", "Exp", "Log", "logistic", "sigmoid", "IsPositive", "Split",
        "Gate", "Copy", "Condition", "Power", "Ratio", "Difference", "Negate",
        # Prefixes de noms generes par le compilateur Infer.NET (v + type).
        "vdouble", "vVector", "vbool", "vDirichlet", "vGamma", "vGaussian",
    }
)

DEFAULT_NOTEBOOKS = (
    "Infer-02-Gaussian-Mixtures.ipynb",
    "Infer-05-Causal-Inference.ipynb",
    "Infer-11-Topic-Models.ipynb",
    "Infer-15-Recommenders.ipynb",
    "Infer-16-Sparse-Gaussian-Process.ipynb",
)


def cell_source(cell: dict) -> str:
    src = cell.get("source", [])
    return "".join(src) if isinstance(src, list) else src


def code_tokens(doc: dict) -> set[str]:
    """Identifiants presents dans les sources de cellules code du carnet."""
    tokens: set[str] = set()
    for cell in doc["cells"]:
        if cell.get("cell_type") == "code":
            tokens.update(TOKEN_RE.findall(cell_source(cell)))
    return tokens


def svg_label_tokens(html: str) -> set[str]:
    """Identifiants de modele extraits des labels de noeuds du SVG.

    Seuls les contenus <text>...</text> sont lus : les attributs XML
    (class="graph", <title>Model</title>) sont du boilerplate Graphviz.
    """
    tokens: set[str] = set()
    for label in TEXT_LABEL_RE.findall(html):
        for tok in TOKEN_RE.findall(label):
            if len(tok) >= MIN_TOKEN_LEN and tok not in FRAMEWORK_LABELS:
                tokens.add(tok)
    return tokens


def svg_outputs(doc: dict) -> list[tuple[int, str]]:
    """Sorties SVG par cellule : (index de cellule, texte html concatene)."""
    found: list[tuple[int, str]] = []
    for idx, cell in enumerate(doc["cells"]):
        if cell.get("cell_type") != "code":
            continue
        chunks: list[str] = []
        for out in cell.get("outputs", []):
            data = out.get("data", {})
            html = data.get("text/html")
            if html:
                text = "".join(html) if isinstance(html, list) else html
                if "<svg" in text:
                    chunks.append(text)
        if chunks:
            found.append((idx, "\n".join(chunks)))
    return found


def main(argv: list[str]) -> int:
    here = Path(__file__).resolve().parent
    infer_dir = here.parent
    if argv:
        paths = [Path(a).resolve() for a in argv]
    else:
        paths = [infer_dir / name for name in DEFAULT_NOTEBOOKS]

    docs: dict[str, dict] = {}
    for path in paths:
        if not path.exists():
            print(f"ERREUR: carnet introuvable: {path}")
            return 2
        docs[path.name] = json.loads(path.read_text(encoding="utf-8"))

    tokens_by_nb = {name: code_tokens(doc) for name, doc in docs.items()}
    svg_by_nb = {name: svg_outputs(doc) for name, doc in docs.items()}

    leaks = 0
    unattributed: set[str] = set()
    for victim_name, svg_cells in svg_by_nb.items():
        victim_source = tokens_by_nb[victim_name]
        others_source: set[str] = set()
        for other_name, other_tokens in tokens_by_nb.items():
            if other_name != victim_name:
                others_source |= other_tokens
        for cell_idx, svg_text in svg_cells:
            for tok in sorted(svg_label_tokens(svg_text)):
                if tok in victim_source:
                    continue
                if tok in others_source:
                    owner = next(
                        n for n, t in tokens_by_nb.items()
                        if n != victim_name and tok in t
                    )
                    print(
                        f"FUITE: {victim_name} cellule {cell_idx} affiche "
                        f"'{tok}', identifiant distinctif de {owner}"
                    )
                    leaks += 1
                else:
                    # Absent de tout source : nom genere par le compilateur,
                    # inattribuable — pas un signal d'appartenance.
                    unattributed.add(tok)

    # Controle positif (advisory) : chaque carnet a affichage doit rendre au
    # moins un identifiant de son PROPRE source — sinon l'affichage est
    # peut-etre un graphe generique, a verifier a la main.
    for name, svg_cells in svg_by_nb.items():
        own_hits = 0
        for _idx, svg_text in svg_cells:
            own_hits += sum(
                1 for tok in svg_label_tokens(svg_text) if tok in tokens_by_nb[name]
            )
        if svg_cells and own_hits == 0:
            print(
                f"AVERTISSEMENT: {name} affiche {len(svg_cells)} graphe(s) sans "
                f"aucun identifiant de son propre source — verifier a la main"
            )

    total_svgs = sum(len(v) for v in svg_by_nb.values())
    print(
        f"Carnets verifies: {len(docs)} | cellules SVG: {total_svgs} | "
        f"fuites croisees: {leaks}"
    )
    if leaks:
        print("VERDICT: FAIL — fuite croisee de factor graph")
        return 1
    print("VERDICT: OK — aucun identifiant distinctif ne fuite entre carnets")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
