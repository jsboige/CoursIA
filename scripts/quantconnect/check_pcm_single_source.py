#!/usr/bin/env python3
"""Garde de source unique du PCM par poches (QuantConnect) — issue #20188, critère 2.

**Ce que le défaut était.** Le modèle de construction de portefeuille par
poches (`MultiStrategyPCM`) existait en neuf copies sous
`MyIA.AI.Notebooks/QuantConnect/`, en six variantes, et le correctif
`additive` (#19740) n'était présent que dans trois d'entre elles. Un
correctif posé sur une copie ne se propageait pas : rien ne signalait qu'une
nouvelle composite avait pris une variante sans le correctif.

**Ce que l'extraction a laissé.** `projects/SharedPCM/pouches_pcm.py` est
devenue la source canonique (`MultiStrategyPouchesPCM`) ; les composites
composites l'importent (`from SharedPCM.pouches_pcm import ...`). Deux
copies subsistent, pour deux raisons qui ne se corrigent pas par un
copier-coller :

- le kit pédagogique `03-Framework-Composite` est **autonome** (le code est
  copié dans `main.py` par l'apprenant, sans bibliothèque QC attachée) ;
- `projects/TrendWeatherPointInTime` est **gelé** : le registre de l'ombre
  (`ML-Training-Pipeline/shadow/registry.json`, entrée `tw-pit`) épingle
  l'empreinte de ses trois fichiers, et l'extraction ne touche pas une
  entrée gelée.

**Ce que fait cette garde.** Elle refuse qu'une **nouvelle** copie du modèle
apparaisse sans déclaration, et elle refuse qu'une copie **déclarée** soit
modifiée sans re-déclaration. Le manifeste
(`scripts/quantconnect/pcm_single_source.json`) porte la source canonique,
les copies déclarées et la raison de chaque déclaration.

**Ce qu'elle refuse aussi (invariant du défaut).** Le défaut `additive` du
canonique doit rester `False` : un consommateur qui omet le paramètre
hériterait sinon d'un mode qu'il n'a pas demandé — et, avec le défaut `True`
d'avant, `additive=True` sans `algorithm` était un `ValueError` chez un
consommateur qui ne l'aurait pas vu venir. Aucun consommateur ne doit
instancier le canonique sans passer `additive` explicitement : il hériterait
du défaut, et son comportement changerait si le défaut change. Les deux
contrôles sont syntaxiques (AST) : le défaut est lu dans la signature, et
la fourniture du paramètre est lue dans l'appel — par mot-clé **ou par
position** (la position de `additive` est elle-même lue dans la signature du
canonique ; un appel positionnel dont la position n'est pas établissable est
déclaré non certifiable, `CANONICAL_SIGNATURE_UNREADABLE`).

**Contrôle positif.** Une copie volontairement modifiée fait rougir la
garde : c'est le cas `DECLARATION_STALE` du corps de tests
(`scripts/quantconnect/tests/test_check_pcm_single_source.py`), qui crée un
arbre temporaire où une copie déclarée diffère de son empreinte et exige un
verdict rouge. Le cas nominal (arbre du dépôt) doit rester vert.

**Angle mort connu — le nom de classe est la signature.** La garde
reconnaît la famille par le **nom** de la classe (`MultiStrategy*PCM`) :
aucune analyse du corps ne rattache une classe à la famille. Une copie
renommée (`PouchesPCM`, ou n'importe quel nom qui ne se termine pas par
`PCM`) échappe donc au filtre, et une classe légitime hors famille
(`MultiStrategyOrchestrator`) est hors périmètre par construction — les
deux cas sont le même mécanisme. Un angle mort documenté n'est pas un
angle mort : une copie de la famille qui change de nom doit être déclarée
dans le manifeste, pas laissée au silence de la garde. Le cas mesuré :
un nom de classe constant est ce que la garantie « refuse qu'une nouvelle
copie apparaisse » recouvre.

**Limite — le `super()` doit être capturé, pas analysé.** La discrimination
« spécialisation vs copie » est **syntaxique** : un
`super().determine_target_percent(...)` compte comme délégation si son
**résultat est capturé** (affecté à une variable, retourné, passé en argument) ;
un même appel posé en statement nu (résultat jeté) ne compte pas, car la classe
recalcule alors sa propre valeur. La garde ne fait **aucune analyse de flux** :
une variable affectée puis jamais relue resterait exempte — la borne est
assumée, elle n'est pas comblée.

**Empreinte.** `sha256` du texte normalisé (fins de ligne ramenées à `\n`),
afin que l'empreinte soit la même sur un checkout Windows (`core.autocrlf`)
et sur un checkout Linux.

Usage :
    python scripts/quantconnect/check_pcm_single_source.py
    python scripts/quantconnect/check_pcm_single_source.py --json
    python scripts/quantconnect/check_pcm_single_source.py --root <checkout>
    python scripts/quantconnect/check_pcm_single_source.py --print-hashes
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MANIFEST = REPO_ROOT / "scripts" / "quantconnect" / "pcm_single_source.json"
SCAN_SUBTREE = "MyIA.AI.Notebooks/QuantConnect"

CANONICAL_CLASS = "MultiStrategyPouchesPCM"
# Methode canonique dont la specialisation legitime appelle super() : une
# sous-classe qui la redefinit SANS deleguer est une copie, pas une
# specialisation (le mode de defaillance #19740 : une variante sans le
# correctif `additive` reapparaît). La seule chaine des bases ne permettait
# pas cette discrimination (contournement « sonde A » du contre-audit).
TARGET_METHOD = "determine_target_percent"

# Famille du PCM par poches : le nom de classe suffit a designer le modele.
# `RiskParityPCM`, `MeanVariancePCM` ou `CappedPouchesPCM` sont d'autres
# modeles (ou une specialisation du canonique) : ils ne sont pas concernes.
# Les parentheses sont optionnelles : `class MultiStrategyPCM:` (sans base)
# est bien une definition de la famille — l'obligation de `\s*\(` la masquait.
CLASS_RE = re.compile(
    r"^class\s+(MultiStrategy\w*PCM)\s*(?:\(([^)]*)\))?", re.MULTILINE
)

# Codes de verdict : `blocking` = la garde rougit, `info` = signale sans
# bloquer (un carnet qui definit une classe de la famille est compte, non bloque).
CODES = {
    "CANONICAL_MISSING": "La source canonique du PCM par poches est absente du depot.",
    "CANONICAL_DRIFT": "La source canonique a change : le manifeste doit etre re-declare.",
    "UNDECLARED_COPY": "Une copie du PCM par poches existe hors de la source canonique, sans declaration.",
    "DECLARATION_STALE": "Une copie declaree a ete modifiee sans re-declaration.",
    "DECLARED_COPY_MISSING": "Une copie declaree n'existe plus : declaration a retirer.",
    "CLASS_MISMATCH": "Les classes declarees ne correspondent pas au contenu du fichier.",
    "CANONICAL_DEFAULT_UNSAFE": "Le defaut `additive` du canonique n'est pas `False` : un consommateur qui omet le parametre herite d'un mode qu'il n'a pas demande.",
    "CONSUMER_IMPLICIT_DEFAULT": "Un consommateur instancie le canonique sans passer `additive` : il herite du defaut, son comportement changerait si le defaut change.",
}


def normalized_sha256(path: Path) -> str:
    """sha256 du texte normalise (fins de ligne LF) — insensible a l'OS."""
    data = path.read_bytes()
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        text = data.decode("utf-8", errors="replace")
    text = text.replace("\r\n", "\n").replace("\r", "\n")
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _class_flags(node: ast.ClassDef) -> tuple[list[str], bool, bool]:
    """Noms des bases d'une classe + redéfinit TARGET_METHOD + appelle super().TARGET_METHOD ?"""
    base_names: list[str] = []
    for base in node.bases:
        if isinstance(base, ast.Name):
            base_names.append(base.id)
        elif isinstance(base, ast.Attribute):
            base_names.append(base.attr)
    redefines = False
    calls_super = False
    for stmt in node.body:
        if (
            isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef))
            and stmt.name == TARGET_METHOD
        ):
            redefines = True
            # Un `super().determine_target_percent(...)` posé en statement nu
            # (ast.Expr) JETTE le résultat : la classe recalcule alors sa propre
            # valeur — c'est une copie, pas une spécialisation (contre-exemple
            # de l'ajoint, #24627). La délégation ne compte que si le résultat
            # de super() est capturé. Limite assumée : aucune analyse de flux
            # (une variable affectée puis jamais relue resterait exempte).
            discarded = {
                id(expr.value)
                for expr in ast.walk(stmt)
                if isinstance(expr, ast.Expr)
            }
            for sub in ast.walk(stmt):
                if (
                    isinstance(sub, ast.Call)
                    and isinstance(sub.func, ast.Attribute)
                    and sub.func.attr == TARGET_METHOD
                    # Le récepteur doit être un appel `super(...)` : un appel
                    # `other.determine_target_percent(...)` ou
                    # `self.determine_target_percent(...)` ne délègue PAS au
                    # parent et ne compte pas comme une spécialisation.
                    and isinstance(sub.func.value, ast.Call)
                    and isinstance(sub.func.value.func, ast.Name)
                    and sub.func.value.func.id == "super"
                    # ... et son résultat doit être capturé, pas jeté en
                    # statement nu : un résultat jeté ne délègue pas.
                    and id(sub) not in discarded
                ):
                    calls_super = True
    return base_names, redefines, calls_super


def find_definitions(path: Path) -> list[dict]:
    """Classes de la famille definies dans un fichier .py.

    L'AST porte la discrimination que le regex ne pouvait pas : une sous-classe
    du canonique qui redéfinit `determine_target_percent` **sans** `super()`
    remplace la reconstruction canonique — c'est une copie, pas une
    specialisation. Le regex ne sert plus que de repli quand le fichier ne se
    parse pas.
    """
    text = path.read_text(encoding="utf-8", errors="replace")
    try:
        tree = ast.parse(text)
    except (SyntaxError, ValueError):
        tree = None
    if tree is not None:
        found = []
        for node in ast.walk(tree):
            if isinstance(node, ast.ClassDef) and re.match(
                r"MultiStrategy\w*PCM$", node.name
            ):
                base_names, redefines, calls_super = _class_flags(node)
                inherits = (
                    node.name != CANONICAL_CLASS
                    and CANONICAL_CLASS in base_names
                )
                is_copy = inherits and redefines and not calls_super
                found.append(
                    {
                        "class": node.name,
                        "line": node.lineno,
                        "inherits_canonical": inherits and not is_copy,
                        "redefines_target_without_super": is_copy,
                    }
                )
        return found
    found = []
    for match in CLASS_RE.finditer(text):
        name = match.group(1)
        bases = match.group(2) or ""
        found.append(
            {
                "class": name,
                "line": text[: match.start()].count("\n") + 1,
                "inherits_canonical": name != CANONICAL_CLASS
                and CANONICAL_CLASS in bases,
                "redefines_target_without_super": False,
            }
        )
    return found


def scan_copies(root: Path) -> list[dict]:
    """Tous les sites de definition de la famille, sous l'arborescence QC."""
    sites = []
    base = root / SCAN_SUBTREE
    if not base.is_dir():
        return sites
    for path in sorted(base.rglob("*.py")):
        if any(part.endswith(".lake") for part in path.parts):
            continue
        for definition in find_definitions(path):
            rel = path.relative_to(root).as_posix()
            sites.append({"path": rel, **definition})
    return sites


def scan_notebook_copies(root: Path) -> list[str]:
    """Carnets definissant une classe de la famille (informatif, non bloquant).

    Un carnet porte le code sous forme de JSON : les sources sont donc
    concatenees cellule par cellule avant d'appliquer le motif de classe.
    Seul un carnet qui *definit* une classe `MultiStrategy*PCM` est compte —
    pas tout carnet contenant la chaine.
    """
    base = root / SCAN_SUBTREE
    hits = []
    if not base.is_dir():
        return hits
    for path in sorted(base.rglob("*.ipynb")):
        try:
            notebook = json.loads(path.read_text(encoding="utf-8", errors="replace"))
        except (OSError, ValueError):
            continue
        chunks = []
        for cell in notebook.get("cells", []):
            source = cell.get("source", "")
            chunks.append("".join(source) if isinstance(source, list) else str(source))
        if CLASS_RE.search("\n".join(chunks)):
            hits.append(path.relative_to(root).as_posix())
    return hits


def canonical_additive_default(path: Path) -> tuple[str, object]:
    """Etat du parametre `additive` du canonique.

    Retourne (etat, valeur) :
      ("default", True/False) — le parametre a un defaut booleen litteral ;
      ("default", None)       — le defaut n'est pas une constante booleenne ;
      ("required", None)      — le parametre est exige, sans defaut ;
      ("absent", None)        — le parametre n'existe pas, ou le fichier ne
                                 se parse pas (les deux font echouer la
                                 garde : fail-CLOSED).
    """
    try:
        tree = ast.parse(path.read_text(encoding="utf-8", errors="replace"))
    except (OSError, SyntaxError, ValueError):
        return ("absent", None)
    for node in ast.walk(tree):
        if not (isinstance(node, ast.ClassDef) and node.name == CANONICAL_CLASS):
            continue
        for sub in node.body:
            if isinstance(sub, ast.FunctionDef) and sub.name == "__init__":
                args = sub.args
                index = None
                for position, arg in enumerate(args.args):
                    if arg.arg == "additive":
                        index = position
                        break
                if index is None:
                    return ("absent", None)
                first_default = len(args.args) - len(args.defaults)
                if index < first_default:
                    return ("required", None)
                default = args.defaults[index - first_default]
                if isinstance(default, ast.Constant) and isinstance(default.value, bool):
                    return ("default", default.value)
                return ("default", None)
    return ("absent", None)


def additive_positional_index(path: Path) -> int | None:
    """Position de `additive` parmi les arguments de `__init__` du canonique.

    Renvoie l'index du parametre dans la liste des arguments (index 0 =
    `self`), ou None quand la position ne peut pas etre etablie : classe
    sans `__init__`, signature illisible, ou `*args` present — dans ce
    dernier cas la correspondance positionnelle est ambigue.

    L'index sert a lever un angle mort de la garde des consommateurs : un
    appel `MultiStrategyPouchesPCM(allocations, rebalance, False)` passe
    `additive` en positionnel. Signaler ce code correct serait un faux
    positif sur du code valide (reserve de la revue Hermes sur #25924).
    """
    try:
        tree = ast.parse(path.read_text(encoding="utf-8", errors="replace"))
    except (OSError, SyntaxError, ValueError):
        return None
    for node in ast.walk(tree):
        if not (isinstance(node, ast.ClassDef) and node.name == CANONICAL_CLASS):
            continue
        for sub in node.body:
            if not (isinstance(sub, ast.FunctionDef) and sub.name == "__init__"):
                continue
            if sub.args.vararg is not None:
                return None  # `*args` : correspondance positionnelle ambigue
            for position, arg in enumerate(sub.args.args):
                if arg.arg == "additive":
                    return position
            return None
    return None


def scan_implicit_consumers(
    root: Path, canonical_rel: str, additive_index: int | None = None
) -> list[dict]:
    """Consommateurs qui instancient le canonique SANS passer `additive`.

    Un consommateur qui n'ecrit pas le parametre herite du defaut du
    canonique : si le defaut change, son comportement change aussi, et
    personne ne le voit. C'est l'invariant que #20188 veut tenir (« chaque
    projet garde son comportement actuel »).

    `additive` passe en positionnel compte comme passe : la position du
    parametre est lue dans la signature du canonique
    (`additive_positional_index`), et un appel dont le nombre d'arguments
    positionnels atteint cette position n'est pas signale — c'etait un faux
    positif sur du code correct (reserve Hermes sur #25924). Si la position
    ne peut pas etre etablie, aucun appel positionnel n'est signale : la
    garde ne peut pas certifier l'invariant dans ce cas, et le dit
    (`CANONICAL_SIGNATURE_UNREADABLE`).

    Bornes assumees : un appel qui passe `**kwargs` n'est pas compte (le
    parametre peut y etre fourni) ; un appel dont le symbole est aliase
    n'est pas vu non plus — l'angle mort du nom de symbole, le meme que
    celui de la famille de classes.
    """
    base = root / SCAN_SUBTREE
    hits: list[dict] = []
    if not base.is_dir():
        return hits
    for path in sorted(base.rglob("*.py")):
        rel = path.relative_to(root).as_posix()
        if rel == canonical_rel:
            continue
        try:
            tree = ast.parse(path.read_text(encoding="utf-8", errors="replace"))
        except (OSError, SyntaxError, ValueError):
            continue
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            func = node.func
            if isinstance(func, ast.Name):
                name = func.id
            elif isinstance(func, ast.Attribute):
                name = func.attr
            else:
                continue
            if name != CANONICAL_CLASS:
                continue
            if any(keyword.arg is None for keyword in node.keywords):
                continue  # **kwargs : le parametre peut etre fourni ailleurs
            if any(keyword.arg == "additive" for keyword in node.keywords):
                continue
            if additive_index is not None and len(node.args) >= additive_index:
                continue  # `additive` passe en positionnel : il est fourni
            if additive_index is None and node.args:
                continue  # position non etablie : ne pas signaler du code correct
            hits.append({"path": rel, "line": node.lineno})
    return hits


def analyse(root: Path, manifest_path: Path) -> dict:
    findings = []
    # Empreintes pleines (declaree + actuelle) : la « cle » qui permet de
    # re-declarer un manifeste — le message de finding est tronque a 12
    # caracteres, seul le rapport JSON / --print-hashes porte l'empreinte
    # complete (contournement « sonde §2 » : CANONICAL_DRIFT / DECLARATION_STALE
    # etaient inlevables, aucune empreinte n'etait publiee).
    hashes = {}
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        return {
            "verdict": "ERROR",
            "findings": [
                {
                    "code": "MANIFEST_UNREADABLE",
                    "path": manifest_path.as_posix(),
                    "detail": str(exc),
                }
            ],
            "canonical": None,
            "declared_copies": [],
            "notebook_copies": [],
        }

    canonical = manifest.get("canonical", {})
    canonical_rel = canonical.get("path", "")
    declared = {entry["path"]: entry for entry in manifest.get("declared_copies", [])}

    sites = scan_copies(root)
    notebook_copies = scan_notebook_copies(root)

    # 1. La source canonique est presente, unique, et conforme a son empreinte.
    canonical_path = root / canonical_rel if canonical_rel else None
    canonical_sites = [s for s in sites if s["path"] == canonical_rel]
    if not canonical_path or not canonical_path.is_file():
        findings.append(
            {
                "code": "CANONICAL_MISSING",
                "path": canonical_rel,
                "detail": "fichier absent du checkout",
            }
        )
    else:
        if len(canonical_sites) != 1:
            findings.append(
                {
                    "code": "CANONICAL_MISSING",
                    "path": canonical_rel,
                    "detail": "%d definitions de la famille dans le fichier canonique" % len(canonical_sites),
                }
            )
        digest = normalized_sha256(canonical_path)
        hashes[canonical_rel] = {
            "declared": canonical.get("sha256"),
            "actual": digest,
        }
        if canonical.get("sha256") and digest != canonical["sha256"]:
            findings.append(
                {
                    "code": "CANONICAL_DRIFT",
                    "path": canonical_rel,
                    "detail": "empreinte actuelle %s, empreinte declaree %s"
                    % (digest[:12], canonical["sha256"][:12]),
                }
            )
        declared_classes = set(canonical.get("classes", []))
        found_classes = {s["class"] for s in canonical_sites}
        if declared_classes and found_classes != declared_classes:
            findings.append(
                {
                    "code": "CLASS_MISMATCH",
                    "path": canonical_rel,
                    "detail": "declare %s, trouve %s"
                    % (sorted(declared_classes), sorted(found_classes)),
                }
            )

    # 2. Chaque copie declaree existe, declare les bonnes classes, et son
    #    contenu est celui que la declaration decrit.
    for rel, entry in sorted(declared.items()):
        path = root / rel
        if not path.is_file():
            findings.append(
                {
                    "code": "DECLARED_COPY_MISSING",
                    "path": rel,
                    "detail": "declaration a retirer du manifeste",
                }
            )
            continue
        digest = normalized_sha256(path)
        hashes[rel] = {
            "declared": entry.get("sha256"),
            "actual": digest,
        }
        if entry.get("sha256") and digest != entry["sha256"]:
            findings.append(
                {
                    "code": "DECLARATION_STALE",
                    "path": rel,
                    "detail": "empreinte actuelle %s, empreinte declaree %s"
                    % (digest[:12], entry["sha256"][:12]),
                }
            )
        found_classes = {s["class"] for s in sites if s["path"] == rel}
        declared_classes = set(entry.get("classes", []))
        if declared_classes and found_classes != declared_classes:
            findings.append(
                {
                    "code": "CLASS_MISMATCH",
                    "path": rel,
                    "detail": "declare %s, trouve %s"
                    % (sorted(declared_classes), sorted(found_classes)),
                }
            )

    # 3. Aucune copie non declaree.
    for site in sites:
        rel = site["path"]
        if rel == canonical_rel or rel in declared:
            continue
        if site.get("inherits_canonical"):
            # Une specialisation legitime du canonique n'est pas une copie :
            # elle delegue la reconstruction a super() (cf _class_flags).
            continue
        if site.get("redefines_target_without_super"):
            detail = (
                "class %s (ligne %d) — specialisation du canonique qui redéfinit "
                "%s sans super() : c'est une copie, declarer la copie ou deleguer"
                % (site["class"], site["line"], TARGET_METHOD)
            )
        else:
            detail = (
                "class %s (ligne %d) — declarer la copie ou importer le canonique"
                % (site["class"], site["line"])
            )
        findings.append(
            {
                "code": "UNDECLARED_COPY",
                "path": rel,
                "detail": detail,
            }
        )

    # 4. Le defaut du canonique est sur (`additive=False`) et aucun
    #    consommateur n'en herite : changer le defaut ne peut alors changer
    #    le comportement d'aucun projet qui ne l'a pas demande.
    additive_index = None
    if canonical_path and canonical_path.is_file():
        state, value = canonical_additive_default(canonical_path)
        if not (state == "default" and value is False):
            detail = {
                "required": "parametre `additive` exige, sans defaut "
                "(attendu `additive=False`)",
                "absent": "parametre `additive` absent du canonique "
                "(attendu `additive=False`)",
            }.get(
                state,
                "defaut `additive` = %s (attendu `additive=False`)" % value,
            )
            findings.append(
                {
                    "code": "CANONICAL_DEFAULT_UNSAFE",
                    "path": canonical_rel,
                    "detail": detail,
                }
            )
        # Position positionnelle de `additive` : sans elle, la garde ne peut
        # pas distinguer « passe en positionnel » de « omis » sur un appel
        # positionnel. On ne le devine pas : on le dit (fail-CLOSED), plutot
        # que de laisser l'invariant non verifie en silence.
        additive_index = additive_positional_index(canonical_path)
        if additive_index is None:
            findings.append(
                {
                    "code": "CANONICAL_SIGNATURE_UNREADABLE",
                    "path": canonical_rel,
                    "detail": "position positionnelle de `additive` non "
                    "etablie (classe sans `__init__`, signature illisible ou "
                    "`*args`) : la garde ne peut pas certifier l'invariant "
                    "du defaut sur les appels positionnels",
                }
            )
    for hit in scan_implicit_consumers(root, canonical_rel, additive_index):
        findings.append(
            {
                "code": "CONSUMER_IMPLICIT_DEFAULT",
                "path": hit["path"],
                "detail": "instancie %s sans passer `additive` (ligne %d) : "
                "il herite du defaut, son comportement suivrait un changement "
                "de defaut" % (CANONICAL_CLASS, hit["line"]),
            }
        )

    blocking = [f for f in findings if f["code"] != "INFO"]
    return {
        "verdict": "OK" if not blocking else "FAIL",
        "findings": findings,
        "canonical": canonical_rel,
        "declared_copies": sorted(declared),
        "notebook_copies": notebook_copies,
        "hashes": hashes,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--root",
        default=str(REPO_ROOT),
        help="racine du depot (contient MyIA.AI.Notebooks/...)",
    )
    parser.add_argument(
        "--manifest",
        default=str(DEFAULT_MANIFEST),
        help="manifeste des declarations",
    )
    parser.add_argument("--json", action="store_true", help="sortie structuree")
    parser.add_argument(
        "--print-hashes",
        action="store_true",
        help="afficher les empreintes normalisees (pleines) du canonique et des "
        "copies declarees, pour re-declaration du manifeste",
    )
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    manifest_path = Path(args.manifest).resolve()

    if args.print_hashes:
        try:
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        except (OSError, ValueError) as exc:
            print("manifeste illisible : %s" % exc, file=sys.stderr)
            return 2
        rels = [manifest.get("canonical", {}).get("path", "")]
        rels += [entry["path"] for entry in manifest.get("declared_copies", [])]
        for rel in rels:
            if not rel:
                continue
            path = root / rel
            if path.is_file():
                print("%s  %s" % (rel, normalized_sha256(path)))
            else:
                print("%s  (absent du checkout)" % rel)
        return 0

    report = analyse(root, manifest_path)

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        print("Garde de source unique du PCM par poches — #20188 critere 2")
        print("Source canonique : %s" % (report["canonical"] or "(absente)"))
        print("Copies declarees  : %d" % len(report["declared_copies"]))
        if report["notebook_copies"]:
            print(
                "Carnets definissant une classe de la famille (informatif, non "
                "bloquant) : %d" % len(report["notebook_copies"])
            )
        if report["verdict"] == "OK":
            print("VERDICT: OK — aucune copie non declaree, aucune declaration perimee.")
        elif report["verdict"] == "ERROR":
            print("VERDICT: ERROR — le manifeste est illisible : la garde ne peut pas statuer.")
        else:
            print("VERDICT: FAIL")
            for finding in report["findings"]:
                print(
                    "  [%s] %s — %s (%s)"
                    % (
                        finding["code"],
                        finding["path"],
                        finding.get("detail", ""),
                        CODES.get(finding["code"], ""),
                    )
                )

    if report["verdict"] == "ERROR":
        return 2
    return 0 if report["verdict"] == "OK" else 1


if __name__ == "__main__":
    sys.exit(main())
