#!/usr/bin/env python3
"""Recensement des strategies QC qui dependent du nombre exact de barres rendues.

Contexte (#20286)
-----------------
Sur une demi-seance (cloture americaine a 13:00, New York), ``self.history(...)``
en resolution journaliere rend moins de barres que demandees : 105 pour 126
demandees le 2019-07-03 (mesure #20286, projet QC ``20286-SectorRotation-diag``).
Une garde ``len(series) < N`` qui suppose que la demande est servie en entier
ecarte alors le titre ; quand la garde porte sur l'ensemble des titres, le livre
part en defensif (SHY sur ``Cloud-SectorRotation-Momentum``, IEF sur
``Cloud-VolTargeting`` en version 3).

Le correctif est le meme partout : demander une **fenetre double** et garder les
``N`` dernieres barres. On peut alors perdre la moitie de la fenetre sans que
la garde ne change de verdict.

Ce script rend le recensement executable et reproductible. Il ne juge pas la
strategie : il mesure une dependance a la forme du fournisseur de donnees.

Classes
-------
``EXPOSE``   la garde suppose que la demande est servie en entier : meme
             expression de seuil et de demande, ou marge inferieure au
             raccourcissement mesure (21 barres, ``--shortfall``).
``RISQUE``   la marge absorbe le raccourcissement mesure, mais la demande
             reste inferieure au double du seuil : le code depend encore de la
             forme du fournisseur.
``PROTEGE``  la demande vaut au moins le double du seuil : perdre la moitie de
             la fenetre ne change pas le verdict de la garde.

``INCONNU``  la demande ou le seuil n'a pas pu etre evalue : l'organe ne
             devine pas, il le signale. Un INCONNU est un angle mort de
             l'instrument, pas un verdict sur la strategie.

Limite connue
--------------
L'outil mesure la dependance a la **longueur** de l'historique. Il ne detecte
pas le cas ou la serie est consommee sans etrelicee (fenetre qui se raccourcit
silencieusement sans ecarter le titre) : cela demande une analyse du
consommateur de la serie, hors perimetre ici.

Portee des constantes
---------------------
Les expressions sont evaluees sur les constantes **visibles depuis la
fonction** : constantes de module, de classe, attributs d'instance, valeurs par
defaut des parametres, variables locales de la fonction. Une variable locale
masque le reste (portee Python) : deux fonctions qui utilisent le meme nom
pour deux valeurs differentes restent distinctes (mesure : ``lookback`` vaut
278 dans un training et 26 dans un scoring).

Usage
-----
    python scripts/ci/check_qc_half_session_history.py                # tableau, exit 1 si EXPOSE
    python scripts/ci/check_qc_half_session_history.py --json         # sortie machine
    python scripts/ci/check_qc_half_session_history.py --all          # inclut les classes non EXPOSE
    python scripts/ci/check_qc_half_session_history.py --shortfall 5  # autre seuil de mesure
"""

from __future__ import annotations

import argparse
import ast
import json
import os
import sys

DEFAULT_PROJECTS = os.path.join("MyIA.AI.Notebooks", "QuantConnect", "projects")

# Cas justifies : le projet est mesure, mais la dependance est assumee et notee.
# (vide a ce jour : la reference du modele, Cloud-SectorRotation-Momentum, est
# protegee par la fenetre double de #20330 et reste donc visible au recensement.)
EXCEPTIONS = {}


def _num(node, consts):
    """Evalue une expression arithmetique sur des entiers connus, sinon None.

    Resout aussi les formes portees par la fenetre double canonique (#20330) :
    `self.MOM_WINDOWS[-1]` (index de liste constante, index negatif compris) et
    `max(self.MOM_WINDOWS)` (extremum d'une liste constante). Sans cela, les
    occurrences corrigees restaient INCONNU pour l'organe.
    """
    if node is None:
        return None
    if isinstance(node, ast.Constant) and isinstance(node.value, (int, float)) \
            and not isinstance(node.value, bool):
        return node.value
    if isinstance(node, ast.Attribute):
        return _scalar(consts.get(node.attr))
    if isinstance(node, ast.Name):
        return _scalar(consts.get(node.id))
    if isinstance(node, ast.Subscript):
        base = _seq(node.value, consts)
        if base is None:
            return None
        index = _num(node.slice, consts)
        if index is None or not isinstance(index, int):
            return None
        try:
            return base[index]
        except IndexError:
            return None
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) \
            and node.func.id in ("max", "min") and node.args:
        values = []
        for arg in node.args:
            seq = _seq(arg, consts)
            if seq is not None:
                values.extend(seq)
                continue
            scalar = _num(arg, consts)
            if scalar is None:
                return None
            values.append(scalar)
        if not values:
            return None
        return max(values) if node.func.id == "max" else min(values)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
        val = _num(node.operand, consts)
        if val is None:
            return None
        return -val if isinstance(node.op, ast.USub) else val
    if isinstance(node, ast.BinOp):
        left = _num(node.left, consts)
        right = _num(node.right, consts)
        if left is None or right is None:
            return None
        if isinstance(node.op, ast.Add):
            return left + right
        if isinstance(node.op, ast.Sub):
            return left - right
        if isinstance(node.op, ast.Mult):
            return left * right
        if isinstance(node.op, ast.FloorDiv):
            return left // right if right else None
    return None


def _scalar(value):
    """Valeur scalaire connue, ou None (une liste n'est pas un nombre)."""
    if isinstance(value, bool):
        return None
    if isinstance(value, (int, float)):
        return value
    return None


def _seq(node, consts):
    """Resout une expression en liste de nombres connus, sinon None."""
    if node is None:
        return None
    if isinstance(node, (ast.List, ast.Tuple)):
        values = []
        for element in node.elts:
            value = _num(element, consts)
            if value is None:
                return None
            values.append(value)
        return values
    if isinstance(node, ast.Attribute):
        value = consts.get(node.attr)
        return value if isinstance(value, list) else None
    if isinstance(node, ast.Name):
        value = consts.get(node.id)
        return value if isinstance(value, list) else None
    return None


def _over_request(count_node):
    """Vrai si la demande est explicitement un multiple (>= 2) d'une autre expression."""
    if isinstance(count_node, ast.BinOp) and isinstance(count_node.op, ast.Mult):
        factor = _num(count_node.left, {}) or _num(count_node.right, {})
        if factor is not None and factor >= 2:
            return True
    return False


def _target_name(target):
    """Nom d'une cible d'affectation : attribut de self, ou variable simple."""
    if isinstance(target, ast.Attribute) and isinstance(target.value, ast.Name) \
            and target.value.id == "self":
        return target.attr
    if isinstance(target, ast.Name):
        return target.id
    return None


def _assignments_in(body):
    """(cible, valeur, ligne) des affectations d'un corps, en ordre source.

    Ne descend ni dans une fonction ni dans une classe imbriquee : leurs corps
    ont leur propre portee.
    """
    found = []
    stack = list(body)
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef,
                             ast.Lambda)):
            continue
        if isinstance(node, ast.Assign) and len(node.targets) == 1:
            found.append((node.targets[0], node.value, node.lineno))
        for child in ast.iter_child_nodes(node):
            stack.append(child)
    found.sort(key=lambda item: item[2])
    return found


def _value_of(node, consts):
    """Valeur scalaire ou liste connue pour une expression, sinon None."""
    scalar = _num(node, consts)
    if scalar is not None:
        return scalar
    return _seq(node, consts)


def _defaults(func, consts):
    """Valeurs par defaut des parametres d'une fonction, resolues si constantes.

    Une fenetre de reglage est portee par le defaut d'un parametre
    (``def __init__(..., lookback=252)``) : sans cette resolution, l'attribut
    pose sur ``self`` reste inconnu de l'organe.
    """
    args = func.args
    out = {}
    positional = list(getattr(args, "posonlyargs", [])) + list(args.args)
    defaults = list(args.defaults)
    offset = len(positional) - len(defaults)
    for index, node in enumerate(defaults):
        if index + offset >= len(positional):
            continue
        value = _value_of(node, consts)
        if value is not None:
            out[positional[index + offset].arg] = value
    for arg, node in zip(args.kwonlyargs, args.kw_defaults):
        if node is None:
            continue
        value = _value_of(node, consts)
        if value is not None:
            out[arg.arg] = value
    return out


def _constants(tree):
    """Constantes de module, de classe et attributs d'instance.

    Les variables locales de fonction ne sont PAS resolues ici : deux
    fonctions peuvent utiliser le meme nom pour deux valeurs differentes
    (mesure : `lookback` vaut 278 dans un training et 26 dans un scoring) ;
    leur resolution est faite par fonction (_function_constants).
    """
    consts = {}
    for target, value, _ in _assignments_in(tree.body):
        name = _target_name(target)
        if name is None:
            continue
        resolved = _value_of(value, consts)
        if resolved is not None:
            consts[name] = resolved

    for cls in [node for node in ast.walk(tree) if isinstance(node, ast.ClassDef)]:
        class_consts = dict(consts)
        for target, value, _ in _assignments_in(cls.body):
            name = _target_name(target)
            if name is None:
                continue
            resolved = _value_of(value, class_consts)
            if resolved is not None:
                class_consts[name] = resolved
        consts.update(class_consts)

        # Attributs d'instance poses dans les methodes de la classe.
        for method in cls.body:
            if not isinstance(method, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            method_consts = dict(class_consts)
            method_consts.update(_defaults(method, class_consts))
            for target, value, _ in _assignments_in(method.body):
                if not (isinstance(target, ast.Attribute)
                        and isinstance(target.value, ast.Name)
                        and target.value.id == "self"):
                    continue
                resolved = _value_of(value, method_consts)
                if resolved is not None:
                    consts[target.attr] = resolved
    return consts


def _function_constants(func, base):
    """Constantes vues par une fonction : base + ses variables locales.

    Une locale masque la base (portee Python), ce qui evite qu'une variable
    homonyme d'une autre fonction fausse la mesure.
    """
    consts = dict(base)
    consts.update(_defaults(func, base))
    for target, value, _ in _assignments_in(func.body):
        if not isinstance(target, ast.Name):
            continue
        resolved = _value_of(value, consts)
        if resolved is not None:
            consts[target.id] = resolved
    return consts


def _history_calls(func, consts):
    """(nom cible, expression de demande, ligne) pour chaque self.history(...)."""
    out = []
    for node in ast.walk(func):
        if not isinstance(node, ast.Assign) or len(node.targets) != 1:
            continue
        target = node.targets[0]
        if not isinstance(target, ast.Name):
            continue
        value = node.value
        if not isinstance(value, ast.Call):
            continue
        func = value.func
        if not (isinstance(func, ast.Attribute) and func.attr == "history"):
            continue
        if len(value.args) < 2:
            continue
        out.append((target.id, value.args[1], node.lineno))
    return out


def _length_guards(func):
    """(nom mesure, seuil, operateur, ligne) pour chaque len(x) < N."""
    out = []
    for node in ast.walk(func):
        if not isinstance(node, ast.Compare) or len(node.ops) != 1:
            continue
        left = node.left
        if not (isinstance(left, ast.Call) and isinstance(left.func, ast.Name)
                and left.func.id == "len" and len(left.args) == 1):
            continue
        arg = left.args[0]
        if not isinstance(arg, ast.Name):
            continue
        op = node.ops[0]
        if not isinstance(op, (ast.Lt, ast.LtE)):
            continue
        out.append((arg.id, node.comparators[0], op, node.lineno))
    return out


def analyse_file(path, shortfall):
    """Renvoie la liste des occurrences mesurees dans un fichier."""
    with open(path, "r", encoding="utf-8") as handle:
        source = handle.read()
    try:
        tree = ast.parse(source)
    except SyntaxError as exc:
        return [{"classe": "ERREUR", "raison": "syntaxe : %s" % exc, "ligne": 0}]

    base_consts = _constants(tree)
    findings = []
    for node in ast.walk(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        consts = _function_constants(node, base_consts)
        histories = _history_calls(node, consts)
        if not histories:
            continue
        guards = _length_guards(node)
        for name, count_node, line in histories:
            matched = [g for g in guards if g[0] == name]
            if not matched:
                continue
            guard_name, threshold_node, op, guard_line = matched[0]
            requested = _num(count_node, consts)
            threshold = _num(threshold_node, consts)
            same_expression = ast.dump(count_node) == ast.dump(threshold_node)

            if _over_request(count_node):
                classe = "PROTEGE"
                raison = "demande = multiple (>= 2) du seuil"
            elif same_expression:
                classe = "EXPOSE"
                raison = "la garde reprend la demande : elle suppose la fenetre servie en entier"
            elif requested is not None and threshold is not None:
                marge = requested - threshold
                if marge < 0:
                    classe = "EXPOSE"
                    raison = "seuil (%s) superieur a la demande (%s)" % (threshold, requested)
                elif marge < shortfall:
                    classe = "EXPOSE"
                    raison = "marge de %s barres, sous le raccourcissement mesure (%s)" % (
                        marge, shortfall)
                elif requested >= 2 * threshold:
                    classe = "PROTEGE"
                    raison = "demande (%s) >= 2 x seuil (%s)" % (requested, threshold)
                else:
                    classe = "RISQUE"
                    raison = "marge de %s barres, demande (%s) < 2 x seuil (%s)" % (
                        marge, requested, threshold)
            else:
                classe = "INCONNU"
                raison = "expression non resolue : %s / %s" % (
                    ast.unparse(count_node), ast.unparse(threshold_node))

            findings.append({
                "classe": classe,
                "raison": raison,
                "fonction": node.name,
                "ligne": guard_line,
                "demande": ast.unparse(count_node),
                "seuil": ast.unparse(threshold_node),
                "demande_num": requested,
                "seuil_num": threshold,
            })
    return findings


def iter_projects(root, projects_dir):
    base = os.path.join(root, projects_dir)
    if not os.path.isdir(base):
        return
    for project in sorted(os.listdir(base)):
        project_dir = os.path.join(base, project)
        if not os.path.isdir(project_dir):
            continue
        for name in sorted(os.listdir(project_dir)):
            if not name.endswith(".py"):
                continue
            yield os.path.join(projects_dir, project, name), os.path.join(project_dir, name)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", default=".", help="racine du depot")
    parser.add_argument("--projects-dir", default=DEFAULT_PROJECTS)
    parser.add_argument("--shortfall", type=int, default=21,
                        help="raccourcissement mesure sur une demi-seance (barres)")
    parser.add_argument("--all", action="store_true",
                        help="affiche aussi les classes non EXPOSE")
    parser.add_argument("--strict", action="store_true",
                        help="code de sortie 1 si une occurrence EXPOSE subsiste "
                             "(mode garde ; par defaut, simple mesure)")
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)

    rows = []
    for rel_path, abs_path in iter_projects(args.root, args.projects_dir):
        if rel_path.replace(os.sep, "/") in EXCEPTIONS:
            continue
        for finding in analyse_file(abs_path, args.shortfall):
            finding["fichier"] = rel_path.replace(os.sep, "/")
            rows.append(finding)

    exposes = [r for r in rows if r["classe"] == "EXPOSE"]
    shown = rows if args.all else [r for r in rows if r["classe"] in ("EXPOSE", "ERREUR")]

    if args.as_json:
        print(json.dumps({
            "shortfall": args.shortfall,
            "total": len(rows),
            "expose": len(exposes),
            "rows": rows,
        }, ensure_ascii=False, indent=2))
    else:
        print("Recensement #20286 — projects QC, dependance a la longueur de history()")
        print("Raccourcissement mesure sur une demi-seance : %d barres" % args.shortfall)
        print()
        for row in sorted(shown, key=lambda r: (r["fichier"], r["ligne"])):
            print("%-8s %s:%d  %s()" % (row["classe"], row["fichier"], row["ligne"],
                                       row.get("fonction", "?")))
            if row.get("raison"):
                print("         %s" % row["raison"])
        print()
        counts = {}
        for row in rows:
            counts[row["classe"]] = counts.get(row["classe"], 0) + 1
        print("Total : %d occurrence(s) — %s" % (
            len(rows), ", ".join("%s %d" % (k, counts[k]) for k in sorted(counts)) or "aucune"))
        print("EXPOSE : %d" % len(exposes))
        if exposes:
            print()
            print("Projets a corriger :")
            for row in exposes:
                print("  %s" % row["fichier"])

    return 1 if (exposes and args.strict) else 0


if __name__ == "__main__":
    sys.exit(main())
