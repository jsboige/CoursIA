#!/usr/bin/env python3
"""#17276 -- une assertion de test ne doit pas faire sortir un secret dans un log.

Le defaut mesure
----------------
Un test qui (1) exerce du code lisant un secret depuis un chemin **resolu au
runtime** (cwd, `Path.home()`, variable d'environnement) et (2) utilise une
assertion qui **interpole la valeur recue** dans son message d'echec, devient un
canal de fuite vers les logs CI -- qui sont souvent moins proteges que le depot.

Mesure du 2026-09-21, en ecrivant un controle negatif pour #17268 :

    self.assertIsNone(models._get_hf_token())
    E   AssertionError: '<jeton reel>' is not None

Le jeton n'a ete ni commite ni poste : l'egress est reste local a la sortie de
test. Mais le schema se rejoue partout ou les deux conditions sont reunies, et il
ne se declenche **que sur echec** -- jamais en regime nominal, et precisement
dans la situation ou l'on veut le plus de diagnostic.

Ce que ce garde regarde, et ce qu'il ne regarde PAS
---------------------------------------------------
Deux etages, et la distinction qui decide :

  INTERPOLE    `assertIsNone(x)` -> "<valeur> is not None" : la valeur sort.
               Idem `assertEqual`, `assertIn`, `assertNotEqual`, ...
  N'INTERPOLE  PAS `assertTrue(x is None)` -> "False is not true" : en echec, la
               valeur ne sort pas. C'est la forme de remplacement proposee, et
               elle ne doit **pas** declencher.

Le nom seul ne suffit pas : `token` a un sens legitime non-secret (jeton d'un
analyseur, variable de boucle sur des chaines). Mesure sur le corpus : un
detecteur par NOM seul donnait **1 faux positif sur 3 candidats** (33%), sur

    for token in ("sae", "state", "recon_mse"):
        self.assertIn(token, msg)

D'ou la separation par ORIGINE de la valeur, qui est le coeur de ce garde :

  LITTERAL  l'identifiant est lie a une constante (boucle sur tuple de chaines,
            affectation a un litteral) -> la valeur ne PEUT pas etre un secret.
  APPEL     la valeur vient d'un appel (`_get_hf_token()`, `os.getenv`,
            `read_text`, ...) -> elle PEUT etre un secret. Seul ce cas compte.

Et par CHAINAGE D'AFFECTATION, a portee de fonction : `tok = _get_hf_token()`
puis `assertTrue(tok is not None, f"...{tok}")` -- `tok` ne ressemble a rien et
aucune regle par nom ne l'attrape. Ce chainage n'est pas cosmetique : il
**recupere L122**, que le recensement par nom ratait purement et simplement
(`result = _get_hf_token()` puis `assertEqual(result, ...)`).

Ce que ce garde mesure, et ce qu'il ne peut PAS mesurer
-------------------------------------------------------
Distinction qui decide du §3 de l'issue, et qu'il faut poser proprement :

  VIOLATION DE CONTRAT  assertion interpolante dont l'argument vient d'un
                        appel et n'est pas lie a un litteral. Mecanique,
                        decidable par l'AST -> **3/3 sur le corpus**.
  DANGER REEL           la valeur peut effectivement etre un secret vivant.
                        Semantique -> **1/3 seulement**.

Sur les 3 sites : L129 est le defaut reel (sous
`patch.dict(os.environ, {}, clear=True)` -- le jeton vient alors du VRAI
environnement ou d'un fichier sur disque). L114 et L122 sont sous un
`patch.dict` qui **injecte un litteral** : le "secret" est ecrit dans le test
lui-meme et ne peut pas etre un vrai jeton -- mais le garde ne sait pas lire
cette difference. La distinguer demanderait d'analyser les `patch.dict`, soit
une seconde machine dont le cout en faux positifs n'est pas mesure, et dont
l'absence de faux positif ne serait donc pas etablie.

Consequence assumee : sur son etat mesure, le flux d'alerte de ce garde vaut
**1 signal pour 3 sites**. Il ne remplace donc PAS la regle de revue -- il la
double, en rougissant sur la PROCHAINE introduction. Un garde annonce sa limite
plutot que d'enfabriquer une precision qu'il n'a pas.

Cout mesure : 5.4 s pour 862 fichiers de test (AST pur, aucune dependance).
La mise a portee re-parcourt chaque fonction : ~2.5x le cout de la version a
portee fichier, qui etait 2.1 s -- et qui produisait 87.5% de faux positifs
(14 sites declenches par un seul `result = _get_hf_token()`).

Modes (convention `check_notebook_navlinks.py` / `check_docs_links.py`)
----------------------------------------------------------------------
    python check_assert_secret_egress.py            # scan, exit 1 si un site
    python check_assert_secret_egress.py --baseline # ecrit la baseline
    python check_assert_secret_egress.py --check    # exit 1 sur site NOUVEAU
    python check_assert_secret_egress.py --json     # sortie machine

La baseline porte les sites **deja connus** : le garde est donc vert sur l'etat
actuel et rouge sur la prochaine introduction. `--check` est le mode destine a
la CI ; le mode nu (sans `--check`) est le constat complet, utile en revue.

Ce garde ne remplace pas une revue : il couvre la forme *interpolante*, pas la
fuite par `print`/log/`assert` nu de pytest (dont l'introspection affiche aussi
les sous-expressions -- mesure separement, cf issue #17276).
"""
from __future__ import annotations

import argparse
import ast
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_BASELINE = Path(__file__).resolve().parent / "tests" / "baseline_assert_secret_egress.json"

# `assertTrue`/`assertFalse` n'impriment que le booleen, jamais la valeur recue :
# ce sont les deux seules formes d'assertion NON interpolantes de `unittest`.
NON_INTERPOLATING = frozenset({"assertTrue", "assertFalse"})

# Noms qui designent une matiere secrete.
SECRET_NAME = re.compile(
    r"(^|_)(api_?key|apikey|secret|password|passwd|credential|hf_token|"
    r"access_token|auth_token|bearer_token|token)$",
    re.IGNORECASE,
)
SECRET_SUBSTR = re.compile(r"hf_token|api_?key|_secret", re.IGNORECASE)

# Repertoires hors perimetre (vendores, archives, caches).
EXCLUDED_PARTS = frozenset({".lake", ".git", "_archives", "node_modules", ".venv"})


def identifiers(node: ast.AST) -> set[str]:
    """Noms portes par une expression : `Name.id`, `Attribute.attr`, et les
    litteraux chaines **passes a un appel**.

    Ces derniers sont necessaires parce qu'une cle de secret se nomme souvent
    dans une chaine : `os.getenv("HF_TOKEN")` n'expose aucun identifiant
    `HF_TOKEN`, seulement l'argument litteral de `getenv`. Sans cette
    collecte, la forme la plus courante de lecture de secret passerait le
    garde -- c'est un test qui l'a montre, pas une relecture.

    La collecte est volontairement LIMITEE aux litteraux situes DANS un appel :
    `assertEqual(x, "token")` compare une valeur litterale, ce n'est pas une
    cle de secret, et le signaler serait le faux positif que ce garde existe
    pour eviter.
    """
    found: set[str] = set()
    for sub in ast.walk(node):
        if isinstance(sub, ast.Name):
            found.add(sub.id)
        elif isinstance(sub, ast.Attribute):
            found.add(sub.attr)
    for sub in ast.walk(node):
        if isinstance(sub, ast.Call):
            for arg in sub.args:
                if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                    found.add(arg.value)
    return found


def secretish(names: set[str]) -> set[str]:
    return {n for n in names if SECRET_NAME.search(n) or SECRET_SUBSTR.search(n)}


def literal_bindings(bodies: list[list[ast.stmt]],
                     names: set[str]) -> set[str]:
    """Identifiants lies a une CONSTANTE dans ces portees.

    Deux formes suffisent a couvrir la mesure : la boucle sur un litteral (le
    cas `for token in ("sae", ...)`) et l'affectation a un litteral.

    Les portees recues sont celles de l'assertion ET de son englobant (le
    module) : un `API_KEY = "valeur-de-test"` au niveau module est une
    constante pour la methode qui l'utilise. En revanche on n'y met PAS les
    portees voisines -- un litteral affecte a `result` dans une autre methode
    ne doit pas innocenter le `result = _get_hf_token()` de celle-ci, ce qui
    serait le symetrique des 14 faux positifs mesures.
    """
    const: set[str] = set()
    for body in bodies:
        for node in scope_nodes(body):
            if isinstance(node, (ast.For, ast.comprehension)):
                targets = identifiers(node.target)
                if not (targets & names):
                    continue
                it = node.iter
                if isinstance(it, ast.Constant):
                    const |= targets
                elif isinstance(it, (ast.Tuple, ast.List, ast.Set)) and all(
                    isinstance(e, ast.Constant) for e in it.elts
                ):
                    const |= targets
            elif isinstance(node, (ast.Assign, ast.AnnAssign)):
                targets: set[str] = set()
                if isinstance(node, ast.Assign):
                    for t in node.targets:
                        targets |= identifiers(t)
                else:
                    targets |= identifiers(node.target)
                if not (targets & names) or node.value is None:
                    continue
                val = node.value
                if isinstance(val, ast.Constant) or (
                    isinstance(val, (ast.Tuple, ast.List, ast.Set))
                    and all(isinstance(e, ast.Constant) for e in val.elts)
                ):
                    const |= targets
    return const


def assertion_name(call: ast.Call) -> str | None:
    fn = call.func
    name = fn.attr if isinstance(fn, ast.Attribute) else (
        fn.id if isinstance(fn, ast.Name) else None
    )
    if name and name.startswith("assert"):
        return name
    return None


def interpolated_exprs(call: ast.Call) -> list[ast.AST]:
    """Expressions dont la VALEUR peut apparaitre dans le message d'echec.

    Deux sources, traitees separement parce qu'elles ne couvrent pas les memes
    formes d'assertion :

    1. **Les arguments positionnels** -- `unittest` compose son message d'echec
       a partir de la valeur recue (`assertIsNone(x)` -> "<valeur> is not
       None"), donc ils sortent en clair. SAUF pour `assertTrue`/`assertFalse`,
       dont la signature est `(expr, msg)`: le premier argument n'est jamais
       interpole, seul le message l'est.
    2. **Le message** -- positionnel (`args[1:]`) ou par mot-cle (`msg=`) selon
       la forme employee par l'auteur. Un
       `assertTrue(tok is not None, f"jeton lu: {tok}")` n'interpole rien par
       lui-meme, mais SON message interpole la valeur : exclure `assertTrue` en
       bloc laisserait passer cette fuite. Un test l'a montre.
    """
    name = assertion_name(call)
    exprs: list[ast.AST] = []
    if name is not None and name not in NON_INTERPOLATING:
        exprs.extend(call.args)
    else:
        # Signature `(expr, msg)` : le message suit l'expression.
        exprs.extend(call.args[1:])
    exprs.extend(kw.value for kw in call.keywords if kw.arg in (None, "msg"))
    return exprs


def _rel(path: Path) -> str:
    """Chemin d'affichage : relatif a la racine si possible, absolu sinon.

    Le repli n'est pas cosmetique : il rend `scan_file` utilisable sur un
    fichier hors du depot (les tests l'exercent sur des cas synthetiques), au
    lieu de lever sur un `relative_to` impossible.
    """
    try:
        return path.relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def scope_nodes(body: list[ast.stmt]):
    """Noeuds d'UNE portee, sans descendre dans les portees imbriquees.

    Une fonction est une portee ; l'oublier est ce qui a produit les 14 faux
    positifs mesures plus bas.
    """
    stack: list[ast.AST] = list(body)
    while stack:
        node = stack.pop()
        yield node
        if isinstance(
            node,
            (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda),
        ):
            continue
        stack.extend(ast.iter_child_nodes(node))


def secret_derived_names(body: list[ast.stmt]) -> set[str]:
    """Variables locales AFFECTEES, DANS CETTE PORTEE, depuis un secret.

    Sans ce chainage, le garde est contournable par le choix du nom : `tok =
    _get_hf_token()` puis `assertTrue(tok is not None, f"...{tok}")` -- `tok`
    ne ressemble a rien, et aucune regle par NOM ne peut l'attraper. C'est un
    test qui l'a montre, apres deux autres trous trouves de la meme facon.

    PORTEE, et c'est la mesure qui l'impose : la premiere version de cette
    fonction prenait l'arbre ENTIER. Sur le corpus, un seul
    `result = _get_hf_token()` (L121 de test_genai_stack_round4.py) a fait
    basculer 14 assertions d'AUTRES methodes -- `result` y valant tour a tour
    `profile_current()`, `check_fit(4096)`, `execute(args)` : **14 faux
    positifs sur 16 sites, soit 87.5%**. La meme regle restreinte a la portee
    de la fonction en produit **0**. Une variable locale est locale.

    La propagation reste a UN saut (l'affectation), pas une analyse de flot :
    elle couvre le cas mesure sans fermeture transitive dont le cout en faux
    positifs ne serait pas, lui aussi, mesure.
    """
    derived: set[str] = set()
    for node in scope_nodes(body):
        if not isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr)):
            continue
        value = node.value
        if value is None or not secretish(identifiers(value)):
            continue
        if isinstance(node, ast.Assign):
            for t in node.targets:
                derived |= identifiers(t)
        else:
            derived |= identifiers(node.target)
    return derived


def _scan_scope(body: list[ast.stmt], outer: list[ast.stmt], label: str,
                sites: list[dict]) -> None:
    """Ajoute les sites d'UNE portee, avec sa propre table de derivation."""
    derived = secret_derived_names(body)
    bodies = [outer, body] if body is not outer else [body]
    for node in scope_nodes(body):
        if not isinstance(node, ast.Call):
            continue
        name = assertion_name(node)
        if name is None:
            continue
        for expr in interpolated_exprs(node):
            names = identifiers(expr)
            hits = secretish(names) | (names & derived)
            if not (hits - literal_bindings(bodies, names)):
                continue
            sites.append(
                {
                    "file": label,
                    "line": node.lineno,
                    "assert": name,
                    "id": sorted(hits),
                    "expr": ast.unparse(expr)[:120],
                    "key": "%s::%s::%s::%s"
                    % (label, name, ",".join(sorted(hits)), ast.unparse(expr)),
                }
            )
            break


def scan_file(path: Path) -> list[dict]:
    """Sites d'un fichier : assertion interpolante + valeur d'ORIGINE SECRETE.

    Une valeur est porteuse de secret si le nom vient (1) d'une affectation a
    une expression porteuse de secret, DANS LA MEME PORTEE, ou (2) est secret
    par lui-meme ET n'est pas lie a un litteral. La regle (2) fait tomber le
    faux positif mesure (`token` en variable de boucle sur des chaines) ; la
    restriction de portee de (1) fait tomber les 14 autres.
    """
    try:
        source = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return []
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []

    label = _rel(path)
    sites: list[dict] = []
    module_body = tree.body
    _scan_scope(module_body, module_body, label, sites)
    for fn in ast.walk(tree):
        if isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
            _scan_scope(fn.body, module_body, label, sites)
    sites.sort(key=lambda s: (s["line"], s["assert"]))
    return sites


def test_files() -> list[Path]:
    return sorted(
        p
        for p in REPO_ROOT.rglob("*.py")
        if (p.name.startswith("test_") or p.name.endswith("_test.py"))
        and not any(part in EXCLUDED_PARTS for part in p.parts)
    )


def scan() -> list[dict]:
    sites: list[dict] = []
    for path in test_files():
        sites.extend(scan_file(path))
    return sites


def load_baseline(path: Path) -> list[str]:
    if not path.exists():
        return []
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return []
    return list(data.get("entries", []))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Detecte les assertions de test qui peuvent faire sortir un secret."
    )
    parser.add_argument("--baseline", action="store_true",
                        help="ecrit la baseline des sites actuels et sort 0")
    parser.add_argument("--check", action="store_true",
                        help="exit 1 seulement sur un site ABSENT de la baseline")
    parser.add_argument("--json", action="store_true", help="sortie machine")
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args(argv)

    sites = scan()
    keys = [s["key"] for s in sites]

    if args.baseline:
        DEFAULT_BASELINE.parent.mkdir(parents=True, exist_ok=True)
        DEFAULT_BASELINE.write_text(
            json.dumps(
                {
                    "note": (
                        "Sites connus de la classe #17276 (assertion interpolante "
                        "sur une valeur derivee d'un secret). Genere par "
                        "check_assert_secret_egress.py --baseline. La lecture de "
                        "ces sites -- combien sont des defauts reels, combien sont "
                        "des litteraux injectes par le test lui-meme -- est dans la "
                        "docstring du garde, pas ici : ce fichier est genere."
                    ),
                    "entries": sorted(keys),
                },
                indent=2,
                ensure_ascii=False,
            )
            + "\n",
            encoding="utf-8",
            newline="",
        )
        if not args.quiet:
            print("baseline ecrite : %s (%d site(s))" % (DEFAULT_BASELINE, len(keys)))
        return 0

    if args.json:
        print(json.dumps({"sites": sites, "count": len(sites)},
                         indent=2, ensure_ascii=False))
        return 0

    baseline = load_baseline(DEFAULT_BASELINE)
    known = set(baseline)
    new = [s for s in sites if s["key"] not in known]

    if args.check:
        if new:
            print("SITE(S) NOUVEAU(X) de la classe #17276 : %d" % len(new))
            for s in new:
                print("  %s:%d  %s  [%s]  %s"
                      % (s["file"], s["line"], s["assert"], ",".join(s["id"]), s["expr"]))
            print("\nUne assertion qui interpole la valeur peut ecrire un secret "
                  "reel dans les logs CI.")
            print("Forme qui n'interpole pas : assertTrue(x is None).")
            print("Si le site est legitime, l'ajouter a la baseline avec --baseline.")
            return 1
        if not args.quiet:
            print("OK: %d site(s) connu(s), 0 nouveau." % len(sites))
        return 0

    if not args.quiet:
        for s in sites:
            print("%s:%d  %s  [%s]  %s"
                  % (s["file"], s["line"], s["assert"], ",".join(s["id"]), s["expr"]))
        print("\n%d site(s) au total, dont %d absent(s) de la baseline."
              % (len(sites), len(new)))
    return 1 if sites else 0


if __name__ == "__main__":
    sys.exit(main())
