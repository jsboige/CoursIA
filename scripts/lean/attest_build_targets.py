#!/usr/bin/env python3
"""Resout les CIBLES d'un `lake build` cible (organe d'attestation, #26699).

Pourquoi ce module existe
-------------------------
`scripts/lean/attest_local_build.py` lance `lake build` **sans cible** : il
construit donc TOUT le lac. Sur le lac `conway`, cela veut dire 8 802 cibles
(Mathlib comprise) et plusieurs heures -- trois essais du coordinateur le
15/11 ont tous expire (OOM a jobs=3, puis deux timeouts a jobs=1), alors que
la PR a attester (#25585) ne touche que **trois** fichiers `.lean` et six
lignes.

La cause n'est pas un reglage de parallélisme : c'est la **portee** du build.
Ce module resout, pour un diff donne, l'ensemble des modules Lean a
construire : les modules **touches**, leurs **jumeaux `_en`**, et leurs
**dependants** dans le lac. Le reste du lac n'est pas construit -- et ce qui
n'est pas construit est **nomme** dans l'attestation, jamais silent.

Ce qui est exclu, et pourquoi
-----------------------------
Un module **agregateur** (`Conway.lean`, `Conway/Life.lean`) n'importe que des
modules, sans porter la moindre commande : c'est un hub de re-export. Il est
dependant de tout ce qu'il importe, mais le construire ne prouverait rien de
plus que construire ses imports -- et cela ramenerait le build du lac
entier. Les agregateurs sont donc **ecartes** de l'ensemble des dependants,
et **listes** dans le rendu : la borne est visible, pas silencieuse.

Un fichier qui porte une **commande** (`attribute`, `notation`, `macro`,
`syntax`, `elab`, `deriving instance`, `#check`, `#eval`, `open ... in`) n'est
**pas** un agregateur (#26966) : ces commandes cassent des que l'import
qu'elles citent est renomme ou retire, donc un tel fichier doit etre
construit.

Et un fichier **non `.lean`** du lake touche (`lakefile.lean`,
`lakefile.toml`) force le **repli sur le lac entier** (#26966) : il change la
compilation de modules que le build cible ne construit pas.

La resolution est **pure** (lecture de fichiers) et **testee** : elle ne
depend d'aucun `lake`, d'aucun reseau, d'aucun etat de la machine.

Usage
-----
    from attest_build_targets import resolve_targets
    verdict = resolve_targets(lake_root, changed_paths, lake_prefix="<lake>/")
    verdict["targets"]      # les modules a passer a `lake build`

Les selecteurs de bibliotheques sont lus par l'organe canonique
`lake_selectors` (meme semantique que `Lake.Glob`) : le parseur local qui
vivait ici ne connaissait ni `.andSubmodules`, ni le sucre `` `X.*`` / ``
`X.+``, ni les lakefiles TOML, ni les commentaires -- et perdait des modules
sur 21 lakes du manifeste (#26812).
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

# L'organe canonique de lecture des selecteurs de bibliotheques Lake est
# `lake_selectors` : c'est lui qui connait les formes `Glob` reelles
# (`one`, `submodules`, `andSubmodules`, le sucre `` `X.*`` / `` `X.+``),
# qui masque les commentaires et qui lit les lakefiles TOML.
#
# Le parseur local qui vivait ici ne connaissait que `one` et `submodules` :
# sur 36 lakes du manifeste, il en oubliait 21 -- dont `knot` (1 module
# enumere sur 49) et `gametheory` (7 sur 70). Parmi ces 21 lakes, 6
# tombaient a zero module : l'enumeration y perdait tous les modules, pas
# seulement une partie. Consequence mesuree : toute
# PR touchant ces lakes retombait sur le build du lac ENTIER, et le verdict
#annonçait « aucun module Lean touche » (#26812). Un doublon d'organe
# etait la cause ; la reparation est de reutiliser l'organe, pas d'en ecrire
# un deuxieme (#24666).
sys.path.insert(0, str(Path(__file__).resolve().parent))

from lake_selectors import LakefileError, lake_selectors  # noqa: E402

#: Un `import Foo.Bar` (en tete de fichier ou dans le corps).
IMPORT_RE = re.compile(
    r"^[ \t]*import[ \t]+([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)",
    re.MULTILINE,
)

#: Lignes **compatibles** avec un agregateur : un hub de re-export. Tout le
#: reste est du contenu et doit etre construit (#26966).
#:
#: `import` importe ; `namespace` / `end` ouvrent et ferment un espace de
#: noms ; `open X` ouvre un espace de noms **sans** argument de commande.
#: `open X in` est une **commande** : elle agit sur la suite du fichier, donc
#: c'est du contenu.
AGGREGATOR_LINE_RE = re.compile(
    r"^(?:import[ \t]+\S.*"
    r"|namespace[ \t]+\S.*"
    r"|end\b.*"
    r"|open[ \t]+[A-Za-z_][A-Za-z0-9_'.]*[ \t]*)$"
)

#: `srcDir := "..."` (Lean) ou `srcDir = "..."` (TOML).
SRCDIR_RE = re.compile(r"srcDir[ \t]*(?::=|=)[ \t]*\"([^\"]+)\"")

#: Les NOMS de document d'un lake : un `README`, un `LICENSE`, un
#: `CHANGELOG`... Un fichier de ce nom ne change pas la compilation : c'est
#: une entree **prouvee documentaire**.
DOC_NOMS = ("readme", "notice", "licence", "license", "copying", "changelog",
            "contributing", "authors", "contributors", "code_of_conduct",
            "security", "governance", "citation")

#: Un nom de document, suivi au plus d'un suffixe : `README.md`,
#: `README.en.md`, `LICENSE-APACHE-2.0`...
DOC_RE = re.compile(
    r"^(?:" + "|".join(DOC_NOMS) + r")(?:[-_.].*)?$", re.IGNORECASE)


def est_documentaire(rel: str) -> bool:
    """Vrai si le fichier est un document PROUVE : il ne change pas la
    compilation du lac.

    La preuve est **stricte et fermee** : le nom du fichier est un nom de
    document connu (`README`, `LICENSE`, `CHANGELOG`...), suivi au plus
    d'un suffixe. Tout autre fichier non-`.lean` reste une entree de
    BUILD : il force le repli sur le lac entier, comme `lakefile.toml`,
    `lake-manifest.json` ou `lean-toolchain`.
    """
    nom = rel.replace("\\", "/").rsplit("/", 1)[-1]
    return bool(DOC_RE.match(nom))


def _read(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


def lake_root_of(repo_root: Path, project_path: str) -> Path:
    """Chemin absolu de la racine d'un lake, depuis son `project-path`."""
    return (repo_root / project_path).resolve()


def source_root(lake_root: Path) -> Path:
    """Racine des sources d'un lake : `srcDir` declare, sinon la racine.

    Le `srcDir` est lu dans le lakefile (Lean ou TOML) ; en cas d'absence ou
    de lecture impossible, la racine du lake est retenue (le defaut de Lake).
    """
    for name in ("lakefile.lean", "lakefile.toml"):
        text = _read(lake_root / name)
        if not text:
            continue
        match = SRCDIR_RE.search(text)
        if match:
            return (lake_root / match.group(1).replace("\\", "/")).resolve()
    return lake_root.resolve()


def selectors(lake_root: Path) -> list[tuple[str, str]]:
    """Les selecteurs de bibliotheques du lake, lus par l'organe canonique.

    Une entree est un couple `(kind, nom)` :

    - `one` -- ce module et lui seul ;
    - `sub` -- les modules **strictement** sous ce prefixe ;
    - `all` -- le prefixe **et** ses sous-modules.

    C'est la semantique de `Lake.Glob.matches` (`one n` : `n == m` ;
    `submodules n` : `n.isPrefixOf m && n != m` ; `andSubmodules n` :
    `n.isPrefixOf m`), et le sucre `` `X.*`` / `` `X.+`` la desugarise.

    Un lakefile illisible ou ambigu ne se devine pas : la liste est VIDE et
    l'appelant bascule sur le build integral.
    """
    try:
        return lake_selectors(lake_root)
    except (LakefileError, OSError):
        return []


def module_name_of(rel_to_src: str) -> str | None:
    """Chemin relatif a la racine des sources -> nom de module Lean."""
    if not rel_to_src.endswith(".lean"):
        return None
    stem = rel_to_src[: -len(".lean")]
    return stem.replace("/", ".")


def enumerate_modules(lake_root: Path) -> dict[str, str]:
    """Les modules du lake : nom de module -> chemin relatif a sa racine.

    L'ensemble suit les **selecteurs** du lakefile : un fichier `.lean` qui
    n'appartient a aucune bibliotheque declaree n'est pas un module
    constructible (le nommer a `lake build` echouerait). Un lake dont le
    lakefile est illisible donne un ensemble vide : l'appelant bascule sur le
    build integral.

    L'enumeration suit `Lake.Glob.forEachModuleIn` : `one` prend le seul
    fichier du prefixe, `sub` les fichiers **sous** le prefixe, `all` le
    prefixe et ces fichiers.
    """
    sels = selectors(lake_root)
    if not sels:
        return {}
    src = source_root(lake_root)
    modules: dict[str, str] = {}
    for kind, name in sels:
        rel_prefix = name.replace(".", "/")
        if kind == "one":
            candidate = src / (rel_prefix + ".lean")
            if candidate.is_file():
                modules[name] = candidate.relative_to(src).as_posix()
            continue
        if kind == "all":
            leaf = src / (rel_prefix + ".lean")
            if leaf.is_file():
                modules[name] = leaf.relative_to(src).as_posix()
        base = src / rel_prefix
        if base.is_dir():
            for candidate in sorted(base.rglob("*.lean")):
                rel = candidate.relative_to(src).as_posix()
                module = module_name_of(rel)
                if module:
                    modules[module] = rel
    return modules


def import_graph(lake_root: Path, modules: dict[str, str]) -> dict[str, set[str]]:
    """Graphe des imports **internes** au lake : module -> modules importes.

    Seuls les imports qui designent un module du lac sont retenus : les
    dependances externes (Mathlib) ne sont pas des modules de ce lac.
    """
    src = source_root(lake_root)
    graph: dict[str, set[str]] = {module: set() for module in modules}
    for module, rel in modules.items():
        text = _read(src / rel)
        for imported in IMPORT_RE.findall(text):
            if imported in modules and imported != module:
                graph[module].add(imported)
    return graph


def _strip_comments(text: str) -> str:
    """Retire les commentaires Lean : `--` (ligne) et `/- ... -/` (bloc,
    **imbrique**).

    Un commentaire n'est pas une declaration : un fichier dont le seul
    contenu est un commentaire n'a pas de corps a construire.
    """
    out: list[str] = []
    i = 0
    n = len(text)
    depth = 0
    in_string = False
    while i < n:
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                i += 2
                continue
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue
        if in_string:
            out.append(text[i])
            if text[i] == '"':
                in_string = False
            i += 1
            continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            i += 2
            continue
        if text[i] == '"':
            in_string = True
            out.append(text[i])
            i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def is_aggregator(text: str) -> bool:
    """Vrai si le fichier est un hub de re-export : des imports, rien d'autre.

    Un aggregateur ne porte **aucune commande** : il n'importe que des
    modules, sans declarer. Le construire ne prouve rien que ses imports ne
    prouvent pas -- et l'inclure dans les dependants ramene le build du lac
    entier.

    La definition est **stricte** (#26966) : un agregateur est un fichier
    dont **toutes** les lignes -- hors commentaires et lignes vides -- sont
    des `import`, `namespace`, `end` ou `open` sans argument de commande.
    Tout le reste est du **contenu** et doit etre construit : une commande
    comme `attribute [simp] foo`, `notation`, `macro`, `syntax`, `elab`,
    `deriving instance`, `#check`, `#eval` ou `open ... in` casse des que
    l'import qu'elle cite est renomme ou retire -- et un tel fichier, ecarte
    comme agregateur, ne serait jamais construit.
    """
    lines = [
        line.strip()
        for line in _strip_comments(text or "").splitlines()
    ]
    lines = [line for line in lines if line]
    if not lines:
        # Un fichier vide (ou fait de commentaires) n'a rien a construire.
        return True
    for line in lines:
        if not AGGREGATOR_LINE_RE.match(line):
            return False
    return True


def dependents_of(graph: dict[str, set[str]], roots: set[str]) -> set[str]:
    """Dependants TRANSITIFS des racines (fermeture sur les aretes inverses).

    Le calcul est une fermeture, pas un voisinage : un module qui depend
    d'un dependant depend aussi de la racine.
    """
    reverse: dict[str, set[str]] = {}
    for module, imports in graph.items():
        for imported in imports:
            reverse.setdefault(imported, set()).add(module)
    seen: set[str] = set()
    stack = list(roots)
    while stack:
        current = stack.pop()
        for dependent in reverse.get(current, ()):  # noqa: B007
            if dependent in seen:
                continue
            seen.add(dependent)
            stack.append(dependent)
    return seen


def sibling_en_module(modules: dict[str, str], module: str) -> str | None:
    """Le jumeau `_en` d'un module, s'il existe dans le lake.

    Convention i18n EPIC #4980 : `Foo.lean` et `Foo_en.lean` sont deux
    fichiers distincts, donc deux modules distincts. Toucher l'un doit
    construire l'autre : les deux doivent compiler.
    """
    rel = modules.get(module)
    if not rel:
        return None
    if rel.endswith("_en.lean"):
        base = rel[: -len("_en.lean")]
    else:
        base = rel[: -len(".lean")]
    for candidate in (base + "_en.lean", base + ".lean"):
        name = module_name_of(candidate)
        if name and name != module and name in modules:
            return name
    return None


def resolve_targets(lake_root: Path, changed_paths: list[str],
                    lake_prefix: str | None = None,
                    repo_root: Path | None = None) -> dict:
    """Les cibles de `lake build` pour les fichiers touches par le diff.

    `changed_paths` : chemins **relatifs au depot** (tels que rendus par
    l'API des fichiers d'une PR).

    `lake_prefix` : le prefixe du lake, relatif au depot, avec separateur
    final (par defaut, deduit de `repo_root`). Il est passe explicitement
    quand le lake est lu dans un **worktree** : le prefixe y est le meme
    (meme depot, meme arborescence), mais le chemin du lake n'y est plus
    sous `repo_root`.

    Rendu :
      ``ok``      -- les cibles sont exploitables (False : repli sur `all`) ;
      ``reason``  -- pourquoi le repli, quand il y a repli ;
      ``targets`` -- les modules a passer a `lake build` ;
      ``roots``   -- les modules touches (+ jumeaux `_en`) ;
      ``dependents`` -- les dependants retenus ;
      ``skipped_aggregators`` -- les agregateurs ecartes (la borne, nommee) ;
      ``unresolved`` -- les fichiers `.lean` touches qui ne sont pas des
      modules de ce lake (le repli est alors obligatoire) ;
      ``non_lean_touched`` -- les fichiers **non `.lean`** du lake touches
      qui sont des **entrees de build** (le repli est alors obligatoire :
      ces fichiers changent la compilation du lac) ;
      ``documentaire_touched`` -- les fichiers **non `.lean`** du lake
      touches qui sont **prouves documentaires** (un `README`, un
      `LICENSE`) : ils ne changent pas la compilation, ils ne forcent
      donc **pas** le repli ;
      ``module_count`` -- le nombre de modules du lake.
    """
    verdict = {
        "ok": False,
        "reason": "",
        "targets": [],
        "roots": [],
        "dependents": [],
        "skipped_aggregators": [],
        "unresolved": [],
        "non_lean_touched": [],
        "documentaire_touched": [],
        "module_count": 0,
    }
    modules = enumerate_modules(lake_root)
    verdict["module_count"] = len(modules)
    if not modules:
        verdict["reason"] = "modules du lake illisibles (lakefile absent ou non parse)"
        return verdict

    if lake_prefix is None:
        if repo_root is None:
            raise ValueError("lake_prefix ou repo_root est requis")
        lake_prefix = _relative_prefix(lake_root, repo_root)
    roots: set[str] = set()
    unresolved: list[str] = []
    non_lean: list[str] = []
    documentaire: list[str] = []
    for path in changed_paths:
        normalized = path.replace("\\", "/")
        if not normalized.startswith(lake_prefix):
            continue
        rel_to_lake = normalized[len(lake_prefix):]
        if not normalized.endswith(".lean"):
            # Un fichier **non `.lean`** du lake est touche : `lakefile.lean`
            # (options du build, globs, `moreLeanArgs`), `lakefile.toml`,
            # `lean-toolchain`... Ces fichiers ne sont pas des modules, mais
            # ils **changent la compilation** du lac entier. Un build cible
            # n'attesterait alors que les modules cites, pendant que le
            # changement peut en casser d'autres (#26966) : le repli sur le
            # lac entier est obligatoire, et sa raison est nommee.
            #
            # Exception **prouvee** : un DOCUMENT du lac (`README.md`,
            # `LICENSE-Apache-2.0`, `CHANGELOG.md`...). Un document ne
            # change pas la compilation : il ne doit pas forcer le repli.
            # La preuve est stricte (nom de document connu + extension de
            # document) ; tout le reste reste une entree de build.
            if est_documentaire(rel_to_lake):
                documentaire.append(normalized)
            else:
                non_lean.append(normalized)
            continue
        module = module_name_of(rel_to_lake)
        if module is None or module not in modules:
            unresolved.append(normalized)
            continue
        roots.add(module)

    verdict["documentaire_touched"] = sorted(documentaire)
    if non_lean:
        verdict["reason"] = (
            "fichier non-.lean touche dans le lake ({}) : un build cible "
            "n'attesterait que les modules cites, alors que ce fichier "
            "change la compilation du lac -- repli sur le lac entier".format(
                ", ".join(sorted(non_lean)[:5])
            )
        )
        verdict["non_lean_touched"] = sorted(non_lean)
        return verdict

    if not roots:
        # Les fichiers `.lean` touches qui ne sont PAS des modules du lake
        # sont la cause du repli : ils sont NOMMES. Les perdre ici
        # transformait une cause lisible (« ce fichier n'est pas un
        # module ») en un verdict trompeur (« aucun module touche »),
        # et c'est ce qui a fait chercher le defaut dans les globs au lieu
        # de le chercher ici (#26812).
        verdict["unresolved"] = sorted(unresolved)
        verdict["reason"] = (
            "fichier .lean touche hors module : {}".format(
                ", ".join(sorted(unresolved)[:5])
            )
            if unresolved
            else "aucun module Lean touche dans ce lake"
        )
        return verdict
    if unresolved:
        # Un fichier `.lean` touche qui n'est pas un module du lake : le
        # nommer a `lake build` echouerait, et l'ignorer masquerait un
        # changement. Le repli sur le build integral est la seule issue
        # honnete.
        verdict["reason"] = "fichier .lean touche hors module : {}".format(
            ", ".join(sorted(unresolved)[:5])
        )
        verdict["unresolved"] = sorted(unresolved)
        return verdict

    # Les jumeaux `_en` des modules touches : deux fichiers, deux modules.
    for module in sorted(roots):
        twin = sibling_en_module(modules, module)
        if twin:
            roots.add(twin)

    graph = import_graph(lake_root, modules)
    dependents = dependents_of(graph, roots)

    src = source_root(lake_root)
    skipped: list[str] = []
    kept: set[str] = set()
    for module in sorted(dependents):
        if module in roots:
            continue
        rel = modules.get(module)
        if rel and is_aggregator(_read(src / rel)):
            skipped.append(module)
            continue
        kept.add(module)

    verdict["ok"] = True
    verdict["roots"] = sorted(roots)
    verdict["dependents"] = sorted(kept)
    verdict["skipped_aggregators"] = skipped
    verdict["targets"] = sorted(roots | kept)
    return verdict


def _relative_prefix(lake_root: Path, repo_root: Path) -> str:
    """Prefixe du lake, relatif au depot, avec separateur final."""
    try:
        rel = lake_root.resolve().relative_to(repo_root.resolve()).as_posix()
    except ValueError:
        return ""
    return rel.rstrip("/") + "/"


# NOTE -- ce module est PUR : il resout des cibles, il ne COMPOSE aucune
# commande. Le payload de build (`lake build <cibles>`) est construit par
# l'organe qui la confie a `scripts/lean/lean_exec.py`, au point de la
# remise : c'est la seule forme que le garde
# `scripts/lean/check_lake_direct_invocation.py` accepte (liste de
# commande remise DIRECTEMENT a un conducteur de l'organe). Un litteral
# `["lake", "build"]` ici serait un argv de commande hors de la main de
# l'organe -- c'est-a-dire une voie directe, que le garde refuse.
