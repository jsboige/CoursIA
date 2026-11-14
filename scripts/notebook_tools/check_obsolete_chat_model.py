"""Garde #22783 : aucun appel de chat ne doit cibler un modele de chat obsolete.

Regle (issue #22783, consigne du mainteneur 26/10) : l'execution d'un carnet
ne doit pas cibler un modele de chat obsolete ; la cible par defaut est le
vLLM local (Swift), le repli est le modele courant du mapping
``docs/genai/model-mapping-openai.md``. Ce script est l'organe de detection
statique de cette regle : il ROUGIT (exit 1) quand un site d'appel chat
resout, par analyse bornee inter-cellules, vers un identifiant de la liste
obsolete chat.

Les trois categories de #22783 et ce que l'organe en fait :

  EXECUTION     un appel chat (``*.chat.completions.create`` / ``.parse``,
                ``*.responses.create``, ``*ChatCompletion.create`` legacy,
                ``dspy.LM(...)``, ``ChatOpenAI(...)``, ou HTTP brut
                ``requests.post`` / ``httpx.post`` / ``urllib.request.
                urlopen`` dont l'URL cible ``*/chat/completions``) dont
                l'argument ``model`` (pour l'HTTP brut, dans le corps
                ``json=``/``data=``) resout vers un identifiant obsolete ->
                FINDING, exit 1.
  DOCUMENTATION une mention en CHAINE LITTERALE de code NON consommee par
                un appel chat -> advisory ``DOC-MENTION`` sans effet sur
                l'exit : la prose qui garde un modele obsolete doit le
                declarer par un marqueur explicite ``# obsolescence: DOC``
                (ou equivalent reconnu, voir ``DOC_MARKER_PATTERNS``).
                L'organe ne DEDUIT PAS le statut documentaire : il exige le
                marqueur. Les commentaires (ignores par l'AST) et les
                cellules markdown/raw (non scannees) ne produisent jamais
                rien.
  SPECIFIQUE    modeles TTS / transcribe / realtime / embeddings
                (``gpt-4o-mini-tts*``, ``gpt-4o-transcribe*``,
                ``gpt-4o-mini-transcribe``, ``whisper-*``, ``tts-1*``,
                ``text-embedding-*``, ...) -> jamais signales :
                l'appariement est EXACT (jamais par prefixe -- un prefixe
                ``gpt-4o`` accuserait a tort ``gpt-4o-mini-tts``), et ces
                familles ne figurent pas dans la liste obsolete chat.

Resolution bornee inter-cellules, dans l'ordre d'execution du carnet :

  * affectation litterale           ``llm_model = "gpt-4o-mini"``
  * defaut d'environnement          ``m = os.getenv("M", "gpt-4o-mini")``
    (le defaut declare dans la source est le seul chemin statiquement
    visible : il est juge comme une cible ; une variable d'environnement
    qui le surcharge a l'execution est invisible -- limite declaree)
  * alias de variable               ``m2 = llm_model``
  * cle de dictionnaire litteral    ``cfg["test_model"]``
  * parametre avec defaut           ``def f(model="gpt-4o-mini")`` puis
                                    ``create(model=model)``
  * attribut d'instance             ``self.llm_model`` via ``__init__`` et
                                    les instanciations de la classe

Cas fondateur (mesure, triage c.6428439365) :
``GenAI/Audio/04-Applications/04-5-LiveCoding-LLM-Music.ipynb`` -- cell 1
definit ``llm_model = "gpt-4o-mini"``, les cellules 20 et 33 appellent
``client.chat.completions.create(model=llm_model, ...)`` et la cellule 36
passe par ``MusicSession(llm_model, ...)`` puis
``create(model=self.llm_model, ...)``. Trois findings attendus.

Un marqueur ``# obsolescence: DOC`` N'EXONERE JAMAIS un appel chat reel :
il n'est consulte que pour le tier advisory des mentions non consommees.
Les temoins negatifs calibres sur le triage : la ``test_model`` du carnet
``00-3-API-Endpoints-Configuration`` (configuration seulement imprimee et
sondee via ``/models``) reste silencieuse, le ``dspy.LM`` propose en
markdown du ``22c_DSPy_Prompt_Compile`` n'est pas vu (markdown), et les
modeles TTS ``gpt-4o-mini-tts`` ne sont jamais accuses.

LIMITES DECLAREES (pas de pretention d'analyse dynamique exhaustive) :

  * Python uniquement. Cellules non-Python (magics ``#!csharp`` etc.),
    cellules brutes et markdown : non scannees, comptees dans les stats.
    Le cas Semantic-fleet (wrapper .NET du sous-module) se resout par
    lecture de l'organe source (``Program.cs`` au gitlink), pas par ce
    garde.
  * Modules ``.py`` du depot : scannables (une unite par module, sans
    report inter-cellules) quand la ligne de commande les nomme ou les
    atteint par un dossier. Le garde CI, lui, reste borne aux carnets
    (``iterate_paths=["**.ipynb"]`` dans le registre fast-lane, incident
    #13220) : l'extension de perimetre du garde est une decision separee,
    pas un effet de bord de cette option.
  * Les appels situes dans un corps de fonction sont resolus a l'etat du
    carnet au point de DEFINITION, avec reprise sur l'etat final si le nom
    n'etait pas encore lie -- pas a chaque appel runtime.
  * Un parametre de fonction SANS defaut n'est pas trace a ses sites
    d'appel. Un modele dynamique (f-string, calcul, retour de fonction)
    est rapporte ``unresolved``, jamais accuse.
  * Dictionnaires : seule la CLE DIRECTE d'un dictionnaire litteral plat
    (valeurs chaines) resout ; les dictionnaires imbriques ne sont pas
    suivis. La LISTE DE DICTIONNAIRES (``BATTERY = [{...}, {...}]``) est
    suivie depuis #23387 : ``BATTERY[i]["cle"]`` et ``for cfg in BATTERY:``
    puis ``cfg["cle"]`` resolvent chaque entree, et une entree obsolete est
    ACCUSEE (la boucle l'execute, donc le site est atteignable) ; seul
    l'index dynamique reste non resolu. Une batterie dont une entree n'est
    pas resoluble statiquement n'est pas suivie du tout (pas de resolution
    partielle devinee).
  * ``self.X`` : toute instanciation de la classe resolvant X vers un
    modele obsolete produit le finding (approximation documentee, sans
    desambiguation multi-instances).
  * Les sorties commises (outputs) ne sont pas scannees : ce garde police
    le chemin d'execution de la SOURCE ; l'honnetete des sorties releve
    de C.2 / re-execution (regle 6).

Exit codes : 0 = rien a signaler ; 1 = au moins un FINDING ;
2 = erreur d'exploitation (fichier introuvable, JSON invalide, git).
"""

from __future__ import annotations

import argparse
import ast
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from urllib.parse import urlsplit

# ---------------------------------------------------------------------------
# Constantes de la regle
# ---------------------------------------------------------------------------

#: Identifiants de CHAT obsoletes -- table de correspondance de
#: docs/genai/model-mapping-openai.md (lignes chat, familles principal,
#: heritage, mini, nano). Appariement EXACT, jamais par prefixe.
OBSOLETE_CHAT_MODELS: frozenset[str] = frozenset({
    # chat -- principal
    "gpt-4", "gpt-4-turbo", "gpt-4o", "gpt-4o-2024-08-06", "gpt-4.1",
    # chat -- heritage
    "gpt-3.5", "gpt-3.5-turbo",
    # chat -- mini / nano
    "gpt-4o-mini", "gpt-4.1-mini", "gpt-4.1-nano",
})

#: Snapshot date d'une base obsolete (``gpt-4o-mini-2024-07-18`` suit sa
#: base). Les variantes datees des familles SPECIFIQUES ne matchent pas :
#: ``gpt-4o-mini-tts-2025-03-20`` -> base ``gpt-4o-mini-tts``, absente de
#: la liste chat.
DATE_SNAPSHOT_RE = re.compile(r"-\d{4}-\d{2}-\d{2}$")

#: Marqueurs documentaires reconnus pour le tier advisory (equivalents du
#: canonique ``# obsolescence: DOC``). Ils n'exonerent jamais un appel chat.
DOC_MARKER_PATTERNS = tuple(re.compile(p, re.IGNORECASE) for p in (
    r"obsolescence\s*:\s*doc\b",
    r"#\s*obsolescence\b",
    r"#\s*mod[eè]le\s+obsol[eè]te\b",
    r"#\s*obsolete\b",
))

#: Magics de cellule .NET / non-Python (noyau interactive).
NON_PYTHON_MAGIC_RE = re.compile(r"^#!\s*(\w+)")
PYTHON_MAGICS = {"python", "python3"}
IPYTHON_MAGIC_LINE_RE = re.compile(r"^(%|!|\?)")


# ---------------------------------------------------------------------------
# Structures
# ---------------------------------------------------------------------------

@dataclass
class Binding:
    """Valeur statique liee a un nom (litteral, defaut d'env, ou inconnue)."""
    value: str | None
    kind: str            # "literal" | "env_default" | "unresolved"
    origin: str          # chaine humaine citee dans le finding
    node_id: int | None = None  # id() du noeud Constant d'origine


UNRESOLVED = Binding(None, "unresolved", "non resolu")

#: Sentinelle d'absence (distingue "pas de binding precedent" d'une valeur None).
_ABSENT = object()


@dataclass
class ClassInfo:
    """Ce qu'on sait d'une classe definie dans le carnet."""
    init_params: list = field(default_factory=list)   # [(nom, Binding|None)]
    self_from_params: dict = field(default_factory=dict)  # attr -> param
    self_literals: dict = field(default_factory=dict)     # attr -> Binding


@dataclass
class Ctx:
    """Contexte lexical pendant la marche."""
    cell_index: int
    func_name: str | None = None
    func_params: dict | None = None   # nom -> Binding | None (sans defaut)
    class_name: str | None = None
    locals: dict = field(default_factory=dict)       # nom -> Binding
    local_dicts: dict = field(default_factory=dict)  # nom -> {cle: Binding}
    multi_dicts: dict = field(default_factory=dict)  # nom -> [{cle: Binding}, ...]
    local_dict_model: dict = field(default_factory=dict)  # nom -> node "model"


@dataclass
class PendingSelfSite:
    """Site d'appel chat avec model=self.X, resolu apres la marche."""
    cell_index: int
    cell_id: str
    line: int
    site: str
    class_name: str
    attr: str
    path: str


@dataclass
class RetryNameSite:
    """Site dont le nom n'etait pas lie au point de definition : repris
    contre l'etat final du carnet."""
    cell_index: int
    cell_id: str
    line: int
    site: str
    name: str
    path: str


# ---------------------------------------------------------------------------
# Aides AST
# ---------------------------------------------------------------------------

def attr_chain(node: ast.AST) -> list[str]:
    """Chaine d'attributs d'une expression (``client.chat...create`` ->
    ["client", "chat", "completions", "create"]). Vide si la base n'est pas
    un simple Name."""
    parts: list[str] = []
    while isinstance(node, ast.Attribute):
        parts.append(node.attr)
        node = node.value
    if isinstance(node, ast.Name):
        parts.append(node.id)
    parts.reverse()
    return parts


def iter_code_nodes(root: ast.AST):
    """Sous-arbre de ``root`` SANS descendre dans les portees imbriquees
    (fonctions, classes, lambda) : elles sont visitees comme instructions
    a part entiere, avec leur propre contexte."""
    stack = list(ast.iter_child_nodes(root))
    while stack:
        node = stack.pop()
        yield node
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.ClassDef, ast.Lambda)):
            stack.extend(ast.iter_child_nodes(node))


def _dict_model_entry(node: ast.AST) -> ast.AST | None:
    """Node de la valeur de la cle "model" d'un littéral dict plat, ou None."""
    if not isinstance(node, ast.Dict):
        return None
    for key, value in zip(node.keys, node.values):
        if isinstance(key, ast.Constant) and key.value == "model":
            return value
    return None


def classify_chat_call(call: ast.Call, dspy_imported: bool) -> tuple[str, bool] | None:
    """Classe un Call en site chat -> (libelle, model_positionnel_bool).

    ``model_positionnel_bool`` dit si le premier argument positionnel est le
    modele (vrai pour l'API OpenAI chat et les constructeurs, faux sinon).
    """
    parts = attr_chain(call.func)
    if not parts:
        return None
    if len(parts) >= 3 and tuple(parts[-3:]) == ("chat", "completions", "create"):
        return "chat.completions.create", True
    if len(parts) >= 3 and tuple(parts[-3:]) == ("chat", "completions", "parse"):
        return "chat.completions.parse", True
    if len(parts) >= 2 and tuple(parts[-2:]) == ("responses", "create"):
        return "responses.create", True
    if len(parts) >= 2 and tuple(parts[-2:]) == ("ChatCompletion", "create"):
        return "ChatCompletion.create", True
    if parts and parts[-1] == "ChatOpenAI":
        return "ChatOpenAI", True
    if len(parts) == 2 and parts == ["dspy", "LM"]:
        return "dspy.LM", True
    if len(parts) == 1 and parts == ["LM"] and dspy_imported:
        return "dspy.LM", True
    # HTTP brut (forme non-SDK, #25072) : requests.post / httpx.post /
    # urllib.request.urlopen dont l'URL cible */chat/completions. Le model
    # n'est PAS l'argument positionnel (c'est l'URL) : positional=False,
    # extraction du "model" dans le corps (json=/data=) via _http_model_node.
    if (tuple(parts[-2:]) in (("requests", "post"), ("httpx", "post"))
            or tuple(parts[-3:]) == ("urllib", "request", "urlopen")):
        url = call.args[0] if call.args else next(
            (kw.value for kw in call.keywords if kw.arg == "url"), None)
        if (tuple(parts[-3:]) == ("urllib", "request", "urlopen")
                and isinstance(url, ast.Call)
                and attr_chain(url.func)[-1:] == ["Request"]):
            url = url.args[0] if url.args else next(
                (kw.value for kw in url.keywords if kw.arg == "url"), None)
        if targets_chat_completions(url):
            return "http.chat.completions", False
    return None


def targets_chat_completions(node: ast.AST | None) -> bool:
    """Retourne vrai si l'URL contient explicitement la route chat.

    Pour les f-strings, seule la partie litterale est examinee :
    ``f"{base}/chat/completions"`` est reconnu, alors qu'un endpoint
    dynamique sans cette route reste hors perimetre.
    """
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        template = node.value
    elif isinstance(node, ast.JoinedStr):
        # Garder les separateurs query/fragment entre segments litteraux,
        # meme si une interpolation les separe du texte qui suit.
        template = "".join(value.value if isinstance(value, ast.Constant)
                           and isinstance(value.value, str) else "{variable}"
                           for value in node.values)
    else:
        return False
    try:
        path = urlsplit(template).path
    except ValueError:
        return False
    return path.rstrip("/").endswith("/chat/completions")


def model_arg_node(call: ast.Call, positional: bool) -> ast.AST | None:
    for kw in call.keywords:
        if kw.arg == "model":
            return kw.value
    if positional and call.args:
        return call.args[0]
    return None


def normalize_model(value: str) -> str:
    """Normalise un identifiant : trim + retrait du prefixe fournisseur
    (``openai/gpt-4o-mini`` -> ``gpt-4o-mini``)."""
    v = value.strip()
    if "/" in v:
        v = v.rsplit("/", 1)[-1]
    return v


def is_obsolete_chat_model(value: str) -> bool:
    model = normalize_model(value)
    if model in OBSOLETE_CHAT_MODELS:
        return True
    base = DATE_SNAPSHOT_RE.sub("", model)
    return base != model and base in OBSOLETE_CHAT_MODELS


def has_doc_marker(source: str) -> bool:
    return any(p.search(source) for p in DOC_MARKER_PATTERNS)


def cell_kind(source: str) -> tuple[str, ast.Module | None]:
    """Classe une cellule : ("python", tree) | ("non_python", None) |
    ("unparsed", None). Les magics IPython (% ! ?) sont retires avant parse."""
    magic_lang = None
    stripped: list[str] = []
    for line in source.splitlines():
        if not stripped and not line.strip():
            continue  # lignes vides de tete
        if not stripped:
            m = NON_PYTHON_MAGIC_RE.match(line.strip())
            if m and m.group(1).lower() not in PYTHON_MAGICS:
                magic_lang = m.group(1)
        if IPYTHON_MAGIC_LINE_RE.match(line.strip()):
            stripped.append(f"# {line}")  # neutralisee, conserve le numero de ligne
        else:
            stripped.append(line)
    if magic_lang is not None:
        return f"non_python[{magic_lang}]", None
    try:
        return "python", ast.parse("\n".join(stripped))
    except SyntaxError:
        return "unparsed", None


# ---------------------------------------------------------------------------
# Scanner d'un carnet
# ---------------------------------------------------------------------------

class NotebookScanner:
    """Marche bornee inter-cellules d'un notebook Python."""

    def __init__(self, path: str):
        self.path = path
        self.module_values: dict[str, Binding] = {}
        self.dict_values: dict[str, dict[str, Binding]] = {}
        #: Nom d'un dict littéral -> node de l'entree "model" (HTTP brut
        #: ``json=<nom>``, #25072) ; le version scope local vit dans Ctx.
        self.dict_model_nodes: dict[str, ast.AST] = {}
        #: Batteries ``NAME = [{cle: valeur}, ...]`` (liste de dictionnaires) :
        #: chaque entree est une table cle -> Binding (forme #23387 point 3).
        self.multi_dict_values: dict[str, list[dict[str, Binding]]] = {}
        self.class_infos: dict[str, ClassInfo] = {}
        self.class_attr_values: dict[str, dict[str, list[Binding]]] = {}
        self.findings: list[dict] = []
        self.doc_mentions: list[dict] = []
        self.doc_marked_cells = 0
        self.unresolved: list[dict] = []
        self.pending_self: list[PendingSelfSite] = []
        self.retry_names: list[RetryNameSite] = []
        self.consumed_node_ids: set[int] = set()
        self.doc_candidates: list[tuple[int, int, str]] = []  # (node, cell, value)
        self.dspy_imported = False
        self.stats = {"code_cells": 0, "python_cells": 0,
                      "non_python_cells": 0, "unparsed_cells": 0,
                      "chat_sites": 0}
        self._cell_sources: dict[int, str] = {}
        self._ids: dict[int, str] = {}

    # -- entree -----------------------------------------------------------

    def scan(self, cells: list[dict]) -> None:
        self._ids = {i: str(cell.get("id", ""))
                     for i, cell in enumerate(cells)}
        for index, cell in enumerate(cells):
            if cell.get("cell_type") != "code":
                continue
            self.stats["code_cells"] += 1
            src = cell.get("source", "")
            source = "".join(src) if isinstance(src, list) else str(src)
            self._cell_sources[index] = source
            kind, tree = cell_kind(source)
            if kind == "python":
                self.stats["python_cells"] += 1
                if re.search(r"^\s*(import\s+dspy|from\s+dspy\b)", source, re.M):
                    self.dspy_imported = True
                self.visit_block(tree.body, Ctx(cell_index=index))
            elif kind.startswith("non_python"):
                self.stats["non_python_cells"] += 1
            else:
                self.stats["unparsed_cells"] += 1
        self._finalize()

    def scan_python_source(self, source: str) -> None:
        """Scanne un module ``.py`` : une seule unite, pas d'inter-cellules.

        Le module est traite comme une cellule unique (index 0) : la meme
        marche bornee s'applique (liaison au niveau module, defauts de
        parametres, attributs d'instance via ``__init__``), sans le report
        inter-cellules qui n'a pas de sens hors carnet. Les commentaires
        restent ignores par l'AST ; un module non parsable est compte
        ``unparsed_cells`` et jamais accuse.
        """
        self.stats["code_cells"] += 1
        self._cell_sources[0] = source
        kind, tree = cell_kind(source)
        if kind == "python":
            self.stats["python_cells"] += 1
            if re.search(r"^\s*(import\s+dspy|from\s+dspy\b)", source, re.M):
                self.dspy_imported = True
            self.visit_block(tree.body, Ctx(cell_index=0))
        elif kind.startswith("non_python"):
            self.stats["non_python_cells"] += 1
        else:
            self.stats["unparsed_cells"] += 1
        self._finalize()

    # -- marche des instructions -------------------------------------------

    def visit_block(self, stmts: list[ast.stmt], ctx: Ctx) -> None:
        for stmt in stmts:
            self.visit_stmt(stmt, ctx)

    def visit_stmt(self, stmt: ast.stmt, ctx: Ctx) -> None:
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
            self.handle_def(stmt, ctx)
            return
        if isinstance(stmt, ast.ClassDef):
            self.handle_class(stmt, ctx)
            return
        if isinstance(stmt, ast.For):
            self.handle_for(stmt, ctx)
            return
        if isinstance(stmt, ast.Assign):
            self.handle_assign(stmt, ctx)
            return
        if isinstance(stmt, ast.AnnAssign) and stmt.value is not None:
            self.handle_annassign(stmt, ctx)
            return
        # Generique : scan des expressions hors sous-blocs, recursion des
        # corps (If/Try/For/While/With/Match...).
        stmt_lists: list[list[ast.stmt]] = []
        expr_nodes: list[ast.AST] = []
        for _name, value in ast.iter_fields(stmt):
            if isinstance(value, list):
                sub_stmts = [x for x in value if isinstance(x, ast.stmt)]
                others = [x for x in value
                          if isinstance(x, ast.AST)
                          and not isinstance(x, ast.stmt)]
                if sub_stmts:
                    stmt_lists.append(sub_stmts)
                expr_nodes.extend(others)
            elif isinstance(value, ast.AST) and not isinstance(value, ast.stmt):
                expr_nodes.append(value)
        for node in expr_nodes:
            self.scan_expr(node, ctx)
        for sub in stmt_lists:
            self.visit_block(sub, ctx)

    def handle_def(self, stmt, ctx: Ctx) -> None:
        params: dict[str, Binding | None] = {}
        a = stmt.args
        positional = list(a.posonlyargs) + list(a.args)
        defaults: list[ast.expr] = list(a.defaults)
        offset = len(positional) - len(defaults)
        for i, arg in enumerate(positional):
            if i >= offset:
                params[arg.arg] = self.bind_value(defaults[i - offset], ctx)
            else:
                params[arg.arg] = None
        for arg, default in zip(a.kwonlyargs, a.kw_defaults):
            params[arg.arg] = (self.bind_value(default, ctx)
                               if default is not None else None)
        for default in list(a.defaults) + [d for d in a.kw_defaults
                                           if d is not None]:
            self.scan_expr(default, ctx)
        for dec in stmt.decorator_list:
            self.scan_expr(dec, ctx)
        inner = Ctx(cell_index=ctx.cell_index, func_name=stmt.name,
                    func_params=params, class_name=ctx.class_name,
                    locals={}, local_dicts={})
        self.visit_block(stmt.body, inner)

    def handle_class(self, stmt: ast.ClassDef, ctx: Ctx) -> None:
        info = ClassInfo()
        init = next((b for b in stmt.body
                     if isinstance(b, (ast.FunctionDef, ast.AsyncFunctionDef))
                     and b.name == "__init__"), None)
        if init is not None:
            a = init.args
            positional = list(a.posonlyargs) + list(a.args)[1:]  # sans self
            defaults = list(a.defaults)
            offset = len(positional) - len(defaults)
            for i, arg in enumerate(positional):
                if i >= offset:
                    info.init_params.append(
                        (arg.arg, self.bind_value(defaults[i - offset], ctx)))
                else:
                    info.init_params.append((arg.arg, None))
            for node in init.body:
                if (isinstance(node, ast.Assign) and len(node.targets) == 1
                        and isinstance(node.targets[0], ast.Attribute)
                        and isinstance(node.targets[0].value, ast.Name)
                        and node.targets[0].value.id == "self"):
                    attr = node.targets[0].attr
                    value = node.value
                    if isinstance(value, ast.Name):
                        info.self_from_params[attr] = value.id
                    else:
                        binding = self.bind_value(value, ctx)
                        if binding.kind != "unresolved":
                            info.self_literals[attr] = binding
        self.class_infos[stmt.name] = info
        # Le corps de classe est son propre scope (non visible des methodes
        # en semantique Python) : les affectations de classe restent locales.
        inner = Ctx(cell_index=ctx.cell_index, class_name=stmt.name,
                    locals={}, local_dicts={})
        self.visit_block(stmt.body, inner)

    def handle_assign(self, stmt: ast.Assign, ctx: Ctx) -> None:
        self.scan_expr(stmt.value, ctx)
        dict_binding = self.dict_literal(stmt.value, ctx)
        list_binding = self.list_dict_literal(stmt.value, ctx)
        binding = self.bind_value(stmt.value, ctx)
        for target in stmt.targets:
            self.bind_target(target, binding, dict_binding, ctx, list_binding)
        # HTTP brut (#25072) : retenir l'entree "model" d'un littéral dict
        # lié à un nom (à la scope de l'affectation) pour les appels json=<nom>.
        if (len(stmt.targets) == 1
                and isinstance(stmt.targets[0], ast.Name)):
            entry = _dict_model_entry(stmt.value)
            if entry is not None:
                name = stmt.targets[0].id
                if ctx.func_name is not None or ctx.class_name is not None:
                    ctx.local_dict_model[name] = entry
                else:
                    self.dict_model_nodes[name] = entry

    def handle_annassign(self, stmt: ast.AnnAssign, ctx: Ctx) -> None:
        self.scan_expr(stmt.value, ctx)
        dict_binding = self.dict_literal(stmt.value, ctx)
        list_binding = self.list_dict_literal(stmt.value, ctx)
        binding = self.bind_value(stmt.value, ctx)
        self.bind_target(stmt.target, binding, dict_binding, ctx, list_binding)
        # HTTP brut (#25072) : même retention pour l'affectation annotée
        # (``payload: dict = {"model": ...}``).
        if isinstance(stmt.target, ast.Name):
            entry = _dict_model_entry(stmt.value)
            if entry is not None:
                name = stmt.target.id
                if ctx.func_name is not None or ctx.class_name is not None:
                    ctx.local_dict_model[name] = entry
                else:
                    self.dict_model_nodes[name] = entry

    def handle_for(self, stmt: ast.stmt, ctx: Ctx) -> None:
        """Boucle sur une batterie de dictionnaires.

        ``for cfg in BATTERY:`` lie ``cfg`` a la LISTE des tables de la
        batterie : chaque entree est un tour de boucle, donc un site
        atteignable. Le binding ne sort pas de la boucle (restauration
        apres le corps), et un iterable qui n'est pas une batterie laisse
        le corps se visiter exactement comme avant -- aucune resolution
        existante n'est perdue.
        """
        self.scan_expr(stmt.iter, ctx)
        tables = (self._multi_tables(stmt.iter.id, ctx)
                  if isinstance(stmt.iter, ast.Name) else None)
        if tables is not None and isinstance(stmt.target, ast.Name):
            name = stmt.target.id
            previous = ctx.multi_dicts.get(name, _ABSENT)
            ctx.multi_dicts[name] = tables
            try:
                self.visit_block(stmt.body, ctx)
            finally:
                if previous is _ABSENT:
                    ctx.multi_dicts.pop(name, None)
                else:
                    ctx.multi_dicts[name] = previous
        else:
            self.visit_block(stmt.body, ctx)
        if stmt.orelse:
            self.visit_block(stmt.orelse, ctx)

    def bind_target(self, target, binding: Binding,
                    dict_binding: dict | None, ctx: Ctx,
                    list_binding: list | None = None) -> None:
        if isinstance(target, ast.Name):
            if ctx.func_name is not None or ctx.class_name is not None:
                # Scope LOCAL (corps de fonction ou de classe) : la locale
                # ne sort JAMAIS du scope. Sans cette garde, la locale
                # d'une fonction jamais appelee polluerait la resolution
                # globale (faux positif mesure, review PR #22800) -- et
                # inversement une locale courante blanchirait un global
                # obsolete consomme ailleurs.
                if list_binding is not None:
                    ctx.multi_dicts[target.id] = list_binding
                    ctx.locals.pop(target.id, None)
                    ctx.local_dicts.pop(target.id, None)
                elif dict_binding is not None:
                    ctx.local_dicts[target.id] = dict_binding
                    ctx.multi_dicts.pop(target.id, None)
                else:
                    ctx.locals[target.id] = binding
                    ctx.local_dicts.pop(target.id, None)
                    ctx.multi_dicts.pop(target.id, None)
            elif list_binding is not None:
                self.multi_dict_values[target.id] = list_binding
                self.module_values[target.id] = UNRESOLVED
                self.dict_values.pop(target.id, None)
            elif dict_binding is not None:
                self.dict_values[target.id] = dict_binding
                self.module_values[target.id] = UNRESOLVED
                self.multi_dict_values.pop(target.id, None)
            else:
                self.module_values[target.id] = binding
                self.dict_values.pop(target.id, None)
                self.multi_dict_values.pop(target.id, None)
        elif isinstance(target, ast.Tuple):
            if ctx.func_name is not None or ctx.class_name is not None:
                for elt in target.elts:
                    if isinstance(elt, ast.Name):
                        ctx.locals[elt.id] = UNRESOLVED
        elif isinstance(target, ast.Attribute) and ctx.class_name:
            base = target.value
            if isinstance(base, ast.Name) and base.id == "self" \
                    and binding.kind != "unresolved":
                self.class_attr_values.setdefault(
                    ctx.class_name, {}).setdefault(target.attr, []).append(
                    self._reorigin(binding, ctx))

    def _reorigin(self, binding: Binding, ctx: Ctx) -> Binding:
        return Binding(binding.value, binding.kind,
                       f"{binding.origin} (self.{ctx.class_name}, cell {ctx.cell_index})",
                       binding.node_id)

    # -- expressions --------------------------------------------------------

    def scan_expr(self, node: ast.AST, ctx: Ctx) -> None:
        # Le noeud passe en argument peut ETRE le site chat lui-meme
        # (Expr(Call) ou Assign dont la valeur est le Call) : il est examine
        # en premier, puis son sous-arbre hors portees imbriquees.
        for sub in (node, *iter_code_nodes(node)):
            if isinstance(sub, ast.Call):
                self.handle_call(sub, ctx)
            elif (isinstance(sub, ast.Constant) and isinstance(sub.value, str)
                    and is_obsolete_chat_model(sub.value)):
                self.doc_candidates.append((id(sub), ctx.cell_index, sub.value))

    def handle_call(self, call: ast.Call, ctx: Ctx) -> None:
        # Instantiation d'une classe connue -> resolution des self.X
        func = call.func
        if isinstance(func, ast.Name) and func.id in self.class_infos:
            self.resolve_instantiation(call, func.id, ctx)
        site = classify_chat_call(call, self.dspy_imported)
        if site is None:
            return
        label, positional = site
        self.stats["chat_sites"] += 1
        cell_id = self._cell_id(ctx.cell_index)
        arg = (self._http_model_node(call, ctx)
               if label == "http.chat.completions"
               else model_arg_node(call, positional))
        if arg is None:
            self.unresolved.append(self._site(ctx, cell_id, call, label,
                                              "sans argument model"))
            return
        self.resolve_model_expr(arg, label, call, ctx, defer_self=True)

    def _http_model_node(self, call: ast.Call, ctx: Ctx) -> ast.AST | None:
        """Site HTTP brut (#25072) : le "model" vit dans le corps de la
        requête (``json=``/``data=``), pas en argument ``model=``.

        Deux formes : un littéral dict inline (``json={"model": ...}``) et
        un dict lié à un nom (``payload = {"model": ...}`` puis
        ``json=payload``), ce dernier résolu via ``dict_model_nodes``
        (scope local d'abord, puis module).
        """
        request = call.args[0] if call.args else next(
            (kw.value for kw in call.keywords if kw.arg == "url"), None)
        if (tuple(attr_chain(call.func)[-3:]) == ("urllib", "request", "urlopen")
                and isinstance(request, ast.Call)
                and attr_chain(request.func)[-1:] == ["Request"]):
            call = request
        body: ast.AST | None = None
        for kw in call.keywords:
            if kw.arg in ("json", "data"):
                body = kw.value
                break
        if body is None and len(call.args) >= 2:
            body = call.args[1]  # urllib.request.urlopen(url, data)
        if body is None:
            return None
        if isinstance(body, ast.Call):
            if (isinstance(body.func, ast.Attribute)
                    and body.func.attr == "encode"
                    and isinstance(body.func.value, ast.Call)
                    and attr_chain(body.func.value.func)[-2:] == ["json", "dumps"]
                    and body.func.value.args and not body.keywords
                    and (not body.args or (len(body.args) == 1
                         and isinstance(body.args[0], ast.Constant)
                         and isinstance(body.args[0].value, str)
                         and body.args[0].value.lower() in ("utf-8", "utf8")))):
                body = body.func.value.args[0]
            elif attr_chain(body.func)[-2:] == ["json", "dumps"] and body.args:
                body = body.args[0]
            else:
                return None
        if isinstance(body, ast.Dict):
            return _dict_model_entry(body)
        if isinstance(body, ast.Name):
            return (ctx.local_dict_model.get(body.id)
                    or self.dict_model_nodes.get(body.id))
        return None

    def resolve_model_expr(self, node: ast.AST, label: str, call: ast.Call,
                           ctx: Ctx, defer_self: bool) -> None:
        cell_id = self._cell_id(ctx.cell_index)
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            self._evaluate(Binding(node.value, "literal",
                                   f"litteral (cell {ctx.cell_index})",
                                   id(node)), label, ctx, call)
        elif isinstance(node, ast.Name):
            self._resolve_name(node.id, label, ctx, call)
        elif (isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name)
              and node.value.id == "self"):
            if defer_self and ctx.class_name:
                self.pending_self.append(PendingSelfSite(
                    ctx.cell_index, cell_id, call.func.lineno, label,
                    ctx.class_name, node.attr, self.path))
            elif ctx.class_name:
                bindings = (self.class_attr_values.get(ctx.class_name, {})
                            .get(node.attr))
                if bindings:
                    self._evaluate(bindings[-1], label, ctx, call)
                else:
                    self.unresolved.append(self._site(
                        ctx, cell_id, call, label,
                        f"self.{node.attr} non lie"))
            else:
                self.unresolved.append(self._site(
                    ctx, cell_id, call, label, "self hors classe"))
        elif isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name):
            dict_name = node.value.id
            if dict_name in ctx.local_dicts:
                table = ctx.local_dicts[dict_name]
            elif dict_name in ctx.locals or (
                    ctx.func_params is not None
                    and dict_name in ctx.func_params):
                # Le nom est LOCAL (scalaire ou parametre homonyme) : il
                # MASQUE le dictionnaire global -- jamais de repli sur la
                # table module (defaut 3, review PR #22800).
                table = None
            elif dict_name in self.dict_values:
                table = self.dict_values[dict_name]
            else:
                table = None
            key = (node.slice.value if isinstance(node.slice, ast.Constant)
                   and isinstance(node.slice.value, str) else None)
            if table is not None and key is not None and key in table:
                self._evaluate(table[key], label, ctx, call)
            elif key is not None and self._multi_tables(dict_name, ctx):
                # Batterie ``[{...}, {...}]`` : chaque entree est un tour de
                # boucle, donc un site atteignable (defaut mesure : la
                # batterie retombait en ``unresolved`` et le modele obsolete
                # qu'elle porte n'etait JAMAIS accuse, #23387 point 3).
                self._evaluate_many(
                    [entry[key] for entry in self._multi_tables(dict_name, ctx)
                     if key in entry], label, ctx, call)
            else:
                self.unresolved.append(self._site(
                    ctx, cell_id, call, label,
                    f"cle {ast.dump(node.slice)[:40]} non resolue"))
        elif (isinstance(node, ast.Subscript)
              and isinstance(node.value, ast.Subscript)):
            # ``BATTERY[0]["cle"]`` : entree designee par un index litteral.
            tables = self._indexed_tables(node.value, ctx)
            key = (node.slice.value if isinstance(node.slice, ast.Constant)
                   and isinstance(node.slice.value, str) else None)
            if tables is not None and key is not None:
                self._evaluate_many([entry[key] for entry in tables
                                     if key in entry], label, ctx, call)
            else:
                self.unresolved.append(self._site(
                    ctx, cell_id, call, label,
                    f"index {ast.dump(node.value)[:40]} non resolu"))
        else:
            reason = ("f-string dynamique" if isinstance(node, ast.JoinedStr)
                      else f"expression dynamique ({type(node).__name__})")
            self.unresolved.append(self._site(ctx, cell_id, call, label, reason))

    def _resolve_name(self, name: str, label: str, ctx: Ctx, call: ast.Call) -> None:
        cell_id = self._cell_id(ctx.cell_index)
        if name in ctx.locals:
            binding = ctx.locals[name]
            if binding.kind == "unresolved":
                # Locale DYNAMIQUE : jamais de repli module -- le nom est
                # local pour tout le scope (semantique Python), sa valeur
                # non litterale reste non resolue, point final (defaut 3,
                # review PR #22800 : le repli "etat final" accusait la
                # globale homonyme).
                self.unresolved.append(self._site(
                    ctx, cell_id, call, label,
                    f'variable locale "{name}" dynamique '
                    f'(sans repli module)'))
            else:
                self._evaluate(binding, label, ctx, call)
            return
        if ctx.func_params is not None and name in ctx.func_params:
            param = ctx.func_params[name]
            if param is None:
                self.unresolved.append(self._site(
                    ctx, cell_id, call, label,
                    f'parametre "{name}" sans defaut trace'))
                return
            self._evaluate(param, label, ctx, call)
            return
        if name in self.module_values:
            binding = self.module_values[name]
            if binding.kind == "unresolved":
                self.retry_names.append(RetryNameSite(
                    ctx.cell_index, cell_id, call.func.lineno, label,
                    name, self.path))
                self.unresolved.append(self._site(
                    ctx, cell_id, call, label,
                    f'variable "{name}" dynamique au point d\'appel'))
            else:
                self._evaluate(binding, label, ctx, call)
            return
        self.retry_names.append(RetryNameSite(
            ctx.cell_index, cell_id, call.func.lineno, label, name, self.path))
        self.unresolved.append(self._site(
            ctx, cell_id, call, label, f'variable "{name}" pas encore liee'))

    def _evaluate(self, binding: Binding, label: str, ctx: Ctx,
                  call: ast.Call) -> None:
        cell_id = self._cell_id(ctx.cell_index)
        if binding.value is None:
            self.unresolved.append(self._site(ctx, cell_id, call, label,
                                              binding.origin))
            return
        if is_obsolete_chat_model(binding.value):
            if binding.node_id is not None:
                self.consumed_node_ids.add(binding.node_id)
            self.findings.append({
                "path": self.path,
                "cell": ctx.cell_index,
                "cell_id": cell_id,
                "line": call.func.lineno,
                "site": label,
                "model": normalize_model(binding.value),
                "via": binding.origin,
            })

    def _evaluate_many(self, bindings: list[Binding], label: str, ctx: Ctx,
                       call: ast.Call) -> None:
        """Evaluate the candidate bindings of the SAME key across the entries
        of a battery.

        The loop over a battery executes every entry, so an entry carrying
        an obsolete model IS a reachable site : it is flagged, and ``via``
        names the entry index. One finding per distinct model (two entries
        on ``gpt-4o-mini`` are one model, not two). Entries that do not
        resolve are dropped -- never accused -- and a battery with no
        resolved entry at all is reported ``unresolved``.
        """
        seen: set[str] = set()
        resolved = 0
        for binding in bindings:
            if binding.value is None:
                continue
            resolved += 1
            normalized = normalize_model(binding.value)
            if normalized in seen:
                continue
            seen.add(normalized)
            self._evaluate(binding, label, ctx, call)
        if resolved == 0:
            cell_id = self._cell_id(ctx.cell_index)
            self.unresolved.append(self._site(
                ctx, cell_id, call, label,
                "batterie de dictionnaires sans entree resolue"))

    def _site(self, ctx: Ctx, cell_id: str, call: ast.Call, label: str,
              reason: str) -> dict:
        return {"path": self.path, "cell": ctx.cell_index,
                "cell_id": cell_id, "line": call.func.lineno,
                "site": label, "reason": reason}

    def _cell_id(self, index: int) -> str:
        return self._ids.get(index, "")

    # -- valeurs -----------------------------------------------------------

    def bind_value(self, node: ast.AST | None, ctx: Ctx) -> Binding:
        if node is None:
            return UNRESOLVED
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            return Binding(node.value, "literal",
                           f"litteral (cell {ctx.cell_index})", id(node))
        if isinstance(node, ast.BoolOp) and isinstance(node.op, ast.Or):
            # ``variable or os.environ.get("M", "<modele>")`` : les operandes
            # s'evaluent de gauche a droite et le premier litteral VRAI
            # court-circuite, donc le premier litteral declare est la valeur
            # statiquement visible -- et c'est le repli par defaut de la
            # chaine. Sans ce cas, la chaine n'etait ni findee ni meme
            # ``unresolved`` proprement : le litteral restait une mention doc
            # et le site chat tombait en ``unresolved`` (faux negatif mesure
            # sur ``scripts/slides/livecoding_video_pipeline.py``, repli
            # ``gpt-4o-mini``).
            for operand in node.values:
                candidate = self.bind_value(operand, ctx)
                if candidate.value is not None:
                    return Binding(candidate.value, candidate.kind,
                                   f"repli 'or' -> {candidate.origin}",
                                   candidate.node_id)
            return Binding(None, "unresolved", "chaine 'or' sans litteral")
        if isinstance(node, ast.Call):
            parts = attr_chain(node.func)
            if parts and (tuple(parts[-1:]) == ("getenv",)
                          or tuple(parts[-2:]) == ("environ", "get")):
                if (len(node.args) >= 2
                        and isinstance(node.args[1], ast.Constant)
                        and isinstance(node.args[1].value, str)):
                    var = (node.args[0].value
                           if isinstance(node.args[0], ast.Constant)
                           and isinstance(node.args[0].value, str) else "?")
                    return Binding(node.args[1].value, "env_default",
                                   f'defaut de os.getenv("{var}", ...) '
                                   f'(cell {ctx.cell_index})',
                                   id(node.args[1]))
                return Binding(None, "unresolved",
                               "os.getenv sans defaut litteral")
        if isinstance(node, ast.Name):
            if node.id in ctx.locals:
                local = ctx.locals[node.id]
                return Binding(local.value, local.kind,
                               f'"{node.id}" (local) <- {local.origin}',
                               local.node_id)
            if ctx.func_params is not None and node.id in ctx.func_params:
                param = ctx.func_params[node.id]
                return param if param is not None else UNRESOLVED
            if node.id in self.module_values:
                binding = self.module_values[node.id]
                return Binding(binding.value, binding.kind,
                               f'"{node.id}" <- {binding.origin}',
                               binding.node_id)
        return UNRESOLVED

    def dict_literal(self, node: ast.AST, ctx: Ctx) -> dict[str, Binding] | None:
        if not isinstance(node, ast.Dict):
            return None
        table: dict[str, Binding] = {}
        for key, value in zip(node.keys, node.values):
            if (isinstance(key, ast.Constant) and isinstance(key.value, str)
                    and isinstance(value, ast.Constant)
                    and isinstance(value.value, str)):
                table[key.value] = Binding(
                    value.value, "literal",
                    f'cle "{key.value}" du dictionnaire (cell {ctx.cell_index})',
                    id(value))
        return table or None

    def list_dict_literal(self, node: ast.AST,
                          ctx: Ctx) -> list[dict[str, Binding]] | None:
        """Batterie de modeles ecrite en LISTE DE DICTIONNAIRES.

        Forme pedagogique courante, tres lisible dans un carnet :

            BATTERY = [{"model": "gpt-5.6-luna", "label": "mini"},
                       {"model": "gpt-4o-mini", "label": "ancien"}]
            for cfg in BATTERY:
                client.chat.completions.create(model=cfg["model"], ...)

        Chaque entree passe par ``dict_literal`` ; une seule entree non
        resoluble fait retomber la batterie entiere en non suivie (pas de
        resolution partielle devinee). Les origines portent l'indice de
        l'entree, ce qui localise le modele obsolete dans le finding.
        """
        if not isinstance(node, ast.List) or not node.elts:
            return None
        tables: list[dict[str, Binding]] = []
        for index, element in enumerate(node.elts):
            table = self.dict_literal(element, ctx)
            if table is None:
                return None
            tables.append({
                key: Binding(value.value, value.kind,
                             f"entree {index} -> {value.origin}",
                             value.node_id)
                for key, value in table.items()
            })
        return tables

    def _multi_tables(self, name: str, ctx: Ctx
                      ) -> list[dict[str, Binding]] | None:
        """Tables d'une batterie designee par ``name``, ou None.

        Un nom LOCAL (scalaire, parametre ou dictionnaire plat) MASQUE la
        batterie globale -- meme doctrine que la cle de dictionnaire
        (defaut 3, review PR #22800) : jamais de repli silencieux sur la
        table module quand le nom est lie localement.
        """
        if name in ctx.multi_dicts:
            return ctx.multi_dicts[name]
        if name in ctx.locals or name in ctx.local_dicts or (
                ctx.func_params is not None and name in ctx.func_params):
            return None
        return self.multi_dict_values.get(name)

    def _indexed_tables(self, expr: ast.Subscript, ctx: Ctx
                        ) -> list[dict[str, Binding]] | None:
        """``BATTERY[0]["cle"]`` : l'entree designee par un index entier
        litteral. Tout index dynamique reste non resolu (jamais devine)."""
        if not isinstance(expr.value, ast.Name):
            return None
        index = (expr.slice.value
                 if isinstance(expr.slice, ast.Constant)
                 and isinstance(expr.slice.value, int)
                 and not isinstance(expr.slice.value, bool) else None)
        if index is None:
            return None
        tables = self._multi_tables(expr.value.id, ctx)
        if tables is None or not 0 <= index < len(tables):
            return None
        return [tables[index]]

    def resolve_instantiation(self, call: ast.Call, class_name: str,
                              ctx: Ctx) -> None:
        info = self.class_infos[class_name]
        resolved: dict[str, Binding] = {}
        by_name = {name: default for name, default in info.init_params}
        positional = [name for name, _ in info.init_params]
        for i, arg in enumerate(call.args):
            if i < len(positional):
                resolved[positional[i]] = self.bind_value(arg, ctx)
        for kw in call.keywords:
            if kw.arg in by_name:
                resolved[kw.arg] = self.bind_value(kw.value, ctx)
        attrs = self.class_attr_values.setdefault(class_name, {})
        for attr, param in info.self_from_params.items():
            if param in resolved:
                binding = resolved[param]
                attrs.setdefault(attr, []).append(
                    Binding(binding.value, binding.kind,
                            f"self.{attr} <- {class_name}(...) {binding.origin} "
                            f"(cell {ctx.cell_index})",
                            binding.node_id))
        for attr, binding in info.self_literals.items():
            attrs.setdefault(attr, []).append(binding)

    # -- finalisation --------------------------------------------------------

    def _finalize(self) -> None:
        for site in self.pending_self:
            bindings = (self.class_attr_values.get(site.class_name, {})
                        .get(site.attr))
            info = self.class_infos.get(site.class_name)
            if not bindings and info is not None \
                    and site.attr in info.self_literals:
                bindings = [info.self_literals[site.attr]]
            if bindings:
                for binding in bindings:
                    if binding.value is not None \
                            and is_obsolete_chat_model(binding.value):
                        if binding.node_id is not None:
                            self.consumed_node_ids.add(binding.node_id)
                        self.findings.append({
                            "path": site.path,
                            "cell": site.cell_index,
                            "cell_id": site.cell_id,
                            "line": site.line,
                            "site": site.site,
                            "model": normalize_model(binding.value),
                            "via": binding.origin,
                        })
            else:
                self.unresolved.append({
                    "path": site.path, "cell": site.cell_index,
                    "cell_id": site.cell_id, "line": site.line,
                    "site": site.site,
                    "reason": f"self.{site.attr} jamais lie par instanciation"})
        for retry in self.retry_names:
            binding = self.module_values.get(retry.name)
            if binding is not None and binding.value is not None \
                    and is_obsolete_chat_model(binding.value):
                if binding.node_id is not None:
                    self.consumed_node_ids.add(binding.node_id)
                self.findings.append({
                    "path": retry.path, "cell": retry.cell_index,
                    "cell_id": retry.cell_id, "line": retry.line,
                    "site": retry.site,
                    "model": normalize_model(binding.value),
                    "via": f'"{retry.name}" <- {binding.origin} '
                           f'(etat final du carnet)',
                })
        self._collect_doc_mentions()

    def _collect_doc_mentions(self) -> None:
        per_cell: dict[int, set[str]] = {}
        for node_id, cell_index, value in self.doc_candidates:
            if node_id in self.consumed_node_ids:
                continue
            per_cell.setdefault(cell_index, set()).add(normalize_model(value))
        for cell_index, models in sorted(per_cell.items()):
            source = self._cell_sources.get(cell_index, "")
            if has_doc_marker(source):
                self.doc_marked_cells += 1
                continue
            self.doc_mentions.append({
                "path": self.path,
                "cell": cell_index,
                "cell_id": self._cell_id(cell_index),
                "models": sorted(models),
                "marker": False,
            })


# ---------------------------------------------------------------------------
# Analyse d'un carnet
# ---------------------------------------------------------------------------

def _report(path: str, kind: str, scanner: NotebookScanner) -> dict:
    if kind == "python":
        scanner.stats["python_modules"] = 1
    return {
        "kind": kind,
        "notebook": path,
        "findings": scanner.findings,
        "doc_mentions": scanner.doc_mentions,
        "doc_marked_cells": scanner.doc_marked_cells,
        "unresolved": scanner.unresolved,
        "stats": scanner.stats,
    }


def analyze_notebook(path: str) -> dict:
    p = Path(path)
    if not p.exists():
        raise FileNotFoundError(path)
    try:
        notebook = json.loads(p.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        raise ValueError(f"JSON invalide: {path}: {exc}") from exc
    scanner = NotebookScanner(path)
    scanner.scan(notebook.get("cells", []))
    return _report(path, "notebook", scanner)


def _skipped_report(path: str) -> dict:
    """Rapport d'un module ``.py`` injoignable : compte comme saute, zero finding.

    Ne traverse pas ``_report`` (pas de scanner) : le fichier n'a pu etre ni
    stat ni lu. La mention part sur stderr pour rester visible dans un log.
    """
    print(f"AVERTISSEMENT: module .py injoignable, saute: {path}",
          file=sys.stderr)
    return {
        "kind": "python",
        "notebook": path,
        "findings": [],
        "doc_mentions": [],
        "doc_marked_cells": 0,
        "unresolved": [],
        "stats": {"skipped": 1},
    }


def analyze_python_module(path: str) -> dict:
    """Scanne un module ``.py`` du depot (hors carnet).

    Les carnets ne sont pas le seul lieu d'un appel chat : des modules
    consommes par les carnets portent des replis litteraux (mesure
    firsthand : ``scripts/slides/livecoding_video_pipeline.py`` repliait sur un
    ``os.environ.get("OPENAI_MODEL", "<modele obsolete>")``). La detection
    y est identique, la forme du rapport aussi, seule l'unite change.
    """
    p = Path(path)
    try:
        exists = p.exists()
    except OSError:
        # ``exists()`` lui-meme peut lever (chemin long / fichier verrou,
        # WinError 1920) : la collecte ci-dessous est censee avoir ecarte ces
        # dossiers ; si un fichier echappe, il degrade en skip rapporte, jamais
        # en crash de la passe entiere.
        return _skipped_report(path)
    if not exists:
        raise FileNotFoundError(path)
    try:
        source = p.read_text(encoding="utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError(f"encodage invalide: {path}: {exc}") from exc
    except OSError:
        return _skipped_report(path)
    scanner = NotebookScanner(path)
    scanner.scan_python_source(source)
    return _report(path, "python", scanner)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

SOURCE_SUFFIXES = (".ipynb", ".py")

# Dossiers de build / dependances / cache : jamais une source premiere partie
# a scanner. Les descendre est a la fois lent, faux, et sur Windows source
# d'echec d'acces a chemin long dans l'arbre de build d'une toolchain vendue
# (WinError 1920 : .lake/packages/mathlib crashait la passe sur SymbolicAI,
# po-2024, #14755). ``.lake`` est git-ignore : de la sortie de build pure.
SKIP_DIR_NAMES = frozenset({
    ".lake", ".git", "__pycache__", "node_modules", ".venv", "venv",
    ".mypy_cache", ".pytest_cache", ".ruff_cache", ".ipynb_checkpoints",
    "dist", "build", ".eggs", ".tox",
})


def source_kind(p: Path) -> str:
    return "notebook" if p.suffix == ".ipynb" else "python"


def _is_skipped(q: Path) -> bool:
    """Vrai si ``q`` vit sous un dossier de build/dependance a ne pas scanner."""
    return any(part in SKIP_DIR_NAMES for part in q.parts)


def collect_sources(paths: list[str]) -> list[tuple[Path, str]]:
    """Rend les unites a scanner : ``(chemin, "notebook"|"python")``.

    Un dossier descend sur les deux suffixes ; un fichier est accepte s'il
    porte l'un des deux. Ce que la ligne de commande accepte ne dit PAS ce que
    le garde CI itere : le cablage fast-lane reste volontairement borne aux
    carnets (``iterate_paths=["**.ipynb"]``, incident #13220), le module
    n'etant atteignable que par un appel explicite. Les dossiers de
    build/dependance (``SKIP_DIR_NAMES``) sont ecarter de la descente.
    """
    out: list[tuple[Path, str]] = []
    for raw in paths:
        p = Path(raw)
        if p.is_dir():
            for pattern in ("*.ipynb", "*.py"):
                out.extend(
                    (q, source_kind(q))
                    for q in sorted(p.rglob(pattern))
                    if not _is_skipped(q)
                )
        elif p.suffix in SOURCE_SUFFIXES:
            out.append((p, source_kind(p)))
        else:
            raise FileNotFoundError(f"ni carnet, ni module .py, ni dossier: {raw}")
    return out


def git_output(args: list[str], cwd: str) -> str:
    proc = subprocess.run(["git", *args], cwd=cwd, capture_output=True,
                          text=True, encoding="utf-8", errors="replace")
    if proc.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)}: {proc.stderr.strip()}")
    return proc.stdout


def filter_base(sources: list[tuple[Path, str]], base: str
                ) -> tuple[list[tuple[Path, str]], str]:
    """Restreint aux unites modifiees depuis merge-base(base, HEAD)."""
    top = git_output(["rev-parse", "--show-toplevel"], ".").strip()
    merge_base = git_output(["merge-base", base, "HEAD"], top).strip()
    rel_sources = []
    for p, kind in sources:
        abs_p = p.resolve()
        try:
            rel = abs_p.relative_to(top).as_posix()
        except ValueError:
            rel = abs_p.as_posix()
        rel_sources.append((p, kind, rel))
    changed = git_output(
        ["diff", "--name-only", merge_base, "--",
         *[rel for _, _, rel in rel_sources]], top).split()
    changed_set = set(changed)
    return [(p, kind) for p, kind, rel in rel_sources if rel in changed_set], \
        merge_base


def print_text(reports: list[dict], merge_base: str | None) -> None:
    findings = [f for r in reports for f in r["findings"]]
    mentions = [m for r in reports for m in r["doc_mentions"]]
    unresolved = [u for r in reports for u in r["unresolved"]]
    stats = {k: sum(r["stats"].get(k, 0) for r in reports) for k in
             ("code_cells", "python_cells", "non_python_cells",
              "unparsed_cells", "chat_sites", "python_modules")}
    print("== check_obsolete_chat_model (#22783) ==")
    if merge_base:
        print(f"perimetre : carnets modifies depuis merge-base {merge_base}")
    for f in findings:
        cid = f" id {f['cell_id']}" if f["cell_id"] else ""
        print(f"FINDING {f['path']} cell {f['cell']}{cid} line {f['line']}: "
              f"{f['site']} cible le modele chat obsolete '{f['model']}' "
              f"-- via {f['via']}")
    for m in mentions:
        print(f"DOC-MENTION {m['path']} cell {m['cell']}: "
              f"mentions {', '.join(m['models'])} sans marqueur "
              f"'# obsolescence: DOC' (advisory, sans effet sur l'exit)")
    marked = sum(r["doc_marked_cells"] for r in reports)
    print(f"-- {len(findings)} finding(s) ; {len(unresolved)} site(s) chat non "
          f"resolus statiquement (rapportes, jamais accuses) ; "
          f"{len(mentions)} mention(s) doc sans marqueur, {marked} cellule(s) "
          f"marquee(s).")
    print(f"-- unites : {sum(1 for r in reports if r.get('kind') != 'python')} "
          f"carnet(s), {stats['python_modules']} module(s) .py.")
    print(f"-- cellules : {stats['python_cells']} python, "
          f"{stats['non_python_cells']} non-python, {stats['unparsed_cells']} "
          f"non-parsables, {stats['chat_sites']} site(s) chat vus.")
    print("-- limites : AST Python seul (markdown/raw/.NET non scannes) ; "
          "resolution bornee (voir en-tete du script) ; un module .py est une "
          "unite, sans report inter-cellules.")


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description="Detecte les appels chat ciblant un modele obsolete "
                    "(regle #22783).")
    parser.add_argument("paths", nargs="+",
                        help="carnets .ipynb, modules .py ou dossiers a scanner")
    parser.add_argument("--json", action="store_true", dest="as_json",
                        help="sortie JSON structuree")
    parser.add_argument("--obsolete", action="append", default=[],
                        metavar="MODEL",
                        help="identifiant obsolete additionnel (exact)")
    parser.add_argument("--base", metavar="REF",
                        help="ne scanner que les carnets modifies depuis "
                             "merge-base(REF, HEAD)")
    args = parser.parse_args(argv)

    global OBSOLETE_CHAT_MODELS
    if args.obsolete:
        OBSOLETE_CHAT_MODELS = frozenset(
            set(OBSOLETE_CHAT_MODELS) | set(args.obsolete))

    try:
        sources = collect_sources(args.paths)
        merge_base = None
        if args.base:
            sources, merge_base = filter_base(sources, args.base)
        reports = [analyze_notebook(str(p)) if kind == "notebook"
                   else analyze_python_module(str(p))
                   for p, kind in sources]
    except (FileNotFoundError, ValueError, RuntimeError) as exc:
        print(f"ERREUR: {exc}", file=sys.stderr)
        return 2

    if args.as_json:
        findings = [f for r in reports for f in r["findings"]]
        print(json.dumps({
            "tool": "check_obsolete_chat_model",
            "rule": "issue #22783 + docs/genai/model-mapping-openai.md",
            "merge_base": merge_base,
            "obsolete_models": sorted(OBSOLETE_CHAT_MODELS),
            "findings": findings,
            "doc_mentions": [m for r in reports for m in r["doc_mentions"]],
            "unresolved": [u for r in reports for u in r["unresolved"]],
            "stats": {
                "notebooks": sum(1 for r in reports
                                 if r.get("kind") != "python"),
                "python_modules": sum(1 for r in reports
                                      if r.get("kind") == "python"),
                **{k: sum(r["stats"].get(k, 0) for r in reports) for k in
                   ("code_cells", "python_cells", "non_python_cells",
                    "unparsed_cells", "chat_sites")},
                "doc_marked_cells": sum(r["doc_marked_cells"]
                                        for r in reports),
            },
        }, ensure_ascii=False, indent=2))
    else:
        print_text(reports, merge_base)

    return 1 if any(r["findings"] for r in reports) else 0


if __name__ == "__main__":
    sys.exit(main())
