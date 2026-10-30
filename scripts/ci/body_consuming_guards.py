#!/usr/bin/env python3
"""Inventaire des gardes qui consomment le body d'une PR (#22603).

Suite de #21552 : le ratchet `output-collapse` lisait un body vide parce que son
workflow ne le lui passait pas, et le garde rendait alors un verdict sur une
PR sans justification ecrite au lieu de signaler le cablage absent. Rien dans le
depot ne permettait de voir d'un coup d'oeil **quels scripts lisent le body
d'une PR, et par quel canal**. Ce module porte cet inventaire.

Ce que l'organe fait, en trois temps :

1. **Decouverte mecanique** (`discover_consumers`) : il analyse la source des
   scripts du depot avec `ast` et releve les canaux de body qu'ils declarent.
   Aucune liste de resultats n'est codee en dur -- un garde ajoute au depot est
   vu du seul fait qu'il lit le body.
2. **Table de reference** (`REFERENCE`) : l'etat constate, fige, canal par canal,
   avec le workflow qui cable chacun. Elle est derivee par `--emit-reference` et
   non ecrite a la main ; `uncabled_reason` documente les cas ou une absence de
   cablage est volontaire (script qui va chercher son body lui-meme, canal
   garde pour l'usage local).
3. **Verification** (`--check`, sortie 1 en cas d'ecart) : un consommateur
   apparu ou disparu, un canal qui n'est plus lu, un cablage declare qui a
   disparu d'un workflow -- chacun rougit l'organe. Un cablage **ajoute** est
   signale sans rougir (regle et motif dans la docstring de `compare`).

Les cinq formes de canal reconnues
----------------------------------

``cli:--pr-body-file``   le body est lu dans un fichier nomme en argument.
``cli:--pr-body``        le body passe en texte litteral sur la ligne de commande.
``env:NAME``             le body arrive en memoire par une variable d'environnement.
``env-file:NAME``        la variable d'environnement nomme un fichier a lire.
``api-gh``               le script va lui-meme chercher le body (`gh pr view --json body`).

Perimetre -- ce que l'organe ne couvre pas, et pourquoi
------------------------------------------------------

La famille **always-on** (`scripts/ci/always_on_body_organs.sh` et les taches
shell de `variation-tag-guard.yml`, `lane-claim-guard.yml`,
`source-output-ratchet.yml`, `organ-duplication-advisory.yml`) lit le body pour
ses **marqueurs de protocole** (`Grain:`, `prev:`, close-keyword, adjacency,
lane-claim) et non pour une exemption redigee dans la prose de la PR. Elle a
deja son inventaire propre, `always_on_body_organs.sh`. L'organe ne scanne donc
que les scripts Python de `scripts/`, hors `scripts/tests/` (les tests ne sont
pas des gardes de PR).

Sortie
------

Sans option : table lisible de l'inventaire mesure.
``--json``          : le meme inventaire, machine-lisible.
``--emit-reference``: le bloc `REFERENCE` a coller (derive, pas ecrit a la main).
``--check``         : compare le depot a `REFERENCE`, sortie 1 en cas d'ecart.
``--root <dir>``    : racine a inspecter (defaut : racine du depot).
"""

from __future__ import annotations

import argparse
import ast
import json
import re
import sys
import warnings
from dataclasses import dataclass, field
from pathlib import Path

# ---------------------------------------------------------------------------
# Formes de canal
# ---------------------------------------------------------------------------

CLI_FILE = "cli:--pr-body-file"
CLI_LITERAL = "cli:--pr-body"
ENV_PREFIX = "env:"
ENV_FILE_PREFIX = "env-file:"
API_GH = "api-gh"

#: Option argparse -> etiquette de canal. Deux options distinctes, deux canaux
#: distincts : un garde peut n'en lire qu'une.
CLI_OPTIONS = {"--pr-body-file": CLI_FILE, "--pr-body": CLI_LITERAL}

ENV_CHANNEL_PREFIXES = (ENV_PREFIX, ENV_FILE_PREFIX)

#: Nom de variable d'environnement portant un body de PR. Convention du depot :
#: un prefixe de famille optionnel en majuscules, puis `PR_BODY`, puis un
#: suffixe optionnel (`_FILE` pour un chemin de fichier). Le prefixe est
#: optionnel pour que `PR_BODY` et `PR_BODY_FILE` soient vus comme des canaux
#: (mesure : `check_kernel_drift.py` lit exactement `PR_BODY_FILE`).
#: Les commentaires ne sont pas des noeuds `ast.Constant`, donc les mentions en
#: prose ne sont pas comptees. Les docstrings sont des `ast.Constant`, mais un
#: nom d'environnement n'est releve que dans trois positions precises (lecture
#: d'environnement, valeur par defaut d'une option, acces indexe), jamais dans
#: une chaine quelconque : une docstring ne peut donc pas fabriquer un canal.
ENV_NAME_RE = re.compile(r"^(?:[A-Z][A-Z0-9_]*)?PR_BODY[A-Z0-9_]*$")

#: Fonctions de lecture d'environnement reconnues, telles que `ast.unparse` les
#: rend. La forme nue (`environ.get`) vient de `from os import environ`.
ENV_READERS = frozenset(
    {"os.environ.get", "os.getenv", "environ.get", "os.environ.getenv"}
)
ENV_MAPPINGS = frozenset({"os.environ", "environ"})

#: Dossiers de scripts parcourus, relatifs a la racine.
SCRIPT_ROOT = "scripts"
#: Segment de chemin exclu : les tests ne sont pas des gardes de PR.
EXCLUDED_SEGMENT = "tests"
#: Dossier des workflows, relatif a la racine.
WORKFLOW_ROOT = ".github/workflows"


class Deviation:
    """Un ecart entre le depot et la table de reference."""

    __slots__ = ("code", "detail", "path")

    def __init__(self, code: str, path: str, detail: str = "") -> None:
        self.code = code
        self.path = path
        self.detail = detail

    def __str__(self) -> str:
        suffix = f" -- {self.detail}" if self.detail else ""
        return f"{self.code} {self.path}{suffix}"


# ---------------------------------------------------------------------------
# Decouverte
# ---------------------------------------------------------------------------


@dataclass
class Consumer:
    """Un script consommateur et les canaux par lesquels il lit le body."""

    path: str
    channels: dict[str, dict] = field(default_factory=dict)

    def add(self, channel: str, line: int, dynamic_name: bool = False) -> None:
        entry = self.channels.setdefault(
            channel, {"lines": [], "dynamic_name": False}
        )
        if line not in entry["lines"]:
            entry["lines"].append(line)
        entry["dynamic_name"] = entry["dynamic_name"] or dynamic_name

    def sorted_channels(self) -> list[str]:
        return sorted(self.channels)


def _is_env_name(value: object) -> bool:
    return isinstance(value, str) and bool(ENV_NAME_RE.match(value))


def _channel_for_env_name(name: str) -> str:
    if name.endswith("_FILE"):
        return ENV_FILE_PREFIX + name
    return ENV_PREFIX + name


def _const_str(node: ast.AST) -> str | None:
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    return None


def _scan_tree(tree: ast.AST) -> dict[str, dict]:
    """Releve les canaux d'un module deja parse.

    Rend un dictionnaire canal -> ``{"lines": [...], "dynamic_name": bool}``.
    Un canal dont le nom est choisi a l'execution est soit rattache a son defaut
    declare (marque ``dynamic_name``), soit declare sous ``env:<nom-dynamique>``
    pour rester visible plutot que muet.
    """
    found: dict[str, dict] = {}
    dynamic_env_reads = 0

    def bump(channel: str, line: int, dynamic_name: bool = False) -> None:
        entry = found.setdefault(channel, {"lines": [], "dynamic_name": False})
        if line not in entry["lines"]:
            entry["lines"].append(line)
        entry["dynamic_name"] = entry["dynamic_name"] or dynamic_name

    for node in ast.walk(tree):
        # 1. Options argparse : --pr-body-file / --pr-body, y compris quand
        #    l'option et son argument sont sur des lignes differentes.
        if isinstance(node, ast.Call):
            func = ast.unparse(node.func)
            if func.endswith("add_argument"):
                option = _const_str(node.args[0]) if node.args else None
                channel = CLI_OPTIONS.get(option) if option else None
                if channel:
                    bump(channel, node.lineno)
                for kw in node.keywords:
                    if kw.arg == "default" and _is_env_name(_const_str(kw.value)):
                        bump(
                            _channel_for_env_name(_const_str(kw.value)),
                            node.lineno,
                        )

            # 2. Lectures d'environnement statiques.
            if func in ENV_READERS and node.args:
                name = _const_str(node.args[0])
                if name is not None and _is_env_name(name):
                    bump(_channel_for_env_name(name), node.lineno)
                elif name is None and "body" in ast.unparse(node.args[0]).lower():
                    # Nom choisi a l'execution. On ne le compte que si
                    # l'expression nomme elle-meme un body (`args.body_env`) :
                    # sans ce filtre, toute lecture dynamique d'environnement
                    # du depot deviendrait un faux consommateur.
                    dynamic_env_reads += 1

        # 3. os.environ["NAME"] / environ["NAME"]
        if isinstance(node, ast.Subscript) and ast.unparse(node.value) in ENV_MAPPINGS:
            name = _const_str(node.slice)
            if name is not None and _is_env_name(name):
                bump(_channel_for_env_name(name), node.lineno)

        # 4. Recuperation directe du body par l'API gh. Les elements non
        #    constants de la liste (numero de PR, repo) sont toleres : seul
        #    l'ensemble des jetons constants importe.
        if isinstance(node, (ast.List, ast.Tuple)) and node.elts:
            constants = {
                value for value in map(_const_str, node.elts) if value is not None
            }
            if {"pr", "view", "body"} <= constants:
                bump(API_GH, node.lineno)

    if dynamic_env_reads:
        named = [ch for ch in found if ch.startswith(ENV_CHANNEL_PREFIXES)]
        if named:
            # Le nom du canal est choisi a l'execution : l'etiquette reste
            # celle du defaut declare, mais on note que le workflow peut la
            # renommer (cf `--body-env` du cliquet Lean).
            for channel in named:
                found[channel]["dynamic_name"] = True
        else:
            # Aucun defaut statique pour nommer le canal : l'organe ne peut pas
            # l'etiqueter. Il le declare sous un nom qu'aucune reference ne peut
            # pretendre connaitre, pour qu'il soit visible plutot que tu.
            bump(ENV_PREFIX + "<nom-dynamique>", 0, dynamic_name=True)

    return found


def _iter_script_files(root: Path):
    base = root / SCRIPT_ROOT
    if not base.is_dir():
        return
    for path in sorted(base.rglob("*.py")):
        parts = path.relative_to(root).parts
        if EXCLUDED_SEGMENT in parts:
            continue
        yield path


def discover_consumers(root: Path) -> dict[str, Consumer]:
    """Decouvre les consommateurs de body par analyse syntaxique de la source.

    Aucun nom de script n'est code en dur : le resultat ne depend que du contenu
    des fichiers.
    """
    consumers: dict[str, Consumer] = {}
    for path in _iter_script_files(root):
        rel = path.relative_to(root).as_posix()
        source = path.read_text(encoding="utf-8", errors="replace")
        # Les SyntaxWarning des scripts tiers parses au passage (sequences
        # d'echappement heritees) ne sont pas des ecarts de l'inventaire :
        # on ne masque que ce bruit-la, jamais une erreur de syntaxe.
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", SyntaxWarning)
            tree = ast.parse(source, filename=rel)
        channels = _scan_tree(tree)
        if not channels:
            continue
        consumer = consumers.setdefault(rel, Consumer(rel))
        for channel, entry in channels.items():
            for line in entry["lines"] or [0]:
                consumer.add(channel, line, entry["dynamic_name"])
    return consumers


# ---------------------------------------------------------------------------
# Cablage dans les workflows
# ---------------------------------------------------------------------------


def _workflow_text(root: Path, name: str) -> str | None:
    path = root / WORKFLOW_ROOT / name
    if not path.is_file():
        return None
    return path.read_text(encoding="utf-8", errors="replace")


def _strip_comment_lines(text: str) -> str:
    """Retire les lignes de commentaire YAML/shell.

    Un canal cable est une affectation ou un argument ; sa mention dans un
    commentaire explicatif ne cable rien. Sans ce filtre, un commentaire qui
    documente un canal suffirait a faire croire le cablage present -- c'est
    exactement le faux vert que l'organe doit empecher.
    """
    return "\n".join(
        line for line in text.splitlines() if not line.lstrip().startswith("#")
    )


def _channel_present(text: str, channel: str) -> bool:
    """Vrai si le canal est reellement cable dans le texte d'un workflow."""
    if channel == CLI_FILE:
        return re.search(r"--pr-body-file(?![A-Za-z0-9_-])", text) is not None
    if channel == CLI_LITERAL:
        # Ne doit pas matcher --pr-body-file : le tiret suivant est exclu.
        return re.search(r"--pr-body(?![A-Za-z0-9_-])", text) is not None
    if channel.startswith(ENV_CHANNEL_PREFIXES):
        name = channel.split(":", 1)[1]
        if not name or name.startswith("<"):
            return False
        pattern = (
            r"(?<![A-Za-z0-9_])"
            + re.escape(name)
            + r"(?![A-Za-z0-9_])\s*[:=]"
        )
        return re.search(pattern, text) is not None
    # Le script va chercher le body lui-meme : aucun workflow ne le cable.
    return channel == API_GH


def _script_invoked(text: str, script: str, via_fast_lane: bool) -> bool:
    """Vrai si le workflow peut atteindre ce script.

    Deux voies, toutes deux constatees et non supposees : l'appel direct (le nom
    de base du script figure dans le workflow) et l'appel par le fast lane
    (`fast_lane.py`), qui ne nomme que le registre. Le fast lane ne compte que
    si le registre cite lui-meme le script ; sans cette verification, tout
    workflow lancant le fast lane serait credite de cabler tous les gardes.
    """
    if Path(script).name in text:
        return True
    return via_fast_lane and "fast_lane.py" in text


def discover_fast_lane_scripts(root: Path) -> set[str]:
    """Scripts joignables par le fast lane, d'apres le registre du depot."""
    registry = root / SCRIPT_ROOT / "ci" / "fast_lane_registry.py"
    if not registry.is_file():
        return set()
    text = registry.read_text(encoding="utf-8", errors="replace")
    names: set[str] = set()
    for path in _iter_script_files(root):
        if Path(path).name in text:
            names.add(path.relative_to(root).as_posix())
    return names


def find_cabling(root: Path, script: str, channel: str) -> list[str]:
    """Workflows qui cablent reellement `channel` **pour `script`**.

    Le canal est une etiquette de code, pas une etiquette de workflow : le meme
    `--pr-body-file` figure dans plusieurs workflows qui appellent d'autres
    scripts. Crediter un workflow sur la seule presence du jeton attribuerait a
    un garde un cablage qui ne le concerne pas -- la faute exacte que cet
    inventaire existe pour rendre visible.
    """
    if channel == API_GH:
        # Le script va chercher le body lui-meme : aucun workflow ne le cable.
        return []
    directory = root / WORKFLOW_ROOT
    if not directory.is_dir():
        return []
    via_fast_lane = script in discover_fast_lane_scripts(root)
    cabled: list[str] = []
    for wf in sorted(directory.glob("*.yml")):
        raw = wf.read_text(encoding="utf-8", errors="replace")
        text = _strip_comment_lines(raw)
        if not _channel_present(text, channel):
            continue
        if _script_invoked(text, script, via_fast_lane):
            cabled.append(wf.name)
    return cabled


# ---------------------------------------------------------------------------
# Table de reference (derivee par --emit-reference)
# ---------------------------------------------------------------------------

#: Etat constate sur `main` le 2026-10-26, derive par `--emit-reference`.
#: Chaque entree : canal -> `cabled_in` (workflows qui cablent reellement ce
#: canal **pour ce script**) et, quand `cabled_in` est vide, `uncabled_reason`.
#: Regenerer : `python scripts/ci/body_consuming_guards.py --emit-reference`,
#: puis reporter les `uncabled_reason` (seule partie non derivable : elle dit
#: pourquoi une absence est volontaire).
REFERENCE: dict[str, dict[str, dict]] = {
    "scripts/check_closure_dossier.py": {
        "channels": {
            "api-gh": {
                "cabled_in": [],
                "uncabled_reason": (
                    "va chercher le body lui-meme (`gh pr view --json body`, "
                    "l.260-261) ; aucun workflow ne le lui passe."
                ),
            },
        },
    },
    "scripts/ci/check_hr_substitution.py": {
        "channels": {
            "api-gh": {
                "cabled_in": [],
                "uncabled_reason": (
                    "va chercher le body lui-meme (`gh pr view --json body`, "
                    "l.67-69) ; aucun workflow ne le lui passe."
                ),
            },
        },
    },
    "scripts/lean/check_added_axioms_cliquet.py": {
        "channels": {
            "env:LEAN_CLIQUET_PR_BODY": {
                "cabled_in": ["always-on-guards.yml"],
            },
        },
    },
    "scripts/notebook_tools/check_credited_examples.py": {
        "channels": {
            "cli:--pr-body-file": {
                "cabled_in": [],
                "uncabled_reason": (
                    "option d'appel local ; la CI passe le body a "
                    "check_pr_exercises.py, qui porte le diff des exemples "
                    "credites (exercises-advisory.yml)."
                ),
            },
        },
    },
    "scripts/notebook_tools/check_kernel_drift.py": {
        "channels": {
            "env-file:PR_BODY_FILE": {
                "cabled_in": ["notebook-kernel-drift-guard.yml"],
            },
        },
    },
    "scripts/notebook_tools/check_output_collapse.py": {
        "channels": {
            "cli:--pr-body-file": {
                "cabled_in": [],
                "uncabled_reason": (
                    "canal fichier garde pour l'appel local ; la CI passe le "
                    "body en memoire par COLLAPSE_PR_BODY, pour eviter le "
                    "pattern CodeQL `actions/code-injection`."
                ),
            },
            "env:COLLAPSE_PR_BODY": {
                "cabled_in": [
                    "always-on-guards.yml",
                    "notebook-output-collapse-ratchet.yml",
                ],
            },
        },
    },
    "scripts/notebook_tools/check_pr_dotnet_nuget_block.py": {
        "channels": {
            "cli:--pr-body": {
                "cabled_in": [],
                "uncabled_reason": (
                    "dotnet-nuget-block-advisory.yml passe un fichier "
                    "(`--pr-body-file`) ; l'option litterale sert l'appel local."
                ),
            },
            "cli:--pr-body-file": {
                "cabled_in": ["dotnet-nuget-block-advisory.yml"],
            },
        },
    },
    "scripts/notebook_tools/check_pr_exercises.py": {
        "channels": {
            "cli:--pr-body-file": {
                "cabled_in": ["exercises-advisory.yml"],
            },
        },
    },
    "scripts/notebook_tools/credited_examples_sweep.py": {
        "channels": {
            "api-gh": {
                "cabled_in": [],
                "uncabled_reason": (
                    "va chercher le body PR par PR (`gh pr view --json body`, "
                    "l.303-305) ; aucun workflow ne le lui passe."
                ),
            },
        },
    },
    "scripts/notebook_tools/detect_md_content_loss.py": {
        "channels": {
            "cli:--pr-body": {
                "cabled_in": [],
                "uncabled_reason": (
                    "canal d'appel local ; la CI passe le body en memoire par "
                    "MD_CONTENT_LOSS_PR_BODY."
                ),
            },
            "cli:--pr-body-file": {
                "cabled_in": [],
                "uncabled_reason": (
                    "canal d'appel local ; la CI passe le body en memoire par "
                    "MD_CONTENT_LOSS_PR_BODY."
                ),
            },
            "env-file:MD_CONTENT_LOSS_PR_BODY_FILE": {
                "cabled_in": [],
                "uncabled_reason": (
                    "canal fichier de repli, conserve pour les tests unitaires ; "
                    "aucun workflow ne le cable."
                ),
            },
            "env:MD_CONTENT_LOSS_PR_BODY": {
                "cabled_in": [
                    "always-on-guards.yml",
                    "md-content-loss-gate.yml",
                ],
            },
        },
    },
    "scripts/notebook_tools/detect_notebook_plan_loss.py": {
        "channels": {
            "cli:--pr-body": {
                "cabled_in": [],
                "uncabled_reason": (
                    "canal d'appel local ; la CI passe le body en memoire par "
                    "PLAN_LOSS_PR_BODY."
                ),
            },
            "cli:--pr-body-file": {
                "cabled_in": [],
                "uncabled_reason": (
                    "canal d'appel local ; la CI passe le body en memoire par "
                    "PLAN_LOSS_PR_BODY."
                ),
            },
            "env-file:PLAN_LOSS_PR_BODY_FILE": {
                "cabled_in": [],
                "uncabled_reason": (
                    "canal fichier de repli, conserve pour les tests unitaires ; "
                    "aucun workflow ne le cable."
                ),
            },
            "env:PLAN_LOSS_PR_BODY": {
                "cabled_in": ["notebook-plan-loss-gate.yml"],
            },
        },
    },
    "scripts/notebook_tools/enrich_quality_ci.py": {
        "channels": {
            "cli:--pr-body-file": {
                "cabled_in": [],
                "uncabled_reason": (
                    "la CI passe le body par ENRICH_QUALITY_PR_BODY[_FILE] ; "
                    "l'option sert l'appel local."
                ),
            },
            "env-file:ENRICH_QUALITY_PR_BODY_FILE": {
                "cabled_in": ["enrich-quality-gate.yml"],
            },
            "env:ENRICH_QUALITY_PR_BODY": {
                "cabled_in": ["enrich-quality-gate.yml"],
            },
        },
    },
}


# ---------------------------------------------------------------------------
# Comparaison
# ---------------------------------------------------------------------------


def derive_reference(root: Path) -> dict[str, dict[str, dict]]:
    """Derive la table de reference depuis le depot (mode regeneration)."""
    derived: dict[str, dict[str, dict]] = {}
    for path, consumer in discover_consumers(root).items():
        channels: dict[str, dict] = {}
        for channel in consumer.sorted_channels():
            channels[channel] = {"cabled_in": find_cabling(root, path, channel)}
        derived[path] = {"channels": channels}
    return derived


def _declared_reason(entry: dict) -> str | None:
    reason = entry.get("uncabled_reason")
    return reason if isinstance(reason, str) and reason.strip() else None


def compare(
    root: Path,
    reference: dict[str, dict[str, dict]] | None = None,
) -> tuple[list[Deviation], list[Deviation]]:
    """Compare le depot a `reference`.

    Rend ``(ecarts_bloquants, observations)``. Les observations sont des faits
    a rapporter qui ne bloquent pas : un cablage **ajoute** ne casse rien, il
    informe. Un cablage **retire** est bloquant -- c'est le defaut #21552.
    """
    ref = REFERENCE if reference is None else reference
    discovered = discover_consumers(root)
    fatal: list[Deviation] = []
    notes: list[Deviation] = []

    for path in sorted(discovered):
        if path not in ref:
            for channel in discovered[path].sorted_channels():
                fatal.append(
                    Deviation(
                        "UNDECLARED",
                        path,
                        f"consommateur non declare, canal {channel}",
                    )
                )
            continue
        declared_channels = ref[path].get("channels", {})
        for channel in discovered[path].sorted_channels():
            if channel not in declared_channels:
                fatal.append(
                    Deviation(
                        "UNDECLARED_CHANNEL",
                        path,
                        f"canal {channel} consomme mais absent de la reference",
                    )
                )

    for path in sorted(ref):
        if path not in discovered:
            fatal.append(
                Deviation(
                    "VANISHED",
                    path,
                    "declare dans la reference, plus consomme par le code",
                )
            )
            continue
        for channel in sorted(ref[path].get("channels", {})):
            entry = ref[path]["channels"][channel]
            if channel not in discovered[path].channels:
                fatal.append(
                    Deviation(
                        "CHANNEL_DROPPED",
                        path,
                        f"canal {channel} declare mais plus detecte dans le code",
                    )
                )
                continue
            cabled_in = list(entry.get("cabled_in") or [])
            reason = _declared_reason(entry)
            if not cabled_in:
                if reason is None:
                    fatal.append(
                        Deviation(
                            "UNCABLED",
                            path,
                            f"canal {channel} sans cablage et sans motif "
                            "`uncabled_reason`",
                        )
                    )
                continue
            for wf in cabled_in:
                text = _workflow_text(root, wf)
                if text is None:
                    fatal.append(
                        Deviation(
                            "WORKFLOW_MISSING",
                            path,
                            f"canal {channel} : workflow declare {wf} introuvable",
                        )
                    )
                    continue
                if not _channel_present(_strip_comment_lines(text), channel):
                    fatal.append(
                        Deviation(
                            "CABLING_MISSING",
                            path,
                            f"canal {channel} : {wf} ne le cable plus",
                        )
                    )
            added = sorted(
                set(find_cabling(root, path, channel)) - set(cabled_in)
            )
            for wf in added:
                notes.append(
                    Deviation(
                        "CABLING_ADDED",
                        path,
                        f"canal {channel} : {wf} le cable desormais (a declarer)",
                    )
                )

    return fatal, notes


# ---------------------------------------------------------------------------
# Rendu
# ---------------------------------------------------------------------------


def render_table(root: Path) -> str:
    """Table lisible de l'inventaire mesure."""
    derived = derive_reference(root)
    if not derived:
        return "Aucun consommateur de body de PR detecte."
    lines = [
        f"{'script':<58} {'canal':<40} {'cable dans'}",
        "-" * 58 + " " + "-" * 40 + " " + "-" * 11,
    ]
    for path in sorted(derived):
        for channel in sorted(derived[path]["channels"]):
            cabled = derived[path]["channels"][channel]["cabled_in"]
            target = ", ".join(cabled) if cabled else "(aucun)"
            lines.append(f"{path:<58} {channel:<40} {target}")
    return "\n".join(lines)


def emit_reference(root: Path) -> str:
    """Bloc `REFERENCE` a coller, derive du depot courant."""
    derived = derive_reference(root)
    body = json.dumps(derived, indent=4, ensure_ascii=True, sort_keys=True)
    return "REFERENCE: dict[str, dict[str, dict]] = " + body


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _default_root() -> Path:
    return Path(__file__).resolve().parents[2]


def main(argv: list[str] | None = None, *, reference: dict | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Inventaire des gardes qui consomment le body d'une PR.",
    )
    parser.add_argument(
        "--root", default=None, help="Racine a inspecter (defaut : depot)."
    )
    parser.add_argument(
        "--reference-json",
        default=None,
        help=(
            "Table de reference en JSON (defaut : REFERENCE du module). "
            "Sert a verifier un arbre autre que celui dont la table est figee."
        ),
    )
    parser.add_argument("--json", action="store_true", help="Sortie JSON.")
    parser.add_argument(
        "--check",
        action="store_true",
        help="Compare le depot a REFERENCE ; sortie 1 en cas d'ecart.",
    )
    parser.add_argument(
        "--emit-reference",
        action="store_true",
        help="Affiche le bloc REFERENCE derive (a coller).",
    )
    args = parser.parse_args(argv)
    root = Path(args.root).resolve() if args.root else _default_root()
    if args.reference_json:
        loaded = json.loads(Path(args.reference_json).read_text(encoding="utf-8"))
        if reference is None:
            reference = loaded

    if args.emit_reference:
        print(emit_reference(root))
        return 0

    if args.check:
        fatal, notes = compare(root, reference)
        for note in notes:
            print(f"[observation] {note}")
        for deviation in fatal:
            print(f"[ecart] {deviation}")
        if fatal:
            print(
                f"\n{len(fatal)} ecart(s) : l'inventaire des gardes qui "
                "consomment le body de PR n'est plus a jour."
            )
            return 1
        if any(n.code == "CABLING_ADDED" for n in notes):
            print(
                "\nAucun ecart bloquant ; des cablages ont ete ajoutes "
                "(observations ci-dessus, a declarer dans REFERENCE)."
            )
        else:
            print("REFERENCE a jour : inventaire conforme.")
        return 0

    if args.json:
        print(
            json.dumps(
                derive_reference(root),
                indent=2,
                ensure_ascii=True,
                sort_keys=True,
            )
        )
        return 0

    print(render_table(root))
    return 0


if __name__ == "__main__":
    sys.exit(main())
