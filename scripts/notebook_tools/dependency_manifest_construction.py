#!/usr/bin/env python
"""Module construction de l'organe manifeste des dependances (#27544).

Scission du 20/11 (#26364, cliquet de taille des scripts) : le module
d'origine depassait le plafond des scripts neufs. Les responsabilites
sont separees, la facade `dependency_manifest.py` garde le chemin
d'appel et re-expose l'API.
"""
from __future__ import annotations

import re
import sys
from collections import defaultdict
from pathlib import Path

_TOOLS_DIR = Path(__file__).resolve().parent
if str(_TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(_TOOLS_DIR))

from dependency_manifest_lecture import (
    CODE_MENTION_RE,
    COMPANION_CODE_SUFFIXES,
    ENV_READ_RE,
    ENV_SECRET_NAME_RE,
    EXCLUSION_POLICIES,
    Group,
    IMPORT_RE,
    LOCAL_HOSTS,
    NOTEBOOKS_ROOT,
    OPTIONAL_POLICIES,
    POLICY_RELPATH,
    Requirement,
    SCHEMA_VERSION,
    _LIB_VERSIONS_IMPORT_ERROR,
    _REPO_ROOT,
    _VERSION_FALLBACK_CALLS,
    _cell_sources,
    _companion_sources,
    _compare,
    _descendant_families,
    _endpoints,
    _kernel_family,
    _max_version,
    _min_version,
    _norm_name,
    _norm_ver,
    _notebook_payload,
    _python_constraints,
    _service_calls,
    _split_series,
    _version_sort_key,
    git_ls_files,
    git_sha,
    load_lib_manifest,
    load_policy,
    read_requirements,
    run_census,
)
from dependency_manifest_rendu import (
    _census_summary,
    _group_dict,
)
def _record_endpoints(
    entry: Group, source: str, local_ports: dict, services: dict
) -> None:
    """Note les endpoints vises et les services qu'ils nomment."""
    for host, port in _endpoints(source):
        endpoint = f"{host}:{port}" if port else host
        if host.lower() in LOCAL_HOSTS:
            if endpoint not in entry.local_endpoints:
                entry.local_endpoints.append(endpoint)
            if port and port in local_ports:
                service = local_ports[port]
                if service not in entry.network_services:
                    entry.network_services.append(service)
            continue
        service = services.get(host.lower())
        if service and service not in entry.network_services:
            entry.network_services.append(service)


def _record_service_calls(entry: Group, source: str) -> None:
    """Note les appels de service et ceux dont la cible n'est pas lisible."""
    total, dynamic = _service_calls(source)
    entry.service_calls += total
    entry.dynamic_service_calls += dynamic


def _specifier_bounds(spec: str) -> dict:
    """Decoupe un specification PEP 440 en bornes elementaires."""
    bounds: dict = {"lower": "", "upper": "", "exact": "", "excludes": []}
    for part in (spec or "").split(","):
        part = part.strip()
        if not part:
            continue
        match = re.match(r"^(==|!=|>=|<=|~=|>|<)\s*([^\s,]+)$", part)
        if not match:
            continue
        operator, version = match.groups()
        if operator == "==":
            bounds["exact"] = version
        elif operator == "!=":
            bounds["excludes"].append(version)
        elif operator in (">=", ">"):
            bounds["lower"] = _max_version(bounds["lower"], version)
        elif operator in ("<=", "<"):
            bounds["upper"] = _min_version(bounds["upper"], version)
        elif operator == "~=":
            bounds["lower"] = _max_version(bounds["lower"], version)
    return bounds


def _specifiers_compatible(left: dict, right: dict) -> bool:
    """Deux jeux de bornes ont-ils une intersection non vide ?"""
    if left["exact"] and right["exact"]:
        return _compare(left["exact"], right["exact"]) == 0
    exact = left["exact"] or right["exact"]
    lower = max(filter(None, (left["lower"], right["lower"])), default="", key=_version_sort_key)
    upper = min(filter(None, (left["upper"], right["upper"])), default="", key=_version_sort_key)
    if lower and upper and _compare(lower, upper) > 0:
        return False
    if exact:
        if lower and _compare(exact, lower) < 0:
            return False
        if upper and _compare(exact, upper) > 0:
            return False
        for excluded in left["excludes"] + right["excludes"]:
            if excluded == exact:
                return False
    return True


#: Extensions des fichiers de dependances, toutes conventions de nom confondues.
_DEPENDENCY_FILE_SUFFIXES = (".txt", ".yml", ".yaml")

#: Convention `<Carnet>-requirements.txt` (serie `SymbolicAI/Lean/Noeuds`), avec
#: ses variantes suffixees (`-requirements-legacy.txt`) et sa forme conda
#: (`-environment.yml`). Le nom du carnet precede toujours un tiret.
_NOTEBOOK_PREFIXED_DEPENDENCY = re.compile(
    r"-(?:requirements|environment)(?:-[A-Za-z0-9_.]+)?\.(?:txt|ya?ml)$"
)


def is_dependency_file(path: str) -> bool:
    """Vrai si ``path`` declare des dependances, quelle que soit sa convention.

    Deux conventions coexistent dans le depot : le fichier de serie
    (``requirements*.txt``, ``environment*.yml``) et le fichier rattache a un
    carnet (``<Carnet>-requirements.txt``). Lire l'une sans l'autre laisse une
    serie entiere hors du manifeste, donc hors de l'image d'apprentissage
    (#28878) : les deux sont reconnues ici, en un seul endroit.
    """
    name = Path(path).name
    if not name.endswith(_DEPENDENCY_FILE_SUFFIXES):
        return False
    if name.startswith(("requirements", "environment")):
        return True
    return _NOTEBOOK_PREFIXED_DEPENDENCY.search(name) is not None


def build_manifest(repo_root: Path) -> dict:
    """Construit le manifeste complet (donnees brutes, sans rendu)."""
    _VERSION_FALLBACK_CALLS.clear()
    policy = load_policy(repo_root)
    gpu_re = re.compile("|".join(policy["gpu"]["markers"]), re.IGNORECASE)
    heavy = policy["heavy_distributions"]["entries"]
    licensed = policy["licenses"]["entries"]
    optional_markers = policy["optional_file_markers"]["markers"]
    services = policy["container_services"]["entries"]
    local_ports = policy["local_ports"]["entries"]
    canonical_python = policy["canonical_python_by_kernelspec"]["entries"]
    ambiguous_python = policy["canonical_python_by_kernelspec"].get("ambiguous", {})

    tracked = git_ls_files(repo_root)
    notebooks = [f for f in tracked if f.endswith(".ipynb")]
    dependency_files = [f for f in tracked if is_dependency_file(f)]

    # --- groupes (repertoires qui portent directement des carnets ou deps) ---
    groups: dict[str, Group] = {}

    def group_entry(path: str) -> Group:
        directory = str(Path(path).parent).replace("\\", "/")
        if directory not in groups:
            series, subseries = _split_series(directory)
            groups[directory] = Group(
                path=directory, series=series, subseries=subseries
            )
        return groups[directory]

    notebook_groups: dict[str, str] = {}
    for relative in notebooks:
        if not relative.startswith(NOTEBOOKS_ROOT + "/"):
            continue
        entry = group_entry(relative)
        notebook_groups[relative] = entry.path

    dep_groups: dict[str, str] = {}
    for relative in dependency_files:
        if not relative.startswith(NOTEBOOKS_ROOT + "/"):
            continue
        entry = group_entry(relative)
        dep_groups[relative] = entry.path

    # --- fichiers de code candidats au role de compagnon --------------------
    # Un carnet cite parfois son moteur par son nom de fichier. On ne retient
    # que les noms **uniques** dans l'arbre : un nom ambigu (`utils.py`) ne
    # designe aucun moteur et ne doit pas etre lu comme tel.
    code_files: dict[str, list[str]] = defaultdict(list)
    for relative in tracked:
        if not relative.startswith(NOTEBOOKS_ROOT + "/"):
            continue
        if not relative.endswith(COMPANION_CODE_SUFFIXES):
            continue
        name = Path(relative).name
        code_files[name].append(relative)
        code_files[name[: -len(Path(name).suffix)]].append(relative)
    companion_by_name = {
        name: paths[0] for name, paths in code_files.items() if len(paths) == 1
    }

    # --- carnets : famille de noyau et besoins -------------------------------
    for relative in notebooks:
        entry = groups.get(notebook_groups.get(relative, ""))
        if entry is None:
            continue
        payload = _notebook_payload(repo_root / relative)
        if payload is None:
            continue
        entry.notebooks.append(relative)
        kernelspec = (payload.get("metadata", {}) or {}).get("kernelspec", {}) or {}
        language = (kernelspec.get("language") or "").strip()
        name = (kernelspec.get("name") or language or "inconnu").strip()
        entry.kernelspecs[name] = entry.kernelspecs.get(name, 0) + 1
        joined = "\n".join(_cell_sources(payload))
        for first, second in IMPORT_RE.findall(joined):
            module = (first or second or "").split(".")[0]
            if module:
                entry.imports.add(module)
        if gpu_re.search(joined):
            entry.gpu_notebooks.append(relative)
        for variable in ENV_READ_RE.findall(joined):
            if ENV_SECRET_NAME_RE.search(variable) and variable not in entry.api_keys:
                entry.api_keys.append(variable)
        _record_endpoints(entry, joined, local_ports, services)
        _record_service_calls(entry, joined)
        for token in CODE_MENTION_RE.findall(joined):
            companion = companion_by_name.get(token)
            if companion and companion not in entry.companion_files:
                entry.companion_files.append(companion)

    # --- fichiers de code compagnon : les services qu'ils appellent ---------
    # Le carnet appelle son moteur (le pont Fast Downward en C#) : le service
    # que ce fichier appelle est un besoin du carnet, pas un detail du fichier.
    for entry in groups.values():
        for _relative, source in _companion_sources(
            repo_root, set(entry.companion_files)
        ):
            _record_endpoints(entry, source, local_ports, services)
            _record_service_calls(entry, source)

    # --- fichiers de dependances (heritage des repertoires ancetres) ---------
    for relative, group_path in dep_groups.items():
        groups[group_path].dependency_files.append(relative)
    for group_path, entry in groups.items():
        applicable: list[str] = []
        for relative, dep_group in dep_groups.items():
            if group_path == dep_group or group_path.startswith(dep_group + "/"):
                applicable.append(relative)
        for relative in sorted(applicable):
            entry.requirements.extend(
                read_requirements(repo_root, relative, group_path)
            )

    # --- contraintes d'interpreteur -----------------------------------------
    # Deux champs peuvent declarer une contrainte : le plancher d'installation
    # du paquet (`project.requires-python`) et l'env de la serie
    # (`tool.coursia.pinned_env.requires-python`). C'est l'env de la serie qui
    # prime : c'est elle que les carnets traversent. Lire la seule premiere
    # ferait passer pour compatible un env que la serie n'utilise pas.
    for relative in tracked:
        if not relative.endswith("pyproject.toml"):
            continue
        if not relative.startswith(NOTEBOOKS_ROOT + "/"):
            continue
        constraints = _python_constraints(repo_root, relative)
        if not constraints:
            continue
        directory = str(Path(relative).parent).replace("\\", "/")
        target = groups.get(directory)
        if target is None:
            continue
        target.requires_python_constraints = [
            {"field": name, "constraint": value} for name, value in constraints
        ]
        effective_field, effective = constraints[-1]
        target.requires_python = effective
        target.requires_python_source = f"{relative} [{effective_field}]"

    # --- verdicts ------------------------------------------------------------
    import_aliases = {
        _norm_name(module): _norm_name(package)
        for module, package in policy["import_aliases"]["entries"].items()
    }
    for entry in groups.values():
        motifs: list[dict] = []
        verdict = "inclus"
        declared = {requirement.name for requirement in entry.requirements}
        for module in sorted(entry.imports):
            package = import_aliases.get(module)
            if package and package not in declared:
                entry.gaps.append(package)

        families: list[str] = []
        for kernelspec in entry.kernelspecs:
            family = _kernel_family(kernelspec)
            if family not in families:
                families.append(family)
        families_source = "direct" if families else ""
        if not families:
            # Le groupe ne porte directement aucun carnet : sa famille se lit
            # dans ses sous-repertoires (mesure), et seulement s'il n'y en a
            # pas non plus, la famille reste **inconnue** — ce qui ne vaut pas
            # une exclusion.
            inherited = _descendant_families(entry.path, groups)
            if inherited:
                families = inherited
                families_source = "herite"
        entry.kernel_families = families
        entry.kernel_families_source = families_source or "non mesure"

        if entry.gpu_notebooks:
            motifs.append(
                {
                    "origin": "mesure",
                    "policy": "gpu",
                    "text": (
                        f"GPU requis : marqueur mesure dans {len(entry.gpu_notebooks)} "
                        "carnet(s) de la serie"
                    ),
                }
            )
        heavy_found = sorted(
            {
                heavy[req.name]
                for req in entry.requirements
                if req.name in heavy
            }
        )
        if heavy_found:
            motifs.append(
                {
                    "origin": "declaration",
                    "policy": "heavy_distributions",
                    "text": (
                        "taille : distribution(s) lourde(s) hors image CPU legere ("
                        + ", ".join(heavy_found)
                        + ")"
                    ),
                }
            )
        licensed_found = sorted(
            {
                licensed[req.name]
                for req in entry.requirements
                if req.name in licensed
            }
        )
        if licensed_found:
            motifs.append(
                {
                    "origin": "declaration",
                    "policy": "licenses",
                    "text": "licence : " + ", ".join(licensed_found),
                }
            )
        optional_files = [
            f
            for f in entry.dependency_files
            if any(marker in Path(f).name.lower() for marker in optional_markers)
        ]
        if optional_files:
            motifs.append(
                {
                    "origin": "declaration",
                    "policy": "optional_file_markers",
                    "text": "fichier de dependances optionnel : "
                    + ", ".join(optional_files),
                }
            )
        if entry.network_services:
            motifs.append(
                {
                    "origin": "declaration",
                    "policy": "container_services",
                    "text": "service conteneurise requis (patron Planners) : "
                    + ", ".join(sorted(entry.network_services)),
                }
            )
        if not families:
            # Aucun carnet, donc aucune famille observee : c'est une **absence
            # de mesure**, pas une mesure de non-Python. Exclure sur cette base
            # ferait disparaitre du manifeste consolide des paquets reellement
            # declares (cas `cross-series/matching-cv`, `agent_tests`).
            motifs.append(
                {
                    "origin": "declaration",
                    "policy": "kernel_family_unmeasured",
                    "text": (
                        "aucun carnet dans ce groupe ni dans ses sous-repertoires : "
                        "famille de noyau non mesurable ; l'absence de mesure "
                        "n'exclut pas le groupe"
                    ),
                }
            )
        elif all(family != "Python" for family in families):
            motifs.append(
                {
                    "origin": "mesure",
                    "policy": "kernel_family",
                    "text": (
                        "noyau non-Python ("
                        + ", ".join(families)
                        + ") : hors image CPU Python"
                    ),
                }
            )
        # Conflit de version d'interpreteur : la contrainte effective de la
        # serie vs la version Python canonique de ses noyaux. Le conflit est
        # declare des qu'UN noyau canonique est incompatible : la serie ne
        # tourne pas sous la totalite de ses noyaux.
        if entry.requires_python and entry.kernelspecs:
            bounds = _specifier_bounds(entry.requires_python)
            for kernel in sorted(entry.kernelspecs):
                canonical = canonical_python.get(kernel.lower())
                if canonical is None:
                    note = ambiguous_python.get(kernel.lower())
                    if note:
                        motifs.append(
                            {
                                "origin": "declaration",
                                "policy": "canonical_python_by_kernelspec",
                                "text": (
                                    "version Python canonique ambigue pour le noyau "
                                    f"{kernel} ({note}) : aucun conflit declare"
                                ),
                            }
                        )
                    continue
                allowed = _specifiers_compatible(
                    {"exact": "", "lower": canonical, "upper": "", "excludes": []},
                    {
                        "exact": "",
                        "lower": bounds["lower"],
                        "upper": bounds["upper"],
                        "excludes": bounds["excludes"],
                    },
                )
                if not allowed:
                    motifs.append(
                        {
                            "origin": "mesure",
                            "policy": "requires_python",
                            "text": (
                                "conflit de versions d'interpreteur : "
                                f"{entry.requires_python_source} exige "
                                f"Python {entry.requires_python}, le noyau "
                                f"canonique {kernel} est Python {canonical}"
                            ),
                        }
                    )
                    break
        # Appel de service dont la cible n'est pas lisible : le service ne peut
        # pas etre nomme, donc la serie n'est pas prouvee autonome.
        if entry.dynamic_service_calls:
            motifs.append(
                {
                    "origin": "mesure",
                    "policy": "dynamic_service_calls",
                    "text": (
                        "appel(s) de service dont l'URL n'est pas lisible sur la "
                        f"ligne de l'appel : {entry.dynamic_service_calls}"
                    ),
                }
            )
        # Le verdict est la **consequence** des motifs : une exclusion l'emporte
        # sur un service optionnel, tous les motifs restent affiches.
        policies = {motif["policy"] for motif in motifs}
        if policies & EXCLUSION_POLICIES:
            verdict = "exclu"
        elif policies & OPTIONAL_POLICIES:
            verdict = "service optionnel"
        else:
            verdict = "inclus"
        entry.verdict = verdict
        entry.motifs = motifs

    # --- conflits de versions ------------------------------------------------
    specs: dict[str, list[Requirement]] = defaultdict(list)
    for entry in groups.values():
        for requirement in entry.requirements:
            if requirement.spec:
                specs[requirement.name].append(requirement)
    conflicts: list[dict] = []
    for name in sorted(specs):
        by_spec: dict[str, list[Requirement]] = defaultdict(list)
        for requirement in specs[name]:
            by_spec[requirement.spec].append(requirement)
        # Deux specifications qui disent la meme chose (`>=0.29` et `>=0.29.0`)
        # ne sont pas un conflit : le conflit se mesure sur les **bornes
        # effectives**, pas sur l'ecriture.
        by_bounds: dict[tuple, list[str]] = defaultdict(list)
        bounds: dict[str, dict] = {}
        for spec in sorted(by_spec):
            bound = _specifier_bounds(spec)
            bounds[spec] = bound
            key = (
                _norm_ver(bound["exact"]),
                _norm_ver(bound["lower"]),
                _norm_ver(bound["upper"]),
                tuple(sorted(_norm_ver(item) for item in bound["excludes"])),
            )
            by_bounds[key].append(spec)
        if len(by_bounds) < 2:
            continue
        representatives = sorted(spells[0] for spells in by_bounds.values())
        distinct = representatives
        incompatible = False
        for index, left in enumerate(distinct):
            for right in distinct[index + 1 :]:
                if not _specifiers_compatible(bounds[left], bounds[right]):
                    incompatible = True
        exact_pins = {
            spec: bound["exact"] for spec, bound in bounds.items() if bound["exact"]
        }
        if len({_norm_ver(value) for value in exact_pins.values()}) > 1:
            klass = "pin_exact_divergent"
        elif incompatible:
            klass = "incompatible"
        else:
            klass = "specifier_divergent"
        sources = []
        for spec in distinct:
            spec_key = (
                _norm_ver(bounds[spec]["exact"]),
                _norm_ver(bounds[spec]["lower"]),
                _norm_ver(bounds[spec]["upper"]),
                tuple(sorted(_norm_ver(item) for item in bounds[spec]["excludes"])),
            )
            equivalent = sorted(
                spell
                for spells in by_bounds.values()
                for spell in spells
                if (
                    _norm_ver(_specifier_bounds(spell)["exact"]),
                    _norm_ver(_specifier_bounds(spell)["lower"]),
                    _norm_ver(_specifier_bounds(spell)["upper"]),
                    tuple(
                        sorted(
                            _norm_ver(item)
                            for item in _specifier_bounds(spell)["excludes"]
                        )
                    ),
                )
                == spec_key
            )
            sources.append(
                {
                    "spec": spec,
                    "equivalent_spellings": equivalent,
                    "file": by_spec[spec][0].source_file,
                    "series": by_spec[spec][0].group,
                    "occurrences": len(by_spec[spec]),
                }
            )
        conflicts.append(
            {
                "package": name,
                "class": klass,
                "specifiers": distinct,
                "sources": sources,
                "resolution": _propose_resolution(name, klass, bounds, distinct),
            }
        )

    # --- manifeste consolide -------------------------------------------------
    included = [g for g in groups.values() if g.verdict == "inclus"]
    consolidated: dict[str, dict] = {}
    for entry in included:
        for requirement in entry.requirements:
            record = consolidated.setdefault(
                requirement.name,
                {
                    "package": requirement.name,
                    "version": "",
                    "specs": [],
                    "groups": [],
                    "conflict": False,
                },
            )
            if requirement.spec and requirement.spec not in record["specs"]:
                record["specs"].append(requirement.spec)
            if entry.path not in record["groups"]:
                record["groups"].append(entry.path)
    conflict_names = {conflict["package"] for conflict in conflicts}
    for name, record in consolidated.items():
        record["conflict"] = name in conflict_names
        pins = sorted(
            {
                requirement.pinned
                for entry in included
                for requirement in entry.requirements
                if requirement.name == name and requirement.pinned
            },
            key=_version_sort_key,
        )
        if len(pins) == 1:
            record["version"] = pins[0]
        elif len(pins) > 1:
            record["version"] = ""
        else:
            record["version"] = ""
    consolidated_list = sorted(consolidated.values(), key=lambda r: r["package"])

    # --- divergences canonique/observe (organe #23073) ----------------------
    census: dict | None = None
    census_error = ""
    if run_census is not None and load_lib_manifest is not None:
        try:
            manifest = load_lib_manifest(
                _REPO_ROOT / "scripts/notebook_tools/lib_versions_manifest.json"
            )
            census = run_census(repo_root, manifest)
        except Exception as exc:  # noqa: BLE001 - la degrade du recensement est signalee
            census_error = f"{type(exc).__name__}: {exc}"
    else:
        census_error = (
            "check_lib_versions indisponible : "
            f"{_LIB_VERSIONS_IMPORT_ERROR}"
        )

    infra_files = [
        f
        for f in dependency_files
        if not f.startswith(NOTEBOOKS_ROOT + "/")
    ]

    return {
        "schema_version": SCHEMA_VERSION,
        "generated_from": git_sha(repo_root),
        "policy": POLICY_RELPATH,
        "counts": {
            "tracked_files": len(tracked),
            "notebooks": len(notebooks),
            "dependency_files": len(dependency_files),
            "curriculum_dependency_files": len(dependency_files) - len(infra_files),
            "infra_dependency_files": len(infra_files),
            "groups": len(groups),
            # La racine du cursus (`MyIA.AI.Notebooks`, qui ne porte que
            # `GradeBook.ipynb`) ne **nomme** aucune serie : la compter
            # gonflerait le total d'une serie fantome.
            "series": len({g.series for g in groups.values() if g.series}),
            "included": len(included),
            "conflicts": len(conflicts),
            # Replis de normalisation de version : autant de conflits sont
            # suspects que de replis (l'organe natif des versions etait
            # indisponible sur ces chaines).
            "version_normalization_fallbacks": len(_VERSION_FALLBACK_CALLS),
        },
        "groups": [_group_dict(g) for g in sorted(groups.values(), key=lambda g: g.path)],
        "conflicts": conflicts,
        "consolidated_manifest": consolidated_list,
        "infra_dependency_files": sorted(infra_files),
        "library_census": _census_summary(census),
        "library_census_error": census_error,
    }


def _propose_resolution(
    name: str, klass: str, bounds: dict[str, dict], distinct: list[str]
) -> dict:
    """Propose une resolution de conflit, version par version."""
    if klass == "pin_exact_divergent":
        pins = sorted(
            {bounds[spec]["exact"] for spec in distinct}, key=_version_sort_key
        )
        return {
            "policy": "retenir le pin le plus haut, puis aligner les series en aval",
            "version": pins[-1],
            "note": (
                f"aligner les series qui epinglent une version inferieure sur "
                f"{name}=={pins[-1]} (verifier la compatibilite du noyau)"
            ),
        }
    if klass == "incompatible":
        lowers = [bounds[spec]["lower"] for spec in distinct if bounds[spec]["lower"]]
        uppers = [bounds[spec]["upper"] for spec in distinct if bounds[spec]["upper"]]
        lower = _max_version("", "") if not lowers else lowers[0]
        for candidate in lowers[1:]:
            lower = _max_version(lower, candidate)
        upper = uppers[0] if uppers else ""
        for candidate in uppers[1:]:
            upper = _min_version(upper, candidate)
        return {
            "policy": "aucune version commune : le paquet est ecarte du manifeste consolide",
            "version": "",
            "note": (
                "bornes en presence : "
                + (f"lower={lower} " if lower else "")
                + (f"upper={upper} " if upper else "")
                + " ; aligner les series sur une borne unique avant de reinclure "
                f"{name}"
            ),
        }
    lowers = [bounds[spec]["lower"] for spec in distinct if bounds[spec]["lower"]]
    uppers = [bounds[spec]["upper"] for spec in distinct if bounds[spec]["upper"]]
    lower = lowers[0] if lowers else ""
    for candidate in lowers[1:]:
        lower = _max_version(lower, candidate)
    upper = uppers[0] if uppers else ""
    for candidate in uppers[1:]:
        upper = _min_version(upper, candidate)
    return {
        "policy": "retenir l'intersection des bornes (la plus stricte)",
        "version": (f">={lower}" if lower else "") + (f",<{upper}" if upper else ""),
        "note": (
            f"bornes communes : lower={lower or '-'} upper={upper or '-'}"
        ),
    }


