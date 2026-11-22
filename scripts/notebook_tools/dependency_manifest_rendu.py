#!/usr/bin/env python
"""Module rendu de l'organe manifeste des dependances (#27544).

Scission du 20/11 (#26364, cliquet de taille des scripts) : le module
d'origine depassait le plafond des scripts neufs. Les responsabilites
sont separees, la facade `dependency_manifest.py` garde le chemin
d'appel et re-expose l'API.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

_TOOLS_DIR = Path(__file__).resolve().parent
if str(_TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(_TOOLS_DIR))

from dependency_manifest_lecture import (
    Group,
    OPTIONAL_POLICIES,
)
def _group_dict(entry: Group) -> dict:
    """Serialise une ligne de la table."""
    return {
        "group": entry.path,
        "series": entry.series,
        "subseries": entry.subseries,
        "kernel_families": list(entry.kernel_families),
        "kernel_families_source": entry.kernel_families_source,
        "kernelspecs": dict(sorted(entry.kernelspecs.items())),
        "notebook_count": len(entry.notebooks),
        "dependency_files": entry.dependency_files,
        "package_count": len(entry.requirements),
        "requires_python": entry.requires_python,
        "requires_python_source": entry.requires_python_source,
        "requires_python_constraints": entry.requires_python_constraints,
        "needs": {
            "gpu": bool(entry.gpu_notebooks),
            "gpu_notebooks": entry.gpu_notebooks[:10],
            # Le **nombre** de variables d'environnement secretes, pas leurs
            # noms : un nom n'est pas un secret, mais il n'apporte rien a la
            # decision d'image et le scanner de secrets le refuse (regle
            # « aucune valeur de secret dans le depot »). Les noms restent
            # dans l'organe ; ils ne sont pas publies.
            "api_key_count": len(entry.api_keys),
            "network_services": sorted(entry.network_services),
            "local_endpoints": sorted(entry.local_endpoints)[:10],
            # Appels de service mesures, et ceux dont la cible n'est pas
            # lisible (le service ne peut alors pas etre nomme).
            "service_call_count": entry.service_calls,
            "dynamic_service_calls": entry.dynamic_service_calls,
            # Fichiers de code que le carnet cite (le moteur qu'il appelle).
            "companion_files": sorted(entry.companion_files)[:10],
        },
        "verdict": entry.verdict,
        "service_optionnel": any(
            motif["policy"] in OPTIONAL_POLICIES for motif in entry.motifs
        ),
        "motifs": entry.motifs,
        "gaps": sorted(set(entry.gaps)),
        "packages": sorted({req.name for req in entry.requirements}),
    }


def _census_summary(census: dict | None) -> dict:
    """Reduit le recensement #23073 aux divergences multi-versions."""
    if census is None:
        return {}
    divergences = []
    for library in census.get("libraries", []):
        versions = library.get("versions", [])
        if len(versions) > 1:
            divergences.append(
                {
                    "library": library.get("library"),
                    "canonical": library.get("canonical"),
                    "versions": [
                        {
                            "version": row.get("version"),
                            "count": row.get("count"),
                            "decision": row.get("decision"),
                        }
                        for row in versions
                    ],
                }
            )
    return {
        "organ": "scripts/notebook_tools/check_lib_versions.py (#23073)",
        "divergences": divergences,
        "below_canonical_count": len(census.get("below_canonical", [])),
        "unreadable_notebooks": len(census.get("unreadable_notebooks", [])),
    }


def _yes(value: bool) -> str:
    return "oui" if value else "non"


def render_markdown(manifest: dict) -> str:
    """Rend le manifeste en Markdown (table par groupe, conflits, consolidation)."""
    counts = manifest["counts"]
    lines: list[str] = []
    lines.append("# Manifeste des dependances du cursus")
    lines.append("")
    lines.append(
        "Fichier genere par `scripts/notebook_tools/dependency_manifest.py` (#27544) "
        f"sur `{manifest['generated_from']}`, sans reseau. Politique : "
        f"`{manifest['policy']}`. Ne pas editer a la main : la sortie est "
        "regeneree a chaque execution de l'organe."
    )
    lines.append("")
    lines.append(
        f"Mesure : {counts['notebooks']} carnets, "
        f"fichiers de dependances du cursus et hors cursus, "
        f"{counts['series']} series, {counts['groups']} groupes de repertoires, "
        f"{counts['included']} groupes inclus dans l'image CPU, "
        f"{counts['conflicts']} conflits de versions."
    )
    lines.append("")
    lines.append(
        "**Origine des motifs** : `mesure` = deduit d'une lecture du depot ; "
        "`declaration` = regle ecrite dans la politique versionnee, contestable."
    )
    fallbacks = counts.get("version_normalization_fallbacks", 0)
    if fallbacks:
        lines.append("")
        lines.append(
            f"**Repli de normalisation** : {fallbacks} version(s) comparee(s) sans "
            "l'organe natif des versions (`check_lib_versions.py`) : les conflits "
            "qui les concernent sont suspects et doivent etre relus a la source."
        )
    lines.append("")
    lines.append("## 1. Table par serie et sous-serie")
    lines.append("")
    lines.append(
        "| Groupe | Serie | Sous-serie | Noyaux | Fichiers de dependances | "
        "Carnets | GPU | Cle d'API (nb) | Service reseau | Verdict | Service optionnel | "
        "Motifs (origine) | Lacunes de declaration |"
    )
    lines.append("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for entry in manifest["groups"]:
        needs = entry["needs"]
        files = ", ".join(entry["dependency_files"]) or "aucun"
        motifs = " ; ".join(
            f"{m['origin']} : {m['text']}" for m in entry["motifs"]
        ) or "-"
        families = ", ".join(entry["kernel_families"])
        if not families:
            families = "non mesure"
        elif entry.get("kernel_families_source") == "herite":
            families += " (herite des sous-repertoires)"
        lines.append(
            f"| `{entry['group']}` | {entry['series']} | {entry['subseries'] or '-'} | "
            f"{', '.join(entry['kernel_families']) or '-'} | {files} | "
            f"{entry['notebook_count']} | {_yes(needs['gpu'])} | "
            f"{needs['api_key_count'] or '-'} | "
            f"{', '.join(needs['network_services']) or '-'} | "
            f"**{entry['verdict']}** | {_yes(entry['service_optionnel'])} | "
            f"{motifs} | "
            f"{', '.join(entry['gaps']) or '-'} |"
        )
    lines.append("")
    lines.append("## 2. Conflits de versions")
    lines.append("")
    if not manifest["conflicts"]:
        lines.append(
            "Aucun conflit : chaque paquet porte un specification unique dans tout "
            "le corpus des fichiers de dependances."
        )
    else:
        lines.append("| Paquet | Classe | Specifications en presence | Sources | Resolution proposee |")
        lines.append("|---|---|---|---|---|")
        for conflict in manifest["conflicts"]:
            sources = "; ".join(
                f"{item['spec']} ({item['file']})" for item in conflict["sources"]
            )
            resolution = conflict["resolution"]
            version = resolution["version"] or "paquet ecarte"
            lines.append(
                f"| `{conflict['package']}` | {conflict['class']} | "
                f"{', '.join(conflict['specifiers'])} | {sources} | "
                f"{resolution['policy']} -> {version} |"
            )
    lines.append("")
    lines.append("## 3. Manifeste consolide (source unique des paquets de l'image)")
    lines.append("")
    if not manifest["consolidated_manifest"]:
        lines.append("Aucune serie incluse : le manifeste consolide est vide.")
    else:
        lines.append("| Paquet | Version retenue | Groupes | Conflit |")
        lines.append("|---|---|---|---|")
        for record in manifest["consolidated_manifest"]:
            version = record["version"] or "a resoudre"
            lines.append(
                f"| `{record['package']}` | {version} | "
                f"{len(record['groups'])} | {_yes(record['conflict'])} |"
            )
    census = manifest.get("library_census") or {}
    divergences = census.get("divergences", [])
    lines.append("")
    lines.append("## 4. Lacunes de declaration")
    lines.append("")
    lines.append(
        "Paquets **importes** par les carnets d'un groupe mais **absents** de ses "
        "fichiers de dependances : l'image ne les installera pas, le carnet "
        "echouera a l'execution. La correspondance import -> paquet est une "
        "declaration (voir la politique) ; l'absence dans les fichiers de "
        "dependances est une mesure."
    )
    lines.append("")
    gaps = [(entry["group"], entry["gaps"]) for entry in manifest["groups"] if entry["gaps"]]
    if not gaps:
        lines.append("Aucune lacune detectee sur les paquets de la table d'alias.")
    else:
        lines.append("| Groupe | Paquets importes non declares |")
        lines.append("|---|---|")
        for group, packages in gaps:
            lines.append(f"| `{group}` | {', '.join(packages)} |")
    lines.append("")
    lines.append("## 5. Divergences canonique/observe (organe #23073)")
    lines.append("")
    if manifest.get("library_census_error"):
        lines.append(
            f"Recensement #23073 indisponible : {manifest['library_census_error']}"
        )
    elif not divergences:
        lines.append("Aucune bibliotheque a plusieurs versions dans le corpus.")
    else:
        lines.append("| Bibliotheque | Canonique | Versions observees |")
        lines.append("|---|---|---|")
        for divergence in divergences:
            observed = ", ".join(
                f"{row['version']} ({row['count']} carnets)"
                for row in divergence["versions"]
            )
            lines.append(
                f"| `{divergence['library']}` | {divergence['canonical'] or '-'} | "
                f"{observed} |"
            )
    lines.append("")
    lines.append("## 6. Fichiers de dependances hors cursus")
    lines.append("")
    lines.append(
        "Ces fichiers servent l'outillage et les services, pas les series : ils "
        "n'entrent pas dans le manifeste de l'image."
    )
    lines.append("")
    for relative in manifest["infra_dependency_files"]:
        lines.append(f"- `{relative}`")
    lines.append("")
    return "\n".join(lines)


#: Champs ignores par la garde de fraicheur. Le SHA de generation change a
#: chaque commit et le compte de fichiers suivis change avec l'arbre : les deux
#: decrivent l'ETAT DU DEPOT, pas le contenu du manifeste. Tout le reste est
#: compare : un manifeste qui ne decrit plus l'arbre est perime.
FRESHNESS_IGNORED_TOP = ("generated_from",)
FRESHNESS_IGNORED_COUNTS = ("tracked_files",)
#: Un SHA de commit, neutralise dans la comparaison du Markdown.
SHA_RE = re.compile(r"\b[0-9a-f]{40}\b")


def _normalize_for_freshness(manifest: dict) -> dict:
    """La copie comparable d'un manifeste : hors SHA, hors compte de fichiers.

    Les groupes sont **indexes par leur nom** et non par leur rang : l'ajout
    d'un groupe ne doit pas faire conclure que tous les suivants ont change.
    """
    normalized = {
        key: value
        for key, value in manifest.items()
        if key not in FRESHNESS_IGNORED_TOP
    }
    counts = dict(normalized.get("counts") or {})
    for key in FRESHNESS_IGNORED_COUNTS:
        counts.pop(key, None)
    normalized["counts"] = counts
    groups = normalized.get("groups")
    if isinstance(groups, list):
        normalized["groups"] = {
            str(group.get("group")): group
            for group in groups
            if isinstance(group, dict)
        }
    return normalized


def _diff_paths(left, right, prefix: str = "") -> list[str]:
    """Les chemins JSON qui different entre deux structures."""
    diffs: list[str] = []
    if isinstance(left, dict) and isinstance(right, dict):
        for key in sorted(set(left) | set(right)):
            path = prefix + "/" + str(key)
            if key not in left:
                diffs.append(path + " (absent du manifeste committe)")
            elif key not in right:
                diffs.append(path + " (absent de la regeneration)")
            else:
                diffs.extend(_diff_paths(left[key], right[key], path))
        return diffs
    if isinstance(left, list) and isinstance(right, list):
        if len(left) != len(right):
            return [prefix + " (longueur %d/%d)" % (len(left), len(right))]
        for index, (one, other) in enumerate(zip(left, right)):
            diffs.extend(_diff_paths(one, other, prefix + "/" + str(index)))
        return diffs
    if left != right:
        diffs.append(prefix + " : %r != %r" % (left, right))
    return diffs


def _normalize_markdown(text: str) -> str:
    """Le Markdown compare : le SHA de generation est neutralise."""
    return SHA_RE.sub("<sha>", text)


