#!/usr/bin/env python
"""Manifeste des dependances du cursus, par famille de noyau (#27544).

Cet organe repond a la question posee par le pli 1 de l'Epic #27543 :
**que doit contenir l'image d'apprentissage CPU, et qu'en reste-t-il exclu ?**
Il produit, depuis `git ls-files` et **sans reseau**, la table qui decide du
contenu de l'image 1.2 (cf. #27545).

Ce que fait l'organe
--------------------

1. **Recensement** : il enumere les fichiers de dependances declares
   (`requirements*.txt`, `environment*.yml`, et la convention de carnet
   `<Carnet>-requirements.txt`) et les rattache a la **serie** et
   a la **sous-serie** qui les portent ; il enumere les carnets de ces series
   et en lit le `kernelspec`, d'ou la **famille de noyau** (Python, .NET, Lean,
   Rust). Aucune serie du depot n'est absente de la table : une serie sans
   fichier de dependances y figure avec la mention ``aucun``.

2. **Besoins** : pour chaque serie, il mesure sur les **sources des cellules**
   des carnets trois besoins : **GPU**, **cle d'API**, **service reseau**.
   La mesure porte sur des marqueurs explicites ; rien n'est devine.
   Le service reseau est lu a trois profondeurs : l'URL **en dur**
   (``http://localhost:8200``), l'URL dont le port est une **constante**
   du carnet (``FD_API_PORT = 8200`` puis ``f"http://localhost:{FD_API_PORT}"``),
   et le **fichier de code que le carnet cite** (le pont Fast Downward en C# :
   le service que ce fichier appelle est un besoin du carnet). Les appels de
   service dont l'URL n'est pas lisible sur la ligne de l'appel sont comptes
   a part : ils disent qu'un appel existe, pas quel service il vise.

3. **Verdict d'inclusion** dans l'image CPU, avec un **motif** obligatoire.
   Chaque motif porte son **origine** :

   - ``mesure`` : le verdict se deduit d'une lecture du depot (GPU detecte,
     versions en conflit, noyau non-Python, contrainte ``requires-python``) ;
   - ``declaration`` : le verdict repose sur une regle ecrite dans la
     **politique versionnee** (``dependency_manifest_policy.json``), que le
     lecteur peut contester (poids d'une distribution, dependances
     optionnelles, services containerises).

   Les deux natures sont **distinguees dans la table** : c'est ce qui rend la
   table verifiable. Le motif ``licence`` existe dans la politique mais sa
   liste est **vide a dessein** — aucune source du depot n'etablit, hors
   ligne, une contrainte de licence ; simuler un inventaire de licences serait
   une invention, pas une mesure.

   Les motifs sont **cumulatifs** : une serie exclue pour GPU et pour poids
   porte les deux motifs. Une exclusion l'emporte toujours sur un service
   optionnel ; la colonne **Service optionnel** garde l'information meme
   quand le verdict est ``exclu``.

4. **Conflits de versions** : un meme paquet declare avec des **specificateurs
   differents** dans deux fichiers de dependances est un conflit nomme, avec
   pour chaque specification sa source (fichier + serie), sa classe
   (``pin_exact_divergent``, ``specifier_divergent``, ``incompatible``) et une
   **resolution proposee**.

5. **Manifeste consolide** : la seule source de paquets de l'image 1.2. Il ne
   contient que les paquets des series incluses, avec, par paquet, la version
   retenue et les series qui l'apportent. Un paquet en conflit y figure avec
   son marqueur de resolution, jamais avec une version inventee.

Organes natifs reuses (regle « nommer l'organe natif avant de reimplements »)
--------------------------------------------------------------------------

- ``scripts/notebook_tools/check_lib_versions.py`` (#23073) fournit la
  comparaison de versions (``version_key`` / ``compare_versions``) et, via
  ``run_census``, le recensement des divergences canonique/observe. Le
  manifeste ne recalcule ni l'un ni l'autre.
- ``scripts/notebook_tools/check_kernel_drift.py`` (#22441) reste l'organe du
  `kernelspec` ; cet organe n'en fait qu'une **lecture agregee par serie**.
- ``docs/reference/kernels-runtime.md`` est la reference des versions Python
  canoniques par noyau ; ses valeurs sont reprises dans la politique.

Usage
-----

::

    python scripts/notebook_tools/dependency_manifest.py --out-dir docs/curriculum
    python scripts/notebook_tools/dependency_manifest.py --print
    python scripts/notebook_tools/dependency_manifest.py --check

Les sorties par defaut sont versionnees dans le depot :

- ``docs/curriculum/manifeste-dependances.md`` (la table) ;
- ``docs/curriculum/manifeste-dependances.json`` (la meme table, exploitable).

Le code de sortie vaut 0 lorsque l'inventaire est complet (toutes les series
sont dans la table, tous les conflits sont nommes avec une resolution) et 1
sinon.

Garde de fraicheur (``--check``)
--------------------------------

``--check`` regenere le manifeste depuis l'etat courant du depot et le
compare aux sorties committes : il repond « le manifeste committe decrit-il
encore l'arbre ? ». Le SHA de generation et le compte de fichiers suivis
sont **ignores** -- ils decrivent l'etat du depot, pas le contenu du
manifeste ; tout le reste est compare. Sortie **0** frais, **1** perime,
**2** incident (sortie absente ou illisible : verdict inconnu, jamais un
verdict de perimetre). C'est un garde **advisory** : il signale une
derive, il ne tient aucun merge.
"""
from __future__ import annotations

import sys
from pathlib import Path

# Les modules voisins sont importes par leur nom simple : le dossier des
# outils doit etre dans le `sys.path` (import en package compris).
_TOOLS_DIR = Path(__file__).resolve().parent
if str(_TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(_TOOLS_DIR))

from dependency_manifest_lecture import (  # noqa: E402
    CODE_MENTION_RE,
    COMPANION_CODE_SUFFIXES,
    COMPANION_MAX_BYTES,
    DEFAULT_OUT_DIR,
    ENV_READ_RE,
    ENV_SECRET_NAME_RE,
    EXCLUSION_POLICIES,
    Group,
    IMPORT_RE,
    INT_CONST_RE,
    KERNEL_FAMILY_BY_LANGUAGE,
    LOCAL_HOSTS,
    NON_PYTHON_FAMILIES,
    NOTEBOOKS_ROOT,
    OPTIONAL_POLICIES,
    POLICY_RELPATH,
    Requirement,
    SCHEMA_VERSION,
    SERVICE_CALL_RE,
    URL_RE,
    URL_TEMPLATE_RE,
    _LIB_VERSIONS_IMPORT_ERROR,
    _PIP_OPTIONS,
    _REPO_ROOT,
    _TOOLS_DIR,
    _VERSION_FALLBACK_CALLS,
    _cell_sources,
    _companion_sources,
    _compare,
    _descendant_families,
    _endpoints,
    _git,
    _int_constants,
    _kernel_family,
    _max_version,
    _min_version,
    _norm_name,
    _norm_ver,
    _notebook_payload,
    _parse_requirement_line,
    _python_constraints,
    _service_calls,
    _split_series,
    _version_sort_key,
    compare_versions,
    git_ls_files,
    git_sha,
    load_lib_manifest,
    load_policy,
    read_requirements,
    run_census,
    version_key,
)
from dependency_manifest_construction import (  # noqa: E402
    _propose_resolution,
    _record_endpoints,
    _record_service_calls,
    _specifier_bounds,
    _specifiers_compatible,
    build_manifest,
    is_dependency_file,
)
from dependency_manifest_rendu import (  # noqa: E402
    FRESHNESS_IGNORED_COUNTS,
    FRESHNESS_IGNORED_TOP,
    SHA_RE,
    _census_summary,
    _diff_paths,
    _group_dict,
    _normalize_for_freshness,
    _normalize_markdown,
    _yes,
    render_markdown,
)
from dependency_manifest_cli import (  # noqa: E402
    check_freshness,
    main,
)

__all__ = [
    "CODE_MENTION_RE",
    "COMPANION_CODE_SUFFIXES",
    "COMPANION_MAX_BYTES",
    "DEFAULT_OUT_DIR",
    "ENV_READ_RE",
    "ENV_SECRET_NAME_RE",
    "EXCLUSION_POLICIES",
    "FRESHNESS_IGNORED_COUNTS",
    "FRESHNESS_IGNORED_TOP",
    "Group",
    "IMPORT_RE",
    "INT_CONST_RE",
    "KERNEL_FAMILY_BY_LANGUAGE",
    "LOCAL_HOSTS",
    "NON_PYTHON_FAMILIES",
    "NOTEBOOKS_ROOT",
    "OPTIONAL_POLICIES",
    "POLICY_RELPATH",
    "Requirement",
    "SCHEMA_VERSION",
    "SERVICE_CALL_RE",
    "SHA_RE",
    "URL_RE",
    "URL_TEMPLATE_RE",
    "_LIB_VERSIONS_IMPORT_ERROR",
    "_PIP_OPTIONS",
    "_REPO_ROOT",
    "_TOOLS_DIR",
    "_VERSION_FALLBACK_CALLS",
    "_cell_sources",
    "_census_summary",
    "_companion_sources",
    "_compare",
    "_descendant_families",
    "_diff_paths",
    "_endpoints",
    "_git",
    "_group_dict",
    "_int_constants",
    "_kernel_family",
    "_max_version",
    "_min_version",
    "_norm_name",
    "_norm_ver",
    "_normalize_for_freshness",
    "_normalize_markdown",
    "_notebook_payload",
    "_parse_requirement_line",
    "_propose_resolution",
    "_python_constraints",
    "_record_endpoints",
    "_record_service_calls",
    "_service_calls",
    "_specifier_bounds",
    "_specifiers_compatible",
    "_split_series",
    "_version_sort_key",
    "_yes",
    "build_manifest",
    "check_freshness",
    "compare_versions",
    "git_ls_files",
    "git_sha",
    "is_dependency_file",
    "load_lib_manifest",
    "load_policy",
    "main",
    "read_requirements",
    "render_markdown",
    "run_census",
    "version_key",
]

if __name__ == "__main__":
    raise SystemExit(main())
