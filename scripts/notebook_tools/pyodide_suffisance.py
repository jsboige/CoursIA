#!/usr/bin/env python3
"""La SUFFISANCE d'un carnet pour le bundle JupyterLite (pli 2.1, #27583).

Le bundle JupyterLite publie des **fichiers** et n'installe rien. Un import
n'est donc satisfait que dans trois cas :

1. il est dans la **distribution** (le verrou Pyodide) ;
2. ou le **carnet l'installe lui-meme** (`micropip.install`, `%pip install`,
   `!pip install`) -- le carnet est alors seul juge de ce qu'il amene ;
3. ou il est fourni par un **module de la serie** livre avec le carnet, dont
   les propres imports sont satisfaits (regle recursive).

Un module d'une **autre serie** n'est pas livre par le bundle : il est refuse.

C'est la regle que le deploiement (pli 2.2) applique deja ; elle vit ici pour
que le **critere** dise la meme chose que ce que le bundle livre. Les deux
organes partagent cette semantique : le deploiement l'importe, il ne la
reimplemente pas.

Les trois classes d'ecart (mesurees sur `main`, avant alignement) :

| Classe | Ce qu'elle dit |
| --- | --- |
| `dependance_locale` | un module de la serie a une dependance absente de la distribution |
| `hors_serie` | le carnet importe un module d'une autre serie, non livre par le bundle |
| `absent_distribution` | l'import est une roue pure que le carnet n'installe pas lui-meme |

Les imports de **cuisine** (GPU, reseau, cle d'API) ne sont pas des classes de
sufficiency : le critere les traite deja, et le deploiement les refuse.

Ce module ne lit aucun carnet par lui-meme : il recoit les sources et les
constantes du critere. L'import du critere est **differe** : le critere
importe ce module, l'inverse ferait un cycle.

Usage :
    from pyodide_suffisance import suffisance_carnet
    modules, problemes = suffisance_carnet(root, rel, pyodide_packages,
                                            stdlib_names)
"""
from __future__ import annotations

import json
import os
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Dict, List, Optional, Sequence, Set, Tuple

#: Installation d'un paquet **par le carnet lui-meme** : le bundle n'installe
#: rien, mais un carnet peut installer une roue pure a l'execution.
INSTALL_RE = re.compile(
    r"micropip\.install\s*\(\s*[\"']([A-Za-z0-9_.\-]+)[\"']"
    r"|%\s*pip\s+install\s+([A-Za-z0-9_.\-]+)"
    r"|!\s*pip\s+install\s+([A-Za-z0-9_.\-]+)",
    re.IGNORECASE)

#: Dossiers ignores dans la recherche des modules locaux.
_SKIP_DIRS = {".git", ".tmp", "node_modules", "__pycache__", ".venv", "venv",
              ".pytest_cache", ".mypy_cache", "build", "dist", ".claude"}

#: Les trois classes d'ecart, dans l'ordre de presentation.
CLASSES = ("dependance_locale", "hors_serie", "absent_distribution")


@dataclass(frozen=True)
class Probleme:
    """Une dependance non satisfaite, avec sa classe et sa chaine."""

    classe: str
    detail: str
    chaine: Tuple[str, ...] = ()


@dataclass
class Suffisance:
    """Ce que la suffisance decide pour un carnet."""

    #: Les modules de la serie a embarquer avec le carnet :
    #: ``(nom, chemin relatif au depot, est_paquet)``.
    modules: List[Tuple[str, str, bool]] = field(default_factory=list)
    #: Les dependances non satisfaites, classees.
    problemes: List[Probleme] = field(default_factory=list)
    #: Les paquets que le carnet installe lui-meme.
    installs: Set[str] = field(default_factory=set)

    @property
    def classes(self) -> Set[str]:
        """Les classes rencontrees."""
        return {p.classe for p in self.problemes}


def normalise(nom: str) -> str:
    """Nom de paquet normalise (PyPI accepte `scikit-learn` et `sklearn`)."""
    return nom.replace("-", "_").lower()


def roue_pure(pack: str, wheel_cache: Dict[str, Dict[str, object]],
              probe: bool) -> bool:
    """Le paquet absent de la distribution existe-t-il en roue pure ?

    La sonde est celle du critere (import differé) et le cache est partage :
    un paquet n'est sonde qu'une fois, dans le critere ou ici.
    """
    from pyodide_eligibility import probe_pypi

    entry = wheel_cache.get(pack)
    if entry is None and probe:
        entry = probe_pypi(pack, wheel_cache)
        wheel_cache[pack] = entry
    return bool(entry and entry.get("pure_wheel"))


def paquets_installes_par_le_carnet(sources: Sequence[str]) -> Set[str]:
    """Paquets que le carnet installe lui-meme au moment de l'execution.

    C'est la seule voie par laquelle une roue pure absente de la
    distribution peut devenir disponible dans le bundle : le carnet
    l'installe. Sans cette trace, la dependance est **absente** -- le bundle
    ne l'installera pas a la place du carnet.
    """
    installs: Set[str] = set()
    for texte in sources:
        for trouve in INSTALL_RE.finditer(texte):
            nom = trouve.group(1) or trouve.group(2) or trouve.group(3)
            if nom:
                installs.add(normalise(nom))
    return installs


def _dossiers_candidats(dossier: Path, series_root: Path, root: Path) -> List[Path]:
    """Dossiers ou peut se trouver un module local, du plus proche au plus lointain.

    La montee est **bornee** : elle s'arrete a la racine de la serie, et au
    pire a la racine du depot. Sans cette borne, un carnet pose directement
    sous la racine de sa serie fait monter la recherche jusqu'a la racine du
    systeme de fichiers -- et la construction y passe des heures.
    """
    candidats: List[Path] = [dossier]
    for parent in dossier.parents:
        candidats.append(parent)
        if parent == series_root or parent == root:
            break
    return candidats


def _chercher_module(dossier: Path, nom: str) -> Optional[Tuple[Path, bool]]:
    """Cherche le module `nom` dans `dossier` : (chemin, est_paquet)."""
    direct = dossier / (nom + ".py")
    if direct.is_file():
        return direct, False
    paquet = dossier / nom
    if (paquet / "__init__.py").is_file():
        return paquet, True
    trouves: List[Tuple[int, Path, bool]] = []
    for base, dirs, files in os.walk(dossier):
        dirs[:] = [d for d in dirs if d not in _SKIP_DIRS and not d.startswith(".")]
        profondeur = len(Path(base).relative_to(dossier).parts)
        for nom_fichier in files:
            if nom_fichier == nom + ".py":
                trouves.append((profondeur, Path(base) / nom_fichier, False))
        for d in dirs:
            if d == nom and (Path(base) / d / "__init__.py").is_file():
                trouves.append((profondeur, Path(base) / d, True))
    if not trouves:
        return None
    trouves.sort(key=lambda entree: entree[0])
    return trouves[0][1], trouves[0][2]


def source_du_module(root: Path, rel_path: str, nom: str) -> Optional[Tuple[Path, bool]]:
    """Emplacement du module local `nom` pour le carnet `rel_path`.

    La recherche est limitee a la **serie** du carnet : c'est la seule
    partie du depot que le bundle publie (avec le carnet).
    """
    from pyodide_eligibility import series_of

    path = root / rel_path
    series_root = root / "MyIA.AI.Notebooks" / series_of(rel_path)
    for dossier in _dossiers_candidats(path.parent, series_root, root):
        trouve = _chercher_module(dossier, nom)
        if trouve is not None:
            return trouve
    return None


def _satisfait(pack: str, top: str, pyodide_packages: Dict[str, str],
               installs: Set[str]) -> bool:
    """Le paquet est-il fourni, soit par la distribution, soit par le carnet ?"""
    if pack in pyodide_packages:
        return True
    return normalise(pack) in installs or normalise(top) in installs


def dependances_non_satisfaites(
        source: Path,
        pyodide_packages: Dict[str, str],
        stdlib_names: Set[str],
        resolver: Callable[[str], Optional[Tuple[Path, bool]]],
        vus: Set[str],
        chaine: Tuple[str, ...] = (),
        installs: Optional[Set[str]] = None,
) -> List[Probleme]:
    """Les imports d'un module local que le bundle ne pourra pas fournir.

    Le bundle publie des **fichiers**, il n'installe rien : une dependance
    d'un module local embarque doit donc faire partie de la **distribution**
    (verrou Pyodide), et non etre une roue pure que le carnet installerait
    lui-meme.

    Mesure : le carnet `Causalite-06` importe `dowhy_iv_organs`, qui importe
    `dowhy` ; `dowhy` n'est pas dans la distribution -> le carnet echoue en
    navigation (`ModuleNotFoundError: No module named 'dowhy'`), meme une
    fois le module embarque.

    `installs` porte les paquets que le carnet installe lui-meme : ils sont
    disponibles a l'execution, donc ils satisfont la dependance.
    """
    from pyodide_eligibility import (GPU_MODULES, GPU_PACKAGES, MODULE_TO_PACKAGE,
                                     NETWORK_MODULES, collect_imports,
                                     top_level_module)

    problemes: List[Probleme] = []
    cle = str(source)
    if cle in vus:
        return problemes
    vus.add(cle)
    installs = installs or set()
    fichier = source / "__init__.py" if source.is_dir() else source
    if not fichier.is_file():
        return problemes
    texte = fichier.read_text(encoding="utf-8", errors="replace")
    for module in sorted(collect_imports([texte])):
        top = top_level_module(module)
        if top in stdlib_names:
            continue
        if top in GPU_MODULES or top in GPU_PACKAGES:
            problemes.append(Probleme(
                "dependance_locale",
                "%s : GPU" % (" -> ".join(chaine + (module,))),
                chaine + (module,)))
            continue
        if top in NETWORK_MODULES:
            problemes.append(Probleme(
                "dependance_locale",
                "%s : reseau" % (" -> ".join(chaine + (module,))),
                chaine + (module,)))
            continue
        pack = MODULE_TO_PACKAGE.get(top, top)
        if _satisfait(pack, top, pyodide_packages, installs):
            continue
        local = resolver(top)
        if local is None:
            problemes.append(Probleme(
                "dependance_locale",
                "%s : absent de la distribution" % (" -> ".join(chaine + (module,))),
                chaine + (module,)))
            continue
        problemes.extend(dependances_non_satisfaites(
            local[0], pyodide_packages, stdlib_names, resolver, vus,
            chaine + (module,), installs))
    return problemes


def suffisance_carnet(
        root: Path,
        rel_path: str,
        pyodide_packages: Dict[str, str],
        stdlib_names: Set[str],
        *,
        sources: Optional[Sequence[str]] = None,
        est_roie_pure: Optional[Callable[[str], bool]] = None,
        installs: Optional[Set[str]] = None,
) -> Suffisance:
    """Les modules a embarquer et les dependances non satisfaites d'un carnet.

    `est_roie_pure` dit si un paquet absent de la distribution existe sous
    forme de **roue pure** : c'est ce que le critere sait (son cache de sondes
    PyPI) et ce que le deploiement ignore. La distinction ne change pas le
    verdict -- un paquet absent de la distribution et non installe par le
    carnet est refuse dans les deux cas -- elle change la **classe** du
    probleme, donc le recensement.

    `installs` porte les paquets que le carnet installe lui-meme ; par defaut
    ils sont lus dans les sources du carnet. `sources` evite de relire le
    carnet quand l'appelant l'a deja fait.
    """
    from pyodide_eligibility import (GPU_MODULES, GPU_PACKAGES, MODULE_TO_PACKAGE,
                                     NETWORK_MODULES, collect_imports,
                                     local_modules, notebook_sources,
                                     series_of, top_level_module)

    path = root / rel_path
    if sources is None:
        with path.open(encoding="utf-8") as fh:
            nb = json.load(fh)
        sources = notebook_sources(nb)
    imports = collect_imports(sources)
    series_root = root / "MyIA.AI.Notebooks" / series_of(rel_path)
    local, elsewhere = local_modules(root, path, series_root)
    installs = paquets_installes_par_le_carnet(sources) if installs is None else installs
    est_roie_pure = est_roie_pure or (lambda _paquet: False)

    out = Suffisance(installs=set(installs))
    vus: Set[str] = set()

    def resolver(nom: str):
        return source_du_module(root, rel_path, nom)

    for module in sorted(set(imports)):
        top = top_level_module(module)
        if top in stdlib_names:
            continue
        if top in GPU_MODULES or top in GPU_PACKAGES:
            continue  # motif `gpu` : decide par le critere
        if top in NETWORK_MODULES:
            continue  # motif `reseau` : decide par le critere
        pack = MODULE_TO_PACKAGE.get(top, top)
        if pack in pyodide_packages:
            continue
        if normalise(pack) in installs or normalise(top) in installs:
            continue  # le carnet installe lui-meme la roue
        if top in local or module in local:
            nom = top if top in local else module
            emplacement = resolver(nom)
            if emplacement is None:
                out.problemes.append(Probleme(
                    "dependance_locale", "%s : module local introuvable" % nom, (nom,)))
                continue
            source, est_paquet = emplacement
            out.modules.append((nom, source.relative_to(root).as_posix(), est_paquet))
            out.problemes.extend(dependances_non_satisfaites(
                source, pyodide_packages, stdlib_names, resolver, vus, (nom,),
                installs))
            continue
        if top in elsewhere:
            out.problemes.append(Probleme(
                "hors_serie",
                "%s : module hors serie non livre par le bundle" % module,
                (module,)))
            continue
        classe = "absent_distribution" if est_roie_pure(pack) else "absent"
        out.problemes.append(Probleme(
            classe, "%s : absent de la distribution" % module, (module,)))
    return out
