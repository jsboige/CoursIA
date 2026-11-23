"""Rendus du census d'eligibilite Pyodide : Markdown, TSV, lot.

Ce module est la moitie « sortie » de ``pyodide_eligibility.py``. Il ne lit
aucun carnet et n'applique aucun critere : il recoit des verdicts deja
calcules et les met en forme. La separation existe parce que les trois
responsabilites du census -- calculer un verdict, rendre le tableau, rendre
le detail des refus -- se relisent et se testent separement.

Les constantes de presentation (ordre des motifs, nom du fichier companion)
vivent ici : elles decrivent la forme du rapport, pas le critere.

Issue #27549.
"""

from __future__ import annotations

import os
from typing import TYPE_CHECKING, Dict, List, Sequence, Set

if TYPE_CHECKING:  # pragma: no cover - uniquement pour les annotations
    from pyodide_eligibility import NotebookVerdict

#: Motifs d'exclusion, dans l'ordre de presentation du rapport.
MOTIFS = ("gpu", "cle", "reseau", "import_absent", "suffisance")

#: Les classes d'ecart de suffisance, dans l'ordre de presentation.
CLASSES_SUFFISANCE = ("dependance_locale", "hors_serie", "absent_distribution")

#: Ce que dit chaque classe d'ecart (une ligne par classe).
LIBELLE_CLASSES = {
    "dependance_locale": "un module de la serie a une dependance absente de la distribution",
    "hors_serie": "le carnet importe un module d'une autre serie, non livre par le bundle",
    "absent_distribution": "l'import est une roue pure que le carnet n'installe pas lui-meme",
}

#: Nom du fichier companion qui porte le detail carnet par carnet des refus.
REFUS_TSV_NAME = "pyodide-refus.tsv"

#: Nom du cache versionne des sondes PyPI (reproductibilite hors reseau).
WHEEL_CACHE_NAME = "pyodide-wheel-cache.json"

#: Nom du lock Pyodide commite avec le rapport (source de verite des paquets).
LOCK_NAME = "pyodide-lock.json"


def build_table(verdicts: Sequence["NotebookVerdict"]) -> Dict[str, object]:
    """Table par serie : comptes d'eligibles et de refus par motif."""
    table: Dict[str, Dict[str, object]] = {}
    for v in verdicts:
        row = table.setdefault(
            v.series,
            {
                "carnets": 0,
                "eligibles": 0,
                "refuses": 0,
                "par_motif": {m: 0 for m in MOTIFS},
                "erreurs": 0,
            },
        )
        row["carnets"] = int(row["carnets"]) + 1
        if v.error:
            row["erreurs"] = int(row["erreurs"]) + 1
        if v.eligible:
            row["eligibles"] = int(row["eligibles"]) + 1
        else:
            row["refuses"] = int(row["refuses"]) + 1
            for motif in v.motifs:
                pm = row["par_motif"]
                pm[motif] = int(pm.get(motif, 0)) + 1
    return table


def eligible_avant_suffisance(verdicts: Sequence["NotebookVerdict"]) -> int:
    """Le nombre de carnets que le critere acceptait **avant** l'alignement.

    C'est le verdict sans le motif `suffisance` : les autres motifs (GPU,
    cle, reseau, import absent) sont anterieurs a l'alignement, un carnet
    refuse pour un GPU l'a toujours ete. La comparaison avant/apres se lit
    donc sur la meme population.
    """
    return sum(1 for v in verdicts
               if not v.error and not [m for m in v.motifs if m != "suffisance"])


def census_suffisance(verdicts: Sequence["NotebookVerdict"]) -> Dict[str, int]:
    """Le nombre de carnets touches par chaque classe d'ecart.

    Seuls les carnets que le critere **acceptait avant** l'alignement sont
    comptes : c'est la population qui portait l'ecart. Un carnet compte
    **une fois** par classe, meme s'il porte plusieurs dependances de cette
    classe : le recensement est par carnet, comme le reste du rapport.
    """
    compte: Dict[str, int] = {classe: 0 for classe in CLASSES_SUFFISANCE}
    for v in verdicts:
        if v.error or [m for m in v.motifs if m != "suffisance"]:
            continue
        vues = {p.classe for p in (v.problemes or [])}
        for classe in vues:
            if classe in compte:
                compte[classe] += 1
    return compte


def render_markdown(
    verdicts: Sequence["NotebookVerdict"],
    table: Dict[str, Dict[str, object]],
    lock_info: Dict[str, object],
) -> str:
    """Rend le tableau Markdown et le critere relisible."""
    eligibles = [v for v in verdicts if v.eligible]
    refuses = [v for v in verdicts if not v.eligible]

    lines: List[str] = []
    lines.append("# Eligibilite Pyodide (JupyterLite) des carnets Python")
    lines.append("")
    lines.append("<!-- Genere par scripts/notebook_tools/pyodide_eligibility.py -- ne pas editer a la main. -->")
    lines.append("")
    lines.append("Perimetre : carnets Python suivis par git, hors `_output`, `_en` et `_archive`.")
    lines.append("La famille Python se lit sur la langue declaree (`language_info.name`), le nom du")
    lines.append("noyau ne servant que de repli : un carnet sans langue ni noyau Python n'est pas")
    lines.append("compte -- le census ne suppose pas Python par defaut. Le compte d'une serie peut")
    lines.append("donc etre inferieur au nombre de fichiers `.ipynb` qu'elle contient.")
    lines.append("Census : **%d** carnets Python, **%d** eligibles, **%d** refuses." %
                 (len(verdicts), len(eligibles), len(refuses)))
    lines.append("")
    lines.append("Source de verite des paquets : `pyodide-lock.json` (%s ; %s paquets)," %
                 (lock_description(lock_info),
                  lock_info.get("package_count", "?")))
    lines.append("commite avec le rapport (`docs/reference/%s`), ainsi que le cache des sondes" % LOCK_NAME)
    lines.append("PyPI (`docs/reference/%s`) : la regeneration ci-dessous est entierement hors" % WHEEL_CACHE_NAME)
    lines.append("reseau. Un import absent du lock et absent de la bibliotheque standard est")
    lines.append("refuse, sauf si le cache (ou une sonde `--probe-pypi`, acces reseau explicite)")
    lines.append("a constate une roue pure ; sans l'un ni l'autre, le refus est rendu tel quel.")
    lines.append("")
    lines.append("Le lock commite provient du canal `dev` de Pyodide, qui avance : le bump du lock")
    lines.append("est un geste delibere (regenerer puis committer lock, cache et rapport ensemble),")
    lines.append("et un ecart de census entre deux regenerations s'explique d'abord par la")
    lines.append("difference de lock, pas par le critere.")
    lines.append("")
    lines.append("Regeneration (hors reseau, deterministe) :")
    lines.append("")
    lines.append("```bash")
    lines.append("python scripts/notebook_tools/pyodide_eligibility.py --format md \\")
    lines.append("  --out docs/reference/pyodide-eligibilite.md \\")
    lines.append("  --refus-out docs/reference/pyodide-refus.tsv \\")
    lines.append("  --pyodide-lock docs/reference/%s \\" % LOCK_NAME)
    lines.append("  --wheel-cache docs/reference/%s" % WHEEL_CACHE_NAME)
    lines.append("```")
    lines.append("")
    lines.append("## Critere d'eligibilite")
    lines.append("")
    lines.append("Un carnet est **eligible** si et seulement si les quatre conditions suivantes sont reunies.")
    lines.append("Ce paragraphe est la source de verite : la regenereation du site s'appuie sur ce critere,")
    lines.append("jamais sur une liste maintenue a la main.")
    lines.append("")
    lines.append("1. **Aucun GPU** : aucun import de `torch`, `tensorflow`, `jax`, `cupy`, `onnxruntime`,")
    lines.append("   ni usage explicite de `torch.cuda` ou de `nvidia-smi`.")
    lines.append("2. **Aucune cle d'API** : aucune variable d'environnement dont le nom ressemble a une")
    lines.append("   cle (`*KEY*`, `*TOKEN*`, `*SECRET*`, `*PASSWORD*`, `*CREDENTIAL*`), ni saisie")
    lines.append("   interactive de secret. Seuls les **noms** sont collectes, jamais les valeurs.")
    lines.append("3. **Aucun service reseau** : aucun appel a un hote distant (`http(s)://`), aucun port")
    lines.append("   local de service, aucun module client reseau (`requests`, `httpx`, `socket`, ...).")
    lines.append("4. **Tous les imports satisfaits par le bundle** : chaque import est soit dans la")
    lines.append("   bibliotheque standard, soit un paquet present dans `pyodide-lock.json`, soit")
    lines.append("   installe par le carnet lui-meme (`micropip`, `%pip`, `!pip`), soit fourni par un")
    lines.append("   module de la **serie** du carnet livre avec lui (helper du carnet, **paquet")
    lines.append("   inclus** : un dossier porteur d'un `__init__.py` compte comme un module local)")
    lines.append("   dont les propres dependances sont satisfaites. Le bundle publie des fichiers")
    lines.append("   et n'installe rien : une roue pure que le carnet n'installe pas n'est pas")
    lines.append("   fournie, et un module d'une autre serie n'est pas livre.")
    lines.append("")
    lines.append("Le refus porte toujours un motif : `gpu`, `cle`, `reseau`, `import_absent` ou")
    lines.append("`suffisance` (une dependance que le bundle ne pourra pas fournir).")
    lines.append("")
    lines.append("Lock de reference : `%s` (%s, %s paquets)." % (
        os.path.basename(str(lock_info.get("lock"))),
        lock_description(lock_info),
        lock_info.get("package_count", "?")))
    lines.append("")
    lines.append("Les **noms** des variables d'environnement ne sont pas publies : un nom qui ressemble")
    lines.append("a une cle (`*_API_KEY`) fait echouer le scanner de secrets du depot, alors que le nom")
    lines.append("seul n'est pas un secret. Le detail des refus (`pyodide-refus.tsv`) publie donc le")
    lines.append("**nombre** de variables detectees (`cle=N`), pas leurs noms ; les noms restent")
    lines.append("accessibles en local avec `--detail-cle` (sortie a ne pas committer).")
    lines.append("")

    lines.append("## Table par serie")
    lines.append("")
    lines.append("| Serie | Carnets Python | Eligibles | Refuses | dont GPU | dont cle | dont reseau | dont import absent | dont suffisance |")
    lines.append("|---|---:|---:|---:|---:|---:|---:|---:|---:|")
    for serie in sorted(table):
        row = table[serie]
        pm = row["par_motif"]
        lines.append("| %s | %d | %d | %d | %d | %d | %d | %d | %d |" % (
            serie, row["carnets"], row["eligibles"], row["refuses"],
            pm.get("gpu", 0), pm.get("cle", 0), pm.get("reseau", 0),
            pm.get("import_absent", 0), pm.get("suffisance", 0)))
    lines.append("")

    lines.append("## Classes d'ecart de suffisance")
    lines.append("")
    lines.append("Le bundle publie des fichiers et n'installe rien : un import n'est fourni que s'il")
    lines.append("est dans la distribution, s'il est installe par le carnet, ou s'il vient d'un module")
    lines.append("de la serie livre avec le carnet. Trois classes d'ecart separent alors le critere de")
    lines.append("ce que le bundle livre -- chacune compte des **carnets**, un carnet compte une fois")
    lines.append("par classe :")
    lines.append("")
    lines.append("| Classe | Ce qu'elle dit | Carnets |")
    lines.append("|---|---|---:|")
    census = census_suffisance(verdicts)
    for classe in CLASSES_SUFFISANCE:
        lines.append("| `%s` | %s | %d |" % (
            classe, LIBELLE_CLASSES[classe], census.get(classe, 0)))
    lines.append("")
    lines.append("Ces trois classes sont mesurees sur la population que le critere acceptait")
    lines.append("**avant** l'alignement -- un carnet deja refuse pour un GPU ou une cle n'y")
    lines.append("figure pas : son ecart de suffisance ne changeait rien a ce que le critere")
    lines.append("disait. Le comptage avant/apres est donc sur la meme population :")
    lines.append("")
    lines.append("| Mesure | Avant | Apres |")
    lines.append("|---|---:|---:|")
    lines.append("| Carnets eligibles | %d | %d |" % (
        eligible_avant_suffisance(verdicts), len(eligibles)))
    lines.append("")
    lines.append("Le detail des dependances est dans le fichier `%s` (colonne `suffisance`)."
                 % os.path.basename(REFUS_TSV_NAME))
    lines.append("")

    lines.append("## Carnets eligibles")
    lines.append("")
    lines.append("| Carnet | Serie | Noyau | Imports Pyodide | Roues pures |")
    lines.append("|---|---|---|---|---|")
    for v in sorted(eligibles, key=lambda x: (x.series, x.path)):
        lines.append("| `%s` | %s | %s | %s | %s |" % (
            v.path, v.series, v.kernel or "-",
            ", ".join(sorted(set(v.pyodide_packages))) or "-",
            ", ".join(sorted(set(v.pure_wheels))) or "-"))
    lines.append("")

    lines.append("## Refuses : motifs par serie")
    lines.append("")
    lines.append("Le detail **carnet par carnet** des refus (motif et element declencheur) est dans le")
    lines.append("fichier `%s`, une ligne par carnet refuse." % os.path.basename(REFUS_TSV_NAME))
    lines.append("")
    lines.append("| Serie | Motifs rencontres | Imports absents (les plus frequents) |")
    lines.append("|---|---|---|")
    for serie in sorted(table):
        motifs_seen: Set[str] = set()
        missing: Dict[str, int] = {}
        for v in refuses:
            if v.series != serie:
                continue
            motifs_seen.update(v.motifs)
            for name in v.missing_imports:
                missing[name] = missing.get(name, 0) + 1
        if not motifs_seen:
            continue
        top = sorted(missing.items(), key=lambda kv: (-kv[1], kv[0]))[:6]
        lines.append("| %s | %s | %s |" % (
            serie, ", ".join(sorted(motifs_seen)),
            ", ".join("%s (%d)" % (name, count) for name, count in top) or "-"))
    lines.append("")
    lines.append("Les motifs **se cumulent** : un carnet refuse pour une cle d'API et pour un import")
    lines.append("absent compte dans les deux colonnes de la table par serie.")
    lines.append("")
    return "\n".join(lines)


def sanitize_verdict(data: Dict[str, object], with_key_names: bool = False) -> Dict[str, object]:
    """Retire les noms de variables d'environnement d'un verdict serialise.

    Un nom de variable qui ressemble a une cle (`*_API_KEY`) fait echouer le
    scanner de secrets du depot, alors que le nom seul n'est pas un secret.
    Les sorties versionnees publient donc un **nombre** ; les noms restent
    accessibles en local avec `--detail-cle`.
    """
    if with_key_names:
        return data
    result = dict(data)
    names = result.get("key_detail") or []
    result["key_detail"] = []
    result["cle_n"] = len([n for n in names if n != "saisie interactive de secret"])
    return result


def render_refus_tsv(verdicts: Sequence["NotebookVerdict"],
                    with_key_names: bool = False) -> str:
    """Rend le detail des refus : une ligne TSV par carnet refuse.

    Les **noms** des variables d'environnement ne sont pas publies par
    defaut. Un nom qui ressemble a une cle (`*_API_KEY`, `*_PASSWORD`) fait
    echouer le scanner de secrets du depot, alors que le nom seul n'est pas
    un secret : on publie donc le **nombre** de variables detectees, et les
    noms restent accessibles en local avec `--detail-cle` (sortie a ne pas
    committer).
    """
    lines: List[str] = ["# chemin\tserie\tmotifs\tdetail"]
    for v in sorted((x for x in verdicts if not x.eligible), key=lambda x: (x.series, x.path)):
        detail: List[str] = []
        if v.gpu_detail:
            detail.append("gpu=%s" % ",".join(sorted(set(v.gpu_detail))))
        if v.key_detail:
            names = sorted(set(v.key_detail))
            interactive = "saisie interactive de secret" in names
            env_names = [n for n in names if n != "saisie interactive de secret"]
            if with_key_names:
                detail.append("cle=%s" % ",".join(names))
            else:
                detail.append("cle=%d" % len(env_names))
                if interactive:
                    detail.append("cle_interactive")
        if v.network_detail:
            detail.append("reseau=%s" % ",".join(sorted(set(v.network_detail))[:4]))
        if v.missing_imports:
            detail.append("import_absent=%s" % ",".join(sorted(set(v.missing_imports))[:6]))
        if v.problemes:
            detail.append("suffisance=%s" % ";".join(
                "%s:%s" % (p.classe, p.detail) for p in v.problemes[:4]))
        if v.error:
            detail.append("erreur=%s" % v.error[:120])
        lines.append("%s\t%s\t%s\t%s" % (
            v.path, v.series, ",".join(v.motifs), ";".join(detail)))
    return "\n".join(lines) + "\n"


def select_lot(verdicts: Sequence["NotebookVerdict"], size: int) -> List["NotebookVerdict"]:
    """Choisit un lot de carnets eligibles etape par etape, sans tri manuel.

    Regle declaree : on repartit le lot sur des series distinctes (une serie
    par tour, dans l'ordre alphabetique des series), on prefere les carnets
    qui n'ont besoin d'aucune roue pure a installer dans le navigateur, puis
    ceux qui ne lisent aucun fichier du depot. Le lot est donc reproductible
    : il sort du critere, il n'est pas pose a la main.
    """
    eligible = [v for v in verdicts if v.eligible]
    by_series: Dict[str, List["NotebookVerdict"]] = {}
    for v in eligible:
        by_series.setdefault(v.series, []).append(v)
    for series in by_series:
        by_series[series].sort(key=lambda v: (len(v.pure_wheels), len(v.local_files),
                                              v.code_cells, v.path))

    chosen: List["NotebookVerdict"] = []
    used_paths: Set[str] = set()
    series_order = sorted(by_series)
    while len(chosen) < size and series_order:
        remaining: List[str] = []
        for series in series_order:
            pick = next((v for v in by_series[series] if v.path not in used_paths), None)
            if pick is None:
                continue
            used_paths.add(pick.path)
            chosen.append(pick)
            if len(chosen) >= size:
                break
            remaining.append(series)
        if len(chosen) >= size:
            break
        if not remaining:
            break
        series_order = remaining
    return chosen


def lock_description(lock_info: Dict[str, object]) -> str:
    """Decrit la source de verite des paquets, telle que le lock la porte.

    Le fichier `pyodide-lock.json` ne porte pas toujours une version de
    distribution : on rend donc les metadonnees qu'il contient reellement
    (ABI, version de Python, cible), plutot qu'une version supposee.
    """
    bits: List[str] = []
    if lock_info.get("pyodide_version"):
        bits.append("distribution %s" % lock_info["pyodide_version"])
    if lock_info.get("abi_version"):
        bits.append("ABI %s" % lock_info["abi_version"])
    if lock_info.get("python"):
        bits.append("Python %s" % lock_info["python"])
    if lock_info.get("arch"):
        bits.append(str(lock_info["arch"]))
    if lock_info.get("platform"):
        bits.append(str(lock_info["platform"]))
    return ", ".join(bits) if bits else "metadonnees absentes"