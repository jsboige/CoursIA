#!/usr/bin/env python3
"""Génère docs/curriculum/prerequis.qmd — carte des prérequis dérivée de la taxonomie.

La carte ne se dessine pas à la main : les arêtes carnet -> carnet sont dérivées
des prérequis conceptuels de docs/curriculum/taxonomy/*.json, et la page entière
est réécrite par ce script (patron COURSE_CATALOG : artefact généré, jamais édité).

Algorithme (dérivation carnet -> carnet) :
    un concept ENSEIGNÉ dans le carnet A (via ses citations) qui PRÉREQUIERT un
    concept enseigné dans le carnet B crée l'arête B --> A (« B précède A »).
    Les références de prérequis se résolvent par id (UUID) puis par chemin.

Usage :
    python3 scripts/curriculum/generate_prereq_map.py            # écrit la page
    python3 scripts/curriculum/generate_prereq_map.py --check    # exit 1 si périmée
    python3 scripts/curriculum/generate_prereq_map.py --stdout   # affiche sans écrire

La couverture de chaque série est mesurée contre l'inventaire RÉEL du disque
(*.ipynb sous le dossier de la série), jamais contre la liste auto-déclarée par
la taxonomie : une série qui ne cite qu'une partie de ses carnets est partielle
même si sa liste `notebooks` est courte.

`--check` compare UNIQUEMENT la partie dérivée de la taxonomie (#27657, DM
coordinateur 2026-11-24) : le bloc « Couverture des séries » est mesuré contre
le DISQUE, donc chaque carnet fusionné hors taxonomie le ferait re-périmer —
la page commise ne peut jamais tenir cette comparaison, et une PR de contenu
serait accusée d'une dérive qu'elle ne cause pas. La fraîcheur de ce bloc
appartient à la régénération périodique (catalog-cron, quarto-pages-deploy :
il est régénéré avant chaque rendu), pas à un prédicat absolu sur les PRs.
Le marqueur COVERAGE_BEGIN / COVERAGE_END borne ce bloc.

Issue : #27556 (carte des prérequis, Pli 4.2 de l'Epic #24993).
"""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
TAXONOMY_DIR = REPO_ROOT / "docs" / "curriculum" / "taxonomy"
OUTPUT = REPO_ROOT / "docs" / "curriculum" / "prerequis.qmd"
PILOT = "z3-linq2z3"
SCHEMA = "schema.json"

# Bloc de couverture : mesuré contre le disque, donc HORS du prédicat `--check`.
# Les marqueurs restent dans la page commise pour que la comparaison soit stable.
COVERAGE_BEGIN = "<!-- COVERAGE-INVENTAIRE-DISQUE:BEGIN -->"
COVERAGE_END = "<!-- COVERAGE-INVENTAIRE-DISQUE:END -->"

# Le dossier de la page dans l'arbre du site : docs/curriculum/ -> racine = ../../
SITE_ROOT_FROM_PAGE = "../../"


# --------------------------------------------------------------- utilitaires --


def esc_label(text: str) -> str:
    """Étiquette mermaid : le guillemet ferme la chaîne, le dièse ouvre une entité."""
    return str(text).replace('"', "'").replace("#", "♯")


def esc_cell(text: str) -> str:
    """Cellule de tableau markdown : la barre verticale sépare les colonnes."""
    return str(text).replace("|", "\\|")


def site_url(repo_path: str) -> str:
    """Chemin du carnet rendu, depuis docs/curriculum/."""
    repo_path = repo_path.replace("\\", "/")
    if repo_path.endswith(".ipynb"):
        repo_path = repo_path[: -len(".ipynb")] + ".html"
    return SITE_ROOT_FROM_PAGE + repo_path


def nb_base(repo_path: str) -> str:
    return repo_path.replace("\\", "/").rsplit("/", 1)[-1]


def dec_key(decimal_path: str) -> tuple[int, ...]:
    """Clé de tri NUMÉRIQUE : 1.10 vient après 1.2 (un tri de chaînes l'inverse)."""
    return tuple(int(part) for part in str(decimal_path or "").replace(".", " ").split())


# -------------------------------------------------------------------- données --


def load_series() -> tuple[list[dict], dict, dict]:
    """Charge toutes les séries, indexe les concepts par id et par chemin.

    L'index est GLOBAL : une arête inter-séries apparaît dès que la taxonomie en
    porte une, sans changement de ce script.
    """
    series_list: list[dict] = []
    by_id: dict[str, tuple[dict, dict]] = {}
    by_path: dict[str, tuple[dict, dict]] = {}

    for path in sorted(TAXONOMY_DIR.glob("*.json")):
        if path.name == SCHEMA:
            continue
        data = json.loads(path.read_text(encoding="utf-8"))
        concepts = data.get("concepts")
        if not concepts:
            continue
        series = {
            "key": path.stem,
            "name": data.get("series") or path.stem,
            "notebooks": data.get("notebooks") or [],
            "tree": data.get("notebook_tree") or [],
            "concepts": concepts,
            "taught": {},  # concept id -> {repo_path: True}
            "concepts_in_nb": {},  # repo_path -> [label_fr, ...] (ordre du fichier)
        }
        for concept in concepts:
            if concept.get("id"):
                by_id[concept["id"]] = (series, concept)
            if concept.get("path"):
                by_path[concept["path"]] = (series, concept)
            seen_nb: set[str] = set()
            for citation in concept.get("citations") or []:
                nb = citation.get("notebook")
                if not nb:
                    continue
                nb = nb.replace("\\", "/")
                series["taught"].setdefault(concept["id"], {})[nb] = True
                if nb not in seen_nb:
                    seen_nb.add(nb)
                    labels = series["concepts_in_nb"].setdefault(nb, [])
                    labels.append(concept.get("label_fr") or concept.get("path") or concept["id"])
        series_list.append(series)
    return series_list, by_id, by_path


def derive_edges(
    series_list: list[dict],
    by_id: dict[str, tuple[dict, dict]],
    by_path: dict[str, tuple[dict, dict]],
) -> tuple[dict[tuple[str, str], int], list[dict], int, int]:
    """Dérive les arêtes carnet -> carnet sur toutes les séries.

    Retourne (edges, cross, unresolved, total_refs) où edges est un dict
    (source, cible) -> poids, et cross la liste des arêtes inter-séries.
    """
    edges: dict[tuple[str, str], int] = {}
    cross: list[dict] = []
    unresolved = 0
    total_refs = 0

    for series in series_list:
        for concept in series["concepts"]:
            sources = series["taught"].get(concept["id"])
            if not sources:
                continue
            for ref in concept.get("prerequisites") or []:
                total_refs += 1
                target = by_id.get(ref) or by_path.get(ref)
                if target is None:
                    unresolved += 1
                    continue
                target_series, target_concept = target
                for before in sources:
                    for after in target_series["taught"].get(target_concept["id"], {}):
                        if before == after:
                            continue
                        key = (after, before)
                        edges[key] = edges.get(key, 0) + 1
                        if target_series is not series:
                            cross.append(
                                {
                                    "from": after,
                                    "to": before,
                                    "concept": target_concept.get("label_fr") or target_concept["id"],
                                    "needed_by": concept.get("label_fr") or concept["id"],
                                }
                            )
    return edges, cross, unresolved, total_refs


def tree_notebooks(series: dict) -> list[dict]:
    """Carnets de la série, triés par chemin décimal numérique."""
    entries = [
        entry
        for entry in series["tree"]
        if entry.get("level") == "notebook" and entry.get("repository_path")
    ]
    if entries:
        return sorted(entries, key=lambda e: dec_key(e.get("decimal_path")))
    # repli : pas d'arbre -> liste `notebooks`, ordre du fichier
    return [
        {"repository_path": path, "path": nb_base(path), "label_fr": nb_base(path)}
        for path in series["notebooks"]
    ]


def real_inventory(series: dict) -> set[str]:
    """Carnets RÉELS sur le disque, sous le dossier commun de la série.

    Dénominateur honnête de la couverture : la liste `notebooks` de la taxonomie
    dit ce qu'elle couvre, pas ce qui existe.
    """
    notebooks = [n.replace("\\", "/") for n in series["notebooks"]]
    dirs = sorted({n.rsplit("/", 1)[0] for n in notebooks if "/" in n})
    if not dirs:
        return set()
    common = dirs[0] if len(dirs) == 1 else os.path.commonpath(dirs)
    root = REPO_ROOT / common
    if not root.is_dir():
        return set()
    return {
        p.relative_to(REPO_ROOT).as_posix()
        for p in root.rglob("*.ipynb")
        if ".ipynb_checkpoints" not in p.parts and not p.name.endswith("_output.ipynb")
    }


# --------------------------------------------------------------------- sortie --


def mermaid_drawn(edges: dict[tuple[str, str], int], series: dict) -> list[tuple[str, str]]:
    """Arêtes effectivement dessinées : les deux carnets appartiennent à la série.

    Source unique du décompte affiché par la page ET par le résumé de génération :
    les deux chiffres ne peuvent pas diverger.
    """
    paths = {e["repository_path"].replace("\\", "/") for e in tree_notebooks(series)}
    return sorted((src, dst) for src, dst in edges if src in paths and dst in paths)


# Plages de carnets : regroupement ÉDITORIAL du générateur, pas une donnée de la
# taxonomie. Il ne sert qu'à rendre la carte lisible — 26 des 33 arêtes du pilote
# partent des carnets 01 et 02 vers tous les carnets 10 à 20, ce qui impose sinon
# un rang de quatorze nœuds dont les étiquettes deviennent illisibles.
CHAPTERS = (
    ("A", "Carnets 01–04", 4),
    ("B", "Carnets 05–09", 9),
    ("C", "Carnets 10–20", 99),
)


def chapter_of(repo_path: str) -> str:
    """Plage d'un carnet, d'après le numéro qui préfixe son nom de fichier."""
    base = nb_base(repo_path)
    head = base.split("_", 1)[0]
    if not head.isdigit():
        return ""
    number = int(head)
    for key, _label, upper in CHAPTERS:
        if number <= upper:
            return key
    return ""


def _chapter_label(key: str) -> str:
    return next((label for k, label, _upper in CHAPTERS if k == key), key)


def flowchart_direction(nodes: list[str], edges: list[tuple[str, str]]) -> str:
    """Orientation qui garde les étiquettes lisibles, mesurée sur la forme du graphe.

    Un rang large est le piège : en TB ses nœuds s'alignent en largeur (onze
    carnets cibles ont donné 3226 px de large, texte rendu à 25 %), alors qu'en LR
    ils s'empilent en hauteur. Une chaîne, elle, devient une ligne interminable en
    LR (1990 px de large mesurés) et se lit très bien en TB.
    """
    level = {node: 0 for node in nodes}
    for _ in range(len(nodes)):
        changed = False
        for before, after in edges:
            if level[after] < level[before] + 1:
                level[after] = level[before] + 1
                changed = True
        if not changed:
            break
    widest = max((sum(1 for value in level.values() if value == rank) for rank in set(level.values())), default=0)
    return "LR" if widest > 3 else "TB"


def overview_source(series: dict, edges: dict[tuple[str, str], int]) -> tuple[str, dict[str, int]]:
    """Vue d'ensemble : un nœud par plage, une arête par flux entre plages.

    Les arêtes internes à une plage ne sont pas dessinées ici (une boucle sur un
    nœud de plage ne dirait rien) ; le décompte part dans la légende.
    """
    drawn = mermaid_drawn(edges, series)
    weights: dict[tuple[str, str], int] = {}
    internal: dict[str, int] = {}
    for before, after in drawn:
        key_before, key_after = chapter_of(before), chapter_of(after)
        if not key_before or not key_after:
            continue
        if key_before == key_after:
            internal[key_before] = internal.get(key_before, 0) + 1
        else:
            weights[(key_before, key_after)] = weights.get((key_before, key_after), 0) + 1

    counts = {
        key: sum(1 for entry in tree_notebooks(series) if chapter_of(entry["repository_path"]) == key)
        for key, _label, _upper in CHAPTERS
    }
    keys = [key for key, _label, _upper in CHAPTERS if counts.get(key)]
    lines = [f"flowchart {flowchart_direction(keys, list(weights))}"]
    for key, label, _upper in CHAPTERS:
        if key not in keys:
            continue
        lines.append(f'  {key}["{esc_label(label)}<br/>{counts[key]} carnets"]')
    for (key_before, key_after), weight in sorted(weights.items()):
        plural = "s" if weight > 1 else ""
        lines.append(f"  {key_before} -->|{weight} arête{plural}| {key_after}")
    return "\n".join(lines), internal


def detail_source(series: dict, edges: dict[tuple[str, str], int], key: str) -> tuple[str, int]:
    """Détail d'une plage : ses carnets, plus les carnets d'autres plages qui les alimentent.

    Les nœuds d'entrée venus d'une autre plage sont arrondis — sans eux la carte
    de la plage C perdrait ses deux sources et paraîtrait sans prérequis.
    """
    entries = [e for e in tree_notebooks(series) if chapter_of(e["repository_path"]) == key]
    if not entries:
        return "", 0
    in_chapter = {e["repository_path"].replace("\\", "/") for e in entries}
    drawn = mermaid_drawn(edges, series)
    feeding = {
        before
        for before, after in drawn
        if after in in_chapter and chapter_of(before) != key and chapter_of(before)
    }

    ordered = [e for e in tree_notebooks(series) if e["repository_path"].replace("\\", "/") in feeding]
    ordered += entries
    node_paths = [e["repository_path"].replace("\\", "/") for e in ordered]
    inside = [(a, b) for a, b in drawn if b in in_chapter and a in set(node_paths)]
    direction = flowchart_direction(node_paths, inside)

    id_of: dict[str, str] = {}
    # La direction se pose AUSSI dans le sous-graphe : mermaid 11 ne la fait pas
    # hériter du diagramme, et un sous-graphe reste en TB même quand le diagramme
    # est déclaré LR.
    lines = [
        f"flowchart {direction}",
        f'  subgraph S["{esc_label(_chapter_label(key))}"]',
        f"    direction {direction}",
    ]
    for entry in ordered:
        repo_path = entry["repository_path"].replace("\\", "/")
        node_id = f"n{len(id_of) + 1:02d}"
        id_of[repo_path] = node_id
        num = (entry.get("path") or repo_path).replace("\\", "/").rsplit("/", 1)[-1]
        label = esc_label(f"{num} — {entry.get('label_fr') or nb_base(repo_path)}")
        shape = ("(", ")") if repo_path in feeding else ("[", "]")
        lines.append(f"    {node_id}{shape[0]}\"{label}\"{shape[1]}")
    lines.append("  end")

    for before, after in inside:
        lines.append(f"  {id_of[before]} --> {id_of[after]}")

    for repo_path, node_id in id_of.items():
        lines.append(f'  click {node_id} href "{site_url(repo_path)}" "Ouvrir le carnet"')

    return "\n".join(lines), len(inside)


def concepts_table(series: dict) -> str:
    rows = ["| Carnet | Notions enseignées (taxonomie) |", "|---|---|"]
    for entry in tree_notebooks(series):
        repo_path = entry["repository_path"].replace("\\", "/")
        labels = series["concepts_in_nb"].get(repo_path)
        notions = esc_cell(" · ".join(labels)) if labels else "—"
        label = esc_cell(entry.get("label_fr") or nb_base(repo_path))
        rows.append(f"| [{label}]({site_url(repo_path)}) | {notions} |")
    return "\n".join(rows)


def coverage_table(series_list: list[dict], pilot: dict | None) -> tuple[str, list[str]]:
    rows = ["| Série | Notions citées | Carnets cités / réels | Couverture |", "|---|---|---|---|"]
    notes: list[str] = []
    # Deux séries peuvent partager un nom d'affichage (tweety et semanticweb
    # s'appellent toutes deux « SymbolicAI ») : la clé de fichier départage.
    name_counts: dict[str, int] = {}
    for series in series_list:
        name_counts[series["name"]] = name_counts.get(series["name"], 0) + 1
    for series in sorted(series_list, key=lambda s: s["key"]):
        cited = {nb for nbs in series["taught"].values() for nb in nbs}
        taught = sum(1 for nbs in series["taught"].values() if nbs)
        real_set = real_inventory(series)
        cited_real = cited & real_set

        display = series["name"]
        if name_counts.get(display, 0) > 1:
            display = f"{display} (`{series['key']}`)"
        name = esc_cell(display + (" *(pilote)*" if series is pilot else ""))
        if not real_set:
            mark = "non mesurée"
            notes.append(f"`{series['key']}` : aucun carnet réel trouvé sous le dossier de la série")
        elif len(cited_real) == len(real_set):
            mark = "complète"
        else:
            mark = f"{100 * len(cited_real) // len(real_set)} %"
        rows.append(
            f"| {name} | {taught} / {len(series['concepts'])} | "
            f"{len(cited_real)} / {len(real_set)} | {mark} |"
        )
    return "\n".join(rows), notes


def render_page(
    series_list: list[dict],
    edges: dict[tuple[str, str], int],
    cross: list[dict],
    unresolved: int,
    total_refs: int,
) -> str:
    pilot = next((s for s in series_list if s["key"] == PILOT), None)
    if pilot is None:
        raise SystemExit(f"série pilote '{PILOT}' absente de {TAXONOMY_DIR}")

    drawn = mermaid_drawn(edges, pilot)
    node_count = len(tree_notebooks(pilot))
    overview, internal = overview_source(pilot, edges)
    details = [(key, label, detail_source(pilot, edges, key)) for key, label, _upper in CHAPTERS]
    coverage, notes = coverage_table(series_list, pilot)

    parts: list[str] = []
    parts.append(
        "---\n"
        'title: "Carte des prérequis"\n'
        'description: "Dépendances entre carnets dérivées de la taxonomie conceptuelle — '
        'régénérées avant chaque rendu de déploiement."\n'
        # Le projet rend les cellules avec echo:true (les carnets affichent leur
        # code) ; ici le « code » est le source mermaid de la carte, du bruit de
        # 100 lignes au-dessus du diagramme. `#| echo: false` DANS le bloc n'est
        # pas reconnu par ce build (la ligne part chez mermaid -> syntax error),
        # l'option se pose donc au niveau du document.
        "format:\n"
        "  html:\n"
        "    echo: false\n"
        "---\n"
    )
    parts.append(
        "<!-- FICHIER GÉNÉRÉ — ne pas éditer à la main.\n"
        "     Source     : docs/curriculum/taxonomy/*.json\n"
        "     Générateur : scripts/curriculum/generate_prereq_map.py\n"
        "     La CI de déploiement le rejoue avant chaque rendu du site. -->\n"
    )
    parts.append(
        "Cette page ne se dessine jamais à la main : la carte, les tables et les comptes\n"
        "sont **générés** depuis la taxonomie conceptuelle du dépôt\n"
        "(`docs/curriculum/taxonomy/`, issue #24993), par\n"
        "[`scripts/curriculum/generate_prereq_map.py`]"
        "(https://github.com/jsboige/CoursIA/blob/main/scripts/curriculum/generate_prereq_map.py).\n"
        "Une mise à jour de la taxonomie (nouveau carnet, nouvelle notion, nouveau\n"
        "prérequis) se propage au prochain rendu du site, sans retouche de cette page.\n"
    )
    parts.append(
        "## Comment lire la carte\n"
        "\n"
        "- Chaque **nœud** est un carnet de la série ; chaque **flèche** `A -> B` se lit\n"
        "  « le carnet A enseigne une notion prérequise par le carnet B » : suivez les\n"
        "  flèches pour savoir quoi ouvrir avant.\n"
        "- L'arête est **dérivée, pas déclarée** : elle existe parce qu'une notion citée\n"
        "  dans B référence comme prérequis une notion citée dans A. Les références non\n"
        "  résolues sont comptées sous la carte plutôt que silencieusement ignorées.\n"
        "- La série pilote est **Z3-Linq2Z3**, la seule dont la taxonomie couvre\n"
        "  aujourd'hui l'inventaire réel de ses carnets — la table « Couverture des\n"
        "  séries » mesure l'état des autres contre le disque.\n"
    )
    parts.append(f"## Carte — {pilot['name']} (série pilote)\n")
    parts.append(
        "La carte est scindée en une vue d'ensemble puis un détail par plage de carnets :\n"
        "les carnets 01 et 02 sont les prérequis de presque tout le catalogue, et un\n"
        "diagramme unique de vingt nœuds rendrait chaque étiquette illisible. Les plages\n"
        "sont un regroupement de lecture du générateur, pas une donnée de la taxonomie.\n"
    )

    parts.append("### Vue d'ensemble\n")
    parts.append("```{mermaid}\n" + overview + "\n```\n")
    inside_parts = " · ".join(
        f"**{_chapter_label(key)}** {count} arête(s)" for key, count in sorted(internal.items())
    )
    parts.append(
        "Le nombre porté par une flèche compte les arêtes carnet→carnet entre deux\n"
        f"plages ; les arêtes internes restent dans les détails ({inside_parts or 'aucune'}).\n"
    )

    for key, label, (source, count) in details:
        if not source:
            continue
        parts.append(f"### Détail — {label}\n")
        parts.append("```{mermaid}\n" + source + "\n```\n")

    parts.append(
        f"Mesuré à la génération : **{len(drawn)} arêtes** carnet→carnet sur "
        f"**{node_count} carnets**, {unresolved} référence(s) de prérequis non "
        f"résolue(s) sur {total_refs}. Chaque flèche se lit « le carnet source est un "
        "prérequis du carnet cible » ; le nombre d'arêtes suit la taxonomie, pas un dessin.\n"
        "Dans les détails, un nœud **arrondi** est un carnet d'une autre plage, rappelé\n"
        "comme entrée : sans lui la plage paraîtrait sans prérequis.\n"
    )
    parts.append("## Notions par carnet\n")
    parts.append(concepts_table(pilot) + "\n")
    parts.append(
        "## Couverture des séries\n"
        "\n"
        "La carte ci-dessus se dessine pour la série pilote ; cette table mesure, pour\n"
        "chaque série, la part des carnets **réellement présents sur le disque** que la\n"
        "taxonomie cite. Le dénominateur est l'inventaire mesuré (`*.ipynb` sous le\n"
        "dossier de la série), jamais la liste que la taxonomie déclare : une série qui\n"
        "ne cite qu'une partie de ses carnets reste partielle même si sa liste est courte.\n"
        "\n"
        "Ce bloc suit l'inventaire du disque : il est régénéré avant chaque rendu du\n"
        "site, et la garde de fraîcheur de la PR compare le reste de la page.\n"
        + COVERAGE_BEGIN + "\n\n" + coverage + "\n"
    )
    if notes:
        parts.append("\nNotes de mesure : " + " ; ".join(notes) + ".\n")
    parts.append(COVERAGE_END + "\n")
    parts.append("## Liens inter-séries\n")
    if not cross:
        parts.append(
            "Aucune arête inter-séries dans la taxonomie aujourd'hui : les prérequis\n"
            "référencés résolvent tous dans leur série d'origine. Dès que la densification\n"
            "conceptuelle (#26646) croise les séries, les liens apparaissent ici\n"
            "automatiquement — cette section, comme la carte, est régénérée.\n"
        )
    else:
        rows = ["| Depuis (prérequis) | Vers | Notion requise | Pour |", "|---|---|---|---|"]
        for edge in cross:
            rows.append(
                f"| [{nb_base(edge['from'])}]({site_url(edge['from'])}) "
                f"| [{nb_base(edge['to'])}]({site_url(edge['to'])}) "
                f"| {esc_cell(esc_label(edge['concept']))} "
                f"| {esc_cell(esc_label(edge['needed_by']))} |"
            )
        parts.append(
            f"{len(cross)} arête(s) inter-séries mesurée(s) à la génération :\n\n"
            + "\n".join(rows)
            + "\n"
        )

    return "\n".join(parts).rstrip("\n") + "\n"


def strip_disk_measured(page: str) -> str:
    """Retire de la page le bloc mesuré contre le disque (cf. COVERAGE_BEGIN).

    C'est l'objet de la comparaison `--check` : tout le reste de la page dérive
    de la taxonomie et du générateur seuls, donc une page commise qui en diffère
    est périmée. Le bloc de couverture, lui, dépend des carnets présents sur le
    disque : le comparer condamnerait toute PR ajoutant un carnet hors taxonomie.
    """
    begin = page.find(COVERAGE_BEGIN)
    end = page.find(COVERAGE_END)
    if begin == -1 or end == -1 or end < begin:
        # Page sans bloc délimité (antérieure aux marqueurs) : tout comparer.
        return page
    return page[:begin] + page[end + len(COVERAGE_END) :]


# ----------------------------------------------------------------------- main --


def main(argv: list[str]) -> int:
    series_list, by_id, by_path = load_series()
    edges, cross, unresolved, total_refs = derive_edges(series_list, by_id, by_path)
    page = render_page(series_list, edges, cross, unresolved, total_refs)

    if "--stdout" in argv:
        sys.stdout.write(page)
        return 0

    if "--check" in argv:
        current = OUTPUT.read_text(encoding="utf-8") if OUTPUT.exists() else ""
        if strip_disk_measured(current) != strip_disk_measured(page):
            print(
                f"PÉRIMÉ : {OUTPUT.relative_to(REPO_ROOT)} — relancer sans --check "
                "(le bloc de couverture, mesuré contre le disque, est hors comparaison)",
                file=sys.stderr,
            )
            return 1
        stale_block = current != page
        verdict = "À JOUR" if not stale_block else "À JOUR (bloc de couverture seul périmé)"
        print(f"{verdict} : {OUTPUT.relative_to(REPO_ROOT)}")
        return 0

    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    previous = OUTPUT.read_text(encoding="utf-8") if OUTPUT.exists() else None
    if previous == page:
        print(f"INCHANGÉ : {OUTPUT.relative_to(REPO_ROOT)}")
    else:
        OUTPUT.write_text(page, encoding="utf-8", newline="\n")
        print(f"ÉCRIT : {OUTPUT.relative_to(REPO_ROOT)}")

    pilot = next(s for s in series_list if s["key"] == PILOT)
    drawn = sum(1 for _src, _dst in mermaid_drawn(edges, pilot))
    nodes = len(tree_notebooks(pilot))
    print(
        f"mesure : {drawn} arêtes dessinées sur {nodes} carnets (pilote {PILOT}), "
        f"{len(edges)} arêtes toutes séries, "
        f"{unresolved} référence(s) non résolue(s) / {total_refs}, "
        f"{len(cross)} arête(s) inter-séries, {len(series_list)} séries"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))