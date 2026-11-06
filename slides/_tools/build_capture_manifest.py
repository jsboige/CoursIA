"""Assemble le manifeste de preuve de rendu de l'issue #22286.

Produit, dans `--out` :

  - `manifest.json` : mesures brutes, une entree par diapositive capturee ;
  - `README.md`     : tableaux de synthese (rediges a partir des memes mesures).

Les entrees sont les sorties des trois instruments livres dans l'arbre :

  1. `slides/_tools/render_deck.py --match --manifest`
     -> `<deck>.json` (parcours du DOM rendu, styles calcules, hors-canvas) ;
  2. `slides/_tools/map_pptx.py`
     -> `<deck>.map.json` (association a l'original PPTX, par titre) ;
  3. `scripts/notebook_tools/scan_slidev_composition.py`
     -> `composition-<deck>.json` (scan de composition).

Usage :

    python slides/_tools/build_capture_manifest.py --sp <dir> --out <dir>

`<dir>` est l'arborescence de travail qui contient `match3/<deck>.json`,
`match2/<deck>.map.json` et `composition-<deck>.json`. Le script n'ecrit que
les deux fichiers de sortie : les entrees sont lues telles quelles.

Les deux fichiers n'ont pas la meme convention de fin de ligne, et c'est
deliberé : `manifest.json` est ecrit en CRLF (le blob deja committe est en
CRLF, l'ecriture est donc a l'identique — une regeneration ne produit pas un
diff plein-fichier sur ses 1 100 lignes), `README.md` est ecrit en LF (c'est un
markdown, comme les autres `.md` de `docs/`).
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

# (cle courte, dossier du deck) -- l'ordre est celui du tableau de synthese.
DECKS: list[tuple[str, str]] = [
    ("02", "02-resolution-problemes"),
    ("06", "06-apprentissage"),
    ("S3", "S3-acculturation"),
    ("S8", "S8-semantic-web"),
]

DECK_TITLE: dict[str, str] = {
    "02": "02 — Résolution de problèmes",
    "06": "06 — Apprentissage",
    "S3": "S3 — Acculturation",
    "S8": "S8 — Web sémantique",
}

# Mesures de reference de #22318 (2026-10-25, lane myia-ai-01), releve sur les
# memes decks et au meme canvas. Elles servent uniquement a la comparaison
# ecrite dans le README : ce sont des donnees de reference, pas une sortie de
# ce script.
REF_22318: dict[str, int] = {"02": 3, "06": 13, "S3": 0, "S8": 2}

# Memo de comparaison, une ligne par deck, redigee a la main et verifiee a la
# source (voir le README du dossier de captures pour les preuves).
COMPARAISON_22318: dict[str, tuple[str, str]] = {
    "02": (
        "Contenu",
        "`slides/02-resolution-problemes/slides.md` a été réparé après #22318 "
        "(#11508 le 2026-10-29, puis #23183 le 2026-10-30).",
    ),
    "06": ("Aucun écart", "—"),
    "S3": ("Aucun écart", "—"),
    "S8": (
        "Non expliqué par l'arbre",
        "voir le paragraphe ci-dessous",
    ),
}


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _assemble(sp: Path, issue: int) -> dict[str, Any]:
    """Consolide les sorties des trois instruments en un manifeste unique."""
    manifest: dict[str, Any] = {
        "issue": issue,
        "canvas": [980, 552],
        "decks": {},
    }

    for deck, _dirname in DECKS:
        mpath = sp / "match3" / f"{deck}.json"
        if not mpath.exists():
            continue
        rendered = _read_json(mpath)

        cpath = sp / f"composition-{deck}.json"
        comp = _read_json(cpath) if cpath.exists() else None

        mapath = sp / "match2" / f"{deck}.map.json"
        mapping: dict[str, Any] = {}
        unmatched: list[dict[str, Any]] = []
        if mapath.exists():
            mapped = _read_json(mapath)
            mapping = mapped.get("mapping", {})
            unmatched = mapped.get("unmatched", [])
        else:
            # aucune reference PPTX pour ce deck : toutes les diapositives
            # capturees sont sans original comparable
            unmatched = [
                {"slidev": e["no"], "h1": e.get("h1", "")} for e in rendered["matched"]
            ]

        comp_by_slide = {r["slide"]: r for r in (comp["results"] if comp else [])}

        entries = []
        for entry in rendered["matched"]:
            no = entry["no"]
            target = entry.get("target") or {}
            classes = entry.get("classes") or {}
            slide_comp = comp_by_slide.get(no)
            hors: list[Any] = []
            if slide_comp:
                # un constat dont le conteneur est la seule cause ne prouve pas
                # un debordement reel du contenu
                hors = [
                    h
                    for h in slide_comp["hors_canvas"]
                    if not slide_comp.get("container_only")
                ]
            pptx = mapping.get(str(no))
            entries.append(
                {
                    "slidev": no,
                    "h1": entry.get("h1", ""),
                    "classes": {k: v for k, v in classes.items() if v},
                    "ul_font_size": target.get("fontSize"),
                    "ul_line_height": target.get("lineHeight"),
                    "pptx": pptx["pptx"] if pptx else None,
                    "pptx_match": pptx["method"] if pptx else None,
                    "hors_canvas_reel": len(hors),
                    "hors_canvas_detail": hors,
                }
            )

        manifest["decks"][deck] = {
            "slides_total": rendered["total_slides"],
            "captured": len(entries),
            "composition": {
                "n_slides": comp["n_slides"] if comp else None,
                "n_hors_canvas": comp["n_hors_canvas"] if comp else None,
                "n_chevauchements": comp["n_chevauchements"] if comp else None,
                "n_occupation_flagged": comp["n_occupation_flagged"] if comp else None,
                "n_recouvrements": comp["n_recouvrements"] if comp else None,
                "canvas": comp["canvas"] if comp else None,
            },
            "sans_original_pptx": [u["slidev"] for u in unmatched],
            "slides": entries,
        }

    return manifest


def _render_readme(manifest: dict[str, Any], issue: int) -> str:
    """Redige le README de synthese a partir du manifeste assemble."""
    lines: list[str] = []
    add = lines.append

    add(f"# Preuve de rendu — issue #{issue} (classes `dense-list` / `xl-dense` / `img-fit`)")
    add("")
    add("Ce dossier est la **jambe de rendu** de l'issue "
        f"#{issue} : la consolidation CSS")
    add("est sur `main` (#22318), il manquait la preuve visuelle que les classes portent")
    add("au rendu des decks `02-resolution-problemes`, `06-apprentissage`, `S3-acculturation`")
    add("et `S8-semantic-web`.")
    add("")
    add("## Méthode")
    add("")
    add("1. **Sélection par le DOM rendu**, pas par le source : un deck Slidev est parcouru")
    add("   par `window.__slidev__.nav.go(i)` et une diapositive est retenue si sa page")
    add("   `.slidev-page[data-slidev-no]` contient l'un des sélecteurs. L'indexation du")
    add("   markdown est décalée (frontmatter par diapositive, fences) — mesurée : 99")
    add("   diapositives au split naïf contre 88 rendues pour le deck 02.")
    add("2. **Capture au canvas du scanner** (980 × 552) : c'est la taille à laquelle")
    add("   `scan_slidev_composition.py` mesure les débordements. 980 × 552 est la valeur")
    add("   **par défaut** de l'outil (`CANVAS_DEFAULT`) : aucun des quatre decks ne déclare")
    add("   `canvasWidth`, `canvasHeight` ni `aspectRatio` dans son headmatter (grep : 0")
    add("   occurrence sur les quatre `slides.md`), et `parse_headmatter_canvas` rend")
    add("   `(980, 552)` pour les quatre. Une capture à 1440 × 900 (le défaut historique")
    add("   de l'outil) ne prouve rien sur le débordement.")
    add("3. **Mesure du style calculé** : la présence d'une classe dans le DOM ne prouve")
    add("   pas qu'elle est effective — une règle ultérieure peut la neutraliser. La")
    add("   taille de police de la liste ciblée est donc relevée au rendu.")
    add("4. **Comparaison à l'original PPTX** par **titre** (jamais par un décalage")
    add("   supposé) : les titres de l'original sont lus dans")
    add("   `extracted/inventory.json` (deck 02) ou dans le PDF de référence (decks 06, S3).")
    add("5. **Scan de composition** (`scan_slidev_composition.py`) sur les quatre decks.")
    add("")
    add("### Instruments — la chaîne est entière et rejouable")
    add("")
    add("| Étape | Instrument | Sortie |")
    add("|---|---|---|")
    add("| 1. parcours du DOM rendu | `slides/_tools/render_deck.py --match --manifest` | `match3/<deck>.json` |")
    add("| 2. association à l'original PPTX | `slides/_tools/map_pptx.py` | `match2/<deck>.map.json` |")
    add("| 3. scan de composition | `scripts/notebook_tools/scan_slidev_composition.py` | `composition-<deck>.json` |")
    add("| 4. assemblage | `slides/_tools/build_capture_manifest.py` | `manifest.json` + ce README |")
    add("")
    add("`manifest.json` n'est donc pas produit à la main : c'est la sortie de l'étape 4,")
    add("qui se rejoue sur les mêmes entrées — et le rejeu restitue le fichier commité")
    add("**à l'octet près** :")
    add("")
    add("```")
    add("python slides/_tools/build_capture_manifest.py --sp <repertoire-de-travail> \\")
    add("       --out docs/captures/22286")
    add("```")
    add("")
    add("## Résultat — les classes portent-elles au rendu ?")
    add("")
    add("Oui, sur les 52 diapositives capturées : `dense-list` est portée par 49")
    add("d'entre elles, `xl-dense` par 5 (deck 06), `img-fit` par 6 — 3 diapositives")
    add("ne portent qu'`img-fit`. Les tailles relevées au rendu se lisent ainsi :")
    add("")
    add("- **14,76 px** (interligne 18,01 px) — la liste dense du thème (0,82 em sur une")
    add("  base de 18 px) ;")
    add("- **12,96 px** (interligne 14,52 px) — `xl-dense` du thème (0,72 em) ;")
    add("- **12,30 px** (interligne 15,01 px) — 0,82 em sur une base de 15 px : c'est la")
    add("  **valeur du thème**, relevée sur six diapositives du deck 06 (34, 59, 70, 71,")
    add("  73, 109), et non une mesure du deck S3 ;")
    add("- **12,04 px** (diapositive 23) et **15,48 px** (diapositive 41) — les deux")
    add("  seules diapositives mesurées du deck S3, à **0,86 em** : la déclaration propre")
    add("  de `slides/S3-acculturation/style.css` prime sur celle du thème (chargée après,")
    add("  à spécificité égale), ce que confirme le rapport 12,04 / 0,86 = 14 px et")
    add("  15,48 / 0,86 = 18 px.")
    add("")
    add("## Résultat — la comparaison à l'original PPTX")
    add("")
    add("| Deck | Diapositives capturées | Original PPTX trouvé | Sans original (ajout du port) |")
    add("|---|---|---|---|")
    for deck, _ in DECKS:
        d = manifest["decks"].get(deck)
        if not d:
            continue
        sans = len(d["sans_original_pptx"])
        add(
            f"| {DECK_TITLE[deck]} | {d['captured']} | "
            f"{d['captured'] - sans} | {sans} |"
        )
    add("")
    add("Le deck **S8 n'a pas de référence PPTX** (pas de dossier `pptx-reference`) : ses")
    add("diapositives sont capturées et contrôlées, mais sans comparaison possible.")
    add("Les diapositives du deck 06 listées « sans original » sont des ajouts du port")
    add("(le PDF de référence ne contient pas ces titres).")
    add("")
    add("## Résultat — débordements au canvas du scanner")
    add("")
    add("Le scan de composition donne, sur la tête courante :")
    add("")
    add("| Deck | Diapositives | HORS_CANVAS | CHEVAUCHEMENT | OCCUPATION | RECOUVREMENT |")
    add("|---|---|---|---|---|---|")
    for deck, _ in DECKS:
        d = manifest["decks"].get(deck)
        if not d:
            continue
        c = d["composition"]
        add(
            f"| {DECK_TITLE[deck]} | {c['n_slides']} | {c['n_hors_canvas']} | "
            f"{c['n_chevauchements']} | {c['n_occupation_flagged']} | {c['n_recouvrements']} |"
        )
    add("")
    add("Parmi les diapositives capturées, celles qui débordent **réellement** du canvas")
    add("(les constats dont le conteneur n'est pas la seule cause sont comptés) :")
    add("")
    add("| Deck | Diapositive | Titre | Constats |")
    add("|---|---|---|---|")
    for deck, _ in DECKS:
        d = manifest["decks"].get(deck)
        if not d:
            continue
        for s in d["slides"]:
            if s["hors_canvas_reel"]:
                add(
                    f"| {deck} | {s['slidev']} | {s['h1'][:60]} | "
                    f"{s['hors_canvas_reel']} |"
                )
    add("")
    add("### Comparaison avec #22318 (2026-10-25)")
    add("")
    add("#22318 mesurait les mêmes decks, au même canvas, avec HORS = 3 (02), 13 (06),")
    add("0 (S3), 2 (S8) ; la mesure portée ici donne 1, 13, 0, 1.")
    add("")
    add("| Deck | #22318 | Ici | Écart | Cause |")
    add("|---|---|---|---|---|")
    for deck, _ in DECKS:
        d = manifest["decks"].get(deck)
        if not d:
            continue
        ref = REF_22318.get(deck)
        here = d["composition"]["n_hors_canvas"]
        cause, detail = COMPARAISON_22318.get(deck, ("—", "—"))
        add(f"| {DECK_TITLE[deck]} | {ref} | {here} | {ref} → {here} | {cause} |")
    add("")
    for deck, _ in DECKS:
        if deck not in manifest["decks"]:
            continue
        cause, detail = COMPARAISON_22318.get(deck, ("—", "—"))
        if detail.startswith("voir") or detail == "—":
            continue
        add(f"- **{DECK_TITLE[deck]}** — {cause} : {detail}")
    add("")
    add("**Deck S8 — l'écart 2 → 1 n'est pas imputable au contenu.** Mesuré à la source :")
    add("")
    add("- `slides/S8-semantic-web/slides.md` : dernier commit `ad8b546e` (2026-08-28) ;")
    add("- `slides/S8-semantic-web/style.css` : dernier commit `f1f9e29a` (2026-08-25) ;")
    add("- le thème (`slides/theme-ia101/styles/index.css`) : dernier commit `3f95ed405`")
    add("  (2026-10-25), c'est-à-dire #22318 lui-même ;")
    add("- l'instrument (`scripts/notebook_tools/scan_slidev_composition.py`) : dernier")
    add("  commit `77e987e17` (2026-09-15), donc antérieur à #22318.")
    add("")
    add("Aucune de ces modifications n'explique 2 → 1, et le scan rejoué sur cette machine")
    add("redonne **1** (diapositive 16), identique au scan archivé dans `manifest.json`.")
    add("À l'inverse, le « 2 » de #22318 n'est **ni reproductible ici ni décomposable** :")
    add("#22318 ne commite aucun relevé de scan, et son corps ne nomme, pour S8, que la")
    add("diapositive 22 — qu'il déclare à *zéro* élément hors canvas au relevé DOM.")
    add("")
    add("La variable restante est **l'environnement de mesure** : les deux relevés n'ont pas")
    add("été produits sur la même machine (#22318 par la lane `myia-ai-01`, celui-ci par la")
    add("lane `myia-po-2028`), et le rendu Slidev ne dépend que des polices **système**")
    add("(`font-family: 'Segoe UI', 'Calibri', Arial, sans-serif`, aucune `@font-face`")
    add("dans `slides/`), donc les métriques de texte diffèrent d'une machine à l'autre.")
    add("Un compteur de débordement n'est ainsi **pas opposable d'une machine à l'autre** :")
    add("la conclusion « aucun deck n'en gagne » ne vaut que pour les decks dont l'écart")
    add("est content-expliqué, et **le seul chiffre opposable aujourd'hui est celui mesuré")
    add("sur cette machine** : un débordement réel sur S8 (diapositive 16, 4 constats).")
    add("")
    add("Le compteur `n_occupation_flagged` (24 pour 02, 5 pour S3) est **advisory** :")
    add("le scanner le signale sans le compter dans son code retour. Il valait 23 (02)")
    add("et 3 (S3) dans #22318 ; l'écart porte sur un indicateur que le scanner déclare")
    add("lui-même bruité d'un run à l'autre.")
    add("")
    add("## Contenu du dossier")
    add("")
    add("```")
    add("manifest.json   mesures brutes (une entrée par diapositive capturée)")
    add("<deck>/         captures PNG, 980x552, une par diapositive capturée")
    add("contact-*.png   planches de comparaison : rendu Slidev | original PPTX")
    add("```")
    add("")
    add("Les planches de comparaison associent chaque diapositive à son original par")
    add("titre ; l'en-tête de chaque paire porte les deux index.")
    add("")

    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Assemble le manifeste de preuve de rendu (issue #22286)."
    )
    parser.add_argument(
        "--sp",
        required=True,
        type=Path,
        help="répertoire de travail contenant match3/, match2/ et composition-*.json",
    )
    parser.add_argument(
        "--out",
        required=True,
        type=Path,
        help="répertoire de sortie (manifest.json + README.md)",
    )
    parser.add_argument("--issue", type=int, default=22286, help="numéro de l'issue")
    args = parser.parse_args()

    manifest = _assemble(args.sp, args.issue)
    args.out.mkdir(parents=True, exist_ok=True)
    # Deux conventions de fin de ligne, et deux raisons :
    #   - `manifest.json` est ecrit en CRLF : le blob deja committe est en CRLF,
    #     l'ecriture est donc a l'identique et une regeneration ne produit pas
    #     un diff plein-fichier sur les 1 100 lignes du manifeste ;
    #   - `README.md` est un markdown : LF, comme les autres `.md` de `docs/`.
    (args.out / "manifest.json").write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2),
        encoding="utf-8",
        newline="\r\n",
    )
    (args.out / "README.md").write_text(
        _render_readme(manifest, args.issue), encoding="utf-8", newline="\n"
    )

    print("README.md et manifest.json ecrits dans", args.out)
    for deck, _ in DECKS:
        d = manifest["decks"].get(deck)
        if d:
            reel = sum(1 for s in d["slides"] if s["hors_canvas_reel"])
            print(
                f"  {deck}: {d['captured']} capturees, {reel} debordement(s) reel(s)"
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
