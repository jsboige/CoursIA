#!/usr/bin/env python3
"""Rendu de la feuille d'annotation pour les evaluateurs humains (#20222).

Grain 3 de #20222 (tranche C de #17578, grand-mere #10355). Les deux premiers
grains ont livre les instruments de bout de chaine : ``sample_external_eval.py``
produit une feuille **aveugle** (``sheet.jsonl``, champs ``item_id`` et ``text``
seulement) avec sa cle et son manifeste ; ``score_external_eval.py`` transforme
des feuilles remplies en alpha de Krippendorff et IC de Wilson. Il manquait le
maillon du milieu : **le document qu'un humain peut lire et remplir**.

Ce script comble ce trou sans rouvrir l'instrument qu'il consomme :

1. ``render`` -- rend une feuille aveugle en un document Markdown lisible
   (enonces numerotes, espace de reponse **ferme** groupe par famille) plus un
   gabarit de reponses CSV. L'espace de reponse est la liste des noeuds de la
   taxonomie : c'est l'information que le protocole (section 3, passage 1
   « annotation nue ») donne a l'evaluateur -- ni definitions, ni exemples.

2. ``convert`` -- convertit le gabarit rempli en la forme exacte que
   ``score_external_eval.py`` consomme (``{item_id, node}`` en JSONL), en
   derivant la famille de premier niveau du noeud. Une faute de frappe sur un
   noeud est refusee **ici**, avec son numero de ligne, plutot que de devenir
   une note vide au moment du calcul d'alpha.

Trois proprietes sont tenues par construction, pas par convention :

- **L'aveuglement est verifie a l'entree.** ``render`` refuse toute feuille dont
  un enregistrement porte un champ autre que ``item_id`` et ``text`` : la
  feuille d'une autre campagne (ou la cle elle-meme) est rejetee en nommant le
  champ fautif, jamais rendue avec son etiquette.
- **La famille ne peut pas contredire le noeud.** ``convert`` la derive du
  noeud par la meme regle que l'echantillonneur et le mesureur
  (``node.split(separator)[0]``) ; le controle de coherence du mesureur ne peut
  donc pas se declencher sur une feuille passee par ici.
- **Rien ne disparait en silence.** ``render`` refuse une feuille vide ou un
  identifiant en double ; ``convert`` refuse par defaut une feuille
  partiellement remplie et ne la convertit qu'avec ``--allow-partial``, en
  annoncant le nombre de lignes ecartees.

Aucun fichier produit ici ne contient d'etiquette cible : le document et le
gabarit derivent de la seule feuille aveugle. La cle et le manifeste de la
campagne restent ou l'echantillonneur les a mis (hors depot, cf protocole
section 6).

Usage::

    # 1. rendre la feuille pour un evaluateur
    python scripts/fallacy_detection/render_annotation_sheet.py render \
        --sheet .../external_eval/run1/sheet.jsonl \
        --vocab data/academic/aligned.jsonl \
        --out-dir .../external_eval/run1/pass1/reviewer-1 \
        --label reviewer-1

    # 2. convertir le gabarit rempli en feuille mesurable
    python scripts/fallacy_detection/render_annotation_sheet.py convert \
        --answers .../pass1/reviewer-1/answers_reviewer-1.csv \
        --vocab data/academic/aligned.jsonl \
        --out .../pass1/reviewer-1.jsonl
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import sys
from pathlib import Path

# Champs autorises sur une feuille d'annotation. Tout autre champ est traite
# comme une fuite potentielle d'etiquette : la feuille d'une autre campagne
# porte ``node``/``family``, et la cle de correction porte les deux.
SHEET_FIELDS = frozenset({"item_id", "text"})

# Colonnes du gabarit de reponses : l'evaluateur ne remplit que ``node``.
ANSWER_COLUMNS = ("item_id", "node")


def sha256_of(path: Path) -> str:
    """Empreinte SHA-256 d'un fichier, lue par blocs."""
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def read_jsonl(path: Path) -> list[dict]:
    """Lit un JSONL en refusant toute ligne illisible (fail-closed)."""
    records: list[dict] = []
    with path.open(encoding="utf-8") as handle:
        for lineno, line in enumerate(handle, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError as exc:
                raise SystemExit(f"{path}:{lineno} : JSON illisible ({exc.msg}).")
            if not isinstance(record, dict):
                raise SystemExit(
                    f"{path}:{lineno} : objet JSON attendu, {type(record).__name__} recu."
                )
            records.append(record)
    return records


def family_of(node: str, separator: str) -> str:
    """Famille de premier niveau d'un noeud, meme regle que l'echantillonneur."""
    return node.split(separator)[0].strip()


def load_sheet(path: Path) -> list[dict]:
    """Feuille aveugle : ``item_id`` + ``text``, rien d'autre.

    L'aveuglement de l'instrument amont est verifie ici plutot que suppose : une
    feuille qui porterait ``node`` ou ``family`` (cle de correction, feuille
    d'une autre campagne) est refusee en nommant le champ et l'item, parce que
    rendre ce document la publierait mot pour mot a l'evaluateur.
    """
    records = read_jsonl(path)
    if not records:
        raise SystemExit(f"{path} : feuille vide -- rien a rendre.")
    seen: set[str] = set()
    sheet: list[dict] = []
    for lineno, record in enumerate(records, start=1):
        extra = sorted(set(record) - SHEET_FIELDS)
        if extra:
            raise SystemExit(
                f"{path}:{lineno} : champ(s) {extra} sur la feuille d'annotation. "
                "Une feuille aveugle ne porte que 'item_id' et 'text' -- "
                "verifier qu'il s'agit bien de sheet.jsonl et non de key.jsonl."
            )
        item_id = str(record.get("item_id", "")).strip()
        text = record.get("text", "")
        if not item_id:
            raise SystemExit(f"{path}:{lineno} : 'item_id' vide.")
        if not isinstance(text, str) or not text.strip():
            raise SystemExit(f"{path}:{lineno} : 'text' vide ou non textuel pour '{item_id}'.")
        if item_id in seen:
            raise SystemExit(f"{path}:{lineno} : item_id '{item_id}' present deux fois.")
        seen.add(item_id)
        sheet.append({"item_id": item_id, "text": text})
    return sheet


def load_vocabulary(path: Path, separator: str) -> dict[str, list[str]]:
    """Espace de reponse ferme : famille de premier niveau -> noeuds tries.

    Toute source JSONL portant un champ ``node`` convient (le corpus aligne
    lui-meme, ou un export de taxonomie) : le rendu n'invente pas l'espace de
    reponse, il le lit la ou il est deja defini.
    """
    records = read_jsonl(path)
    if not records:
        raise SystemExit(f"{path} : vocabulaire vide -- aucun noeud a proposer.")
    vocabulary: dict[str, set[str]] = {}
    for lineno, record in enumerate(records, start=1):
        node = record.get("node")
        if not isinstance(node, str) or not node.strip():
            raise SystemExit(
                f"{path}:{lineno} : champ 'node' manquant ou vide -- "
                "le vocabulaire attend un JSONL portant 'node' (le corpus aligne convient)."
            )
        node = node.strip()
        family = family_of(node, separator)
        if not family:
            raise SystemExit(
                f"{path}:{lineno} : famille de premier niveau vide pour le noeud '{node}' "
                f"(separateur '{separator}')."
            )
        vocabulary.setdefault(family, set()).add(node)
    return {family: sorted(nodes) for family, nodes in sorted(vocabulary.items())}


def fence_for(text: str) -> str:
    """Cloture de bloc assez longue pour que le texte s'affiche sans alteration.

    Un texte contenant lui-meme des backticks fermerait un bloc de trois
    caracteres : la cloture est donc calculee sur la plus longue serie presente.
    """
    longest = 0
    current = 0
    for char in text:
        if char == "`":
            current += 1
            longest = max(longest, current)
        else:
            current = 0
    return "`" * max(3, longest + 1)


def render_markdown(
    sheet: list[dict],
    vocabulary: dict[str, list[str]],
    label: str,
    title: str,
    separator: str,
) -> str:
    """Document remis a l'evaluateur : consigne, espace de reponse, enonces."""
    node_total = sum(len(nodes) for nodes in vocabulary.values())
    lines: list[str] = [
        f"# {title}",
        "",
        f"Evaluateur : **{label}** — {len(sheet)} enonces a annoter.",
        "",
        "## Ce qui est demande",
        "",
        (
            "Pour chaque enonce ci-dessous, indiquer **le noeud de la taxonomie qui "
            "correspond le mieux**, choisi dans la liste fermee de la section suivante. "
            "Un seul noeud par enonce."
        ),
        "",
        (
            f"- La reponse s'ecrit dans le fichier `answers_{label}.csv`, colonne `node`, "
            "en recopiant le chemin **exactement** tel qu'il apparait dans la liste "
            f"(famille puis noeud, separes par `{separator}`)."
        ),
        (
            "- Une ligne laissee vide vaut « non annote » : elle est signalee, jamais "
            "comptee comme une reponse."
        ),
        (
            "- Aucune definition ni exemple n'est fourni : c'est le principe de ce "
            "passage. La liste ci-dessous est le seul vocabulaire autorise."
        ),
        "",
        f"## Espace de reponse ({len(vocabulary)} familles, {node_total} noeuds)",
        "",
    ]
    for family, nodes in vocabulary.items():
        lines.append(f"### {family}")
        lines.append("")
        for node in nodes:
            lines.append(f"- `{node}`")
        lines.append("")

    lines += ["## Enonces", ""]
    for position, item in enumerate(sheet, start=1):
        fence = fence_for(item["text"])
        lines.append(f"### Enonce {position} — `{item['item_id']}`")
        lines.append("")
        lines.append(fence)
        lines.append(item["text"])
        lines.append(fence)
        lines.append("")
    return "\n".join(lines).rstrip("\n") + "\n"


def write_answers_template(path: Path, sheet: list[dict]) -> None:
    """Gabarit CSV : une ligne par enonce, colonne ``node`` a remplir."""
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(ANSWER_COLUMNS)
        for item in sheet:
            writer.writerow([item["item_id"], ""])


def safe_label(label: str) -> str:
    """Etiquette de fichier : pas de separateur, pas de nom reserve."""
    cleaned = label.strip()
    if not cleaned or any(char in cleaned for char in '\\/:*?"<>|') or cleaned in {".", ".."}:
        raise SystemExit(
            f"Etiquette '{label}' inutilisable comme nom de fichier. "
            "Attendu : pseudonyme simple (lettres, chiffres, '-', '_')."
        )
    return cleaned


def cmd_render(args: argparse.Namespace) -> int:
    label = safe_label(args.label)
    sheet = load_sheet(args.sheet)
    vocabulary = load_vocabulary(args.vocab, args.family_separator)
    known = {node for nodes in vocabulary.values() for node in nodes}

    args.out_dir.mkdir(parents=True, exist_ok=True)
    document_path = args.out_dir / f"annotation_{label}.md"
    answers_path = args.out_dir / f"answers_{label}.csv"
    manifest_path = args.out_dir / "render_manifest.json"

    document_path.write_text(
        render_markdown(sheet, vocabulary, label, args.title, args.family_separator),
        encoding="utf-8",
    )
    write_answers_template(answers_path, sheet)

    manifest = {
        "issue": 20222,
        "label": label,
        "items": len(sheet),
        "families": len(vocabulary),
        "vocabulary_nodes": len(known),
        "family_separator": args.family_separator,
        "sheet": {"path": str(args.sheet), "sha256": sha256_of(args.sheet)},
        "vocab": {"path": str(args.vocab), "sha256": sha256_of(args.vocab)},
        "document_sha256": sha256_of(document_path),
        "answers_template_sha256": sha256_of(answers_path),
        "note": "Document et gabarit derives de la seule feuille aveugle : aucune etiquette cible n'y figure.",
    }
    manifest_path.write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )

    print(f"Enonces rendus    : {len(sheet)}")
    print(f"Espace de reponse : {len(vocabulary)} familles, {len(known)} noeuds")
    print(f"Document          : {document_path}")
    print(f"Gabarit reponses  : {answers_path}")
    print(f"Manifeste         : {manifest_path}")
    return 0


def read_answers(path: Path) -> list[dict]:
    """Lit le gabarit rempli en refusant les colonnes absentes."""
    if not path.is_file():
        raise SystemExit(f"{path} : feuille de reponses introuvable.")
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        fields = reader.fieldnames or []
        missing = [column for column in ANSWER_COLUMNS if column not in fields]
        if missing:
            raise SystemExit(
                f"{path} : colonne(s) {missing} absente(s) -- attendu {list(ANSWER_COLUMNS)}."
            )
        rows: list[dict] = []
        for lineno, row in enumerate(reader, start=2):
            item_id = (row.get("item_id") or "").strip()
            node = (row.get("node") or "").strip()
            if not item_id and not node:
                continue
            if not item_id:
                raise SystemExit(f"{path}:{lineno} : 'item_id' vide alors que 'node' est rempli.")
            rows.append({"item_id": item_id, "node": node, "lineno": lineno})
    if not rows:
        raise SystemExit(f"{path} : aucune ligne de reponse -- rien a convertir.")
    return rows


def cmd_convert(args: argparse.Namespace) -> int:
    vocabulary = load_vocabulary(args.vocab, args.family_separator)
    known = {node for nodes in vocabulary.values() for node in nodes}
    rows = read_answers(args.answers)

    answered: list[dict] = []
    unanswered: list[dict] = []
    seen: set[str] = set()
    for row in rows:
        if not row["node"]:
            unanswered.append(row)
            continue
        if row["node"] not in known:
            raise SystemExit(
                f"{args.answers}:{row['lineno']} : noeud '{row['node']}' absent du vocabulaire. "
                "Le chemin doit etre recopie exactement depuis l'espace de reponse "
                f"(separateur '{args.family_separator}')."
            )
        if row["item_id"] in seen:
            raise SystemExit(
                f"{args.answers}:{row['lineno']} : item '{row['item_id']}' note deux fois."
            )
        seen.add(row["item_id"])
        answered.append(row)

    if unanswered and not args.allow_partial:
        raise SystemExit(
            f"{args.answers} : {len(unanswered)} enonce(s) non rempli(s) sur {len(rows)} "
            f"(premier : ligne {unanswered[0]['lineno']}, item '{unanswered[0]['item_id']}'). "
            "Completer la feuille, ou relancer avec --allow-partial pour convertir "
            "les seules lignes remplies -- elles sont alors annoncees, jamais tues."
        )
    if not answered:
        raise SystemExit(
            f"{args.answers} : aucune reponse exploitable ({len(unanswered)} ligne(s) vide(s))."
        )

    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", encoding="utf-8") as handle:
        for row in answered:
            # La famille est derivee du noeud par la regle du mesureur : une
            # feuille passee par ici ne peut pas le contredire.
            record = {
                "item_id": row["item_id"],
                "node": row["node"],
                "family": family_of(row["node"], args.family_separator),
            }
            handle.write(json.dumps(record, ensure_ascii=False) + "\n")

    print(f"Reponses converties : {len(answered)}")
    if unanswered:
        print(f"Lignes vides ecartees : {len(unanswered)} (--allow-partial)")
    print(f"Feuille mesurable   : {args.out}  (sha256 {sha256_of(args.out)[:12]})")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    subparsers = parser.add_subparsers(dest="command", required=True)

    render = subparsers.add_parser("render", help="rendre une feuille aveugle pour un evaluateur")
    render.add_argument("--sheet", required=True, type=Path, help="sheet.jsonl (item_id, text)")
    render.add_argument(
        "--vocab",
        required=True,
        type=Path,
        help="JSONL portant 'node' (le corpus aligne convient) = espace de reponse ferme",
    )
    render.add_argument("--out-dir", required=True, type=Path, help="repertoire de sortie")
    render.add_argument("--label", required=True, help="pseudonyme de l'evaluateur (nom de fichier)")
    render.add_argument("--title", default="Feuille d'annotation — test externe", help="titre du document")
    render.add_argument("--family-separator", default="/", help="separateur de chemin du noeud (defaut '/')")
    render.set_defaults(handler=cmd_render)

    convert = subparsers.add_parser("convert", help="convertir le gabarit rempli en feuille mesurable")
    convert.add_argument("--answers", required=True, type=Path, help="answers_<label>.csv rempli")
    convert.add_argument("--vocab", required=True, type=Path, help="meme vocabulaire que le rendu")
    convert.add_argument("--out", required=True, type=Path, help="JSONL de sortie (forme du mesureur)")
    convert.add_argument("--family-separator", default="/", help="separateur de chemin du noeud (defaut '/')")
    convert.add_argument(
        "--allow-partial",
        action="store_true",
        help="convertir malgre des lignes vides (elles sont comptees et annoncees)",
    )
    convert.set_defaults(handler=cmd_convert)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    return args.handler(args)


if __name__ == "__main__":
    sys.exit(main())
