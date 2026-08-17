"""
P3 — ajoute bandeaux typés bicolores sur 9 slides comparatives 2-cols.

Pattern cohérent avec P2 slide 18:
  Bandeau bicolore bg-orange-700 + bg-slate-800, texte blanc, pleine largeur,
  inséré après le H1 et avant le premier paragraphe.

Préserve CRLF (fichier source en CRLF sur cette branche).

Cible:
  - 377  Arbre d'exploration           Idée de base | Exemple : Énigme
  - 507  Jeux                          Jeux vs Exploration | Arbre Minimax
  - 551  Problèmes à satisfaction ...  Définition CSPs | Techniques
  - 714  Application: argumentation    Code de conduite | Qu'est-ce qu'un argument ?
  - 801  Application: Planification    Expression de problème | Approches
  - 1054 Théorie des jeux (1/2)       Environnement multi-agents | Optimisation de stratégies
  - 1092 Théorie des jeux (2/2)       Jeux simultanés | Jeux séquentiels
  - 1169 Conception de mécanismes     Concepts | Résultats
"""

import sys
from pathlib import Path

SLIDES_PATH = Path(r"C:/dev/CoursIA-s3-acculturation/slides/S3-acculturation/slides.md")

TARGETS = [
    (377, "Idée de base",       "Exemple : Énigme"),
    (507, "Jeux vs Exploration", "Arbre Minimax"),
    (551, "Définition CSPs",     "Techniques"),
    (714, "Code de conduite",    "Qu'est-ce qu'un argument ?"),
    (801, "Expression de problème", "Approches"),
    (1054, "Environnement multi-agents", "Optimisation de stratégies"),
    (1092, "Jeux simultanés",    "Jeux séquentiels"),
    (1169, "Concepts",           "Résultats"),
]

BANDEAU_TEMPLATE = (
    '<div class="grid grid-cols-2 gap-0 -mt-4 -mb-2">\r\n'
    '<div class="bg-orange-700 text-white px-4 py-2 text-base font-bold text-center">{LEFT}</div>\r\n'
    '<div class="bg-slate-800 text-white px-4 py-2 text-base font-bold text-center">{RIGHT}</div>\r\n'
    '</div>\r\n\r\n'
)


def main():
    raw = SLIDES_PATH.read_bytes()
    # Préserver CRLF: travailler en bytes, splitter sur \r\n
    # Détection auto du line ending
    has_crlf = b"\r\n" in raw
    le = b"\r\n" if has_crlf else b"\n"
    text = raw.decode("utf-8")

    # Split sur \n (CRLF ou LF), garder les \r en fin de ligne
    # Python str.splitlines(keepends=True) gère correctement les deux
    lines = text.splitlines(keepends=True)

    n_inserted = 0
    # On itère EN ORDRE DÉCROISSANT des indices pour ne pas perturber les décalages
    insertions = []
    for target_line_no, left, right in TARGETS:
        idx = target_line_no - 1  # 0-based
        if idx >= len(lines):
            print(f"[SKIP] ligne {target_line_no} hors range", file=sys.stderr)
            continue
        # Le H1 doit commencer par "# " et matcher (on ne valide pas le texte exact ici)
        h1_line = lines[idx]
        if not h1_line.lstrip("\r\n").startswith("# "):
            print(f"[WARN] ligne {target_line_no} ne commence pas par '# ': {h1_line!r}", file=sys.stderr)
        # On insère APRES la ligne vide qui suit le H1
        # Pattern: H1 (idx), vide (idx+1), suite (idx+2)
        # On insère entre vide (idx+1) et suite (idx+2)
        insert_at = idx + 2
        bandeau = BANDEAU_TEMPLATE.format(LEFT=left, RIGHT=right)
        insertions.append((insert_at, bandeau, target_line_no, left, right))

    # Appliquer en ordre décroissant pour préserver les indices
    insertions.sort(key=lambda x: -x[0])
    for insert_at, bandeau, target_line_no, left, right in insertions:
        lines.insert(insert_at, bandeau)
        n_inserted += 1
        print(f"[OK] ligne {target_line_no}: '{left}' | '{right}'")

    new_text = "".join(lines)
    SLIDES_PATH.write_bytes(new_text.encode("utf-8"))
    print(f"\n{n_inserted} bandeaux insérés sur {len(TARGETS)} cibles.")


if __name__ == "__main__":
    main()