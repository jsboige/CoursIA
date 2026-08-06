"""Refuse les compteurs quantitatifs ecrits a la main dans la prose.

Mandat user 2026-08-04 : « les donnees quantitatives doivent etre tenues par le
CI, pas dans la prose manuelle ». Registre : issue #9377 (compteurs d'artefacts
du depot) ET issue #9434 (mesures non reproductibles : machine/env/stochastique).

Le catalogue genere (`COURSE_CATALOG.generated.*` + marqueurs `CATALOG-STATUS`)
a ete mis en place parce que les agents ouvraient des PR sans fin pour
resynchroniser des decomptes de notebooks. Le genre n'a pas disparu : il a
migre vers la prose, ou aucun generateur ne l'atteint. 11 PR de resynchro
mergees en 3 semaines au 2026-08-04, dont une (#9153) dont le titre avoue
« re-drift post #6914 ».

Le tri est celui de l'issue : **calcule = legitime, prose = interdit**.

  - Une cellule *code* qui compte et affiche est la bonne facon de porter un
    chiffre : il se recalcule a chaque execution. On ne la regarde pas.
  - Une cellule *markdown* qui affirme « (140 lignes) » fige une mesure que
    rien ne remesure. Elle derive des qu'un tiers touche au fichier cite --
    y compris pour une raison sans rapport (sur game_theory_lean, 4 des 6
    commits de juillet sont des flips de docstrings FR/EN, qui changent le
    nombre de lignes sans toucher une ligne de mathematiques).

Ce qui reste autorise : les predicats (`0 sorry` dit que la preuve est
complete), et tout nombre qui n'est pas une mesure d'artefact du depot.

Angle mort connu -- mesure VIVANTE vs mesure FIGEE
--------------------------------------------------
Le scanner voit la forme (« N lignes »), pas le temps du recit. Il flague donc
aussi les chiffres qui datent d'un incident **clos**, ou le nombre decrit un
fait passe et ne peut plus deriver : personne n'ouvrira de PR pour
resynchroniser une mesure d'evenement. Exemple rencontre a la mise en service
(`variation-protocol-detail.md`) : « ~98 lignes redigees trois fois » chiffre
le doublon #8961/#8983/#8996 du 2026-07-31 -- c'est la PIECE qui fonde le
verdict, pas un compteur a tenir.

La ligne de partage : un decompte d'**artefact vivant** derive et revient au
CI ; un decompte **fige dans un recit au passe** est une preuve, et se garde.
D'ou le mode advisory par defaut -- l'arbitrage est humain. Ne PAS « corriger »
un chiffre d'incident au motif que le guard l'a signale : ce serait supprimer
la preuve pour faire taire l'organe.

Taxonomie #9434 -- quatre classes de mesures non reproductibles
---------------------------------------------------------------
Le scanner couvre desormais, en plus du compteur d'artefacts #9377, les quatre
classes de l'EPIC #9434 (mesures que la prose ne devrait pas figer parce qu'elles
ne se recalculent pas a l'execution) :

  - ``artifact``   (defaut, #9377) : nombre colle a un artefact du depot
                    (« 140 lignes », « 224 notebooks »). Derive a chaque commit.
  - ``machine``    (#9434) : duree absolue machine-dependante (« 24-127 ms »,
                    « ~530 ms », « 1.9 s »). Derive avec la charge machine.
  - ``env``        (#9434) : version de librairie/ecosystem figee en prose
                    (« NumPy 2.4.2 », « Mathlib v4.31.0-rc1 »). Derive quand
                    l'environnement monte de version -- doit etre tenu par le
                    fichier d'environnement (toolchain, requirements), pas la prose.
  - ``stochastic`` (#9434) : valeur a flotant non reproductible (« fitness 41.71 »)
                    quand le carnet ne seme pas (pas de seed amont). Derive a
                    chaque execution.
  - ``structural`` (#9434) : ordre de grandeur d'un speedup determine par la
                    taille du probleme (« 2.78e24x », « 4x »). **LEGITIME en
                    prose** : deterministe, ne derive pas. Explicitement EXCLU
                    du signalement -- il faut le demander explicitement
                    (``--class structural``) pour le voir inventorier, et il
                    ne fait jamais echouer.

La classe par defaut reste ``artifact`` : le contrat CI
(``prose-counts-guard.yml`` appelle ``--diff`` sans ``--class``) est preserve
exact. Les classes #9434 s'auditent en opt-in, pour poser le before/after d'un
drainage par classe.

Usage
-----
    # CI sur une PR : ne juge que les lignes AJOUTEES (classe artifact, defaut)
    python check_prose_quantitative_claims.py --diff origin/main...HEAD

    # Inventaire du stock #9377 restant
    python check_prose_quantitative_claims.py --all

    # Inventaire d'une classe #9434 (drainage)
    python check_prose_quantitative_claims.py --all --class machine
    python check_prose_quantitative_claims.py --all --class env
    python check_prose_quantitative_claims.py --all --class stochastic
    python check_prose_quantitative_claims.py --all --class structural  # legitime, rc=0

    # Toutes les classes flaggables (artifact + machine + env + stochastic)
    python check_prose_quantitative_claims.py --all --class all

    # Bloquant (une fois le stock vide)
    python check_prose_quantitative_claims.py --diff origin/main...HEAD --strict
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

# ----------------------------------------------------------------------------
# Classe « artifact » (#9377) -- compteurs d'artefacts du depot
# ----------------------------------------------------------------------------
# Noms d'artefacts du depot. Un nombre colle a l'un d'eux est une mesure d'etat
# du depot, donc perissable. Volontairement restreint : « 4 proprietes de Nash »
# ou « 3 joueurs » sont du contenu pedagogique, pas de l'etat de depot, et ne
# doivent jamais declencher.
ARTIFACT_NOUNS = r"(?:lignes?|lines?|cellules?|cells?|notebooks?|modules?|fichiers?|files?)"

# Formes attrapees : « (140 lignes) », « ~525 lignes », « **224** notebooks »,
# « 87 cellules ». Le nombre doit preceder immediatement le nom d'artefact.
#
# Note fix (#9434 angle-mort t2) : le lookbehind exclut aussi « # » -- un nombre
# precedent immediatement un diese est une reference (issue/PR GitHub « #5101 »,
# couleur hex « #333333 », ancre/titre markdown), jamais une mesure d'artefact.
COUNT_RE = re.compile(
    r"(?<![\w.#])~?\*{0,2}\d{1,6}\*{0,2}\s+" + ARTIFACT_NOUNS + r"(?![\w-])",
    re.IGNORECASE,
)

# ----------------------------------------------------------------------------
# Classe « machine » (#9434) -- durees absolues machine-dependantes
# ----------------------------------------------------------------------------
# Formes attrapees : « 24-127 ms », « ~144 ms », « 0.006 ms », « ~1.9 sec »,
# « 0.2 s », « 2 min ». Unite monolettre « s » (secondes) exige un espace
# avant elle pour eviter les collisions (suffixes, abreviations) ; les unites
# multilettres (ms/sec/min/...) tolerent un espace optionnel. Advisory : un FP
# residuel est acceptable, l'arbitrage est humain (cf angle-mort header).
#
# Note fix (#9434 angle-mort t2, incident ICT-21) : le lookbehind exclut « # »
# -- sinon un numero d'issue « #5101 s'en dérive » (cell26 ICT-21) etait matche
# comme la duree « 5101 s ». Idem pour toute reference « #NNNN » suivie d'un mot
# en s-/m-/ms/sec/min (144 occurrences repertoriees : issues, couleurs hex).
# Une vraie mesure « ~50 s » (precedee de ~, pas de #) reste capturee.
#
# Note fix (#9434 angle-mort t3) : le lookahead final exclut aussi les
# apostrophes (' et '). Sinon « s » (secondes) collidait avec le debut d'un
# verbe reflechi francais : « les annees 80 s'ecoulent », « 3 s'appliquent »
# etaient matches comme les durees « 80 s », « 3 s ». Une mesure reelle n'est
# JAMAIS suivie immediatement d'une apostrophe (toujours espace/fin/ponctuation) ;
# un « s' » est le debut de s'en/s'applique/s'etend, pas l'unite secondes. Les
# vraies mesures (« ~50 s sur GPU », « 12 s ») restent capturees.
MACHINE_RE = re.compile(
    r"(?<![\w.#])~?\d{1,6}(?:[.,]\d{1,3})?"
    r"(?:"
    r"\s?(?:ms|millisecondes?|sec(?:ondes?)?|min(?:utes?)?)"
    r"|\ss"
    r")"
    r"(?![\w\-'’-])",
    re.IGNORECASE,
)

# ----------------------------------------------------------------------------
# Classe « env » (#9434) -- versions de librairie/ecosystem figees en prose
# ----------------------------------------------------------------------------
# Formes attrapees : « NumPy 2.4.2 », « JAX 0.4 », « Mathlib v4.31.0-rc1 »,
# « PyTorch 2.1.0 ». Une version en prose derive quand l'env monte ; elle doit
# etre portee par le fichier d'environnement (lean-toolchain, requirements,
# .csproj), pas par la prose. Liste curee des libs presentes dans le depot.
ENV_LIBS = (
    r"NumPy|Pandas|PyTorch|TensorFlow|Keras|scikit-learn|sklearn|SciPy|"
    r"Transformers|LangChain|spaCy|OpenCV|cv2|Matplotlib|Seaborn|NetworkX|"
    r"SymPy|PyMC|ArviZ|Statsmodels|XGBoost|LightGBM|ONNX|vLLM|fastembed|"
    r"jpype|Tweety|OpenSpiel|SemanticKernel|Mathlib|JAX|PyPhi|pyphi"
)
ENV_RE = re.compile(
    r"\b(?:" + ENV_LIBS + r")\s+v?\d+(?:\.\d+){1,3}\b",
    re.IGNORECASE,
)

# ----------------------------------------------------------------------------
# Classe « stochastic » (#9434) -- valeurs non reproductibles sans seed
# ----------------------------------------------------------------------------
# Une mesure a virgule (>=2 decimales, signature d'un resultat numerique) co-
# occurrent avec un mot-clef de metrique stochastique sur la meme ligne. Pour
# un .ipynb, on n'accepte le signalement QUE si le carnet ne seme pas (aucun
# seed amont) ; un carnet seme est reproductible, le chiffre est legitime. Pour
# un .md isole (pas de cellule code amont a verifier), on signale en advisory
# en documentant l'incertitude. Heuristique conservatrice : un carnet avec un
# seed n'importe ou est suppose reproductible.
STOCHASTIC_KW_RE = re.compile(
    r"\b(?:fitness|accuracy|pr[eé]cision|score|scores|loss|perte|pertes|"
    r"rendement|f1|wer|bleu|entropy|entropie|exactitude|rappel|recall|"
    r"auc|roc|moyenne|moyen)\b",
    re.IGNORECASE,
)
STOCHASTIC_NUM_RE = re.compile(r"(?<![\w.#])~?\*{0,2}\d{1,6}\.\d{2,}\*{0,2}(?![\w])")
SEED_RE = re.compile(
    r"(?:np\.random\.seed|numpy\.random\.seed|random\.seed|"
    r"torch\.manual_seed|tf\.random\.set_seed|jax\.random\.PRNGKey|"
    r"random_state\s*=|seed\s*=\s*\d|rng\s*=\s*\d)",
    re.IGNORECASE,
)

# ----------------------------------------------------------------------------
# Classe « structural » (#9434) -- speedup deterministe par taille (LEGITIME)
# ----------------------------------------------------------------------------
# Formes attrapees : « 2.78e24x », « 2.78e24 », « 4x », « 1,5x ». C'est l'ordre
# de grandeur d'un speedup fixe par la taille du probleme : deterministe, ne
# derive pas. Explicitement EXCLU du signalement (header taxonomie #9434) ;
# ne figure que sur demande explicite ``--class structural``, en banniere LEGITIME.
#
# Note fix (#9434 angle-mort t1) : la forme « 2.78e24x » (notation scientifique
# SUIVIE du suffixe 'x', PR #9427 App-11-Picross) n'etait PAS attrapee par
# l'alternance originale ``(?:e\d+|x)`` : apres avoir consomme « e24 », le
# ``\b`` echouait car le 'x' suivant est un caractere mot. La branche est
# desormais ``(?:e\d+x?|x)`` : la notation scientifique peut etre suivie d'un
# 'x' optionnel. Les dimensions WxH (ex. « 100x100 », « 1280x720 ») restent
# exclues : le ``\b`` apres le premier 'x' echoue (suivi d'un chiffre).
STRUCTURAL_RE = re.compile(
    r"(?<![\w.#])~?\d+(?:[.,]\d+)?(?:e\d+x?|x)\b",
    re.IGNORECASE,
)

# Classes reconnues par --class. L'ordre sert seulement a l'affichage.
CLASS_CHOICES = ("artifact", "machine", "env", "stochastic", "structural", "all")
# Classes flaggables (peuvent faire echouer en --strict). « structural » exclu.
FLAGGABLE = ("artifact", "machine", "env", "stochastic")


def _resolve_classes(klass: str) -> tuple[set[str], bool]:
    """Rend (ensemble de classes a detecter, est_purement_structural)."""
    if klass == "all":
        return set(FLAGGABLE), False
    if klass == "structural":
        return {"structural"}, True
    return {klass}, False


# Une ligne de diff .ipynb qui ouvre un champ JSON autre que "source" est une
# metadonnee machine-ecrite, pas de la prose.
JSON_KEY_RE = re.compile(r'"(?!source")[A-Za-z_][A-Za-z0-9_]*"\s*:')

# Blocs generes : le catalogue a le droit de porter des chiffres, c'est son role.
GENERATED_MARKERS = ("CATALOG-STATUS", "COURSE_CATALOG.generated")

# Hors perimetre. `.claude` est le harnais (regles, memoires d'agents, plans,
# worktrees d'autres sessions) : ce n'est pas de la prose livree a un etudiant,
# et il y cite legitimement des seuils chiffres (« > 3000 lignes »).
SKIP_PARTS = (
    ".claude",
    ".lake",
    "node_modules",
    ".git",
    "_peters",
    "foundry-lib/lib",
    ".pytest_cache",
    "bin",
    "obj",
    "tmp",  # gitignore:582 -- scratch d'execution, pas du contenu livre
)

# Le catalogue genere porte des chiffres : c'est exactement son role.
SKIP_NAME_PREFIXES = ("COURSE_CATALOG.generated",)

# Un fichier qui se declare genere a le droit de porter des chiffres : c'est
# precisement le motif vise (« les donnees quantitatives sont tenues par le
# CI »). L'exemption n'est donc pas une liste de noms a maintenir, mais la
# presence d'un generateur proprietaire, declaree en tete de fichier.
GENERATED_HEADER_RE = re.compile(
    r"fichier\s+g[eé]n[eé]r[eé]"
    r"|ne\s+pas\s+[eé]diter\s+[aà]\s+la\s+main"
    r"|n'est\s+pas\s+maintenu\s+[aà]\s+la\s+main"
    r"|do\s+not\s+edit\s+(?:this\s+file\s+)?(?:by\s+hand|manually)"
    r"|auto(?:matically)?[-\s]generated",
    re.IGNORECASE,
)


def _declares_generated(text: str) -> bool:
    """Vrai si l'en-tete revendique un generateur proprietaire."""
    head = "\n".join(text.splitlines()[:20])
    return bool(GENERATED_HEADER_RE.search(head))


def _skipped(path: Path) -> bool:
    if any(part in SKIP_PARTS for part in path.parts):
        return True
    return path.name.startswith(SKIP_NAME_PREFIXES)


def _iter_markdown_sources(nb_path: Path):
    """Rend (index_cellule, source) pour les seules cellules markdown."""
    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return
    for idx, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        src = cell.get("source", "")
        if isinstance(src, list):
            src = "".join(src)
        yield idx, src


def _notebook_is_seeded(nb_path: Path) -> bool:
    """Vrai si le carnet seme (une cellule code contient un seed).

    Heuristique conservatrice : un seed n'importe ou dans le carnet rend le
    resultat reproductible, donc la mesure stochastique est legitime.
    """
    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False  # indetermine -> on ne supprime pas le signalement
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        src = cell.get("source", "")
        if isinstance(src, list):
            src = "".join(src)
        if SEED_RE.search(src):
            return True
    return False


def _findings_in_text(text: str, location: str, classes: set[str]) -> list[tuple[str, str, str]]:
    """Rend [(location, classe, snippet)] pour les classes demandees.

    La ligne est l'unite de co-occurrence pour stochastic (mot-clef + nombre sur
    la meme ligne) : evite les faux positifs d'un nombre et d'un mot-clef eloignes.
    """
    out: list[tuple[str, str, str]] = []
    for line in text.splitlines():
        if any(m in line for m in GENERATED_MARKERS):
            continue
        if "artifact" in classes:
            for m in COUNT_RE.finditer(line):
                out.append((location, "artifact", m.group(0).strip()))
        if "machine" in classes:
            for m in MACHINE_RE.finditer(line):
                out.append((location, "machine", m.group(0).strip()))
        if "env" in classes:
            for m in ENV_RE.finditer(line):
                out.append((location, "env", m.group(0).strip()))
        if "structural" in classes:
            for m in STRUCTURAL_RE.finditer(line):
                out.append((location, "structural", m.group(0).strip()))
        if "stochastic" in classes and STOCHASTIC_KW_RE.search(line):
            for m in STOCHASTIC_NUM_RE.finditer(line):
                out.append((location, "stochastic", m.group(0).strip()))
    return out


def scan_all(root: Path, classes: set[str]) -> list[tuple[str, str, str]]:
    findings: list[tuple[str, str, str]] = []

    for nb in root.rglob("*.ipynb"):
        if _skipped(nb):
            continue
        rel = nb.relative_to(root).as_posix()
        # stochastic : un carnet seme est reproductible -> on ne signale pas
        # cette classe pour lui (les autres classes restent actives).
        eff_classes = set(classes)
        if "stochastic" in eff_classes and _notebook_is_seeded(nb):
            eff_classes = eff_classes - {"stochastic"}
        for idx, src in _iter_markdown_sources(nb):
            findings += _findings_in_text(src, f"{rel} MD[{idx}]", eff_classes)

    for md in root.rglob("*.md"):
        if _skipped(md):
            continue
        rel = md.relative_to(root).as_posix()
        try:
            text = md.read_text(encoding="utf-8")
        except OSError:
            continue
        if _declares_generated(text):
            continue
        # Neutralise les blocs generes delimites par des marqueurs.
        if "CATALOG-STATUS:START" in text:
            text = re.sub(
                r"<!--\s*CATALOG-STATUS:START.*?CATALOG-STATUS:END\s*-->",
                "",
                text,
                flags=re.DOTALL,
            )
        # Pour un .md isole, on n'a pas de cellule code amont a verifier : on
        # garde stochastic en advisory (incertitude documentee, pas de gate seed).
        findings += _findings_in_text(text, rel, classes)

    return findings


def scan_diff(diff_range: str, classes: set[str]) -> list[tuple[str, str, str]]:
    """Ne juge que les lignes AJOUTEES : le stock existant ne fait pas echouer."""
    try:
        diff = subprocess.run(
            ["git", "diff", "--unified=0", diff_range],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            timeout=180, check=False,
        ).stdout
    except (OSError, subprocess.SubprocessError) as exc:
        print(f"[ERREUR] git diff a echoue : {exc}", file=sys.stderr)
        return []

    findings: list[tuple[str, str, str]] = []
    generated_cache: dict[str, bool] = {}

    def _is_generated_file(rel: str) -> bool:
        if rel not in generated_cache:
            try:
                head = Path(rel).read_text(encoding="utf-8", errors="replace")
                generated_cache[rel] = _declares_generated(head)
            except OSError:
                generated_cache[rel] = False
        return generated_cache[rel]

    # Pour le mode diff, la verification seed par carnet est couteuse et le
    # contrat CI ne demande que la classe artifact par defaut : on applique le
    # gate seed stochastic seulement en --all (scan_all). En diff, stochastic
    # reste advisory brut (incertitude documentee).
    current = "?"
    for line in diff.splitlines():
        if line.startswith("+++ b/"):
            current = line[6:]
            continue
        if not line.startswith("+") or line.startswith("+++"):
            continue
        if not (current.endswith(".ipynb") or current.endswith(".md")):
            continue
        if _skipped(Path(current)):
            continue
        if current.endswith(".md") and _is_generated_file(current):
            continue
        # Dans un .ipynb, seule une valeur de "source" est de la prose. Les
        # champs de metadonnees (`"notes": "... 14/14 cells executed."`, ecrit
        # par le populateur metadata.cost) sont machine-ecrits : ils portent
        # legitimement des chiffres et ne derivent pas en prose.
        if current.endswith(".ipynb"):
            body = line[1:].lstrip()
            if any(k in line for k in ('"output_type"', '"execution_count"', '"outputs"')):
                continue
            if JSON_KEY_RE.match(body):  # "<cle>": ... avec <cle> != source
                continue
            if '"source"' not in line and not body.startswith('"'):
                continue
        findings += _findings_in_text(line[1:], current, classes)

    return findings


def _emit_grouped(findings: list[tuple[str, str, str]], strict: bool, structural_only: bool) -> int:
    """Sortie multi-classes : une section par classe, ou banniere LEGITIME."""
    if structural_only:
        # structural est legitime (speedup deterministe) : on inventorie sans signaler.
        if not findings:
            print("[OK] classe structural : aucun speedup deterministe en prose.")
            return 0
        by_file: dict[str, list[str]] = {}
        for loc, _klass, snippet in findings:
            by_file.setdefault(loc.split(" MD[")[0], []).append(snippet)
        print(
            f"[LEGITIME -- structural] {len(findings)} speedup(s) deterministe(s) en "
            f"prose, {len(by_file)} fichier(s). Exclus du signalement (ne derive pas). :\n"
        )
        for path in sorted(by_file):
            preview = ", ".join(sorted(set(by_file[path]))[:6])
            print(f"  {path}  ({len(by_file[path])})  {preview}")
        return 0  # structural ne fait jamais echouer

    if not findings:
        print("[OK] aucun compteur quantitatif en prose (classe(s) demandee(s)).")
        return 0

    # Regroupe les findings par classe, puis par fichier dans chaque classe.
    by_class: dict[str, dict[str, list[str]]] = {}
    for loc, klass, snippet in findings:
        by_class.setdefault(klass, {}).setdefault(loc.split(" MD[")[0], []).append(snippet)

    total = len(findings)
    label = "REFUS" if strict else "ADVISORY"
    classes_hdr = "/".join(by_class.keys())
    print(f"[{label}] {total} compteur(s) quantitatif(s) en prose ({classes_hdr}), {len(by_class)} classe(s) :\n")
    for klass in (k for k in FLAGGABLE if k in by_class):  # ordre stable
        files = by_class[klass]
        nclass = sum(len(v) for v in files.values())
        print(f"=== [{klass}] {nclass} compteur(s), {len(files)} fichier(s) ===")
        for path in sorted(files):
            preview = ", ".join(sorted(set(files[path]))[:6])
            print(f"  {path}  ({len(files[path])})  {preview}")
        print()

    print(
        "Les donnees quantitatives sont tenues par le CI, pas par la prose "
        "(#9377 compteurs d'artefacts, #9434 mesures non reproductibles).\n"
        "Supprimer la mesure, garder le predicat : `(140 lignes, 0 sorry)` -> `(0 sorry)`."
    )
    return 1 if strict else 0


def _emit_legacy(findings: list[tuple[str, str, str]], strict: bool) -> int:
    """Sortie mono-classe artifact (format d'origine, contrat CI preserve)."""
    if not findings:
        print("[OK] aucun compteur quantitatif en prose.")
        return 0

    by_file: dict[str, list[str]] = {}
    for loc, _klass, snippet in findings:
        by_file.setdefault(loc.split(" MD[")[0], []).append(snippet)

    label = "REFUS" if strict else "ADVISORY"
    print(f"[{label}] {len(findings)} compteur(s) quantitatif(s) en prose, {len(by_file)} fichier(s) :\n")
    for path in sorted(by_file):
        snippets = by_file[path]
        preview = ", ".join(sorted(set(snippets))[:6])
        print(f"  {path}  ({len(snippets)})  {preview}")

    print(
        "\nLes donnees quantitatives sont tenues par le CI, pas par la prose (issue #9377)."
        "\nSupprimer la mesure, garder le predicat : `(140 lignes, 0 sorry)` -> `(0 sorry)`."
    )
    return 1 if strict else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--all", action="store_true", help="inventaire complet du stock (suivi #9377/#9434)")
    g.add_argument("--diff", metavar="RANGE", help="ne juge que les lignes ajoutees (ex: origin/main...HEAD)")
    ap.add_argument(
        "--class",
        dest="klass",
        default="artifact",
        choices=CLASS_CHOICES,
        help="classe a auditer (defaut: artifact=#9377 ; machine/env/stochastic=#9434 ; "
             "structural=legitime-exclu ; all=toutes les flaggables)",
    )
    ap.add_argument("--strict", action="store_true", help="rc=1 sur finding (defaut : advisory, rc=0)")
    ap.add_argument("--root", default=".", help="racine du depot")
    args = ap.parse_args()

    classes, structural_only = _resolve_classes(args.klass)

    if args.all:
        findings = scan_all(Path(args.root).resolve(), classes)
    else:
        findings = scan_diff(args.diff, classes)

    # Format legacy exact pour la classe artifact seule (contrat CI : --diff sans --class).
    if args.klass == "artifact":
        return _emit_legacy(findings, args.strict)
    return _emit_grouped(findings, args.strict, structural_only)


if __name__ == "__main__":
    sys.exit(main())
