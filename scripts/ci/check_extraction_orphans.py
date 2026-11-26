"""Garde extraction-orphelins (#13902) : une PR qui supprime ou deplace un
fichier ne doit pas laisser de consommateur pendouillant.

Defaut ferme (dispatch c0023 sur #13902, contrat de maintenance des
sous-modules) : « le controle qui empeche l'extraction d'orphaniser un carnet
consommateur ». Quand une PR retire un fichier de l'arbre -- extraction vers
un sous-module, deplacement de serie, renommage -- chaque fichier restant qui
referencait l'ancien chemin devient un orphelin : lien de navigation mort,
cle de baseline pointant dans le vide, import casse. L'incident fondateur du
cote de la voie rapide : #27119, ou le deplacement 17b-17f a laisse pendre
la baseline de densite pedagogique, le README Actuariat, un doc curriculum
et un deck de slides -- chacun repare a la main dans un commit de rattrapage.

Principe : le verdict est BORNE AU DIFF (base...head). La garde ne regarde
que les chemins SUPPRIMES ou DEPLACES par la PR courante, puis verifie que
l'arbre resultant ne les reference plus. Elle ne peut donc pas heriter d'un
rouge de la base, et une PR qui ne supprime rien est verte par construction.

Formes de reference reconnues, pour un chemin supprime P et un consommateur
C (toutes en slashs POSIX, convention du depot pour liens, cles JSON et
YAML) :
  1. chemin complet          : P tel quel (cles de baseline repo-relatives) ;
  2. chemin relatif          : relpath(dirname(C) -> P), la forme d'un lien
                               markdown entre voisinage (couvre le lien
                               same-dir, qui se reduit au basename) ;
  3. queue deux-composantes  : parent/basename (cles serie-relatives) ;
  4. basename seul           : uniquement si le basename NE RESOUT PAS a un
                               fichier existant relatif a C -- un lien
                               `](X.ipynb)` dont la cible disparait est un
                               orphelin certain, un basename qui resolve
                               (voisin deplace ensemble) n'en est pas un.
                               Une mention de NOM (bare basename hors cible
                               de lien) n'est pas une reference : seule une
                               cible `](basename)` compte.

Couverture par occurrence : pour CHAQUE forme, une occurrence n'est signalee
que si son token -- etendu vers la gauche sur les caracteres valides d'un
chemin -- ne RESOUT PAS (repo-relative ou relative a C) vers un fichier blob
de l'arbre. Ceci ferme la classe de faux positif mesuree en re-jouant la
garde sur la tete REPAREE de #27119 : un consommateur corrige qui porte le
nouveau chemin (`.../GameTheory-17-MultiAgent-RL/GameTheory-17b-....ipynb`)
contient le basename comme suffixe et etait re-signalé a tort.

Limites documentees : une mention de PROSE sans extension (le stem du
fichier) n'est pas attrapee ; les formes en backslash ne sont pas cherchees
(le depot ecrit ses chemins en slashs) ; les artefacts derives regeneres par
l'automatisation (COURSE_CATALOG.generated.*, translations/) sont exclus --
leur regeneration a lieu au merge, pas dans la PR (mesure #27538). Une cible
URL-encodee (`serie/My%20Notebook.ipynb`) echappe aussi a la preselection : la
recherche `git grep -F` porte sur le basename litteral, espaces compris, qui
n'apparait pas dans le blob encode -- mesure du verdict Hermes du 24/11 sur
cette PR (17 chemins avec espaces dans l'arbre, 0 lien `%20.ipynb` trouve).

Sorties : rc=0 propre ; rc=1 orphelins trouves ; rc=2 panne d'instrument
(git injoignable, rev introuvable). --self-test : pre-controle du moteur
(matcher, resolution, exclusions, parsing) sans depot -- un detecteur qui ne
prouve pas qu'il tire est indiscernable d'un detecteur debranche (lecon
#11685/#12817, pattern pre_argv de la TRANCHE54).
"""

from __future__ import annotations

import argparse
import json
import os
import posixpath
import subprocess
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# Artefacts regeneres par l'automatisation au merge : une PR de renommage les
# laisse volontairement en retard sur la branche (catalogue byte-identique a
# main, cf catalog-pr-hygiene ; traductions derivees, cf #27538).
DERIVED_PREFIXES = ("translations/",)
DERIVED_BASENAME_PREFIXES = ("COURSE_CATALOG.generated", "CURRICULUM.generated")

# Extensions dont le contenu n'est pas du texte cherchable.
BINARY_SUFFIXES = {
    ".png", ".jpg", ".jpeg", ".gif", ".ico", ".pdf", ".zip", ".7z", ".gz",
    ".wasm", ".exe", ".dll", ".so", ".dylib", ".woff", ".woff2", ".ttf",
    ".otf", ".bin", ".parquet", ".npy", ".npz", ".pkl", ".pt", ".onnx",
    ".svgz", ".mp4", ".webm", ".wav", ".snappy", ".zst",
}

MAX_CONSUMER_BYTES = 10 * 1024 * 1024

# Caracteres sur lesquels un token-chemin s'etend vers la gauche depuis une
# occurrence d'aiguille. Tout caractere hors de ce set (guillemets,
# espaces, parentheses...) borne le token : c'est un delimiteur de contexte.
_PATH_CHARS = set(
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789._-/:~")


def git(*args: str) -> str:
    """git en mode texte ; toute panne leve (rc=2 en amont)."""
    r = subprocess.run(
        ["git", "-C", REPO_ROOT, *args],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if r.returncode != 0:
        raise SystemExit(
            f"INSTRUMENT: git {' '.join(args)} -> rc={r.returncode}: {r.stderr.strip()}")
    return r.stdout


def is_derived(path: str) -> bool:
    name = posixpath.basename(path)
    return (any(path.startswith(p) for p in DERIVED_PREFIXES)
            or any(name.startswith(b) for b in DERIVED_BASENAME_PREFIXES))


def is_historical_record(path: str) -> bool:
    """Vrai pour un registre d'HISTORIQUE, qui n'est pas un consommateur vivant.

    Un rename-ledger enregistre PAR DEFINITION les anciens chemins (c'est son
    objet), un snapshot de PRs fermées capture un état passé : leurs references
    a un chemin retire ne sont pas des liens morts. Les signaler bloquerait
    tout deplacement (le ledger existe precisement pour garder la trace du
    deplace) -- faux positif mesure en re-jouant la garde sur la tete reparee
    de #27119 : `rename-ledger.tsv` et le snapshot `list_closed_unmerged_prs`.
    Les exclure ne falsifie rien : on ne reecrit pas l'historique pour apaiser
    un linter, on declare qu'un registre n'est pas un consommateur.
    """
    name = posixpath.basename(path)
    if "rename-ledger" in name:
        return True
    return "fixtures" in path.split("/") and "snapshot" in name


def parse_name_status(out: str) -> tuple[set[str], dict[str, str]]:
    """Extrait (supprimes, renommages old->new) d'un `diff --name-status`."""
    removed: set[str] = set()
    renames: dict[str, str] = {}
    for line in out.splitlines():
        if not line.strip():
            continue
        parts = line.split("\t")
        status, rest = parts[0], parts[1:]
        if status.startswith("R") and len(rest) >= 2:
            renames[rest[0]] = rest[1]
            removed.add(rest[0])
        elif status.startswith("D") and rest:
            removed.add(rest[0])
    return removed, renames


def needles_for(removed: str, consumer: str, resolver) -> list[tuple[str, str]]:
    """Formes de reference a `removed` cherchables dans `consumer`.

    Rend les couples (forme, aiguille) ; la forme sert au rendu, l'aiguille au
    match. Le basename est TOUJOURS suffixe de l'aiguille -- c'est le
    pre-filtre du scan.
    """
    base = posixpath.basename(removed)
    out: list[tuple[str, str]] = []
    if removed != consumer:
        out.append(("path", removed))
    cdir = posixpath.dirname(consumer)
    rel = os.path.relpath(removed, cdir if cdir else ".").replace(os.sep, "/")
    if rel != removed:
        out.append(("relpath", rel))
    tail = "/".join(removed.split("/")[-2:])
    if tail != removed and tail != rel:
        out.append(("tail", tail))
    if not resolver(base, consumer):
        out.append(("basename", base))
    return [(f, n) for f, n in out if n]


def occurrence_uncovered(blob: str, needle: str, consumer_dir: str,
                         tree_files: set[str], require_link: bool = False) -> bool:
    """Vrai si AU MOINS une occurrence de `needle` n'est pas couverte.

    Une occurrence est COUVERTE quand son token -- l'aiguille etendue vers
    la gauche sur les caracteres de chemin -- resolve (repo-relative ou
    relative au consommateur) vers un blob vivant de l'arbre. Ferme le faux
    positif mesure sur #27119 tete reparee : le nouveau chemin contient le
    basename comme suffixe, il ne doit pas etre re-signe. Strictement plus
    etroit qu'un test de sous-chaine : aucune occurrence couverte n'ajoute
    de finding, seules les occurrences non couvertes comptent.

    require_link (forme basename seule) : une occurrence ne compte que si elle
    est une CIBLE de lien markdown (precedee de `](`). Un bare basename dans
    la prose est un NOM, pas une reference qui puisse pendre -- ferme la classe
    des mentions de nom mesuree sur #27119 tete reparee (README consommateurs
    du lake, material-map). Limitation declaree : une reference basename hors
    contexte markdown (un open() en Python) est hors scope ; elle est couverte
    par les formes path/relpath/tail des qu'elle porte un chemin.
    """
    start = 0
    while True:
        i = blob.find(needle, start)
        if i < 0:
            return False
        j = i + len(needle)
        if require_link and blob[max(0, i - 2):i] != "](":
            start = j
            continue
        k = i
        while k > 0 and blob[k - 1] in _PATH_CHARS:
            k -= 1
        token = blob[k:j]
        resolved = (posixpath.normpath(token) in tree_files
                    or posixpath.normpath(
                        posixpath.join(consumer_dir, token)) in tree_files)
        if not resolved:
            return True
        start = j


def self_test() -> int:
    """Pre-controle du moteur, sans depot (pattern pre_argv TRANCHE54)."""
    failures = []

    exists = {"a/b/keep.txt", "new/x.txt", "d/README.md"}

    def resolver(base: str, consumer: str) -> bool:
        cdir = posixpath.dirname(consumer)
        return posixpath.normpath(posixpath.join(cdir, base)) in exists

    # forme path + relpath + queue
    ns = parse_name_status("R100\told/x.ipynb\tnew/x.ipynb\nD\told/y.py\nM\tz.md\n")
    if ns[0] != {"old/x.ipynb", "old/y.py"} or ns[1] != {"old/x.ipynb": "new/x.ipynb"}:
        failures.append(f"parse_name_status: {ns}")
    n = needles_for("old/x.ipynb", "other/dir/c.md", resolver)
    forms = dict(n)
    if forms.get("path") != "old/x.ipynb" or forms.get("relpath") != "../../old/x.ipynb":
        failures.append(f"formes path/relpath: {forms}")
    if "tail" in forms:  # queue == chemin quand removed n'a qu'un etage
        failures.append(f"tail redondant: {forms}")
    # basename : resolu au voisinage -> absent ; non resolu -> present
    n2 = needles_for("a/b/keep.txt", "a/b/c.txt", resolver)
    if "basename" in dict(n2):
        failures.append("basename mal exemptee quand la cible resolve")
    n3 = needles_for("old/x.txt", "old/c.md", resolver)
    if dict(n3).get("basename") != "x.txt":
        failures.append(f"basename non rendue sur cible disparue: {dict(n3)}")
    # basename resolu par un voisin present : consommateur DEPLACE AVEC la
    # cible (old/x.txt et old/c.md partis ensemble vers new/)
    n4 = needles_for("old/x.txt", "new/c.md", resolver)
    if "basename" in dict(n4):
        failures.append("faux positif sur deplacement solidaire")
    # exclusions derivees
    if not is_derived("translations/genai/image.csv"):
        failures.append("translations/ non exclue")
    if not is_derived("docs/COURSE_CATALOG.generated.md"):
        failures.append("COURSE_CATALOG.generated non exclu")
    if is_derived("docs/curriculum/symbolic-formalization.md"):
        failures.append("exclusion trop large")
    # registres d'historique : pas des consommateurs vivants
    if not is_historical_record("docs/reference/rename-ledger.tsv"):
        failures.append("rename-ledger non exclu (historique)")
    if not is_historical_record(
            "scripts/ci/tests/fixtures/list_closed_unmerged_prs_snapshot.json"):
        failures.append("snapshot fixtures non exclu (historique)")
    if is_historical_record("docs/curriculum/actuariat.json"):
        failures.append("consommateur vivant confondu avec un registre")
    if is_historical_record("scripts/tests/fixtures_x/notasnapshot.json"):
        failures.append("fixture non-snapshot confondu avec un registre")
    # couverture par occurrence : le nouveau chemin couvre le basename
    tree = {"new/x.txt", "other/keep.txt"}
    if occurrence_uncovered("voir [x](new/x.txt)", "x.txt", "", tree):
        failures.append("occurrence couverte par chemin neuf signalee (repo)")
    if occurrence_uncovered("[x](../new/x.txt)", "x.txt", "src", tree):
        failures.append("occurrence couverte par chemin neuf signalee (relatif)")
    if not occurrence_uncovered("voir x.txt ici", "x.txt", "a/b", tree):
        failures.append("occurrence nue non signalee")
    if not occurrence_uncovered(
            "[x](old/x.txt)", "old/x.txt", "a/b", tree):
        failures.append("occurrence sur ancien chemin non signalee")
    # forme basename : seule une CIBLE de lien `](basename)` compte
    if not occurrence_uncovered("[s](x.txt)", "x.txt", "a/b", tree,
                                require_link=True):
        failures.append("cible de lien basename non signalee")
    if occurrence_uncovered("voir x.txt ici", "x.txt", "a/b", tree,
                            require_link=True):
        failures.append("mention de nom basename signalee a tort")

    for f in failures:
        print(f"SELF-TEST FAIL: {f}")
    print(f"self-test: {len(failures)} echec(s)")
    return 1 if failures else 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--base", help="rev de base du diff (ex: origin/main)")
    ap.add_argument("--head", default="HEAD", help="rev de tete (defaut: HEAD)")
    ap.add_argument("--json", action="store_true", help="sortie JSON machine")
    ap.add_argument("--self-test", action="store_true",
                    help="pre-controle du moteur sans depot")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()
    if not args.base:
        ap.error("--base requis (hors --self-test)")

    base = git("rev-parse", "--verify", args.base).strip()
    head = git("rev-parse", "--verify", args.head).strip()

    removed, renames = parse_name_status(
        git("diff", "--name-status", "-M", f"{base}...{head}"))
    new_sides = set(renames.values())

    if not removed:
        # Cas commun : la PR ne supprime ni ne deplace rien. Sortie immediate --
        # la garde est bornee au diff, il n'existe aucun orphelin a chercher.
        if args.json:
            print(json.dumps({"base": base, "head": head, "removed": [],
                              "scanned": 0, "skipped_oversize": 0,
                              "findings": []}, ensure_ascii=True))
        else:
            print("[extraction-orphans] aucun chemin supprime/deplace : rien "
                  "a verifier.")
        return 0

    # Ensemble de resolution : TOUT fichier blob track a la tete, non filtre
    # (un lien peut resoudre vers un binaire ou un derive -- ce qui compte est
    # que sa cible existe, pas sa nature).
    tree_files: set[str] = set()
    for line in git("ls-tree", "-r", head).splitlines():
        meta, _, path = line.partition("\t")
        parts = meta.split()
        if len(parts) >= 3 and parts[1] == "blob":
            tree_files.add(path)

    def resolver(basename: str, consumer: str) -> bool:
        cdir = posixpath.dirname(consumer)
        return posixpath.normpath(posixpath.join(cdir, basename)) in tree_files

    basenames = {posixpath.basename(p) for p in removed}

    # Pres election native : le basename est suffixe de TOUTES les formes
    # d'aiguille, donc un consommateur possible contient necessairement l'un
    # des basenames. `git grep -F` scanne l'arbre a la vitesse C et ne rend
    # que les fichiers candidats -- la lecture fine (formes, resolution) ne
    # porte plus que sur cette poignee.
    grep_args = ["grep", "-l", "-I", "-F"]
    for b in sorted(basenames):
        grep_args += ["-e", b]
    r = subprocess.run(
        ["git", "-C", REPO_ROOT, *grep_args, head, "--", "."],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if r.returncode not in (0, 1):
        raise SystemExit(f"INSTRUMENT: git grep -> rc={r.returncode}: {r.stderr.strip()}")
    # git grep prefixe chaque chemin du rev (forme `<rev>:<path>`) ; -l rend
    # un chemin par ligne.
    prefix = f"{head}:"
    candidates = [ln[len(prefix):] for ln in r.stdout.splitlines()
                  if ln.startswith(prefix)]
    consumers = [p for p in candidates
                 if p not in new_sides and p not in removed and not is_derived(p)
                 and not is_historical_record(p)
                 and os.path.splitext(p)[1].lower() not in BINARY_SUFFIXES]

    # Lecture des contenus candidats. La pres election git grep rend le lot
    # minuscule (dizaines de fichiers) : un sous-processus par fichier, pas de
    # protocole --batch a cadrer. Une trame batch a desynchronise en mesure
    # sur l'arbre reel (entete nue sur un README de GenAI/Audio) ; la lecture
    # unitaire n'a pas de trame a casser.
    findings: list[dict[str, str]] = []
    scanned = skipped_big = 0
    for path in consumers:
        r = subprocess.run(
            ["git", "-C", REPO_ROOT, "cat-file", "blob", f"{head}:{path}"],
            capture_output=True,
        )
        if r.returncode != 0:
            # Chemin quote par git (accents) ou evasion : sans consequence,
            # la couverture de ces fichiers est perdue sans faux verdict.
            continue
        if len(r.stdout) > MAX_CONSUMER_BYTES:
            skipped_big += 1
            continue
        blob = r.stdout.decode("utf-8", "replace")
        scanned += 1
        if not any(b in blob for b in basenames):
            continue
        cdir = posixpath.dirname(path)
        for rem in sorted(removed):
            if posixpath.basename(rem) not in blob:
                continue
            forms = [form for form, needle in needles_for(rem, path, resolver)
                     if occurrence_uncovered(
                         blob, needle, cdir, tree_files,
                         require_link=(form == "basename"))]
            if forms:
                findings.append({
                    "consumer": path, "removed": rem,
                    "form": "+".join(forms),
                })

    payload = {
        "base": base, "head": head,
        "removed": sorted(removed), "scanned": scanned,
        "skipped_oversize": skipped_big, "findings": findings,
    }
    if args.json:
        print(json.dumps(payload, ensure_ascii=True, indent=1))
    else:
        print(f"[extraction-orphans] {len(removed)} chemin(s) supprime(s)/deplace(s), "
              f"{scanned} consommateurs scannes ({skipped_big} trop volumineux).")
        for f in findings:
            print(f"ORPHANED-CONSUMER {f['consumer']} -> {f['removed']} "
                  f"(forme: {f['form']})")
        if not findings:
            print("OK: aucun consommateur ne reference un chemin retire par la PR.")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
