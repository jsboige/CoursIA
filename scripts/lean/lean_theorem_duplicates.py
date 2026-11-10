#!/usr/bin/env python3
"""Theoremes en double entre lacs Lean (extension de la carte du materiel).

Issue #24183 (T0). Deux lacs du depot peuvent prouver le ** meme** resultat :
c'est ce que #23097 avait conclu "absent" en comparant les **noms de modules**,
instrument structurellement aveugle a la question posee ("Arrow et Sen sont
prouves deux fois").

Cet organe repond a la question par le **contenu** des declarations :

- le **nom normalise** de la declaration (namespace retire, camelCase decoupe) ;
- les **mots-cles de la docstring** ;
- les **tokens de l'enonce**.

Deux declarations ne sont comparees que si leurs noms **designent le meme
resultat** (l'un est contenu dans l'autre : `arrow` et `arrow_impossibility`),
ET si un **terme discriminant** relie leurs docstrings -- un terme du nom que
les deux docstrings mentionnent, et que le corpus rare. Sans cette seconde
condition, le tableau serait noyé de `refl`, `trans`, `card` et `step`, qui
portent les memes noms dans des lacs sans rapport (les lemmes generiques ne
sont pas des doublons de resultat).

Un candidat est une paire de declarations **de lacs differents**. La sortie
est un **signal**, pas un verdict : retirer, fusionner ou deplacer une preuve
est une decision humaine (la tranche T1 de #24183) ; cet organe ne touche a
aucun fichier de preuve.

Controle positif obligatoire : la paire Arrow
(`MyIA.AI.Notebooks/GameTheory/SocialChoice/social_choice_core_lean/SocialChoice/Arrow.lean`
contre `MyIA.AI.Notebooks/GameTheory/lean_game_defs/SocialChoice.lean`) et la
paire Sen (`.../social_choice_core_lean/SocialChoice/Sen.lean` contre le meme
fichier) doivent apparaitre. Le temoin suit le lac : depuis la descente
#24183, Arrow et Sen vivent dans le lac autonome social_choice_core_lean.

Usage :
    python scripts/lean/lean_theorem_duplicates.py             # candidats (texte)
    python scripts/lean/lean_theorem_duplicates.py --json      # sortie machine
    python scripts/lean/lean_theorem_duplicates.py --write      # regenere la page
    python scripts/lean/lean_theorem_duplicates.py --check      # exit 1 si derive
    python scripts/lean/lean_theorem_duplicates.py --df-max 8

Garde de derive d'arbre (`--ref`, `--require-fresh`) :
    `git ls-files` mesure l'**index de l'arbre courant**, pas une reference. Sur
    un arbre de travail en retard, l'organe mesure donc des fichiers que la
    reference n'a plus -- et le tableau se remplit de paires qui n'existent
    nulle part ailleurs (lacs fantomes). Constat mesure du 09/11/2026 sur
    #24183 : **415 lignes** depuis l'arbre partage contre **49** depuis un
    arbre a `origin/main`, sans un mot d'avertissement. L'organe compare
    desormais sa population a celle de `--ref` (defaut `origin/main`) et
    avertit sur **stderr** -- la page commitee reste byte-identique, donc le
    gate `--check` n'est pas couple a la fraicheur de l'arbre local.
"""

from __future__ import annotations

import argparse
import collections
import json
import re
import subprocess
import sys
import unicodedata
from dataclasses import dataclass, field
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

# Le nom du script, deduit du fichier lui-meme : un nom ecrit en dur dans la
# docstring d'usage ou dans l'en-tete de la page peut deriver de la reality (le
# nom livre a ete `lean_theorem_duplicates.py`, l'organe en citait un autre --
# sept occurrences, dont une sur la page commitee, qui ne pouvait donc etre
# copie sans `No such file or directory`). Le nom vient donc de `__file__`, et
# un test verifie que la docstring d'usage et l'en-tete de page nomment
# exactement ce fichier.
SCRIPT_NAME = Path(__file__).name

# La page generee : son propre fichier, distinct de la carte du materiel
# (`lean-material-map.md`, touchee par une autre lane). Le contenu est
# regenere par `--write` ; `--check` echoue quand page et arbre divergent.
PAGE = REPO_ROOT / "docs" / "reference" / "lean-theorem-duplicates.md"

# Les repertoires exclus : le Lean vendu (`.lake/packages`, `foundry-lib/lib`),
# les references tierces (`_peters/`) et les fixtures de reference du prover.
EXCLUDED_MARKERS = (
    ".lake/",
    "_peters/",
    "foundry-lib/lib/",
    "agent_tests/prover/session_state/reference_docs/",
    "node_modules/",
)

STOPWORDS = frozenset(
    """
    a au aux avec ce ces dans de des du elle en est et eux il je la le les leur lui ma mais me
    meme mes moi ne nos notre nous on ou par pas pour qu que qui sa se ses son sur ta te tes toi
    tu un une vos votre vous c d j l m n s t y ete etee etees etes etant suis es est sommes
    sont sera seront plus moins tout tous toute toutes autre autres apres avant chez
    comme donc alors aussi ainsi cela celui celle ceux chaque entre encore fait faire
    lors lorsque leurs peut peuvent doit doivent cela celle ci comme
    """.split()
)

DECL_RE = re.compile(
    r"^(?P<indent>[ \t]*)"
    r"(?:@\[[^\]]*\][ \t]*)?"
    r"(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)[ \t]+)*"
    r"(?P<kind>theorem|lemma|example)[ \t]+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)"
)

DOC_OPEN = "/--"
DOC_CLOSE = "-/"

# Seuil de rarete d'un terme discriminant : au-dela, le terme est un mot
# generique (`card`, `step`, `refl`) et ne prouve rien sur l'identite du
# resultat. La rarete se mesure sur le **nom** (combien de declarations
# portent ce token), pas sur la docstring.
DEFAULT_DF_MAX = 8
# Contenance minimale des noms : l'un des deux noms doit etre couvert par
# l'autre (`arrow` dans `arrow_impossibility`).
DEFAULT_CONTAINMENT = 0.8
# Proximite minimale des docstrings pour classer une paire en **forte**.
# Mesure sur le corpus : Arrow 0.29 et Sen 0.20 (les deux vrais doublons),
# le meilleur faux positif 0.11.
DEFAULT_DOC_SIM = 0.15


@dataclass
class Declaration:
    """Une declaration de theoreme (ou lemme) avec son contexte."""

    path: str
    lake: str
    name: str
    kind: str
    line: int
    statement: str = ""
    doc: str = ""
    name_tokens: frozenset = field(default_factory=frozenset)
    doc_tokens: frozenset = field(default_factory=frozenset)
    doc_words: frozenset = field(default_factory=frozenset)
    stmt_tokens: frozenset = field(default_factory=frozenset)
    signature: frozenset = field(default_factory=frozenset)

    @property
    def short(self) -> str:
        return "%s:%d" % (self.path, self.line)


def _git(*args: str) -> str:
    try:
        r = subprocess.run(
            ["git", "-C", str(REPO_ROOT), *args],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
    except OSError:
        return ""
    if r.returncode != 0:
        return ""
    return r.stdout


def git_paths(*patterns: str) -> list[str]:
    """Les chemins git correspondant aux motifs (population mesuree)."""
    out = _git("ls-files", "-z", *patterns)
    return [p for p in out.split("\0") if p]


def _git_opt(*args: str) -> str | None:
    """Comme `_git`, mais distingue l'echec de la sortie vide.

    `_git` rend `""` aussi bien quand la commande echoue que quand elle ne rend
    rien. Pour une garde de derive, confondre les deux ferait passer une
    reference illisible pour une reference vide : tous les fichiers mesures
    seraient alors declares « absents de la reference ». La sonde rend donc
    `None` sur echec, et l'appelant traite ce cas comme NON MESURE.
    """
    try:
        r = subprocess.run(
            ["git", "-C", str(REPO_ROOT), *args],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
    except OSError:
        return None
    if r.returncode != 0:
        return None
    return r.stdout


DEFAULT_UPSTREAM = "origin/main"


def drift_between(measured: list[str], upstream: list[str]) -> list[str]:
    """Chemins MESURES absents de la reference, tries.

    Fonction pure (ni disque ni git) : c'est elle que le test exerce. La derive
    d'arbre est un ensemble, pas un compte -- deux arbres differents peuvent
    mesurer le meme nombre de fichiers.
    """
    return sorted(set(measured) - set(upstream))


def measured_lean_paths() -> list[str]:
    """Les `.lean` que `collect()` va reellement mesurer (meme filtre)."""
    return [
        p
        for p in git_paths("*.lean")
        if not any(marker in p for marker in EXCLUDED_MARKERS)
    ]


def upstream_lean_paths(ref: str = DEFAULT_UPSTREAM) -> list[str] | None:
    """Les `.lean` de la reference distante, ou `None` si elle est illisible.

    `git ls-tree` lit l'ARBRE de la reference, la ou `git ls-files` lit l'INDEX
    de l'arbre courant ; c'est cette difference qui rend la derive mesurable.

    Le filtrage se fait **en Python, pas par pathspec**. Mesure du 09/11/2026
    sur git 2.51.0.windows.1 : `git ls-tree -r <ref> -- '*.lean'` rend **0**
    fichier alors que l'arbre en porte 924, et `-- 'CLAUDE*'` rend 0 la ou
    `-- 'CLAUDE.md'` en rend 1 -- les pathspecs a wildcard sont **inertes** sur
    cet `ls-tree` (un chemin litteral, lui, fonctionne). Un filtre `*.lean`
    pose ici aurait donc declare la totalite de la population « absente de la
    reference », c'est-a-dire accuse l'arbre a tort, en silence. On liste tout
    et on filtre soi-meme : aucun wildcard ne peut plus mentir par vide.

    Une liste **vide** est traitee comme NON MESUREE (`None`) : un depot qui
    porte des fichiers `.lean` mesures n'a pas zero fichier `.lean` en amont,
    donc le vide dit l'echec de la sonde, pas une reference vide.
    """
    out = _git_opt("ls-tree", "-r", "--name-only", ref)
    if out is None:
        return None
    paths = [p for p in out.splitlines() if p]
    if not paths:
        return None
    return [p for p in paths if p.endswith(".lean")]


def tree_drift(ref: str = DEFAULT_UPSTREAM) -> tuple[int, list[str]] | None:
    """(nombre de mesures, chemins absents de la reference), ou `None`.

    `None` = reference illisible : la fraicheur n'est pas prouvable, ce qui
    n'est PAS la meme chose qu'une absence de derive.
    """
    measured = measured_lean_paths()
    upstream = upstream_lean_paths(ref)
    if upstream is None:
        return None
    return len(measured), drift_between(measured, upstream)


def warn_if_stale(ref: str = DEFAULT_UPSTREAM, require_fresh: bool = False) -> int:
    """Avertit sur STDERR quand l'arbre mesure derive de la reference.

    Ecrit sur `stderr` et jamais sur `stdout` : la page commitee est comparee
    octet a octet par `--check`, et coupler la garde de derive a cette page
    ferait rougir le gate sur un simple retard d'arbre local.

    Rend 0 en temps normal, 1 seulement sous `--require-fresh` : la garde est
    informative par defaut, bloquante sur demande explicite.
    """
    drift = tree_drift(ref)
    if drift is None:
        print(
            "AVERTISSEMENT : reference `%s` illisible (clone superficiel ou ref"
            " absente) ; la fraicheur de l'arbre n'est pas prouvable." % ref,
            file=sys.stderr,
        )
        return 1 if require_fresh else 0
    total, absent = drift
    if not absent:
        return 0
    print(
        "AVERTISSEMENT : %d fichier(s) `.lean` mesures ici sont ABSENTS de `%s`"
        " (sur %d mesures). L'arbre de travail est en retard sur la reference :"
        " la mesure porte sur des fichiers que la reference n'a plus (lacs"
        " fantomes compris). Relancer depuis un arbre a jour avant de conclure."
        % (len(absent), ref, total),
        file=sys.stderr,
    )
    for path in absent[:5]:
        print("  absent de %s : %s" % (ref, path), file=sys.stderr)
    if len(absent) > 5:
        print("  ... et %d autre(s)" % (len(absent) - 5), file=sys.stderr)
    return 1 if require_fresh else 0


def _deaccent(text: str) -> str:
    return "".join(
        c for c in unicodedata.normalize("NFKD", text) if not unicodedata.combining(c)
    )


def _words(text: str) -> list[str]:
    return re.findall(r"[A-Za-z]+", _deaccent(text).lower())


def raw_name_tokens(name: str) -> frozenset:
    """Tokens du nom, namespace retire, camelCase decoupe.

    Le namespace est retire (`Arrow.arrow` -> `arrow`) ; aucune token n'est
    ecarte ici : c'est la **contenance** (et non le nom nu) qui rapproche
    `arrow` de `arrow_impossibility`.
    """
    simple = name.split(".")[-1]
    parts = re.findall(r"[A-Z]+(?![a-z])|[A-Z][a-z0-9]*|[a-z0-9]+", simple)
    return frozenset(p.lower() for p in parts if p)


def doc_tokens(doc: str) -> frozenset:
    """Mots-cles de la docstring (mots de 5 lettres ou plus, hors stop-words)."""
    return frozenset(w for w in _words(doc) if len(w) >= 5 and w not in STOPWORDS)


def doc_words(doc: str) -> frozenset:
    """Tous les mots de la docstring, quelle que soit leur longueur.

    Distinct de `doc_tokens` : celui-ci sert a la similarite (les mots de
    moins de 5 lettres sont trop generiques pour comparer deux textes), celui
    la sert a la **signature**, ou l'on cherche precisement un terme court
    comme `sen` dans la docstring d'un theorem called `sen_impossibility`.
    """
    return frozenset(_words(doc))


def stmt_tokens(statement: str) -> frozenset:
    """Tokens de l'enonce : identifiants et operateurs, hors ponctuation."""
    return frozenset(w for w in _words(statement) if len(w) >= 2 and w not in STOPWORDS)


def jaccard(a: frozenset, b: frozenset) -> float:
    if not a or not b:
        return 0.0
    inter = len(a & b)
    if not inter:
        return 0.0
    return inter / float(len(a | b))


def containment(a: frozenset, b: frozenset) -> float:
    """Part du plus petit ensemble couverte par l'autre.

    C'est la mesure qui reconnait `arrow` dans `arrow_impossibility` : le
    Jaccard y vaut 0,5, la contenance 1.
    """
    if not a or not b:
        return 0.0
    return len(a & b) / float(min(len(a), len(b)))


def _doc_blocks(lines: list[str]) -> list[tuple[int, str]]:
    """Blocs `/-- ... -/` : (ligne de fin, texte)."""
    blocks: list[tuple[int, str]] = []
    i = 0
    while i < len(lines):
        if DOC_OPEN in lines[i]:
            j = i
            buf = [lines[i]]
            while j < len(lines) and DOC_CLOSE not in lines[j]:
                j += 1
                buf.append(lines[j])
            text = "\n".join(buf)
            text = text.replace(DOC_OPEN, " ", 1)
            text = text.replace(DOC_CLOSE, " ", 1)
            blocks.append((j, text))
            i = j + 1
            continue
        i += 1
    return blocks


_ATTRIBUTE_LINE = re.compile(r"^@\[[^\]]*\]$")
_MODIFIER_ONLY = re.compile(
    r"^(?:private|protected|noncomputable|local|scoped|partial|unsafe|nonrec)$"
)


def _is_transparent(line: str) -> bool:
    """Une ligne intercalee n'emporte-t-elle aucune declaration ?

    Transparente, et RIEN D'AUTRE : une ligne vide, un attribut **seul** sur
    sa ligne (`@[simp]`), un commentaire, une `set_option`, ou un
    modificateur seul (`noncomputable`).

    La reponse est volontairement **stricte** : une ligne qui declare ou
    definit quoi que ce soit -- meme precedee d'un attribut
    (`@[reducible] def scaleW ...`), meme un champ de classe
    (`amalgamates : forall ...`) -- n'est PAS transparente. Rattacher une
    docstring par-dessus une commande intermediaire ferait porter a une
    declaration le texte d'une autre : c'est une faute de l'organe, pire que
    la perte qu'on pretend corriger. Mesure du 2026-11-02 : la regle stricte
    perd 14 docstrings sur la population, la regle tolerante en regagne 14 et
    n'en deplace aucune.
    """
    s = line.strip()
    if not s:
        return True
    if s.startswith("--") or s.startswith("set_option "):
        return True
    if _ATTRIBUTE_LINE.match(s):
        return True
    return bool(_MODIFIER_ONLY.match(s))


def parse_file(path: str, text: str, lake: str) -> list[Declaration]:
    """Les declarations d'un fichier Lean, avec leur docstring et leur enonce."""
    lines = text.splitlines()
    blocks = _doc_blocks(lines)
    decls: list[Declaration] = []
    i = 0
    while i < len(lines):
        m = DECL_RE.match(lines[i])
        if not m:
            i += 1
            continue
        # L'enonce s'acheve au premier `:=` ; le corps de la preuve suit.
        buf = [lines[i][m.end():]]
        j = i
        while j + 1 < len(lines) and ":=" not in "\n".join(buf):
            j += 1
            buf.append(lines[j])
        statement = "\n".join(buf).split(":=", 1)[0]
        # La docstring : le bloc `/--` qui se termine le plus tot avant la
        # declaration, sans ligne **non transparente** entre les deux.
        #
        # La regle stricte (lignes vides seulement) perdait la docstring des
        # declarations precedees d'un attribut (`@[simp]`), d'un commentaire ou
        # d'un modificateur : mesure du 2026-11-02 sur le corpus, 14
        # declarations sur 4 629 (douze derriere un `@[simp]`, une derriere un
        # autre attribut, une derriere des commentaires). Les deux populations
        # -- stricte et toleree -- comptent les memes 4 629 declarations : la
        # regle ne change que l'attachement, pas l'index. Une declaration sans
        # docstring sort de l'index de signature, donc de TOUTE paire possible,
        # sans trace.
        doc = ""
        best = -1
        for end_line, block in blocks:
            if end_line < i and all(
                _is_transparent(lines[k]) for k in range(end_line + 1, i)
            ):
                if end_line > best:
                    best = end_line
                    doc = block
        decl = Declaration(
            path=path,
            lake=lake,
            name=m.group("name"),
            kind=m.group("kind"),
            line=i + 1,
            statement=statement.strip(),
            doc=doc.strip(),
        )
        decl.name_tokens = raw_name_tokens(decl.name)
        decl.doc_tokens = doc_tokens(decl.doc)
        decl.doc_words = doc_words(decl.doc)
        decl.stmt_tokens = stmt_tokens(decl.statement)
        # La signature : les tokens du nom que la docstring elle-meme cite
        # (en un mot entier -- `sen` doit etre reconnu dans `sen`).
        decl.signature = frozenset(t for t in decl.name_tokens if t in decl.doc_words)
        decls.append(decl)
        i = j + 1
    return decls


def lake_dirs() -> list[str]:
    """Les dossiers de lac, du plus long au plus court (attribution par contient)."""
    dirs = []
    for lakefile in git_paths("*lakefile.lean", "*lakefile.toml"):
        dirs.append(lakefile.rsplit("/", 1)[0] if "/" in lakefile else ".")
    return sorted(set(dirs), key=len, reverse=True)


def owner(path: str, dirs: list[str]) -> str:
    """Le lac qui CONTIENT le fichier (pas le dossier immediat)."""
    for d in dirs:
        if path.startswith(d + "/"):
            return d
    return "(hors lac)"


def collect(include_mirrors: bool = False) -> list[Declaration]:
    """Toutes les declarations du depot (population mesuree, hors vendored).

    Les freres `_en` sont **exclus par defaut** : ils republishent le contenu
    FR (convention i18n #4980), les comparer transformerait chaque paire en
    deux paires identiques.
    """
    dirs = lake_dirs()
    decls: list[Declaration] = []
    for path in git_paths("*.lean"):
        if any(marker in path for marker in EXCLUDED_MARKERS):
            continue
        if not include_mirrors and path.endswith("_en.lean"):
            continue
        full = REPO_ROOT / path
        try:
            text = full.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        decls.extend(parse_file(path, text, owner(path, dirs)))
    return decls


def document_frequency(decls: list[Declaration]) -> collections.Counter:
    """Combien de declarations citent chaque mot-cle de docstring."""
    df: collections.Counter = collections.Counter()
    for d in decls:
        df.update(d.doc_tokens)
    return df


def name_frequency(decls: list[Declaration]) -> collections.Counter:
    """Combien de declarations portent chaque token dans leur **nom**.

    C'est la mesure qui distingue un terme discriminant (`arrow`, `sen` : deux
    ou trois occurrences dans tout le depot) d'un terme generique (`card`,
    `trans`, `wf` : des dizaines). Sans elle, la contenance des noms est
    Trompeuse : `card` est « contenu » dans `enumIndex_lt_card`, mais ces deux
    lemmes ne prouvent pas le meme resultat.
    """
    ndf: collections.Counter = collections.Counter()
    for d in decls:
        ndf.update(d.name_tokens)
    return ndf


def _pair_record(a: Declaration, b: Declaration) -> dict:
    doc_sim = jaccard(a.doc_tokens, b.doc_tokens)
    return {
        "score": round(
            max(
                containment(a.name_tokens, b.name_tokens),
                0.5
                * (
                    jaccard(a.doc_tokens, b.doc_tokens)
                    + jaccard(a.stmt_tokens, b.stmt_tokens)
                ),
            ),
            3,
        ),
        "name": a.name,
        "other_name": b.name,
        "a": {
            "path": a.path,
            "line": a.line,
            "lake": a.lake,
            "kind": a.kind,
        },
        "b": {
            "path": b.path,
            "line": b.line,
            "lake": b.lake,
            "kind": b.kind,
        },
        "name_containment": round(containment(a.name_tokens, b.name_tokens), 3),
        "doc_sim": round(jaccard(a.doc_tokens, b.doc_tokens), 3),
        "stmt_sim": round(jaccard(a.stmt_tokens, b.stmt_tokens), 3),
        "shared_terms": sorted(a.signature & b.signature),
    }


def find_duplicates(
    decls: list[Declaration],
    df_max: int = DEFAULT_DF_MAX,
    min_containment: float = DEFAULT_CONTAINMENT,
    df: collections.Counter | None = None,
    ndf: collections.Counter | None = None,
    doc_sim_min: float = DEFAULT_DOC_SIM,
) -> list[dict]:
    """Les paires de declarations de lacs differents qui enoncent le meme resultat.

    Une paire est retenue quand :

    1. les **noms** se recouvrent (`arrow` dans `arrow_impossibility`) sur des
       tokens d'au moins 3 caracteres -- en dessous, `b` ou `le` sont
       contenus dans n'importe quel nom et la mesure ne prouve plus rien ;
    2. un token de nom **discriminant** est commun aux deux : il est porte
       par au plus `df_max` declarations du depot (`arrow`, `sen`), et les
       deux docstrings le mentionnent.

    Les paires internes a un meme lac sont exclues : un lac peut reecrire un
    resultat dans son propre vocabulaire sans que ce soit un doublon.
    """
    if df is None:
        df = document_frequency(decls)
    if ndf is None:
        ndf = name_frequency(decls)
    index: dict[str, list[Declaration]] = collections.defaultdict(list)
    for d in decls:
        for token in d.name_tokens:
            if len(token) >= 3:
                index[token].append(d)

    seen: set[tuple] = set()
    pairs: list[dict] = []
    for token, bucket in index.items():
        for i, a in enumerate(bucket):
            for b in bucket[i + 1:]:
                if a.lake == b.lake or a.path == b.path:
                    continue
                key = (a.path, a.line, b.path, b.line)
                if key in seen:
                    continue
                if containment(a.name_tokens, b.name_tokens) < min_containment:
                    continue
                shared = a.name_tokens & b.name_tokens
                rare = [
                    t
                    for t in shared
                    if ndf.get(t, 0) <= df_max and t in a.signature and t in b.signature
                ]
                if not rare:
                    continue
                seen.add(key)
                record = _pair_record(a, b)
                record["rare_terms"] = sorted(rare)
                # Deux niveaux : une paire **forte** a des docstrings
                # proches (les deux declarations decrivent le meme resultat) ;
                # une paire **faible** ne partage qu'un terme de nom rare.
                record["strength"] = (
                    "forte" if record["doc_sim"] >= doc_sim_min else "faible"
                )
                pairs.append(record)
    pairs.sort(
        key=lambda p: (
            0 if p["strength"] == "forte" else 1,
            -p["score"],
            p["a"]["path"],
            p["b"]["path"],
        )
    )
    return pairs


def render_section(pairs: list[dict], df_max: int, min_containment: float) -> list[str]:
    """La section markdown de la page (generee, jamais ecrite a la main)."""
    strong = [p for p in pairs if p["strength"] == "forte"]
    weak = [p for p in pairs if p["strength"] != "forte"]
    lines: list[str] = []
    lines.append("## Theoremes en double entre lacs")
    lines.append("")
    lines.append(
        "Table generee par `scripts/lean/lean_theorem_duplicates.py`."
        " Une **paire**"
        " represente deux declarations de **lacs differents** dont les noms se"
        " recouvrent (contenance >= %.2f sur des tokens d'au moins trois"
        " caracteres) et dont un **terme discriminant** du nom est commun aux"
        " deux docstrings -- terme porte par au plus %d declarations dans le"
        " depot, ce qui ecarte les lemmes generiques (`card`, `trans`, `wf`)."
        % (min_containment, df_max)
    )
    lines.append("")
    lines.append(
        "Ce tableau est un **signal**, pas un verdict : retirer, fusionner ou"
        " deplacer une preuve est une decision humaine. Les freres `_en`"
        " (convention i18n) et les paires internes a un meme lac sont exclus"
        " par construction."
    )
    lines.append("")
    lines.append("### Paires fortes — docstrings proches")
    lines.append("")
    if not strong:
        lines.append("Aucune paire forte.")
        lines.append("")
    else:
        lines.append("| Nom A | Lac A | Nom B | Lac B | Docstring | Termes |")
        lines.append("|---|---|---|---|---|---|")
        for p in strong:
            lines.append(
                "| `%s` | `%s` | `%s` | `%s` | %.2f | %s |"
                % (
                    p["name"],
                    p["a"]["lake"],
                    p["other_name"],
                    p["b"]["lake"],
                    p["doc_sim"],
                    ", ".join("`%s`" % t for t in p["shared_terms"]) or "-",
                )
            )
        lines.append("")
    lines.append("### Paires faibles — terme de nom commun, docstrings eloignees")
    lines.append("")
    if not weak:
        lines.append("Aucune paire faible.")
        lines.append("")
    else:
        lines.append(
            "Ces paires partagent un terme rare mais ne decrivent pas"
            " clairement le meme resultat ; elles sont listees pour memoire, pas"
            " pour etre traitees."
        )
        lines.append("")
        lines.append("| Nom A | Lac A | Nom B | Lac B | Docstring | Termes |")
        lines.append("|---|---|---|---|---|---|")
        for p in weak:
            lines.append(
                "| `%s` | `%s` | `%s` | `%s` | %.2f | %s |"
                % (
                    p["name"],
                    p["a"]["lake"],
                    p["other_name"],
                    p["b"]["lake"],
                    p["doc_sim"],
                    ", ".join("`%s`" % t for t in p["shared_terms"]) or "-",
                )
            )
        lines.append("")
    lines.append("Detail des paires (fichier et declaration) :")
    lines.append("")
    for p in pairs:
        lines.append(
            "- **%.2f** -- `%s` (%s) et `%s` (%s) -- nom %.2f /"
            " docstring %.2f / enonce %.2f / termes %s"
            % (
                p["score"],
                p["name"],
                p["a"]["path"],
                p["other_name"],
                p["b"]["path"],
                p["name_containment"],
                p["doc_sim"],
                p["stmt_sim"],
                ", ".join(p["shared_terms"]) or "-",
            )
        )
    lines.append("")
    return lines


def render_page(pairs: list[dict], df_max: int, min_containment: float) -> str:
    """La page complete (generee, jamais ecrite a la main)."""
    lines: list[str] = []
    lines.append("# Theoremes en double entre lacs Lean")
    lines.append("")
    lines.append(
        "Page regeneree par `scripts/lean/%s`"
        " (`--write` pour la reecrire, `--check` pour verifier qu'elle suit"
        " l'arbre). Ne pas l'editer a la main." % SCRIPT_NAME
    )
    lines.append("")
    lines.extend(render_section(pairs, df_max, min_containment))
    lines.append("## Methode")
    lines.append("")
    lines.append(
        "1. **Population** : toutes les declarations `theorem` / `lemma` des"
        " fichiers `.lean` du depot, hors Lean vendu (`.lake/packages`),"
        " hors `_peters/` et hors fixtures de reference. Les freres `_en`"
        " (convention i18n #4980) sont exclus : ils republient le contenu FR."
    )
    lines.append(
        "2. **Rapprochement** : les declarations sont indexees par les tokens"
        " de leur **nom** (namespace retire, camelCase decoupe, tokens de trois"
        " caracteres ou plus). Deux declarations ne sont comparees que si un"
        " token de nom est commun."
    )
    lines.append(
        "3. **Filtre de rarete** : le token commun doit etre porte par au"
        " plus %d declarations dans le depot. C'est ce qui ecarte les lemmes"
        " generiques (`card`, `trans`, `wf`, `le`), dont le nom se recoupe"
        " partout sans que les lemmes ne prouvent le meme resultat." % df_max
    )
    lines.append(
        "4. **Filtre de contenu** : le token doit figurer dans la docstring"
        " des **deux** declarations, et les deux docstrings doivent etre"
        " proches (Jaccard >= 0.15) pour classer la paire en **forte**."
    )
    lines.append(
        "5. **Perimetre** : une paire porte sur deux declarations de **lacs"
        " differents**. A l'interieur d'un lac, un resultat reecrit dans le"
        " vocabulaire du lac n'est pas un doublon."
    )
    lines.append("")
    lines.append(
        "**Controle positif** : la paire Arrow"
        " (`MyIA.AI.Notebooks/GameTheory/SocialChoice/social_choice_core_lean/SocialChoice/Arrow.lean`"
        " contre `MyIA.AI.Notebooks/GameTheory/lean_game_defs/SocialChoice.lean`)"
        " et la paire Sen"
        " (`.../social_choice_core_lean/SocialChoice/Sen.lean` contre le meme fichier)"
        " doivent apparaitre parmi les paires fortes -- ce sont les deux"
        " doublons que #23097 avait conclut absents en comparant les noms de"
        " modules. Le test qui verifie ce point est"
        " `scripts/lean/tests/test_lean_theorem_duplicates.py`."
        " (Le temoin suit le lac : depuis la descente #24183, Arrow et Sen"
        " vivent dans le lac autonome `social_choice_core_lean`.)"
    )
    lines.append("")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="sortie machine")
    parser.add_argument("--df-max", type=int, default=DEFAULT_DF_MAX)
    parser.add_argument("--min-containment", type=float, default=DEFAULT_CONTAINMENT)
    parser.add_argument("--include-mirrors", action="store_true")
    parser.add_argument(
        "--write", action="store_true", help="regenere la page de reference"
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="echoue (1) quand la page regeneree differe de l'arbre",
    )
    parser.add_argument(
        "--ref",
        default=DEFAULT_UPSTREAM,
        help="reference de comparaison pour la garde de derive (defaut : %s)"
        % DEFAULT_UPSTREAM,
    )
    parser.add_argument(
        "--require-fresh",
        action="store_true",
        help="echoue (1) quand l'arbre mesure derive de --ref, ou quand --ref"
        " est illisible (fraicheur non prouvable)",
    )
    args = parser.parse_args(argv)

    # La garde passe AVANT la collecte : elle coute un `ls-tree`, et un arbre
    # en retard fausse le resultat qu'on s'apprete a produire.
    stale = warn_if_stale(args.ref, args.require_fresh)
    if stale:
        return stale

    decls = collect(include_mirrors=args.include_mirrors)
    df = document_frequency(decls)
    ndf = name_frequency(decls)
    pairs = find_duplicates(
        decls, args.df_max, args.min_containment, df=df, ndf=ndf
    )
    if args.json:
        print(
            json.dumps(
                {
                    "df_max": args.df_max,
                    "min_containment": args.min_containment,
                    "declarations": len(decls),
                    "pairs": pairs,
                },
                indent=1,
                ensure_ascii=False,
            )
        )
        return 0

    if args.write or args.check:
        page = render_page(pairs, args.df_max, args.min_containment)
        if args.write:
            PAGE.parent.mkdir(parents=True, exist_ok=True)
            PAGE.write_text(page, encoding="utf-8", newline="\n")
            print("ecrit : %s" % PAGE)
        # `--check` est evalue MEME avec `--write`. Avant, le chemin `write`
        # sortait en premier : `--write --check` rendait 0 sans jamais
        # comparer -- un faux feu vert. La comparaison porte desormais sur le
        # fichier reellement present sur le disque, donc elle verifie aussi
        # que l'ecriture a bien atterri.
        current = ""
        if PAGE.is_file():
            current = PAGE.read_text(encoding="utf-8")
        if current != page:
            print(
                "DIVERGENCE : %s ne correspond plus a l'arbre ;"
                " relancer avec --write." % PAGE
            )
            return 1
        if args.check:
            print("OK : %s suit l'arbre." % PAGE)
        return 0

    for line in render_section(pairs, args.df_max, args.min_containment):
        print(line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
