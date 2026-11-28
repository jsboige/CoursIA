#!/usr/bin/env python3
r"""Invariant d'inventaire des regles du harnais (#15204).

Classe de defaut mesuree : une regle **path-gatee** (donc chargee seulement
quand la session touche ses fichiers) qui n'est citee **nulle part** dans le
`CLAUDE.md` devient invisible pour tout agent qui lit le harnais ; et une regle
presente sur disque mais absente de l'inventaire de
`docs/reference/claude-code-config.md` n'est decouvrable par personne.

Instance fondatrice (mesure du 2026-11-23, lane `myia-po-2028:CoursIA`, sur
l'issue #15204) : `lean-lakes-doctrine` (ajoutee par #27597) etait path-gatee
et **citee nulle part** dans le `CLAUDE.md` ; et `lean-lakes-doctrine` comme
`feedback_comment_action_link` manquaient a la table d'inventaire. Les deux
occurrences ont ete corrigees depuis ; **l'invariant, lui, n'etait garde par
aucun organe** -- un defaut de la meme classe serait revenu en silence.

L'organe rend la classe observable, sans dependre de la vigilance :

    ON_DISK_NOT_CITED    regle presente sur disque, absente de l'inventaire
                         `docs/reference/claude-code-config.md`
    GATED_NOT_ANNOUNCED  regle path-gatee absente du bloc "Regles modulaires"
                         du `CLAUDE.md` (la porte la plus grave : une regle
                         chargee conditionnellement et jamais annoncee)
    CITED_NOT_ON_DISK    entree d'inventaire pointant vers une regle absente
                         du dossier `.claude/rules/`

Trois modes de verdict :

    --base <ref>   DELTA : seul un finding **present sur la tete et absent de
                   la base** est rouge. Une PR ne herite donc jamais du rouge
                   de `main` : elle n'est rouge que si elle introduce
                   elle-meme une incoherence. C'est ce qui rend le garde
                   utilisable sur un depot dont la base porte une dette.
    (sans --base)  ETAT : l'integrite de l'arbre entier, tel qu'il est sur
                   disque. C'est le mode du diagnostic local et du test
                   d'integrite du depot vivant.

Codes de retour :

    0   aucune incoherence (delta : aucune *nouvelle*)
    1   au moins une incoherence
    2   incident d'entree (git illisible, base introuvable, fichier manquant)
        -- le verdict est INCONNU, pas un quitus

Perimetres et limites assumees :

- l'inventaire lu est la **table des regles** de
  `docs/reference/claude-code-config.md` (section `## Rules`), pas l'ensemble
  des jetons backtiques du document : un nom cite en prose historique
  (`secrets-roosync-policy`, regle fusionnee) n'est pas une entree
  d'inventaire ;
- la citation dans le `CLAUDE.md` est cherchee dans le **bloc "Regles
  modulaires"** (`CLAUDE.md` §C), la ou le critere 4/5 de #15204 l'exige ;
- une regle path-gatee citee **une seule fois** dans ce bloc est deemee
  annoncee : le critere est "une ligne de renvoi", pas un resume ;
- une regle **non** path-gatee n'a pas a etre citee dans le `CLAUDE.md` (elle
  est deauto-chargee) : seule l'inventaire la concerne ;
- le verdict est **fail-closed sur les trois sens**, jamais fail-open.

Usage :
    python scripts/ci/check_rule_inventory.py
    python scripts/ci/check_rule_inventory.py --json
    python scripts/ci/check_rule_inventory.py --base origin/main
    python scripts/ci/check_rule_inventory.py --repo-root <racine du depot>
    python scripts/ci/check_rule_inventory.py --self
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

RULES_DIR = Path(".claude/rules")
INVENTORY_DOC = Path("docs/reference/claude-code-config.md")
CLAUDE_MD = Path("CLAUDE.md")

#: Forme d'un nom de regle : minuscules, chiffres, tirets, soulignes.
RULE_NAME_RE = re.compile(r"^[a-z0-9][a-z0-9_-]*$")

#: Un jeton backtique dans la premiere colonne d'une ligne d'inventaire.
CELL_TOKEN_RE = re.compile(r"`([^`]+)`")

#: Codes de finding, dans l'ordre d'affichage.
CODES = ("ON_DISK_NOT_CITED", "GATED_NOT_ANNOUNCED", "CITED_NOT_ON_DISK")


# --------------------------------------------------------------------------
# Lecture des surfaces
# --------------------------------------------------------------------------

def _rule_names_in_cell(cell: str) -> list[str]:
    """Noms de regles cites dans une cellule d'inventaire.

    Une cellule peut porter plusieurs regles separees par un point median
    (`` `a` · `b` ``) : chacune compte.
    """
    return [t for t in CELL_TOKEN_RE.findall(cell) if RULE_NAME_RE.match(t)]


def parse_frontmatter_paths(text: str) -> bool:
    """Vrai si la regle porte une clause `paths:` (donc est path-gatee).

    Le frontmatter YAML est delimite par deux lignes `---` en tete de fichier.
    La presence de la **cle** `paths:` suffit : sa valeur (glob ou liste) ne
    change pas le verdict d'inventaire.
    """
    lines = text.splitlines()
    if not lines or lines[0].strip() != "---":
        return False
    for line in lines[1:]:
        if line.strip() == "---":
            break
        if re.match(r"^paths\s*:", line.strip()):
            return True
    return False


def inventory_names(markdown: str) -> set[str]:
    """Noms de regles de la table d'inventaire de `claude-code-config.md`.

    La table est celle de la section `## Rules` : son en-tete porte la
    premiere colonne `| Regle |`. Les lignes de la table sont les lignes
    demarrant par `|` ; la premiere cellule porte les noms.
    """
    lines = markdown.splitlines()
    debut = None
    for i, line in enumerate(lines):
        if line.startswith("## Rules"):
            debut = i
            break
    if debut is None:
        return set()
    names: set[str] = set()
    entete = False
    for line in lines[debut + 1:]:
        if not line.startswith("|"):
            if entete:
                break  # fin de la table
            continue
        if not entete:
            # ligne d'en-tete puis separateur, puis les lignes de la table
            if re.match(r"^\|\s*R[eè]gle", line.strip()):
                entete = True
            continue
        cells = line.split("|")
        if len(cells) < 2:
            continue
        names.update(_rule_names_in_cell(cells[1]))
    return names


def announced_block(claude_md: str) -> str:
    """Bloc "Regles modulaires" du `CLAUDE.md` (la ou le critere 4/5 exige).

    Le bloc commence au titre `Regles modulaires` et s'acheve au titre de
    niveau 2 suivant. Faute de bloc identifiable, le document entier est
    rendu : la surface la plus large, donc la plus permissive -- le sens
    GATED_NOT_ANNOUNCED ne peut pas produire de faux positif.
    """
    lines = claude_md.splitlines()
    for i, line in enumerate(lines):
        if re.search(r"R[eè]gles modulaires", line):
            block = []
            for suite in lines[i + 1:]:
                if suite.startswith("## "):
                    break
                block.append(suite)
            if block:
                return "\n".join(block)
    return claude_md


def cited(text: str, name: str) -> bool:
    """Le nom de la regle est-il cite dans le texte ?

    La citation est recherchee comme mot entier : un mot voisin
    (`lean-lakes-doctrine-extra`) ne vaut pas citation de
    `lean-lakes-doctrine`.
    """
    motif = re.compile(r"(?<![A-Za-z0-9_-])" + re.escape(name) + r"(?![A-Za-z0-9_-])")
    return motif.search(text) is not None


# --------------------------------------------------------------------------
# Etat : regles sur disque / citees / annoncees
# --------------------------------------------------------------------------

def etat(rules: dict[str, bool], cites: set[str], bloc: str) -> dict:
    """Construit l'etat d'inventaire a partir des trois surfaces.

    `rules` associe chaque nom de regle a son caractere path-gate ;
    `cites` est le jeu de noms de la table d'inventaire ; `bloc` est le bloc
    "Regles modulaires" du `CLAUDE.md`.
    """
    sur_disque = set(rules)
    gatees = {name for name, gated in rules.items() if gated}
    return {
        "rules_sur_disque": len(sur_disque),
        "rules_path_gatees": len(gatees),
        "entrees_inventaire": len(cites),
        "on_disk_not_cited": sorted(n for n in sur_disque if n not in cites),
        "gated_not_announced": sorted(n for n in gatees if not cited(bloc, n)),
        "cited_not_on_disk": sorted(n for n in cites if n not in sur_disque),
    }


def findings_of(resultat: dict) -> list[tuple[str, str]]:
    """Findings d'un etat, sous forme de couples (code, regle)."""
    out: list[tuple[str, str]] = []
    for code, cle in zip(CODES, ("on_disk_not_cited", "gated_not_announced",
                                 "cited_not_on_disk")):
        for name in resultat[cle]:
            out.append((code, name))
    return out


def _etat_vers_resultat(state: dict) -> dict:
    """Etat -> resultat serialisable (memes cles que `etat` + findings)."""
    resultat = {
        "rules_sur_disque": state["rules_sur_disque"],
        "rules_path_gatees": state["rules_path_gatees"],
        "entrees_inventaire": state["entrees_inventaire"],
        "on_disk_not_cited": list(state["on_disk_not_cited"]),
        "gated_not_announced": list(state["gated_not_announced"]),
        "cited_not_on_disk": list(state["cited_not_on_disk"]),
    }
    resultat["findings"] = [
        {"code": code, "regle": name} for code, name in findings_of(state)
    ]
    resultat["verdict"] = "OVER" if resultat["findings"] else "OK"
    return resultat


# --------------------------------------------------------------------------
# Lecture de l'etat sur disque (tete)
# --------------------------------------------------------------------------

def collect(repo_root: Path) -> dict:
    """Mesure l'invariant sur l'arbre donne (mode ETAT).

    Retourne les trois listes de findings et les compteurs de surface.
    """
    rules_dir = repo_root / RULES_DIR
    doc = repo_root / INVENTORY_DOC
    claude = repo_root / CLAUDE_MD

    for path, label in ((rules_dir, RULES_DIR), (doc, INVENTORY_DOC),
                        (claude, CLAUDE_MD)):
        if not path.exists():
            raise FileNotFoundError(f"{label} introuvable sous {repo_root}")

    rules: dict[str, bool] = {}
    for path in sorted(rules_dir.glob("*.md")):
        rules[path.stem] = parse_frontmatter_paths(
            path.read_text(encoding="utf-8"))

    cites = inventory_names(doc.read_text(encoding="utf-8"))
    bloc = announced_block(claude.read_text(encoding="utf-8"))
    return etat(rules, cites, bloc)


# --------------------------------------------------------------------------
# Lecture de l'etat dans un commit (base)
# --------------------------------------------------------------------------

def _git(root: Path, args: list[str]) -> tuple[int, str]:
    """Execute une commande git dans `root`. Retourne (rc, sortie)."""
    proc = subprocess.run(
        ["git", *args], cwd=str(root), capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    return proc.returncode, proc.stdout


def _git_blobs(root: Path, ref: str, paths: list[str]) -> dict[str, str]:
    """Contenu des fichiers `paths` a la revision `ref`, en un seul `git`.

    `git cat-file --batch` lit tous les blobs en un processus : une commande
    par fichier serait 38 processus pour une regle, un depot, un cycle.

    Le flux est lu en **BINAIRE** : git annonce les tailles en OCTETS, et
    decouper une chaine decodee decale le curseur des que le fichier contient
    un caractere multi-octets (les docs du depot sont accentues).

    Retourne un dictionnaire chemin -> contenu. Un blob absent de la revision
    est absent du dictionnaire (la regle n'existait pas a la base).
    """
    if not paths:
        return {}
    requetes = "".join(f"{ref}:{p}\n" for p in paths)
    proc = subprocess.run(
        ["git", "cat-file", "--batch"], cwd=str(root),
        input=requetes.encode("utf-8"), capture_output=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"git cat-file en echec : {proc.stderr.decode('utf-8', 'replace').strip()}")
    out: dict[str, str] = {}
    for path, content in zip(paths, _split_batch(proc.stdout, len(paths))):
        if content is not None:
            out[path] = content
    return out


def _split_batch(stdout: bytes, expected: int) -> list[str | None]:
    """Decoupe la sortie de `git cat-file --batch` en contenus de blobs.

    Format par entree : `<sha> <type> <taille>\\n<contenu>\\n`. Un objet
    absent produit une ligne d'en-tete SANS taille : le contenu vaut alors
    `None` et rien n'est a consommer dans le flux.

    Le mot de type n'est pas lu : git le traduit selon la locale de la
    machine (mesure : `blob` rendu `sortie` sur une session francaise), et
    un parseur qui attend `blob` echoue sur un depot sain. Seul le dernier
    jeton, numerique, fait foi.
    """
    chunks: list[str | None] = []
    pos = 0
    for _ in range(expected):
        end = stdout.find(b"\n", pos)
        if end == -1:
            chunks.append(None)
            break
        header = stdout[pos:end]
        pos = end + 1
        parts = header.split()
        if len(parts) < 3 or not parts[-1].isdigit():
            # entree manquante : rien a consommer dans le flux
            chunks.append(None)
            continue
        size = int(parts[-1])
        chunks.append(stdout[pos:pos + size].decode("utf-8", "replace"))
        pos += size + 1  # le contenu est suivi d'un retour a la ligne
    return chunks


def collect_base(root: Path, ref: str) -> dict:
    """Mesure l'etat d'inventaire a la revision `ref` (mode DELTA).

    L'etat de la base est lu dans les objets git : c'est ce qui permet de
    comparer la tete a la base sans modifier l'arbre de travail.
    """
    rc, listing = _git(root, ["ls-tree", "-r", "--name-only", ref, "--",
                               RULES_DIR.as_posix()])
    if rc != 0:
        raise RuntimeError(f"revision {ref!r} illisible")
    rule_paths = [p for p in listing.splitlines()
                  if p.startswith(RULES_DIR.as_posix() + "/")
                  and p.endswith(".md")]
    doc_path = INVENTORY_DOC.as_posix()
    claude_path = CLAUDE_MD.as_posix()
    blobs = _git_blobs(root, ref, rule_paths + [doc_path, claude_path])

    rules: dict[str, bool] = {}
    for path in rule_paths:
        content = blobs.get(path)
        if content is None:
            continue
        rules[Path(path).stem] = parse_frontmatter_paths(content)

    doc = blobs.get(doc_path)
    claude = blobs.get(claude_path)
    if doc is None or claude is None:
        raise RuntimeError(
            f"surfaces d'inventaire absentes de {ref!r} "
            f"({doc_path if doc is None else claude_path})")
    cites = inventory_names(doc)
    bloc = announced_block(claude)
    return etat(rules, cites, bloc)


# --------------------------------------------------------------------------
# Mode DELTA
# --------------------------------------------------------------------------

def delta(base_state: dict, head_state: dict) -> list[tuple[str, str]]:
    """Findings presents sur la tete et ABSENTS de la base.

    Un finding deja present sur la base n'est pas rejoue : il appartient a la
    dette de `main`, pas a la PR. C'est la regle du cliquet (cf le garde
    "path-length ratchet") : le garde ne rougit que sur ce que la PR ajoute.
    """
    base = set(findings_of(base_state))
    return [f for f in findings_of(head_state) if f not in base]


# --------------------------------------------------------------------------
# Auto-controle
# --------------------------------------------------------------------------

def self_test() -> int:
    """Cas de controle de l'organe, sans depot ni reseau.

    Le controle est ANCRE sur la classe de defaut : un etat qui porte les
    trois findings, puis le meme etat dont on retire chaque finding. Un
    detecteur qui ne voit pas sa classe ne prouve rien.
    """
    rules = {"alpha": True, "beta": False, "gamma": False}
    cites = {"alpha", "beta", "gamma"}
    bloc = "- (`alpha`)\n"

    sain = etat(rules, cites, bloc)
    if findings_of(sain):
        sys.stderr.write(f"ECHEC : etat sain porte des findings\n")
        return 1
    if sain["rules_sur_disque"] != 3 or sain["rules_path_gatees"] != 1:
        sys.stderr.write(f"ECHEC : compteurs faux sur l'etat sain\n")
        return 1

    # classe 1 : regle sur disque absente de l'inventaire
    avec1 = etat({**rules, "delta": False}, cites, bloc)
    if ("ON_DISK_NOT_CITED", "delta") not in findings_of(avec1):
        sys.stderr.write("ECHEC : classe 1 non vue\n")
        return 1

    # classe 2 : regle path-gatee non annoncee
    avec2 = etat(rules, cites, "- (`beta`)\n")
    if ("GATED_NOT_ANNOUNCED", "alpha") not in findings_of(avec2):
        sys.stderr.write("ECHEC : classe 2 non vue\n")
        return 1

    # classe 3 : entree d'inventaire pointant vers une regle absente
    avec3 = etat(rules, cites | {"zeta"}, bloc)
    if ("CITED_NOT_ON_DISK", "zeta") not in findings_of(avec3):
        sys.stderr.write("ECHEC : classe 3 non vue\n")
        return 1

    # le delta ignore une dette heritee de la base
    if delta(avec1, avec1):
        sys.stderr.write("ECHEC : le delta rejoue une dette de la base\n")
        return 1
    if delta(sain, avec1) != [("ON_DISK_NOT_CITED", "delta")]:
        sys.stderr.write("ECHEC : le delta ne voit pas le finding nouveau\n")
        return 1

    sys.stdout.write("OK : 3 classes de controle + delta\n")
    return 0


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo-root", default=str(REPO_ROOT),
                        help="racine du depot")
    parser.add_argument("--base", default="",
                        help="revision de reference : mode DELTA (defaut : "
                             "mode ETAT sur l'arbre de travail)")
    parser.add_argument("--json", action="store_true", help="verdict machine")
    parser.add_argument("--self", action="store_true",
                        help="cas de controle, sans depot")
    args = parser.parse_args(argv)

    if args.self:
        return self_test()

    root = Path(args.repo_root)
    try:
        head_state = collect(root)
    except FileNotFoundError as exc:
        sys.stderr.write(f"INCIDENT : {exc}\n")
        return 2

    if args.base:
        try:
            base_state = collect_base(root, args.base)
        except (RuntimeError, ValueError) as exc:
            sys.stderr.write(f"INCIDENT : base illisible ({exc})\n")
            return 2
        nouveaux = delta(base_state, head_state)
        findings = [{"code": code, "regle": name} for code, name in nouveaux]
        verdict = "OVER" if findings else "OK"
        resultat = {
            "mode": "delta",
            "base": args.base,
            "rules_sur_disque": head_state["rules_sur_disque"],
            "rules_path_gatees": head_state["rules_path_gatees"],
            "entrees_inventaire": head_state["entrees_inventaire"],
            "base_findings": [f"{c} {n}" for c, n in findings_of(base_state)],
            "findings": findings,
            "verdict": verdict,
        }
    else:
        resultat = _etat_vers_resultat(head_state)
        resultat["mode"] = "etat"

    rc = 1 if resultat["findings"] else 0

    if args.json:
        print(json.dumps(resultat, ensure_ascii=False, indent=2))
        return rc

    mode = "DELTA" if resultat["mode"] == "delta" else "ETAT"
    print(f"[{mode}] {resultat['rules_sur_disque']} regle(s) sur disque "
          f"({resultat['rules_path_gatees']} path-gatee(s)), "
          f"{resultat['entrees_inventaire']} entree(s) d'inventaire")
    if resultat["mode"] == "delta" and resultat["base_findings"]:
        print(f"  dette de la base ({len(resultat['base_findings'])} "
              f"finding(s), non rejoue(s)) : "
              f"{', '.join(resultat['base_findings'][:5])}")
    for f in resultat["findings"]:
        print(f"  {f['code']} {f['regle']}")
    print("VERDICT:", resultat["verdict"])
    return rc


if __name__ == "__main__":
    sys.exit(main())
