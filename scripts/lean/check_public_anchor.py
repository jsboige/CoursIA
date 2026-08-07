#!/usr/bin/env python3
"""Detecte les ``sorry`` qu'aucune declaration PUBLIQUE n'atteint (issue #8782).

## Le defaut vise

Le gate ``proof-integrity`` mesure les axiomes via ``#print axioms`` sur les
declarations **publiques** d'un module. ``_enumerate_module_declarations``
(``agent_tests/lean_server.py``) saute deliberement les declarations
``private`` -- a raison, car Lean 4 les mangle en
``_private.<Module>.<hash>.<name>`` et ``#print axioms`` repondrait
``unknown constant`` (#8722). La justification ecrite dans ce code est :

    "Nothing is lost by skipping them: a private lemma reaches the kernel only
    through the public theorems that use it, and those are enumerated, so its
    axioms are still counted transitively."

Elle est correcte **mais conditionnelle** : elle suppose qu'un theoreme public
consomme effectivement la chaine. Quand ce n'est pas le cas -- chaine privee sur
toute sa longueur, ou lemme prive que personne ne cite -- le ``sorryAx`` du
``sorry`` n'apparait dans la cloture d'AUCUNE declaration enumeree. Le module
est alors correctement cible, correctement enumere, et **rapporte propre alors
qu'il porte des sorry**.

Cet outil verifie mecaniquement cette hypothese, module par module.

## Pourquoi une analyse statique suffit (et est complete)

En Lean 4, ``private`` est **de portee module** : une declaration privee n'est
pas referencable depuis un autre module. La cloture arriere d'une declaration
privee est donc **entierement contenue dans son propre fichier**, ce qui rend
l'analyse mono-fichier *complete* pour cette question, pas approximative. Aucun
kernel Lean, aucun Mathlib construit n'est requis -- l'outil tourne sur
n'importe quelle machine.

## Biais assume : jamais de fausse alarme, silences possibles

Le graphe de references est bati sur les **noms** (un token identique a un nom de
declaration compte comme une reference). C'est une **sur**-approximation des
aretes : une variable locale homonyme cree une arete qui n'existe pas. L'effet
va toujours dans le meme sens -- plus d'aretes = plus de chances de trouver un
ancrage public = **moins** de verdicts UNANCHORED. L'outil peut donc taire un
angle mort reel, il ne peut pas en inventer un. C'est le bon biais pour un
advisory : un UNANCHORED rapporte merite d'etre regarde.

## Usage

    python scripts/lean/check_public_anchor.py <fichier.lean> [...]
    python scripts/lean/check_public_anchor.py --lake MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean
    python scripts/lean/check_public_anchor.py --lake <dir> --json
    python scripts/lean/check_public_anchor.py --lake <dir> --fail-on-unanchored

Sortie advisory (exit 0) par defaut, comme ``check_target_coverage`` : l'outil
rend visible, il ne decide pas. ``--fail-on-unanchored`` est opt-in.

See #8782 (2e etage), #8722 (cause du saut des private), #8940 (classification
des enumerations vides), #8678 (un compteur nu se perime, un compteur avec son
denominateur se contredit tout seul).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_i18n_siblings import strip_comments  # noqa: E402

# Tetes de declaration porteuses de preuve. ``structure`` / ``inductive`` sont
# exclues : elles ne portent pas de ``sorry`` de preuve.
_DECL_HEAD = re.compile(
    r"^\s*(?P<mods>(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|partial\s+|noncomputable\s+|unsafe\s+|scoped\s+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|example)\b"
    r"(?:\s+(?P<name>[A-Za-z_][A-Za-z0-9_'!?₀-₉]*(?:\.[A-Za-z_][A-Za-z0-9_'!?₀-₉]*)*))?"
)

_NAMESPACE_OPEN = re.compile(r"^\s*namespace\s+(?P<ns>[\w.]+)")
_NAMESPACE_CLOSE = re.compile(r"^\s*end\s+(?P<ns>[\w.]+)\s*$")

# Un identifiant Lean, points inclus (``Conway.Life.foo``).
_TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?₀-₉]*(?:\.[A-Za-z_][A-Za-z0-9_'!?₀-₉]*)*")

# Verdicts, du plus sain au plus preoccupant.
ANCHORED_PUBLIC = "anchored_public"          # le porteur est lui-meme public
ANCHORED_TRANSITIVE = "anchored_transitive"  # prive, mais un public le rejoint
UNANCHORED = "unanchored"                    # prive, aucun public ne le rejoint
ANONYMOUS = "anonymous"                      # ``example`` : jamais adressable
ORPHAN = "orphan_sorry"                      # hors de toute declaration


@dataclass
class Decl:
    """Une declaration et son corps (jusqu'a la tete suivante)."""

    name: str
    kind: str
    line: int
    private: bool
    anonymous: bool
    end: int = 0
    body: str = ""
    refs: set[str] = field(default_factory=set)

    @property
    def label(self) -> str:
        return self.name if not self.anonymous else f"<{self.kind}@{self.line}>"


def parse_declarations(stripped: str) -> list[Decl]:
    """Indexe les declarations du source (deja depouille de ses commentaires).

    Les noms sont qualifies par la pile de ``namespace`` ouverts, avec la meme
    prudence que ``lean_server`` : on ne depile que si le ``end`` reference bien
    le namespace au sommet (un ``end`` de ``section`` ne doit pas desequilibrer
    la pile, cf #8722).
    """
    lines = stripped.splitlines()
    ns: list[str] = []
    decls: list[Decl] = []
    for idx, line in enumerate(lines, start=1):
        m_open = _NAMESPACE_OPEN.match(line)
        if m_open:
            ns.append(m_open.group("ns"))
            continue
        m_close = _NAMESPACE_CLOSE.match(line)
        if m_close:
            if ns and ns[-1] == m_close.group("ns"):
                ns.pop()
            continue
        m = _DECL_HEAD.match(line)
        if not m:
            continue
        raw = m.group("name")
        anonymous = raw is None
        if anonymous:
            name = f"__{m.group('kind')}_{idx}"
        elif raw.startswith("_root_."):
            name = raw[len("_root_.") :]
        else:
            name = ".".join(ns + [raw]) if ns else raw
        decls.append(
            Decl(
                name=name,
                kind=m.group("kind"),
                line=idx,
                private="private" in (m.group("mods") or ""),
                anonymous=anonymous,
            )
        )
    for i, d in enumerate(decls):
        d.end = decls[i + 1].line - 1 if i + 1 < len(decls) else len(lines)
        d.body = "\n".join(lines[d.line - 1 : d.end])
    return decls


def build_reference_graph(decls: list[Decl]) -> None:
    """Renseigne ``d.refs`` : les declarations citees dans le corps de ``d``.

    Un token est reconnu s'il egale un nom qualifie OU son dernier composant --
    une reference intra-namespace s'ecrit couramment en nom court.
    """
    by_qualified = {d.name: d.name for d in decls if not d.anonymous}
    by_short: dict[str, set[str]] = {}
    for d in decls:
        if d.anonymous:
            continue
        by_short.setdefault(d.name.rsplit(".", 1)[-1], set()).add(d.name)
    for d in decls:
        hits: set[str] = set()
        for tok in _TOKEN.findall(d.body):
            if tok in by_qualified:
                hits.add(tok)
            hits |= by_short.get(tok.rsplit(".", 1)[-1], set())
        d.refs = hits - {d.name}


def public_closure_reaches(target: str, decls: list[Decl]) -> tuple[bool, list[str]]:
    """La cloture ARRIERE de ``target`` contient-elle une declaration publique ?

    Retourne ``(atteint, ancrages_publics_tries)``.
    """
    callers: dict[str, set[str]] = {d.name: set() for d in decls}
    for d in decls:
        for r in d.refs:
            if r in callers:
                callers[r].add(d.name)
    by_name = {d.name: d for d in decls}
    seen: set[str] = set()
    frontier = [target]
    while frontier:
        cur = frontier.pop()
        for caller in callers.get(cur, ()):
            if caller not in seen:
                seen.add(caller)
                frontier.append(caller)
    anchors = sorted(
        n for n in seen if n in by_name and not by_name[n].private and not by_name[n].anonymous
    )
    return bool(anchors), anchors


def analyze_module(path: Path) -> dict:
    """Verdict d'un module : un enregistrement par ``sorry`` en position de code."""
    src = path.read_text(encoding="utf-8", errors="replace")
    stripped = strip_comments(src)
    decls = parse_declarations(stripped)
    build_reference_graph(decls)

    sites: list[dict] = []
    for idx, line in enumerate(stripped.splitlines(), start=1):
        for _ in re.finditer(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])", line):
            owner = None
            for d in decls:
                if d.line <= idx <= d.end:
                    owner = d
            if owner is None:
                sites.append({"line": idx, "verdict": ORPHAN, "owner": None, "anchors": []})
                continue
            if owner.anonymous:
                verdict, anchors = ANONYMOUS, []
            elif not owner.private:
                verdict, anchors = ANCHORED_PUBLIC, [owner.name]
            else:
                reached, anchors = public_closure_reaches(owner.name, decls)
                verdict = ANCHORED_TRANSITIVE if reached else UNANCHORED
            sites.append(
                {
                    "line": idx,
                    "verdict": verdict,
                    "owner": owner.label,
                    "owner_private": owner.private,
                    "anchors": anchors,
                }
            )

    return {
        "module": str(path),
        "declarations": len(decls),
        "private_declarations": sum(1 for d in decls if d.private),
        "sorry_sites": len(sites),
        "unanchored": sum(1 for s in sites if s["verdict"] == UNANCHORED),
        "sites": sites,
    }


def lean_sources(root: Path) -> list[Path]:
    """Les ``*.lean`` d'un lake, hors ``.lake/`` (deps vendorees)."""
    return sorted(p for p in root.rglob("*.lean") if ".lake" not in p.parts)


def _render(reports: list[dict]) -> None:
    print("=== ADVISORY: sorry sans ancrage public (proof-integrity 2e etage, #8782) ===")
    tot_sorry = sum(r["sorry_sites"] for r in reports)
    tot_unanchored = sum(r["unanchored"] for r in reports)
    print(f"Modules analyses      : {len(reports)}")
    print(f"Sorry en position code: {tot_sorry}")
    print(f"Dont SANS ancrage     : {tot_unanchored}")
    if tot_sorry:
        print(f"Couverture du gate    : {tot_sorry - tot_unanchored}/{tot_sorry} "
              f"({100.0 * (tot_sorry - tot_unanchored) / tot_sorry:.1f}%)")
    for r in reports:
        flagged = [s for s in r["sites"] if s["verdict"] in (UNANCHORED, ANONYMOUS, ORPHAN)]
        if not flagged:
            continue
        print(f"\n-- {r['module']}")
        print(f"   {r['declarations']} declarations ({r['private_declarations']} private), "
              f"{r['sorry_sites']} sorry")
        for s in flagged:
            owner = s["owner"] or "(hors declaration)"
            print(f"   L{s['line']:<6} {s['verdict']:<21} {owner}")
    if not tot_unanchored:
        print("\nAucun sorry hors de portee des declarations publiques enumerees.")
    else:
        print("\nUn sorry UNANCHORED n'apparait dans la cloture d'axiomes d'AUCUNE")
        print("declaration enumeree : le gate peut rapporter propre sur ce module.")


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Detecte les sorry qu'aucune declaration publique n'atteint (#8782)."
    )
    ap.add_argument("paths", nargs="*", type=Path, help="Fichiers .lean a analyser")
    ap.add_argument("--lake", type=Path, help="Racine d'un lake (recursif, hors .lake/)")
    ap.add_argument("--json", action="store_true", help="Sortie machine-lisible")
    ap.add_argument(
        "--fail-on-unanchored",
        action="store_true",
        help="Exit 1 si au moins un sorry est sans ancrage public (defaut: advisory, exit 0)",
    )
    args = ap.parse_args(argv)

    if not args.paths and not args.lake:
        ap.error("fournir au moins un fichier .lean ou --lake <dir>")

    # Un detecteur d'angle mort ne doit jamais se taire parce qu'il n'a rien
    # regarde -- c'est la classe de defaut qu'il traque (cf EMPTY_* de #8940).
    # Une cible vide ou absente est une ERREUR, pas un rapport propre.
    targets: list[Path] = []
    for p in args.paths:
        if not p.is_file():
            ap.error(f"fichier introuvable : {p}")
        targets.append(p)
    if args.lake:
        if not args.lake.is_dir():
            ap.error(f"lake introuvable : {args.lake}")
        found = lean_sources(args.lake)
        if not found:
            ap.error(f"aucun .lean hors .lake/ sous {args.lake} -- cible vide, rien analyse")
        targets += found

    reports = [analyze_module(p) for p in targets]
    if args.json:
        print(json.dumps(reports, indent=2, ensure_ascii=False))
    else:
        _render(reports)

    unanchored = sum(r["unanchored"] for r in reports)
    return 1 if (args.fail_on_unanchored and unanchored) else 0


if __name__ == "__main__":
    raise SystemExit(main())
