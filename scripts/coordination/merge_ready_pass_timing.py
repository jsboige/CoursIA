#!/usr/bin/env python3
"""Duree d'un passage de ``merge_ready``, groupee par classe -- lu au journal.

Pourquoi cet organe existe (issue #26799)
-----------------------------------------
Le passage du 2026-11-15 a evalue 132 PRs en 1 h 41 pour 11 merges. La mesure
existait deja, prise a la main : 11 merges = 3 040 s (50 %), 17 sauts
``mergeable-state:*`` = 2 426 s (40 %), 103 autres sauts = 437 s (7 %). Mais
elle a demande une lecture manuelle du journal, et rien ne la rejouait.

L'issue designe ce journal comme le verdict : « le journal est deja horodate :
la somme des ecarts inter-lignes d'une passe, groupee par classe, est le
verdict ». Cet organe fait exactement cela, et rien de plus.

Ce qu'il mesure, et ce qu'il ne mesure pas
------------------------------------------
Chaque ligne du journal est ecrite **apres** l'evaluation de sa PR : l'ecart
entre la ligne ``i-1`` et la ligne ``i`` est donc le cout d'evaluation de la PR
de la ligne ``i``, et il est attribue a **sa** classe. Signe, pas suppose :
``append_journal`` est appele apres ``evaluate_pr`` dans la boucle de
``merge_ready``.

La **premiere** ligne d'un passage n'a pas de predecesseur : son cout (demarrage
du passage -- resolution du jeton, ``list_open_prs``, retenues -- plus la
premiere PR) n'est pas mesurable ici et n'est pas invente. L'organe rapporte
donc une **etendue** ``premiere ligne -> derniere ligne``, et dit explicitement
que le demarrage et la derniere ecriture restent hors de cette etendue. Une
etendue qui sous-compte est honnete ; une duree complete reconstituee a partir
d'une borne inconnue ne le serait pas.

Le journal ne porte pas d'identifiant de passage. Un passage se reconnait donc
a deux signaux, tous deux objectifs : une PR **deja vue** dans le passage en
cours (la boucle evalue chaque PR une seule fois) ou un ecart superieur a
``--max-gap`` (les couts par PR d'un passage se comptent en minutes, la cadence
entre passages en dizaines de minutes).

Les lignes ``unevaluated`` (PRs que la passe n'a pas evaluees, arret sur le
budget de duree -- #28009) sont comptees mais **hors cout et hors compte de
PRs** : elles ne representent aucune evaluation, et les compter comme des
PRs evaluees ferait passer un passage lent pour un passage rapide (regle de
trois sur un compte gonfle).

Usage
-----
    python scripts/coordination/merge_ready_pass_timing.py
    python scripts/coordination/merge_ready_pass_timing.py --journal <chemin>
    python scripts/coordination/merge_ready_pass_timing.py --last 3
    python scripts/coordination/merge_ready_pass_timing.py --json
    python scripts/coordination/merge_ready_pass_timing.py --target-minutes 30

Codes de sortie : 0 = rapport rendu (un passage lent est un **verdict**, pas une
erreur d'execution) · 2 = source illisible ou argument invalide. Aucun code 1 :
l'organe ne fait jamais rougir une CI sur une duree, qui depend de la charge
GitHub du moment et non du depot. ``--fail-over-target`` est la seule facon d'en
faire un rouge, et elle est opt-in.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path

#: Ecart au-dela duquel deux lignes consecutives appartiennent a deux passages.
#: Le cout par PR d'un passage se compte en minutes (attente de mergeabilite
#: bornee a 120 s, tests d'arbre ~1 min) ; la cadence entre deux passages est de
#: plusieurs dizaines de minutes. 15 min separe les deux sans ambiguite sur les
#: mesures connues.
DEFAULT_MAX_GAP_S = 900.0

#: Le seuil d'acceptance de #26799 : un passage de 132 PRs sous 30 min.
DEFAULT_TARGET_MINUTES = 30.0
DEFAULT_TARGET_PRS = 132

#: Verdict d'une PR que la passe de ``merge_ready`` n'a pas **evaluee** (arret
#: sur le budget de duree, #28009).
#:
#: Ces lignes ne portent aucun cout d'evaluation : l'organe les COMPTE mais ne
#: les mesure pas. Sans cela, un passage arrete par son budget gonflerait son
#: compte de PRs de centaines de lignes sans evaluation, et la projection
#: ``span * (132 / count)`` -- qui est une regle de trois sur le compte de
#: PRs -- repartirait d'un compte faux : plus de PRs, moins de cout unitaire
#: annonce, un passage lent qui passerait pour rapide.
#:
#: C'est une **recopie** de ``merge_ready.VERDICT_NOT_EVALUATED`` ( meme
#: convention que ``default_journal_path`` : la copie ne derive pas en
#: silence, un test verrouille l'egalite).
NOT_EVALUATED_VERDICT = "unevaluated"


def default_journal_path() -> Path:
    """Le chemin par defaut du journal, celui de ``merge_ready``.

    Il est **recopie** de ``merge_ready.default_journal_path`` et non importe :
    cet organe doit rester lisible sur une machine ou le module de l'organe
    n'est pas importable (dependances de ``merge_ready`` plus larges), et le
    chemin est une convention stable, pas une logique a partager. Le test
    ``test_default_journal_path_matches_merge_ready`` verrouille l'egalite pour
    que la copie ne derive pas en silence.
    """
    import os

    base = Path(os.environ.get("LOCALAPPDATA") or Path.home() / "AppData" / "Local")
    return base / "CoursIA" / "merge_ready" / "journal.jsonl"


def parse_ts(raw: object) -> datetime | None:
    """Horodatage du journal, en UTC explicite. ``None`` si illisible.

    Le journal ecrit ``%Y-%m-%dT%H:%M:%SZ`` (seconde pleine, suffixe Z). On
    accepte aussi les fractions de seconde, au cas ou le format s'affine : un
    horodatage plus precis ne doit pas rendre l'organe muet.
    """
    if not isinstance(raw, str) or not raw.strip():
        return None
    text = raw.strip()
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    try:
        parsed = datetime.fromisoformat(text)
    except ValueError:
        return None
    if parsed.tzinfo is None:
        # Un horodatage sans fuseau dans ce journal est une anomalie : on ne
        # devine pas la zone (une heure locale lue comme UTC fabrique un skew).
        return None
    return parsed.astimezone(timezone.utc)


def reason_class(verdict: object, reason: object) -> str:
    """La classe de cout d'une ligne de journal.

    ``mergeable-state`` garde son second segment : ``unknown`` et ``unstable``
    sont deux situations distinctes (attente de recalcul contre jambes a
    arbitrer) et #26799 les traite separement. Les autres motifs sont replies
    sur leur premier segment, ce qui rend la table lisible sans perdre le
    decoupage que l'issue a elle-meme employe.
    """
    text = str(reason or "").strip()
    parts = [p for p in text.split(":") if p]
    head = parts[0] if parts else ""
    if head == "mergeable-state" and len(parts) > 1:
        return f"mergeable-state:{parts[1]}"
    if head:
        return head
    return str(verdict or "?")


@dataclass
class Row:
    """Une ligne de journal retenue, avec son horodatage deja resolu."""

    index: int
    pr: int | None
    ts: datetime
    verdict: str
    reason: str
    cls: str

    @property
    def label(self) -> str:
        return f"PR #{self.pr}" if self.pr is not None else f"ligne {self.index}"


@dataclass
class Pass:
    """Un passage de ``merge_ready`` et son cout, groupe par classe."""

    rows: list[Row] = field(default_factory=list)
    #: Cout mesure par classe, en secondes : attribue a la ligne dont
    #: l'evaluation s'est terminee a cet horodatage.
    by_class: dict[str, float] = field(default_factory=dict)
    by_class_count: dict[str, int] = field(default_factory=dict)
    #: Les evaluations les plus cheres du passage, (secondes, ligne).
    costs: list[tuple[float, Row]] = field(default_factory=list)
    #: Lignes dont l'horodatage precede celui de la ligne precedente.
    time_travel: int = 0
    #: PRs du passage que la passe n'a pas EVALUEEes (arret sur le budget de
    #: duree, #28009). Elles ne portent aucun cout : elles sont comptees,
    #: pas mesurees.
    not_evaluated: int = 0

    @property
    def start(self) -> datetime | None:
        return self.rows[0].ts if self.rows else None

    @property
    def end(self) -> datetime | None:
        return self.rows[-1].ts if self.rows else None

    @property
    def span_s(self) -> float:
        """Etendue premiere -> derniere ligne. Exclut le demarrage du passage."""
        if len(self.rows) < 2:
            return 0.0
        return (self.rows[-1].ts - self.rows[0].ts).total_seconds()

    @property
    def measured_s(self) -> float:
        """Somme des couts attribues -- doit egaler ``span_s`` a l'arrondi pres."""
        return sum(self.by_class.values())

    @property
    def count(self) -> int:
        return len(self.rows)

    def add(self, row: Row, delta_s: float | None) -> None:
        self.rows.append(row)
        self.by_class_count[row.cls] = self.by_class_count.get(row.cls, 0) + 1
        if delta_s is None:
            return
        self.by_class[row.cls] = self.by_class.get(row.cls, 0.0) + delta_s
        self.costs.append((delta_s, row))


def split_passes(rows: list[Row], max_gap_s: float) -> list[Pass]:
    """Segmente le journal en passages.

    Deux signaux objectifs, dans cet ordre : une PR deja vue dans le passage en
    cours (la boucle de ``merge_ready`` ne l'evalue qu'une fois), ou un ecart
    superieur a ``max_gap_s``. Un horodatage qui recule ouvre aussi un passage :
    il ne peut pas appartenir a la meme mesure, et le compter dans l'ecart
    fabriquerait une duree negative.
    """
    passes: list[Pass] = []
    current = Pass()
    seen: set[int | None] = set()
    previous: Row | None = None
    for row in rows:
        if row.verdict == NOT_EVALUATED_VERDICT:
            # Ligne d'une PR que la passe n'a pas evaluee (arret sur le budget
            # de duree, #28009) : elle ne porte AUCUN cout et son horodatage
            # ne delimite aucune evaluation -- elle ne compte donc ni dans le
            # cout, ni dans le compte de PRs du passage. Elle est COMPTEE, et
            # sa PR reste dans `seen` : evaluee au tour suivant, elle ouvrira
            # un passage (sans cela, les deux passages fusionneraient et la
            # mesure du suivant serait absorbee par le precedent).
            current.not_evaluated += 1
            if row.pr is not None:
                seen.add(row.pr)
            continue
        boundary = False
        went_back = previous is not None and row.ts < previous.ts
        if previous is not None:
            if row.pr is not None and row.pr in seen:
                boundary = True
            elif (row.ts - previous.ts).total_seconds() > max_gap_s:
                boundary = True
            elif went_back:
                boundary = True
        if boundary:
            passes.append(current)
            current = Pass()
            seen = set()
            previous = None
        if went_back:
            # Recule d'horodatage : l'anomalie est comptee sur le passage
            # qu'elle ouvre. C'est la seule trace qu'un journal recolle ou
            # reecrit laisse a l'operateur -- la taire rendrait le passage
            # suivant credible alors que ses bornes ne le sont pas.
            current.time_travel += 1
        delta: float | None = None
        if previous is not None:
            delta = (row.ts - previous.ts).total_seconds()
        current.add(row, delta)
        seen.add(row.pr)
        previous = row
    if current.rows or current.not_evaluated:
        # Un passage qui n'a evalue aucune PR (arret sur le budget avant la
        # premiere PR) reste visible : il porte un compte, meme nul.
        passes.append(current)
    return passes


def read_journal(path: Path) -> tuple[list[Row], int]:
    """Lit le journal ; rend les lignes exploitables et le compte d'illisibles.

    Une ligne illisible ne fait pas echouer l'organe : elle est comptee, et le
    rapport la nomme. Un journal tronque en cours d'ecriture est un cas reel
    (le processus ecrit une ligne a la fois) ; s'arreter dessus rendrait
    l'instrument inutilisable precisement quand on en a besoin.
    """
    rows: list[Row] = []
    unreadable = 0
    with path.open("r", encoding="utf-8") as handle:
        for index, line in enumerate(handle, start=1):
            text = line.strip()
            if not text:
                continue
            try:
                payload = json.loads(text)
            except json.JSONDecodeError:
                unreadable += 1
                continue
            if not isinstance(payload, dict):
                unreadable += 1
                continue
            ts = parse_ts(payload.get("ts"))
            if ts is None:
                unreadable += 1
                continue
            pr_raw = payload.get("pr")
            pr = pr_raw if isinstance(pr_raw, int) else None
            verdict = str(payload.get("verdict") or "")
            reason = str(payload.get("reason") or "")
            rows.append(
                Row(
                    index=index,
                    pr=pr,
                    ts=ts,
                    verdict=verdict,
                    reason=reason,
                    cls=reason_class(verdict, reason),
                )
            )
    # Pas de tri : le journal est append-only, l'ordre du fichier EST l'ordre
    # chronologique. Trier ici « reparerait » un horodatage qui recule -- or
    # c'est precisement l'anomalie qu'un operateur doit voir, et `split_passes`
    # la traite sans fabriquer de duree negative. Le tri rendait aussi le
    # passage fantome invisible (mesure en ecrivant ce module).
    return rows, unreadable


def fmt_seconds(value: float) -> str:
    """Duree lisible : ``1 h 41 min`` / ``2 min 06 s`` / ``12 s``."""
    total = int(round(value))
    if total < 60:
        return f"{total} s"
    minutes, seconds = divmod(total, 60)
    if minutes < 60:
        return f"{minutes} min {seconds:02d} s"
    hours, minutes = divmod(minutes, 60)
    return f"{hours} h {minutes:02d} min"


def pass_report(pass_obj: Pass, index: int) -> dict:
    """Forme structuree d'un passage -- celle que ``--json`` rend telle quelle."""
    span = pass_obj.span_s
    classes = []
    for cls, seconds in sorted(pass_obj.by_class.items(), key=lambda kv: -kv[1]):
        share = (seconds / span * 100.0) if span > 0 else 0.0
        classes.append(
            {
                "class": cls,
                "count": pass_obj.by_class_count.get(cls, 0),
                "seconds": round(seconds, 1),
                "share_pct": round(share, 1),
            }
        )
    return {
        "pass": index,
        "prs": pass_obj.count,
        "start": pass_obj.start.isoformat().replace("+00:00", "Z")
        if pass_obj.start
        else None,
        "end": pass_obj.end.isoformat().replace("+00:00", "Z")
        if pass_obj.end
        else None,
        "span_s": round(span, 1),
        "startup_unmeasured_prs": 1 if pass_obj.count else 0,
        "time_travel": pass_obj.time_travel,
        # PRs que la passe n'a pas evaluees (arret sur le budget de duree) :
        # hors comptage des PRs evaluees, hors cout.
        "not_evaluated": pass_obj.not_evaluated,
        "classes": classes,
    }


def render(pass_obj: Pass, index: int, top: int, target_minutes: float,
           target_prs: int) -> str:
    """Le rapport humain d'un passage : duree, classes, plus cheres evaluations."""
    span = pass_obj.span_s
    lines: list[str] = []
    start = pass_obj.start.strftime("%Y-%m-%dT%H:%M:%SZ") if pass_obj.start else "?"
    end = pass_obj.end.strftime("%H:%M:%SZ") if pass_obj.end else "?"
    lines.append(
        f"passage {index} -- {pass_obj.count} PRs, {start} -> {end}, "
        f"etendue {fmt_seconds(span)}"
    )
    lines.append(
        "  (etendue = premiere -> derniere ligne ; demarrage du passage et "
        "derniere ecriture non mesures)"
    )
    if pass_obj.not_evaluated:
        lines.append(
            f"  {pass_obj.not_evaluated} PR(s) NON evaluee(s) (arret sur le "
            "budget de duree) : comptees, hors cout d'evaluation -- elles "
            "n'entrent ni dans le compte de PRs ni dans la projection."
        )
    lines.append("")
    lines.append(f"  {'classe':<34} {'PRs':>4} {'duree':>12} {'part':>7}")
    lines.append(f"  {'-' * 34} {'-' * 4} {'-' * 12} {'-' * 7}")
    for cls, seconds in sorted(pass_obj.by_class.items(), key=lambda kv: -kv[1]):
        share = (seconds / span * 100.0) if span > 0 else 0.0
        count = pass_obj.by_class_count.get(cls, 0)
        lines.append(
            f"  {cls:<34} {count:>4} {fmt_seconds(seconds):>12} {share:>6.1f}%"
        )
    # Les classes vues seulement sur la premiere ligne n'ont aucun cout
    # attribuable : les nommer evite de les croire absentes.
    missing = sorted(set(pass_obj.by_class_count) - set(pass_obj.by_class))
    if missing:
        lines.append(
            "  sans cout attribuable (premiere ligne du passage) : "
            + ", ".join(missing)
        )
    if top > 0 and pass_obj.costs:
        lines.append("")
        lines.append(f"  {min(top, len(pass_obj.costs))} evaluations les plus cheres :")
        for seconds, row in sorted(pass_obj.costs, key=lambda c: -c[0])[:top]:
            lines.append(
                f"    {fmt_seconds(seconds):>10}  {row.label:<10} {row.cls}"
            )
    lines.append("")
    if span > 0:
        projected = span * (target_prs / pass_obj.count) if pass_obj.count else 0.0
        verdict = (
            "passage SOUS le seuil"
            if projected <= target_minutes * 60
            else "passage AU-DESSUS du seuil"
        )
        lines.append(
            f"  acceptance #26799 : {verdict} -- {fmt_seconds(projected)} "
            f"projete pour {target_prs} PRs (cible {int(target_minutes)} min)."
        )
        if pass_obj.count != target_prs:
            lines.append(
                f"  La projection est une regle de trois sur {pass_obj.count} PRs, "
                "pas une mesure a 132 : elle indique l'echelle, pas le verdict final."
            )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Duree des passages de merge_ready, groupee par classe de verdict, "
            "lue au journal (issue #26799)."
        )
    )
    parser.add_argument("--journal", type=Path, default=None,
                        help="chemin du journal JSONL (defaut : celui de merge_ready)")
    parser.add_argument("--last", type=int, default=1,
                        help="nombre de passages a rendre, du plus recent (defaut : 1)")
    parser.add_argument("--max-gap", type=float, default=DEFAULT_MAX_GAP_S,
                        help=f"ecart (s) qui separe deux passages (defaut : {DEFAULT_MAX_GAP_S:.0f})")
    parser.add_argument("--top", type=int, default=8,
                        help="evaluations les plus cheres a lister par passage (defaut : 8, 0 = aucune)")
    parser.add_argument("--target-minutes", type=float, default=DEFAULT_TARGET_MINUTES,
                        help=f"seuil d'acceptance en minutes (defaut : {DEFAULT_TARGET_MINUTES:.0f})")
    parser.add_argument("--target-prs", type=int, default=DEFAULT_TARGET_PRS,
                        help=f"taille de reference du seuil (defaut : {DEFAULT_TARGET_PRS})")
    parser.add_argument("--json", action="store_true", help="sortie structuree")
    parser.add_argument("--fail-over-target", action="store_true",
                        help="exit 1 si le dernier passage depasse le seuil (opt-in, jamais par defaut)")
    args = parser.parse_args(argv)

    if args.last < 1:
        print("merge_ready_pass_timing : --last doit etre >= 1", file=sys.stderr)
        return 2
    if args.max_gap <= 0:
        print("merge_ready_pass_timing : --max-gap doit etre > 0", file=sys.stderr)
        return 2

    path = args.journal if args.journal is not None else default_journal_path()
    if not path.is_file():
        print(
            f"merge_ready_pass_timing : journal introuvable -- {path}\n"
            "  Le journal vit sur la machine qui execute merge_ready "
            "(sous l'identite du coordinateur). Depuis une autre lane, "
            "passer --journal <copie>.",
            file=sys.stderr,
        )
        return 2
    try:
        rows, unreadable = read_journal(path)
    except OSError as exc:
        print(f"merge_ready_pass_timing : lecture impossible -- {exc}", file=sys.stderr)
        return 2

    if not rows:
        print(
            f"merge_ready_pass_timing : aucune ligne exploitable dans {path} "
            f"({unreadable} illisible(s))",
            file=sys.stderr,
        )
        return 2

    passes = split_passes(rows, args.max_gap)
    selected = list(enumerate(passes, start=1))[-args.last:]
    not_evaluated_total = sum(p.not_evaluated for p in passes)

    if args.json:
        payload = {
            "journal": str(path),
            "passes_total": len(passes),
            "unreadable": unreadable,
            # Lignes de PRs que la passe n'a pas evaluees : comptees, hors
            # cout d'evaluation et hors compte de PRs du passage.
            "not_evaluated": not_evaluated_total,
            "selected": [pass_report(p, i) for i, p in selected],
        }
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        print(
            f"journal : {path} ({len(rows)} lignes dont {not_evaluated_total} "
            f"non evaluee(s), {unreadable} illisible(s))"
        )
        print(f"passages : {len(passes)}")
        print("")
        for position, (i, p) in enumerate(selected):
            if position:
                print("")
            print(render(p, i, args.top, args.target_minutes, args.target_prs))

    if args.fail_over_target and selected:
        last = selected[-1][1]
        span = last.span_s
        projected = span * (args.target_prs / last.count) if last.count else 0.0
        return 1 if projected > args.target_minutes * 60 else 0
    return 0


if __name__ == "__main__":
    raise SystemExit(main())