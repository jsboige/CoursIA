#!/usr/bin/env python3
"""Poste un dossier [ADJOINT PREFLIGHT] ou [CLOSURE PREFLIGHT] sans accident de transport.

Motivation (#18412) : des dossiers partent avec une premiere ligne parasite --
``GH-IDENTITY (WARN, poursuite sous compte actif): ...`` capturee par une
redirection ``2>&1`` -- alors que le gate exige le marqueur d'ouverture en
ligne 1 exacte et rend ``NO-DOSSIER`` alors que la lane croit avoir livre
(3 occurrences mesurees, dont #18386 c.5892248787). La regle ecrite (skill
``adjoint-secretary`` : verifier ``head -1`` avant le POST) n'a pas tenu :
il manque l'organe qui REFUSE de poster, pas une consigne de plus.

Refus (rc 4, RIEN n'est poste) si :

1. la ligne 1 du fichier n'est pas exactement le marqueur d'ouverture, ou
   s'il manque le marqueur de fermeture ;
2. un ``REPLACE_WITH`` reste dans le bloc delimite ;
3. le ``parse_dossier`` de l'organe de la famille (importe, pas reecrit)
   rend des erreurs de forme ;
4. famille PR : le dossier est incoherent **en lui-meme** -- les controles
   auto-portants de ``dossier_self_consistency_errors`` (coherence
   ``verdict``/``domain`` d'abord) rendent des erreurs. Le gate les verifie
   aussi, mais il demande l'instantane de la PR et ne tourne donc qu'APRES le
   POST : sans ce refus, un dossier incoherent partait sur la PR et y devenait
   une surface a supprimer a la main (#19312) ;
5. famille PR : le champ ``head`` n'est pas la tete courante de la PR ;
6. le gate de la famille rend deja 0 ou 3 (dossier intact) pose par une
   AUTRE lane -- anti-double-stamp ; un re-stamp de SA propre lane reste
   licite. Un rc 2 (UNKNOWN) ferme aussi la porte : on ne poste pas
   au-dessus d'un etat illisible. Sur rc 3 (BLOCKED), un re-stamp d'une
   lane tierce est licite si le dossier refute explicitement le dossier
   en place via les champs ``supersedes`` (numero du commentaire de
   l'ancien) et ``supersedes-why`` non vide -- le motif du dossier BLOCKED
   peut etre perime a la meme tete et la lane d'origine peut etre
   indisponible (#19420). Le gate juge ensuite la refutation comme pour
   toute contradiction muette (#18934). rc 0 reste refuse : un second
   tampon n'ouvre pas une guerre de dossiers.

Le POST part par ``gh api ... --input payload.json`` (jamais ``-f body=@``,
cf gh-posting-hygiene.md), puis le corps publie est relu (ligne 1, longueur,
predicat PAYLOAD-TRAP, identite byte-a-byte avec la source) et le gate est
rejoue : son verdict est imprime et le script sort avec SON rc.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Callable, NamedTuple

# Les organes de la famille vivent dans scripts/ : leur parse_dossier est LA
# grammaire du dossier (un seul lecteur, meme discipline que grain_tag).
SCRIPTS_DIR = Path(__file__).resolve().parent.parent
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

import check_adjoint_prevalidation as adjoint_gate  # noqa: E402
import check_closure_dossier as closure_gate  # noqa: E402

REPO = "jsboige/CoursIA"
# Hors de l'espace 0-3 du gate : 0 READY/CLOSE, 1 NO-DOSSIER/REFUSED,
# 2 UNKNOWN, 3 BLOCKED-WITH-SUBSTANCE/KEEP. Un refus du poster ne se lit
# ainsi jamais comme un verdict du gate.
EXIT_REFUSED = 4
# gh-posting-hygiene regle 2, membre metrique : un corps court apres le POST
# d'un fichier est la signature du piege de transport.
MIN_PUBLISHED_LEN = 100


class Family(NamedTuple):
    key: str
    gate_path: Path
    gate: Any
    lane_of: Callable[[dict[str, Any]], str | None]

    def gate_argv(self, repo: str, target: int, json_mode: bool = False) -> list[str]:
        # Le gate PR n'expose pas --repo (depot implicite) ; le gate closure si.
        argv = [sys.executable, str(self.gate_path), str(target)]
        if json_mode:
            argv.append("--json")
        if self.key == "issue":
            argv += ["--repo", repo]
        return argv


ADJOINT = Family(
    "pr",
    SCRIPTS_DIR / "check_adjoint_prevalidation.py",
    adjoint_gate,
    lambda payload: (payload.get("dossier") or {}).get("lane"),
)
CLOSURE = Family(
    "issue",
    SCRIPTS_DIR / "check_closure_dossier.py",
    closure_gate,
    lambda payload: payload.get("lane"),
)


def gh_json(args: list[str]) -> Any:
    proc = subprocess.run(
        ["gh", *args], capture_output=True, text=True, encoding="utf-8"
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.strip() or "gh command failed")
    return json.loads(proc.stdout)


def run_gate(family: Family, repo: str, target: int) -> tuple[int, str]:
    """Joue le gate de la famille en mode JSON : (rc, stdout)."""
    proc = subprocess.run(
        family.gate_argv(repo, target, json_mode=True),
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    return proc.returncode, proc.stdout


def rerun_gate(family: Family, repo: str, target: int) -> int:
    """Rejoue le gate en mode humain (verdict imprime) : son rc fait foi."""
    proc = subprocess.run(family.gate_argv(repo, target))
    return proc.returncode


def load_first_json(stdout: str) -> dict[str, Any]:
    """Extrait le premier objet JSON du stdout du gate.

    La famille closure imprime le verdict humain APRES le bloc JSON ; le
    decoder brutalement depuis la premiere accolade reste exact.
    """
    start = stdout.find("{")
    if start < 0:
        raise ValueError(f"gate stdout carries no JSON: {stdout[:200]!r}")
    payload, _ = json.JSONDecoder().raw_decode(stdout[start:])
    if not isinstance(payload, dict):
        raise ValueError("gate JSON payload is not an object")
    return payload


def refuse(reason: str) -> int:
    print(f"REFUSED -- {reason}", file=sys.stderr)
    return EXIT_REFUSED


def preflight(family: Family, body: str, lane: str) -> tuple[Any, int] | tuple[None, int]:
    """Refus locaux (1, 2, 3) : aucune commande gh n'est lancee."""
    lines = body.splitlines()
    if not lines:
        return None, refuse("dossier file is empty")
    if lines[0].strip() != family.gate.START:
        return None, refuse(
            f"line 1 is not exactly {family.gate.START!r} -- parasite line: "
            f"{lines[0].strip()[:120]!r} (GH-IDENTITY capture par 2>&1, #18412)"
        )
    end_index = next(
        (i for i, line in enumerate(lines[1:], 1) if line.strip() == family.gate.END),
        None,
    )
    if end_index is None:
        return None, refuse(f"missing closing marker {family.gate.END!r}")
    block = lines[1:end_index]
    leftovers = [line for line in block if "REPLACE_WITH" in line]
    if leftovers:
        shown = "; ".join(repr(line.strip()[:80]) for line in leftovers[:3])
        return None, refuse(f"REPLACE_WITH remains in the block: {shown}")
    dossier, errors = family.gate.parse_dossier(body, 0, lane)
    if errors:
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return None, refuse("parse_dossier reports form errors (see above)")
    return dossier, 0


def refuse_incoherent(family: Family, dossier: Any, target: int) -> int | None:
    """Controles auto-portants du dossier, AVANT tout appel gh (#19312).

    Le gate les verifie aussi, mais il demande l'instantane de la PR et ne
    tourne donc qu'APRES le POST : un dossier incoherent partait sur la PR et y
    devenait une surface a supprimer a la main (mesure #19207). On rejoue ici
    les controles qui ne dependent que du dossier, avec le MEME organe
    (importe, jamais reecrit) -- deux lecteurs d'une grammaire divergent.
    """
    if family is not ADJOINT:
        return None
    errors = family.gate.dossier_self_consistency_errors(dossier.fields, target)
    if not errors:
        return None
    for error in errors:
        print(f"  - {error}", file=sys.stderr)
    return refuse(
        "dossier is incoherent on its own (see above): the gate would refuse it "
        "right after the POST (#19312)"
    )


def post_comment(repo: str, target: int, body: str) -> dict[str, Any]:
    """POST par --input : le payload est ASCII pur (json.dumps echappe),
    aucun shell n'intercalle de backtick, aucune ligne ne peut tronquer."""
    payload = json.dumps({"body": body})
    with tempfile.NamedTemporaryFile(
        "w", suffix=".json", delete=False, encoding="ascii"
    ) as handle:
        handle.write(payload)
        payload_path = handle.name
    try:
        return gh_json(
            ["api", f"repos/{repo}/issues/{target}/comments", "--input", payload_path]
        )
    finally:
        Path(payload_path).unlink(missing_ok=True)


def post_post_guards(family: Family, published: str, body: str) -> list[str]:
    """gh-posting-hygiene regle 2 : les deux predicats, plus l'identite byte
    a byte avec la source -- un dossier mutate en route est un dossier faux."""
    failures: list[str] = []
    published_lines = published.splitlines()
    if not published_lines or published_lines[0].strip() != family.gate.START:
        first = published_lines[0][:80] if published_lines else "<empty>"
        failures.append(f"published line 1 is {first!r}, not {family.gate.START!r}")
    if len(published) < MIN_PUBLISHED_LEN:
        failures.append(
            f"published body is {len(published)} chars (< {MIN_PUBLISHED_LEN})"
        )
    try:
        maybe_payload = json.loads(published)
    except ValueError:
        maybe_payload = None
    if isinstance(maybe_payload, dict) and isinstance(maybe_payload.get("body"), str):
        failures.append(
            "PAYLOAD-TRAP: the whole JSON payload was published as the body "
            "(gh-posting-hygiene #17326)"
        )
    if published != body:
        failures.append("published body differs from the source file (byte identity broken)")
    return failures


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    target_group = parser.add_mutually_exclusive_group(required=True)
    target_group.add_argument("--pr", type=int, help="pull request carrying the dossier")
    target_group.add_argument("--issue", type=int, help="issue carrying the dossier")
    parser.add_argument("--file", required=True, type=Path, help="dossier body file")
    parser.add_argument(
        "--lane",
        required=True,
        help="emitting lane <machine:workspace> (anti-double-stamp, re-stamp licite)",
    )
    parser.add_argument("--repo", default=REPO)
    args = parser.parse_args(argv)

    family = ADJOINT if args.pr is not None else CLOSURE
    target = args.pr if args.pr is not None else args.issue
    body = args.file.read_text(encoding="utf-8")

    dossier, rc = preflight(family, body, args.lane)
    if rc != 0:
        return rc
    incoherent_rc = refuse_incoherent(family, dossier, target)
    if incoherent_rc is not None:
        return incoherent_rc

    if family is ADJOINT:
        current_head = gh_json(
            ["pr", "view", str(target), "--json", "headRefOid"]
        )["headRefOid"]
        stated_head = dossier.fields.get("head", "")
        if stated_head != current_head:
            return refuse(
                f"stale head: dossier says {stated_head[:12]}, PR head is "
                f"{current_head[:12]} -- recompute the dossier at the current head"
            )

    gate_rc, gate_stdout = run_gate(family, args.repo, target)
    if gate_rc == 2:
        return refuse(
            "gate returned UNKNOWN (rc 2): cannot prove that no intact dossier "
            "exists -- retry once the gate is readable"
        )
    if gate_rc in (0, 3):
        try:
            gate_payload = load_first_json(gate_stdout)
        except ValueError as exc:
            return refuse(f"gate rc {gate_rc} but its JSON is unreadable: {exc}")
        existing_lane = family.lane_of(gate_payload)
        if existing_lane and existing_lane != args.lane:
            # #19420 -- rc 3 (BLOCKED) admetre un re-stamp d'une lane tierce
            # si le dossier refute le dossier en place (supersedes + why).
            # rc 0 (READY) reste refuse : un second tampon n'ouvre pas une
            # guerre de dossiers, et le gate du dossier mute contradiction
            # (#18934) n'a rien a juger sans supersedes effectif.
            if gate_rc == 3:
                supersedes = dossier.fields.get("supersedes", "").strip()
                supersedes_why = dossier.fields.get("supersedes-why", "").strip()
                if supersedes and supersedes_why:
                    pass  # re-stamp tiers autorise sous refute explicite
                else:
                    return refuse(
                        f"anti-double-stamp: gate rc 3 with an intact dossier by "
                        f"lane {existing_lane!r} -- a re-stamp from {args.lane!r} "
                        "is licite only with non-empty 'supersedes' and "
                        "'supersedes-why' fields naming what is refuted (#19420)"
                    )
            else:
                return refuse(
                    f"anti-double-stamp: gate rc {gate_rc} with an intact dossier by "
                    f"lane {existing_lane!r} -- a re-stamp is licite only for its own lane"
                )

    comment = post_comment(args.repo, target, body)
    comment_id = comment.get("id")
    failures = post_post_guards(family, comment.get("body") or "", body)
    if failures:
        for failure in failures:
            print(f"  - {failure}", file=sys.stderr)
        print(
            f"REMEDIATION: PATCH comment {comment_id} with the true body "
            "(gh-posting-hygiene regle 3) -- do not repost blindly",
            file=sys.stderr,
        )
        return EXIT_REFUSED

    kind = "PR" if family is ADJOINT else "issue"
    print(f"POSTED -- comment {comment_id} on {kind} #{target}; re-running the gate:")
    return rerun_gate(family, args.repo, target)


if __name__ == "__main__":
    sys.exit(main())
