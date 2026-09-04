"""Diagnostic a controle positif du REPL lean4-wsl (#11874).

Contexte : le kernel Jupyter lean4-wsl lance `lake env repl` (via le wrapper
~/.lean4-kernel-wrapper.py). Le mecanisme de casse documente sur #11874
(ai-01, experience controlee) : le binaire `repl` ne trouve sa stdlib QUE si le
toolchain RESOLU par le cwd correspond a sa version de compilation — un repl
compile pour v4.30.0 dans un environnement resolu v4.32.1 rend
`Unknown constant OfNat` sur le controle le plus elementaire possible
(`#eval 2+2`), et les imports impossibles rendent `{"env": N}` MUET
(aucun message d'erreur) — une sonde sans controle positif lit un kernel mort
comme un kernel silencieux. Le health-check du kernel lui-meme
(`#eval Lean.versionString` sans controle du resultat) ne detecte rien.

Cet outil execute la recette a controle positif du body de #11874 et rend un
verdict executable sur toute machine du cluster :

  REPL_HEALTHY          tous les controles positifs passent sur tous les chemins
  REPL_LAKE_ONLY        repl via lake OK, repl nu KO (etat latent typique :
                        le kernel marche tant que le cwd est un lake matchant ;
                        le fallback stub et /tmp sont casses)
  REPL_STDLIB_BROKEN    meme via lake, le controle positif echoue (mismatch
                        toolchain binaire/toolchain resolu) — kernel inutilisable
  REPL_MISSING          binaire repl introuvable
  REPL_TIMEOUT          le repl ne repond pas dans le delai

Sondes par chemin (chaque chemin = un process repl frais) :
  1. controle positif   : `#eval 2+2` (env null) -> doit rendre "4"
  2. import bidon       : `import Totally.Bogus.Xyz` -> doit ERREUR (une
                          reponse muette {"env": N} sans message = ENV_ID_MUTE,
                          danger documente, non bloquant en soi)
  3. version toolchain  : lit lean-toolchain du cwd quand present

Usage :
  python scripts/notebook_tools/check_lean4_wsl_repl.py                     # repl nu + stub + lakes par defaut
  python scripts/notebook_tools/check_lean4_wsl_repl.py --lake ~/proj/mon_lake
  python scripts/notebook_tools/check_lean4_wsl_repl.py --json              # sortie machine-lisible
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys

WSL_DISTRO = "Ubuntu"
WSL_PREFIX = ["wsl.exe", "-d", WSL_DISTRO, "--"]
PROBE_TIMEOUT = 90
STUB_DIR = "~/lean-projects/notebook_context"
BOGUS_IMPORT = "Totally.Bogus.Xyz"

# Reponses du protocole REPL : les commandes sont separees par une ligne vide
# (double \n) ; le repl rend un JSON par commande sur stdin puis EOF.


def wsl_bash(cmd: str, timeout: int = PROBE_TIMEOUT) -> tuple[int, str]:
    """Execute une commande bash dans WSL, rend (exit_code, stdout+stderr)."""
    proc = subprocess.run(
        WSL_PREFIX + ["bash", "-lc", cmd],
        capture_output=True, text=True, timeout=timeout, encoding="utf-8", errors="replace",
    )
    return proc.returncode, (proc.stdout or "") + (proc.stderr or "")


def spawn_repl(cwd: str | None, repl_cmd: str, payload: str) -> tuple[str, str]:
    """Lance le repl via bash -lc, injecte payload, rend (stdout+stderr, meta).

    Le cd doit se produire AVANT le pipeline : `timeout` ne peut pas executer
    le builtin `cd` (exit 125 silencieux -> sonde vide).
    """
    prefix = f"cd {cwd} && " if cwd else ""
    cmd = f'{prefix}printf {json.dumps(payload)} | timeout {PROBE_TIMEOUT} {repl_cmd}'
    returncode, out = wsl_bash(cmd)
    return out, f"exit={returncode}"


def parse_repl_json(raw: str) -> dict | None:
    """Extrait le premier objet JSON de la sortie brute du repl."""
    m = re.search(r"\{.*\}", raw, re.DOTALL)
    if not m:
        return None
    try:
        return json.loads(m.group(0))
    except json.JSONDecodeError:
        return None


def probe_path(cwd: str | None, repl_cmd: str, label: str, toolchain: str | None) -> dict:
    """Sonde un chemin d'execution du repl : controle positif + import bidon."""
    result = {"label": label, "cwd": cwd, "repl_cmd": repl_cmd, "toolchain": toolchain,
              "positive": None, "positive_data": None, "bogus_mute": None}
    # 1. controle positif : #eval 2+2 -> "4"
    payload = '{"cmd": "#eval 2+2", "env": null}\n\n'
    raw, meta = spawn_repl(cwd, repl_cmd, payload)
    parsed = parse_repl_json(raw)
    if parsed is None:
        result["positive"] = "TIMEOUT_OR_UNPARSEABLE"
        result["positive_data"] = (raw or "")[:200]
        return result
    messages = parsed.get("messages", [])
    if any("4" == (m.get("data") or "").strip() for m in messages):
        result["positive"] = "OK"
    elif any("Unknown constant" in (m.get("data") or "") for m in messages):
        result["positive"] = "STDLIB_BROKEN"
        result["positive_data"] = messages[0].get("data", "")[:120]
    else:
        result["positive"] = "OTHER"
        result["positive_data"] = json.dumps(messages[:1], ensure_ascii=False)[:200]
    # 2. import bidon : doit ERREUR ; reponse muette = danger documente
    payload = f'{{"cmd": "import {BOGUS_IMPORT}", "env": null}}\n\n'
    raw, _ = spawn_repl(cwd, repl_cmd, payload)
    parsed = parse_repl_json(raw)
    if parsed is not None:
        has_error = any((m.get("severity") == "error") for m in parsed.get("messages", []))
        # muet = reponse valide SANS message d'erreur alors que l'import est impossible
        result["bogus_mute"] = (not has_error) and ("env" in parsed)
    return result


def read_toolchain(dir_wsl: str) -> str | None:
    rc, out = wsl_bash(f'cat {dir_wsl}/lean-toolchain 2>/dev/null')
    return out.strip() if rc == 0 and out.strip() else None


def classify(results: list[dict]) -> tuple[str, str]:
    """Verdict global a partir des sondes. Fonction pure (testee unitairement)."""
    if not results:
        return "REPL_MISSING", "aucune sonde executable (repl introuvable ?)"
    positives = [r["positive"] for r in results]
    if all(p == "OK" for p in positives):
        notes = [r["label"] for r in results if r.get("bogus_mute")]
        mute_note = f" ; import bidon MUET sur {', '.join(notes)} (danger documente, cf #11874)" if notes else ""
        return "REPL_HEALTHY", "controle positif OK sur tous les chemins" + mute_note
    lake_ok = [r for r in results if r["label"] == "lake" and r["positive"] == "OK"]
    broken = [r for r in results if r["positive"] == "STDLIB_BROKEN"]
    if lake_ok and broken and not all(r["positive"] == "STDLIB_BROKEN" for r in results):
        return ("REPL_LAKE_ONLY",
                f"repl via lake OK ({lake_ok[0]['toolchain']}), repl nu casse ({', '.join(r['label'] for r in broken)}) "
                "— mismatch toolchain binaire/toolchain resolu (cf #11874) ; le kernel ne marche que dans un lake matchant")
    if broken:
        return ("REPL_STDLIB_BROKEN",
                f"controle positif #eval 2+2 echoue partout : {', '.join(r['label'] + '->' + str(r['positive_data'])[:60] for r in broken)}")
    if all(p in ("TIMEOUT_OR_UNPARSEABLE",) for p in positives):
        return "REPL_TIMEOUT", "aucune reponse parsable du repl sur aucun chemin"
    return "REPL_UNCERTAIN", f"sondes heterogenes : {positives}"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--lake", action="append", default=[],
                    help="lake a sonder via `lake env repl` (repeter pour plusieurs)")
    ap.add_argument("--skip-stub", action="store_true",
                    help="ne pas sonder le stub fallback ~/lean-projects/notebook_context")
    ap.add_argument("--json", action="store_true", help="sortie JSON machine-lisible")
    args = ap.parse_args()

    # repl nu (PATH) depuis /tmp : le chemin d'un kernel sans lake
    rc, which = wsl_bash("which repl")
    results = []
    if rc == 0 and which.strip():
        results.append(probe_path("/tmp", "repl", "bare_path_tmp", None))
    else:
        print("WARN : binaire repl introuvable sur le PATH WSL", file=sys.stderr)

    # stub fallback du wrapper
    if not args.skip_stub:
        rc, _ = wsl_bash(f"test -d {STUB_DIR}")
        if rc == 0:
            results.append(probe_path(
                STUB_DIR, "repl", "stub_fallback", read_toolchain(STUB_DIR)))

    # lakes explicites + lakes par defaut du miroir
    lakes = list(args.lake) or ["~/lean-projects/mimo_lean"]
    for lake in lakes:
        rc, _ = wsl_bash(f"test -f {lake}/lakefile.lean -o -f {lake}/lakefile.toml")
        if rc == 0:
            results.append(probe_path(
                lake, "lake env repl", "lake", read_toolchain(lake)))
        else:
            print(f"WARN : lake introuvable : {lake}", file=sys.stderr)

    verdict, detail = classify(results)
    report = {"verdict": verdict, "detail": detail, "probes": results}

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=1))
    else:
        print(f"VERDICT : {verdict}")
        print(f"  {detail}")
        for r in results:
            print(f"  [{r['label']:14s}] toolchain={r.get('toolchain') or '-':24s} "
                  f"positif={r['positive']:22s} bidon_muet={r.get('bogus_mute')}")
    # exit codes : 0 sain/lake-only (etat documente), 1 casse, 2 incertain
    return 0 if verdict in ("REPL_HEALTHY", "REPL_LAKE_ONLY") else (1 if verdict == "REPL_STDLIB_BROKEN" else 2)


if __name__ == "__main__":
    sys.exit(main())
