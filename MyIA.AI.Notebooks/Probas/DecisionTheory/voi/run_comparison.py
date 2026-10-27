# Comparateur cross-engine VoI (tranche 3/3 #13569).
# Execute les DEUX adaptateurs sur chaque probleme du contrat, puis produit
# une table d'accord/desaccord LUE DANS LEURS SORTIES JSON -- jamais depuis
# des constantes. Verifie aussi les controls (discriminant, negatif) sur les
# valeurs mesurees de chaque moteur.
#
# Troisieme colonne (#22374) : la valeur EXACTE de l'organe Lean
# `Bayesian.InformationNoisy`, obtenue par conversion exacte du contrat
# (lean_bridge.py) et re-decidee par le kernel. Elle est comparee aux DEUX
# moteurs du banc, dans la meme tolerance du contrat.
#
# usage: python run_comparison.py [voi_dir] [--skip-dotnet-build]
#                                 [--skip-lean] [--lean-only]

import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lean_bridge  # noqa: E402

TOLERANCE = {
    "probability_abs": 0.01,
    "utility_abs": 20_000.0,
}
# Justification mesuree : Infer.NET (EP exact sur Bernoulli conjugue) rend les
# valeurs exactes ; PyMC echantillonne le meme modele generatif (200k draws,
# seed 42) -- l'ecart observe sur forage-petrolier est 204 EUR sur EVSI, la
# tolerance utility_abs couvre >10x ce bruit. Toute divergence au-dela est
# rapportee telle quelle, sans lissage.

NUMERIC_FIELDS = ["eu_no_info", "evpi", "evsi_brute", "evsi_nette"]
TEXT_FIELDS = ["action_no_info", "decision"]


def run_cmd(cmd, **kw):
    proc = subprocess.run(cmd, capture_output=True, text=True,
                          encoding="utf-8", errors="replace", **kw)
    if proc.returncode != 0:
        print(f"ECHEC {' '.join(str(c) for c in cmd)}\n{proc.stdout}\n{proc.stderr}",
              file=sys.stderr)
        sys.exit(2)
    return proc.stdout.strip()


def compare_problem(name, infer_out, pymc_out):
    rows = []
    agree = True
    for field in NUMERIC_FIELDS:
        a, b = infer_out[field], pymc_out[field]
        ok = abs(a - b) <= TOLERANCE["utility_abs"]
        agree &= ok
        rows.append((field, f"{a:.2f}", f"{b:.2f}", "accord" if ok else "DESACCORD"))
    for field in TEXT_FIELDS:
        a, b = infer_out[field], pymc_out[field]
        ok = a == b
        agree &= ok
        rows.append((field, a, b, "accord" if ok else "DESACCORD"))
    # Posteriors + marginales : probabilites
    for sig in infer_out["posteriors"]:
        for st in infer_out["posteriors"][sig]:
            a = infer_out["posteriors"][sig][st]
            b = pymc_out["posteriors"][sig][st]
            ok = abs(a - b) <= TOLERANCE["probability_abs"]
            agree &= ok
            rows.append((f"P({st}|{sig})", f"{a:.6f}", f"{b:.6f}",
                         "accord" if ok else "DESACCORD"))
    for sig in infer_out["signal_marginals"]:
        a = infer_out["signal_marginals"][sig]
        b = pymc_out["signal_marginals"][sig]
        ok = abs(a - b) <= TOLERANCE["probability_abs"]
        agree &= ok
        rows.append((f"P({sig})", f"{a:.6f}", f"{b:.6f}",
                     "accord" if ok else "DESACCORD"))
    return rows, agree


def check_controls(name, out):
    """Controls lus dans la sortie mesuree du moteur (jamais des constantes)."""
    checks = []
    if name.startswith("forage-petrolier"):
        ok = 0 < out["evsi_nette"] < out["evpi"]
        checks.append(("discriminant 0 < EVSI_nette < EVPI", ok,
                       f"nette={out['evsi_nette']:.0f} evpi={out['evpi']:.0f}"))
    if name.startswith("forage-non-informatif"):
        ok = abs(out["evsi_brute"]) <= TOLERANCE["utility_abs"]
        checks.append(("negatif |EVSI_brute| <= tolerance", ok,
                       f"brute={out['evsi_brute']:.2f}"))
    return checks


def run_lean_column(pb_path, infer_out, pymc_out):
    """Colonne Lean d'une instance : valeurs exactes, kernel, ecarts au banc.

    La conversion contrat -> organe est exacte (Fractions), les theoremes sont
    DECIDES par le kernel, et les ecarts aux deux moteurs sont rapportes dans
    la tolerance du contrat -- jamais lisses.
    """
    spec = lean_bridge.load_problem(pb_path)
    lean_out = lean_bridge.lean_values(spec)
    kernel = lean_bridge.run_lean_check(spec, caller="run-comparison")
    values = lean_bridge.as_json(lean_out)
    comparisons = {}
    for engine, out in (("infer_net", infer_out), ("pymc", pymc_out)):
        rows, agree = lean_bridge.compare_with_bench(lean_out, out, TOLERANCE["utility_abs"])
        comparisons[engine] = {
            "agree": agree,
            "rows": [dict(zip(("field", "lean", "bench", "verdict"), r)) for r in rows],
        }
    controls = [dict(zip(("label", "ok", "detail"), c))
                for c in check_controls(pb_path.stem, values)]
    return {"values": values, "kernel": kernel, "comparisons": comparisons,
            "controls": controls,
            "agree": all(c["agree"] for c in comparisons.values())}


def main(argv):
    flags = [a for a in argv[1:] if a.startswith("--")]
    rest = [a for a in argv[1:] if not a.startswith("--")]
    voi_dir = Path(rest[0]) if rest else Path(__file__).parent
    build = "--skip-dotnet-build" not in flags
    lean_only = "--lean-only" in flags
    lean_on = "--skip-lean" not in flags and lean_bridge.lean_toolchain_available()

    problems = sorted((voi_dir / "problems").glob("*.json"))
    if not problems:
        print("aucun probleme dans problems/", file=sys.stderr)
        return 2

    if "--skip-lean" not in flags and not lean_on:
        print("[INFO] colonne lean ABSENTE : toolchain introuvable "
              f"({lean_bridge.LEAN_EXEC} / {lean_bridge.LAKE_ROOT}) -- "
              "installer l'organe (regle F) ; la comparaison Lean n'est PAS blanchie",
              file=sys.stderr)
    if lean_only and not lean_on:
        print("--lean-only exige une toolchain Lean", file=sys.stderr)
        return 2

    comparison_path = voi_dir / "comparison.json"
    committed = {}
    if lean_only:
        if not comparison_path.exists():
            print("--lean-only exige un comparison.json existant", file=sys.stderr)
            return 2
        committed = json.loads(comparison_path.read_text(encoding="utf-8"))

    dll = voi_dir / "InferNetVoi" / "bin" / "Debug" / "net9.0" / "InferNetVoi.dll"
    if build and not lean_only:
        run_cmd(["dotnet", "build", str(voi_dir / "InferNetVoi" / "InferNetVoi.csproj"),
                 "-o", str(dll.parent)])

    all_ok = True
    report = {"tolerance": TOLERANCE, "problems": {}}
    for pb_path in problems:
        stem = pb_path.stem
        if lean_only:
            entry = committed.get("problems", {}).get(stem)
            if entry is None:
                print(f"[skip] {stem} absent de comparison.json", file=sys.stderr)
                continue
            infer_out = entry["outputs"]["infer_net"]
            pymc_out = entry["outputs"]["pymc"]
        else:
            infer_json = voi_dir / f"out_infer_net_{stem}.json"
            pymc_json = voi_dir / f"out_pymc_{stem}.json"
            run_cmd(["dotnet", str(dll), str(pb_path), str(infer_json)])
            run_cmd([sys.executable, str(voi_dir / "pymc_voi.py"),
                     str(pb_path), str(pymc_json)])
            infer_out = json.loads(infer_json.read_text(encoding="utf-8"))
            pymc_out = json.loads(pymc_json.read_text(encoding="utf-8"))

        rows, agree = compare_problem(stem, infer_out, pymc_out)
        controls = [("infer-net", c) for c in check_controls(stem, infer_out)] \
                 + [("pymc", c) for c in check_controls(stem, pymc_out)]
        controls_ok = all(c[1] for c in controls)

        lean = run_lean_column(pb_path, infer_out, pymc_out) if lean_on else None
        if lean is not None:
            all_ok &= lean["agree"] and all(c["ok"] for c in lean["controls"])
        all_ok &= agree and controls_ok

        print(f"\n=== {stem} ===")
        print(f"{'champ':<28} {'infer-net':>18} {'pymc':>18}  verdict")
        for field, a, b, verdict in rows:
            print(f"{field:<28} {a:>18} {b:>18}  {verdict}")
        for engine, (label, ok, detail) in controls:
            print(f"[{engine}] {label}: {'PASS' if ok else 'FAIL'} ({detail})")
        if lean is not None:
            for bench, blob in lean["comparisons"].items():
                for r in blob["rows"]:
                    print(f"  lean vs {bench:<10} {r['field']:<16} {r['lean']:>16} "
                          f"{r['bench']:>16}  {r['verdict']}")
            for c in lean["controls"]:
                print(f"[lean] {c['label']}: {'PASS' if c['ok'] else 'FAIL'} ({c['detail']})")
            print(f"[lean] kernel decide rc={lean['kernel']['rc']} "
                  f"(echelle p={lean['values']['scaled']['scale']})")
        report["problems"][stem] = {
            "agree": agree, "controls_ok": controls_ok,
            "rows": [dict(zip(("field", "infer_net", "pymc", "verdict"), r)) for r in rows],
            "outputs": {"infer_net": infer_out, "pymc": pymc_out},
        }
        if lean is not None:
            report["problems"][stem].update({
                "lean_agree": lean["agree"],
                "lean_controls_ok": all(c["ok"] for c in lean["controls"]),
                "lean_comparisons": lean["comparisons"],
                "kernel": lean["kernel"],
            })
            report["problems"][stem]["outputs"]["lean"] = lean["values"]

    (voi_dir / "comparison.json").write_text(
        json.dumps(report, indent=2), encoding="utf-8")
    print(f"\nVERDICT: {'ACCORD + CONTROLES PASS' if all_ok else 'DIVERGENCE OU CONTROLE FAIL'}"
          f" (tolerance utility_abs={TOLERANCE['utility_abs']:.0f}, "
          f"probability_abs={TOLERANCE['probability_abs']})"
          f"{', colonne lean incluse' if lean_on else ', colonne lean ABSENTE'}")
    return 0 if all_ok else 1



if __name__ == "__main__":
    sys.exit(main(sys.argv))
