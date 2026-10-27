# Pont Probas -> Lean pour la valeur de l'information bruitee (#22374).
#
# Le contrat VoI vit en probabilites decimales (problems/*.json) ; l'organe
# Lean `Bayesian.InformationNoisy` vit en poids joints ENTIERS non normalises
# (NoisyProblem). Ce pont fait la conversion EXACTE par Fractions -- jamais
# en flottant -- et produit un fichier de verification Lean autonome qui
# DECIDE (kernel, pas native_decide) les trois valeurs de chaque instance,
# plus les controles portees par le JSON (gain nul exact du signal non
# informatif, gain strict du test discriminant).
#
# Les trois valeurs du pont sont aussi calculees ici en miroir exact Python
# (entiers, meme arithmetique que les definitions Lean) : c'est la colonne
# "lean" du comparateur, rejetee par le kernel dans les tests.
#
# usage (module) : from lean_bridge import to_lean_problem, lean_values, ...
# usage (CLI)    : python lean_bridge.py problems/forage-petrolier.json [--run]

import json
import math
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

VOI_DIR = Path(__file__).resolve().parent
REPO_ROOT = VOI_DIR.parents[3]
LAKE_ROOT = REPO_ROOT / "MyIA.AI.Notebooks" / "GameTheory" / "lean_game_defs_ext"
LEAN_EXEC = REPO_ROOT / "scripts" / "lean" / "lean_exec.py"
LAKE_TMP = LAKE_ROOT / ".tmp"

# tolerance du contrat, identique a run_comparison.py (import croche evite :
# les deux fichiers doivent rester executables seuls)
TOLERANCE_UTILITY_ABS = 20_000.0

NUMERIC_FIELDS = ["eu_no_info", "evpi", "evsi_brute", "evsi_nette"]

SUM_EPS = 1e-9


class VoIContractError(Exception):
    """Rejet explicite d'une instance qui viole le contrat du pont.

    Le pont ne blanchit jamais une table invalide par un arrondi : chaque
    violation (poids negatif, colonne de vraisemblance != 1, utilitaire non
    entier, divergence kernel) leve cette exception avec le motif.
    """


def load_problem(path):
    """Charge une instance JSON du contrat."""
    return json.loads(Path(path).read_text(encoding="utf-8"))


def validate_problem(spec):
    """Valide le contrat AVANT toute conversion.

    Leve VoIContractError au premier poids invalide. Les tolerances de somme
    sont celles du contrat (1e-9) ; les utilitaires doivent etre entiers
    (l'organe Lean vit en Int).
    """
    states = spec.get("states") or []
    signals = spec.get("signals") or []
    actions = spec.get("actions") or []
    if not states or not signals or not actions:
        raise VoIContractError("states/signals/actions vides ou absents")

    priors = spec.get("priors", {})
    if set(priors) != set(states):
        raise VoIContractError(f"priors != states : {sorted(priors)} vs {sorted(states)}")
    for s in states:
        if float(priors[s]) < 0:
            raise VoIContractError(f"prior negatif pour {s} : {priors[s]}")
    if abs(sum(float(priors[s]) for s in states) - 1.0) > SUM_EPS:
        raise VoIContractError(
            f"priors ne somment pas a 1 : {sum(float(priors[s]) for s in states)}")

    likelihood = spec.get("likelihood", {})
    if set(likelihood) != set(signals):
        raise VoIContractError("likelihood != signals")
    for sig in signals:
        if set(likelihood[sig]) != set(states):
            raise VoIContractError(f"likelihood[{sig}] != states")
    for s in states:
        col = sum(float(likelihood[sig][s]) for sig in signals)
        if abs(col - 1.0) > SUM_EPS:
            raise VoIContractError(f"likelihood({s}) ne somme pas a 1 : {col}")
    for sig in signals:
        for s in states:
            if float(likelihood[sig][s]) < 0:
                raise VoIContractError(f"likelihood negatif {sig}/{s}")

    utilities = spec.get("utilities", {})
    if set(utilities) != set(actions):
        raise VoIContractError("utilities != actions")
    for a in actions:
        if set(utilities[a]) != set(states):
            raise VoIContractError(f"utilities[{a}] != states")
        for s in states:
            if Fraction(str(utilities[a][s])).denominator != 1:
                raise VoIContractError(
                    f"utilitaire non entier {a}/{s} : {utilities[a][s]} "
                    "(l'organe Lean vit en Int ; echelle des utilitaires non supportee)")
    return True


def to_lean_problem(spec):
    """Conversion EXACTE du contrat vers l'organe Lean.

    joint[s][x] = prior[s] * likelihood[x][s] en Fraction ; le denominateur
    commun minimal SCALE rend tous les poids entiers. Les utilitaires restent
    tels quels (entiers verifies). Renvoie un dict :

        {"nS", "nA", "nX", "p": [[int]], "u": [[int]], "scale": int,
         "states", "actions", "signals", "test_cost"}

    Les valeurs Lean de cette table sont sur l'echelle SCALE ; la division
    par SCALE (en Fraction) les ramene a l'echelle du contrat.
    """
    validate_problem(spec)
    states = spec["states"]
    actions = spec["actions"]
    signals = spec["signals"]

    joint = [[Fraction(str(spec["priors"][s])) * Fraction(str(spec["likelihood"][x][s]))
              for x in signals] for s in states]
    scale = 1
    for row in joint:
        for f in row:
            scale = scale * f.denominator // math.gcd(scale, f.denominator)
    p_int = [[int(f * scale) for f in row] for row in joint]
    u_int = [[int(Fraction(str(spec["utilities"][a][s]))) for a in actions] for s in states]

    return {
        "nS": len(states), "nA": len(actions) - 1, "nX": len(signals) - 1,
        "p": p_int, "u": u_int, "scale": scale,
        "states": states, "actions": actions, "signals": signals,
        "test_cost": spec["test_cost"],
    }


def lean_values(spec):
    """Miroir Python EXACT des trois definitions Lean, sur la table scalee.

    valueNoisyNoInfo  = max_a  sum_s priorMass[s] * u[s][a]
    valueNoisySignal  = sum_x  max_a  sum_s p[s][x] * u[s][a]
    valueNoisyPerfect = sum_s  max_a  priorMass[s] * u[s][a]

    Renvoie les valeurs ENTIERS sur l'echelle SCALE plus les grandeurs du
    contrat (divisions exactes en Fraction, test_cost en euros).
    """
    tab = to_lean_problem(spec)
    p, u = tab["p"], tab["u"]
    n_s, n_a, n_x = tab["nS"], tab["nA"], tab["nX"]
    scale = Fraction(tab["scale"])

    prior = [sum(p[s][x] for x in range(n_x + 1)) for s in range(n_s)]
    v_no_info = max(sum(prior[s] * u[s][a] for s in range(n_s)) for a in range(n_a + 1))
    v_signal = sum(max(sum(p[s][x] * u[s][a] for s in range(n_s))
                       for a in range(n_a + 1)) for x in range(n_x + 1))
    v_perfect = sum(max(prior[s] * u[s][a] for a in range(n_a + 1))
                    for s in range(n_s))

    evsi_brute = Fraction(v_signal - v_no_info, 1) / scale
    evpi = Fraction(v_perfect - v_no_info, 1) / scale
    evsi_nette = evsi_brute - Fraction(str(tab["test_cost"]))
    out = {
        "engine": "lean",
        "eu_no_info": Fraction(v_no_info, 1) / scale,
        "evpi": evpi,
        "evsi_brute": evsi_brute,
        "evsi_nette": evsi_nette,
        "decision": "observer" if evsi_nette > 0 else "agir_sans_test",
        # valeurs entieres brutes, pour le fichier de verification
        "_scaled": {"no_info": v_no_info, "signal": v_signal, "perfect": v_perfect,
                    "scale": tab["scale"]},
    }
    return out


def as_json(lean_out):
    """Vue JSON-safe (floats) des valeurs du pont.

    Les Fractions sont exactes pour le calcul mais ne se serialisent pas :
    la colonne committee les porte en float, les valeurs ENTIERES scalaires
    restant disponibles sous "scaled" (elles, exactes).
    """
    out = {"engine": lean_out["engine"], "decision": lean_out["decision"]}
    for field in NUMERIC_FIELDS:
        out[field] = float(lean_out[field])
    out["scaled"] = dict(lean_out["_scaled"])
    return out


def _table_literal(rows, outer, inner):
    """Table 2D en litteral Lean : fun {outer} {inner} => if-chains imbriques.

    Genere pour toute taille (y compris 1x1) ; les valeurs negatives de u
    deviennent des litteraux Int valides.
    """
    n_i = len(rows)
    n_j = len(rows[0])
    body = _if_chain(
        n_i,
        lambda i: f"({_if_chain(n_j, lambda j: str(rows[i][j]), inner)})",
        outer)
    return f"fun {outer} {inner} => {body}"


def _if_chain(n, render, var):
    """Corps de la chaine : if {var}.val = 0 then ... else if ... then ... else ..."""
    parts = []
    for k in range(n - 1):
        parts.append(f"if {var}.val = {k} then {render(k)} else ")
    parts.append(f"{render(n - 1)}")
    return "".join(parts)


def emit_lean_check(spec, out_path):
    """Ecrit le fichier de verification Lean d'une instance.

    Le fichier importe l'organe, declare la table scalee, puis DECIDE les
    trois valeurs exactes. Les controles du JSON deviennent des theoremes :
    "negative" -> egalite EXACTE no_info = signal (gain nul, pas proche de
    zero) ; "discriminant" -> inegalite stricte no_info < signal <= perfect.
    Jamais de native_decide, jamais de sorry.
    """
    tab = to_lean_problem(spec)
    vals = lean_values(spec)["_scaled"]
    name = spec["problem"]

    p_lit = _table_literal(tab["p"], "s", "x")
    u_lit = _table_literal(tab["u"], "s", "a")

    lines = [
        "import Bayesian.InformationNoisy",
        "",
        f"/-- Instance `{name}` convertie exactement depuis le contrat JSON",
        f"    par lean_bridge.py : poids joints x{vals['scale']} (denominateur",
        "    commun minimal via Fractions), utilitaires entiers inchanges.",
        "    Genere automatiquement -- ne pas editer a la main. -/",
        f"def pb : NoisyProblem where",
        f"  nS := {tab['nS']}",
        f"  nA := {tab['nA']}",
        f"  nX := {tab['nX']}",
        f"  p := {p_lit}",
        f"  u := {u_lit}",
        "",
        f"theorem pb_valueNoisyNoInfo : valueNoisyNoInfo pb = {vals['no_info']} := by decide",
        f"theorem pb_valueNoisySignal : valueNoisySignal pb = {vals['signal']} := by decide",
        f"theorem pb_valueNoisyPerfect : valueNoisyPerfect pb = {vals['perfect']} := by decide",
    ]
    # Les theoremes de controle portent ce que les valeurs EXACTES supportent :
    # le kernel re-evalue valueNoisy* contre le litteral, donc une divergence
    # du miroir Python ferait echouer `decide` -- c'est le controle.
    full = lean_values(spec)
    gain_zero = vals["no_info"] == vals["signal"]
    strict = vals["no_info"] < vals["signal"]
    controls = spec.get("expected_controls", {})

    # enforcement des controles DECLARES par le JSON
    if set(controls) == {"negative"} and not gain_zero:
        raise VoIContractError(
            f"{name} declare un controle negatif (gain nul exact) mais ses valeurs "
            f"montrent un gain {float(full['evsi_brute']):.2f} : instance incoherente")
    if "discriminant" in controls:
        if not strict or not (0 < float(full["evsi_nette"]) < float(full["evpi"])):
            raise VoIContractError(
                f"{name} declare un controle discriminant mais les valeurs ne le "
                f"portent pas (nette={float(full['evsi_nette']):.2f}, "
                f"evpi={float(full['evpi']):.2f})")

    if gain_zero:
        lines.append(
            "theorem pb_zero_gain : valueNoisyNoInfo pb = valueNoisySignal pb := by decide")
    if strict:
        lines.append(
            "theorem pb_strict_gain : valueNoisyNoInfo pb < valueNoisySignal pb := by decide")
        lines.append(
            "theorem pb_signal_le_perfect :"
            " valueNoisySignal pb ≤ valueNoisyPerfect pb := by decide")
    text = "\n".join(lines) + "\n"
    for bad in ("native_decide", "sorry"):
        if bad in text:
            raise VoIContractError(f"emission interdite : {bad} dans le fichier genere")
    Path(out_path).write_text(text, encoding="utf-8")
    return Path(out_path)


def lean_toolchain_available():
    """True si l'organe lean_exec et le lake sont presents sur la machine."""
    return LEAN_EXEC.is_file() and (LAKE_ROOT / "lakefile.toml").is_file()


def run_lean_check(spec, caller="lean-bridge", keep=False):
    """Emet puis rejoue le fichier de verification par le kernel Lean.

    Passe par l'organe scripts/lean/lean_exec.py (budget, detachement) ;
    rc=0 = toutes les theoremes decides par le kernel. Leve VoIContractError
    sur echec kernel OU toolchain absente (jamais de blanchiment silencieux).
    """
    if not lean_toolchain_available():
        raise VoIContractError(
            "toolchain Lean absente (lake ou lean_exec introuvable) : "
            "verification kernel impossible -- installer l'organe (regle F), "
            "ne pas sauter le controle")
    LAKE_TMP.mkdir(exist_ok=True)
    stem = spec["problem"]
    check_path = LAKE_TMP / f"check_{stem}.lean"
    emit_lean_check(spec, check_path)
    rel = check_path.relative_to(LAKE_ROOT).as_posix()

    stdout_f = LAKE_TMP / f"check_{stem}.out"
    stderr_f = LAKE_TMP / f"check_{stem}.err"
    cmd = [sys.executable, str(LEAN_EXEC), "run", "--backend", "native",
           "--caller", caller, "--cwd", str(LAKE_ROOT), "--wait", "0",
           "--budget", "4", "--stdout-file", str(stdout_f),
           "--stderr-file", str(stderr_f), "--",
           "lake", "env", "lean", rel]
    proc = subprocess.run(cmd, capture_output=True, text=True,
                          encoding="utf-8", errors="replace")
    out = (stdout_f.read_text(encoding="utf-8", errors="replace") if stdout_f.exists() else "")
    err = (stderr_f.read_text(encoding="utf-8", errors="replace") if stderr_f.exists() else "")
    if proc.returncode != 0:
        raise VoIContractError(
            f"kernel Lean REJETTE {stem} (rc={proc.returncode}):\n{out[-2000:]}\n{err[-2000:]}")
    if not keep:
        for f in (stdout_f, stderr_f):
            if f.exists():
                f.unlink()
    return {"stem": stem, "kernel": "decide", "rc": 0}


def compare_with_bench(lean_out, bench_out, tolerance=TOLERANCE_UTILITY_ABS):
    """Compare la colonne lean aux sorties mesurees d'un moteur du banc.

    Renvoie (rows, agree) ; une divergence au-dela de la tolerance est
    rapportee telle quelle, jamais lissee.
    """
    rows = []
    agree = True
    for field in NUMERIC_FIELDS:
        a = float(lean_out[field])
        b = float(bench_out[field])
        ok = abs(a - b) <= tolerance
        agree &= ok
        rows.append((field, f"{a:.2f}", f"{b:.2f}", "accord" if ok else "DESACCORD"))
    da = lean_out["decision"]
    db = bench_out["decision"]
    ok = da == db
    agree &= ok
    rows.append(("decision", da, db, "accord" if ok else "DESACCORD"))
    return rows, agree


def main(argv):
    if len(argv) < 2:
        print("usage: python lean_bridge.py problems/<instance>.json [--run]", file=sys.stderr)
        return 2
    spec = load_problem(argv[1])
    tab = to_lean_problem(spec)
    out = lean_values(spec)
    print(f"scale={tab['scale']} p={tab['p']}")
    for field in NUMERIC_FIELDS:
        print(f"{field:>12} = {float(out[field]):.2f}")
    print(f"    decision = {out['decision']}")
    if "--run" in argv:
        print(run_lean_check(spec))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
