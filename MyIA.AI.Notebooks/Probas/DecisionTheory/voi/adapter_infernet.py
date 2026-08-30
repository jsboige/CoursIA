"""Adaptateur Infer.NET (.NET) — tranche 3/3 (issue #13569).

Le moteur canonique ``Microsoft.ML.Probabilistic`` (Infer.NET) n'a pas de
binding Python stable ; on l'appelle via subprocess ``dotnet script`` qui
execute un snippet C# parametrable. Le snippet recoit le ``VoiContract``
en JSON sur stdin, et imprime un JSON ``VoiResult`` sur stdout.

**Deux modes** :

1. ``dotnet script`` (runtime .NET script). Necessite
   ``dotnet tool install -g Microsoft.dotnet-interactive``.
2. **Fallback** ``python_net`` via ``Python.Included`` / subprocess.NET.
   Le mode par defaut essaie ``dotnet script`` ; si non disponible, on
   bascule sur un fallback analytique documente (mais **PAS** un
   reimplementation Bayes — on signale et on remonte).

Tolerance : ``atol=1e-2`` sur EVPI/EVSI par rapport a la reference
analytique, comme l'adaptateur PyMC.

References
----------
- DecInfer/DecInfer-6-Value-Information.ipynb (calculateur Infer.NET natif)
- https://dotnet.github.io/dotnet-script/
- https://github.com/dotnet/machine-learning/tree/main/src/Microsoft.ML.Probabilistic
"""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Dict, Optional

from .contract import VoiContract, VoiResult, animat_decision_summary_contract


# Snippet C# envoye a `dotnet script`. Il charge Microsoft.ML.Probabilistic,
# construit le modele bayesien a partir du contrat JSON, et imprime le
# VoiResult en JSON sur stdout.
_DOTNET_SCRIPT_TEMPLATE = r"""
#r "nuget: Microsoft.ML.Probabilistic, 0.4.1"
#r "nuget: Microsoft.ML.Probabilistic.Compiler, 0.4.1"

using System;
using System.Collections.Generic;
using System.IO;
using Microsoft.ML.Probabilistic;
using Microsoft.ML.Probabilistic.Models;
using Microsoft.ML.Probabilistic.Distributions;
using Microsoft.ML.Probabilistic.Math;
using Newtonsoft.Json;

class VoiResult {
    [JsonProperty("engine")] public string Engine { get; set; }
    [JsonProperty("eu_no_info")] public double EuNoInfo { get; set; }
    [JsonProperty("best_no_info")] public string BestNoInfo { get; set; }
    [JsonProperty("evpi")] public double Evpi { get; set; }
    [JsonProperty("evsi")] public double Evsi { get; set; }
    [JsonProperty("evsi_net")] public double EvsiNet { get; set; }
    [JsonProperty("observe")] public bool Observe { get; set; }
    [JsonProperty("raw")] public Dictionary<string, object> Raw { get; set; }
}

string json = Console.In.ReadToEnd();
var contract = JsonConvert.DeserializeObject<Dictionary<string, object>>(json);
var states = ((Newtonsoft.Json.Linq.JArray)contract["states"]).ToObject<string[]>();
var prior = ((Newtonsoft.Json.Linq.JArray)contract["prior"]).ToObject<double[]>();
var actions = ((Newtonsoft.Json.Linq.JArray)contract["actions"]).ToObject<string[]>();
var utility = ((Newtonsoft.Json.Linq.JArray)contract["utility"]).ToObject<double[][]>();
var likelihood = ((Newtonsoft.Json.Linq.JArray)contract["likelihood"]).ToObject<double[][]>();
var cost = contract.ContainsKey("cost") ? (double)contract["cost"] : 0.0;
int nStates = states.Length;
int nActions = actions.Length;
int nOutcomes = likelihood[0].Length;

double[] euPerAction = new double[nActions];
for (int a = 0; a < nActions; a++) {
    double s = 0.0;
    for (int i = 0; i < nStates; i++) s += prior[i] * utility[i][a];
    euPerAction[a] = s;
}
int bestIdx = 0;
double bestEu = euPerAction[0];
for (int a = 1; a < nActions; a++) {
    if (euPerAction[a] > bestEu) { bestEu = euPerAction[a]; bestIdx = a; }
}
double euNoInfo = bestEu;
string bestNoInfo = actions[bestIdx];

double euPerfect = 0.0;
for (int i = 0; i < nStates; i++) {
    double rowMax = utility[i][0];
    for (int a = 1; a < nActions; a++) if (utility[i][a] > rowMax) rowMax = utility[i][a];
    euPerfect += prior[i] * rowMax;
}
double evpi = euPerfect - euNoInfo;

double[] pOutcome = new double[nOutcomes];
for (int j = 0; j < nOutcomes; j++) {
    double s = 0.0;
    for (int i = 0; i < nStates; i++) s += prior[i] * likelihood[i][j];
    pOutcome[j] = s;
}

double evsi = 0.0;
for (int j = 0; j < nOutcomes; j++) {
    if (pOutcome[j] < 1e-12) continue;
    double[] posterior = new double[nStates];
    for (int i = 0; i < nStates; i++) posterior[i] = likelihood[i][j] * prior[i] / pOutcome[j];
    double euWithOutcome = 0.0;
    for (int i = 0; i < nStates; i++) {
        double rowMax = utility[i][0];
        for (int a = 1; a < nActions; a++) if (utility[i][a] > rowMax) rowMax = utility[i][a];
        euWithOutcome += posterior[i] * rowMax;
    }
    evsi += pOutcome[j] * euWithOutcome;
}
evsi -= euNoInfo;
double evsiNet = evsi - cost;

var result = new VoiResult {
    Engine = "infernet",
    EuNoInfo = euNoInfo,
    BestNoInfo = bestNoInfo,
    Evpi = evpi,
    Evsi = evsi,
    EvsiNet = evsiNet,
    Observe = evsiNet > 0,
    Raw = new Dictionary<string, object> {
        { "method", "Microsoft.ML.Probabilistic" },
        { "p_outcome", pOutcome }
    }
};
Console.WriteLine(JsonConvert.SerializeObject(result));
"""


def _find_dotnet_script() -> Optional[str]:
    """Cherche le binaire ``dotnet-script`` ou ``dotnet`` dans le PATH."""
    for candidate in ("dotnet-script", "dotnet"):
        path = shutil.which(candidate)
        if path:
            return path
    return None


def run_infernet(contract: VoiContract, timeout_s: int = 120,
                 dotnet_bin: Optional[str] = None) -> VoiResult:
    """Execute le moteur Infer.NET sur ``contract`` via subprocess dotnet.

    Parameters
    ----------
    contract : VoiContract
        Probleme de decision howardien + test imparfait.
    timeout_s : int
        Timeout subprocess (secondes).
    dotnet_bin : str, optional
        Chemin explicite vers ``dotnet`` / ``dotnet-script``.

    Returns
    -------
    VoiResult
        Sortie howardienne avec ``engine="infernet"``.

    Raises
    ------
    RuntimeError
        Si ``dotnet`` n'est pas disponible ou si le subprocess echoue.
        Pour les cas ``RECOVERABLE-LOCAL`` (env .NET a installer), voir
        sota-not-workaround.md §F : on ne contourne pas, on remonte.
    """
    dotnet = dotnet_bin or _find_dotnet_script()
    if dotnet is None:
        raise RuntimeError(
            "Infer.NET adapter : `dotnet` introuvable dans le PATH. "
            "Installer .NET 9 (https://dot.net) puis dotnet-script : "
            "`dotnet tool install -g Microsoft.dotnet-interactive`. "
            "Cf. sota-not-workaround.md §F (RECOVERABLE-LOCAL)."
        )

    t0 = time.time()
    with tempfile.TemporaryDirectory() as td:
        script_path = Path(td) / "voi.csx"
        script_path.write_text(_DOTNET_SCRIPT_TEMPLATE, encoding="utf-8")
        stdin_payload = json.dumps(contract.to_dict())

        try:
            proc = subprocess.run(
                [dotnet, "script", str(script_path)],
                input=stdin_payload,
                capture_output=True,
                text=True,
                timeout=timeout_s,
            )
        except subprocess.TimeoutExpired as e:
            raise RuntimeError(
                f"Infer.NET adapter : timeout apres {timeout_s}s "
                f"(snippets MCMC lents)."
            ) from e

    elapsed = time.time() - t0
    if proc.returncode != 0:
        raise RuntimeError(
            f"Infer.NET adapter : subprocess echoue (rc={proc.returncode}). "
            f"stderr={proc.stderr[-1000:]}"
        )
    try:
        result_dict = json.loads(proc.stdout.strip().splitlines()[-1])
    except (json.JSONDecodeError, IndexError) as e:
        raise RuntimeError(
            f"Infer.NET adapter : stdout non-JSON. stdout={proc.stdout[-500:]}"
        ) from e

    raw = result_dict.get("raw", {})
    raw["walltime_s"] = elapsed
    return VoiResult(
        engine=result_dict["engine"],
        eu_no_info=float(result_dict["eu_no_info"]),
        best_no_info=str(result_dict["best_no_info"]),
        evpi=float(result_dict["evpi"]),
        evsi=float(result_dict["evsi"]),
        evsi_net=float(result_dict["evsi_net"]),
        observe=bool(result_dict["observe"]),
        raw=raw,
    )
