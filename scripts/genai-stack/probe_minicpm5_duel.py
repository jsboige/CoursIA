#!/usr/bin/env python3
"""Probe A (issue #15099) : duel MiniCPM5-2B vs Qwen3-4B sur banc fixe local.

Deux jambes sequentielles sur le meme GPU (vLLM, OpenAI-compatible), memes
70 prompts (banc fixe probe_15099_bench.json), meme sampling (temperature=1.0,
top_p=0.95, seed fixe par requete). Metriques :
  - score par axe (Q&A pedagogique FR / math / code-gen), echelle 0-2 ;
  - math : comparaison deterministe au golden (fallback correcteur tiers) ;
  - code : execution reelle des tests du banc (deterministe, pas d'opinion) ;
  - Q&A : correcteur tiers AVEUGLE (ne voit jamais le nom du modele evalue) ;
  - tokens/s : usage completion / temps de requete, generation sequentielle ;
  - VRAM : empreinte poids bf16 mesuree sur disque (somme safetensors).

Correcteur : passerelle claudish models.myia.io (facade OpenAI-compatible,
cle CLAUDISH_PROXY_KEY via .secrets/master.env), fallback OpenRouter
(OPENROUTER_API_KEY). Aucun secret en dur, aucune valeur de cle affichee.

Verdict (acceptance issue) : parite (>= 0.95 x Qwen) sur >= 2 axes/3,
OU parite globale avec win >= 30 % sur VRAM poids ou tokens/s.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.request
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
BENCH_PATH = SCRIPT_DIR / "probe_15099_bench.json"
MASTER_ENV = Path(__file__).resolve().parents[2] / ".secrets" / "master.env"
DEFAULT_PORT = 8199  # 8185 = serveur Qwen permanent de la flotte, ne pas toucher
DEFAULT_GPU = 1  # RTX 3090 (GPU 0 = RTX 5080 occupee par la stack GenAI)
PARITY_RATIO = 0.95
WIN_RATIO = 0.30

ENV_KEYS_NEEDED = ("CLAUDISH_PROXY_KEY", "OPENROUTER_API_KEY")


# ---------------------------------------------------------------- utilitaires

def load_master_env(keys: tuple[str, ...]) -> dict[str, str]:
    """Charge les cles demandees depuis .secrets/master.env (KEY=VALUE).
    Ne retourne jamais les valeurs a l'ecran ; l'appelant les met dans os.environ.
    """
    found: dict[str, str] = {}
    if not MASTER_ENV.is_file():
        return found
    for line in MASTER_ENV.read_text(encoding="utf-8", errors="replace").splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        k, _, v = line.partition("=")
        k = k.strip()
        if k in keys:
            v = v.strip().strip('"').strip("'")
            if v:
                found[k] = v
    return found


def http_post_json(url: str, payload: dict, headers: dict, timeout: float) -> dict:
    body = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(url, data=body, method="POST")
    for k, v in headers.items():
        req.add_header(k, v)
    req.add_header("Content-Type", "application/json")
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return json.loads(resp.read().decode("utf-8"))


def http_get_ok(url: str, timeout: float = 5.0) -> bool:
    try:
        with urllib.request.urlopen(url, timeout=timeout) as resp:
            return resp.status == 200
    except (urllib.error.URLError, TimeoutError, OSError):
        return False


def now_utc() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def gpu_vram_mib(gpu_index: int) -> int | None:
    out = subprocess.run(
        ["nvidia-smi", f"--query-gpu=memory.used", "--format=csv,noheader,nounits",
         "-i", str(gpu_index)],
        capture_output=True, text=True, timeout=15,
    )
    if out.returncode != 0:
        return None
    try:
        return int(out.stdout.strip().splitlines()[0])
    except (ValueError, IndexError):
        return None


class VramMonitor(threading.Thread):
    """Echantillonne la VRAM du GPU pendant toute la vie d'une jambe."""

    def __init__(self, gpu_index: int, poll_s: float = 1.0):
        super().__init__(daemon=True)
        self.gpu_index = gpu_index
        self.poll_s = poll_s
        self._stop = threading.Event()
        self.baseline_mib: int | None = None
        self.peak_mib: int | None = None

    def run(self) -> None:
        self.baseline_mib = gpu_vram_mib(self.gpu_index)
        self.peak_mib = self.baseline_mib
        while not self._stop.is_set():
            v = gpu_vram_mib(self.gpu_index)
            if v is not None and (self.peak_mib is None or v > self.peak_mib):
                self.peak_mib = v
            self._stop.wait(self.poll_s)

    def stop(self) -> None:
        self._stop.set()
        self.join(timeout=5)


def weights_bytes_on_disk(model_path: Path) -> int:
    """Somme des octets des fichiers safetensors du modele (empreinte poids reellement
    servie, bf16). Mesure disque, byte-exact, reproductible."""
    total = 0
    for f in sorted(model_path.rglob("*.safetensors")):
        total += f.stat().st_size
    return total


def chat_template_present(model_path: Path) -> bool:
    """Pre-flight : le template de chat doit venir du snapshot — soit embarque dans
    tokenizer_config.json, soit en fichier separe chat_template.jinja (convention
    recente, cas MiniCPM5) — jamais du README du repo HF (contenu externe non
    fiable, cf issue #15099)."""
    jinja = model_path / "chat_template.jinja"
    if jinja.is_file() and jinja.stat().st_size > 0:
        return True
    cfg = model_path / "tokenizer_config.json"
    if not cfg.is_file():
        return False
    try:
        data = json.loads(cfg.read_text(encoding="utf-8", errors="replace"))
    except json.JSONDecodeError:
        return False
    return bool(data.get("chat_template"))


# ---------------------------------------------------------------- generation

@dataclass
class OneResponse:
    item_id: str
    axis: str
    text: str = ""
    prompt_tokens: int = 0
    completion_tokens: int = 0
    wall_s: float = 0.0
    error: str = ""


def chat_completion(port: int, model_name: str, question: str, max_tokens: int,
                    sampling: dict, extra_body: dict | None = None,
                    timeout: float = 180.0) -> OneResponse:
    payload: dict = {
        "model": model_name,
        "messages": [{"role": "user", "content": question}],
        "temperature": sampling["temperature"],
        "top_p": sampling["top_p"],
        "seed": sampling["seed"],
        "max_tokens": max_tokens,
    }
    if extra_body:
        payload.update(extra_body)
    t0 = time.perf_counter()
    try:
        data = http_post_json(
            f"http://127.0.0.1:{port}/v1/chat/completions", payload, {}, timeout)
    except Exception as exc:  # noqa: BLE001 - erreur reseau = reponse vide tracee
        return OneResponse("", "", "", wall_s=time.perf_counter() - t0,
                           error=f"{type(exc).__name__}: {exc}")
    wall = time.perf_counter() - t0
    try:
        msg = data["choices"][0]["message"]
        content = msg.get("content") or ""
        reasoning = msg.get("reasoning_content")
        if reasoning and not content:
            return OneResponse("", "", "", wall_s=wall,
                               error="reasoning_only_empty_content")
        usage = data.get("usage") or {}
        return OneResponse(
            "", "", content,
            prompt_tokens=int(usage.get("prompt_tokens") or 0),
            completion_tokens=int(usage.get("completion_tokens") or 0),
            wall_s=wall,
        )
    except (KeyError, IndexError, TypeError) as exc:
        return OneResponse("", "", "", wall_s=wall, error=f"bad_payload: {exc}")


# ---------------------------------------------------------------- verification

_NUM_RE = re.compile(r"-?\d[\d\s]*(?:[.,]\d+)?")
_FRAC_RE = re.compile(r"(-?\d+)\s*/\s*(\d+)")


def _norm_number_txt(s: str) -> str:
    return s.replace("\u00a0", " ").replace(",", ".").strip()


def check_math(golden: str, text: str) -> int | None:
    """2 = golden retrouve (nombre pur normalise, ou golden composite en
    sous-chaine), None = indetermine -> correcteur. On ne cherche que dans les
    ~600 derniers caracteres (la reponse utile est rarement noyee avant)."""
    tail = _norm_number_txt(text[-600:])
    g = _norm_number_txt(golden)
    if re.fullmatch(r"-?\d+(?:[.,]\d+)?(?:\s*/\s*-?\d+)?", g):
        # golden = nombre pur ou fraction
        if "/" in g:
            m = _FRAC_RE.search(g)
            if m:
                a, b = int(m.group(1)), int(m.group(2))
                for fm in _FRAC_RE.finditer(tail):
                    if int(fm.group(1)) == a and int(fm.group(2)) == b:
                        return 2
                return None  # pas retrouvee mot-a-mot : le correcteur tranche
        gnum = g.replace(" ", "")
        for m in _NUM_RE.finditer(tail):
            if m.group(0).replace(" ", "") == gnum:
                return 2
        try:  # arrondi proche (ex. 61.2 vs 61.20), tolerance relative 1e-6
            gt = float(gnum)
            for m in _NUM_RE.finditer(tail):
                v = float(m.group(0).replace(" ", ""))
                if abs(v - gt) <= max(1e-6, abs(gt) * 1e-6):
                    return 2
        except ValueError:
            pass
        return None
    # golden composite ("x=4, y=2", "-4 pourcent") : sous-chaine normalisee,
    # sinon indetermine (le modele peut formater autrement) -> correcteur
    if g.lower() in tail.lower():
        return 2
    return None


def extract_code(text: str) -> str:
    fence = re.search(r"```(?:python)?\s*\n(.*?)```", text, re.DOTALL)
    if fence:
        return fence.group(1).strip()
    return text.strip()


def check_code(item: dict, text: str) -> int:
    """2 = tous les tests passent ; 1 = code valide + au moins un test ;
    0 = ne compile pas / aucun test. Execution reelle, isolee, sans reseau."""
    code = extract_code(text)
    if not code or "def " not in code:
        return 0
    fn_name = re.search(r"def\s+([A-Za-z_]\w*)", code)
    if not fn_name:
        return 0
    ns: dict = {}
    import io, contextlib  # noqa: PLC0415 - isolation locale volontaire
    buf = io.StringIO()
    try:
        with contextlib.redirect_stdout(buf):
            exec(compile(code, "<gen>", "exec"), ns)  # noqa: S102 - banc ferme, pas d'input externe
    except Exception:  # noqa: BLE001 - code genere : toute erreur = echec
        return 0
    tests = item.get("tests") or []
    if not tests:
        return 1
    passed = 0
    for t in tests:
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                r = eval(compile(t, "<test>", "eval"), ns)  # noqa: S307
            if r:
                passed += 1
        except Exception:  # noqa: BLE001
            continue
    if passed == len(tests):
        return 2
    if passed >= 1:
        return 1
    return 0


# ---------------------------------------------------------------- correcteur

CORRECTOR_SYSTEM = (
    "Tu es un correcteur strict et impartial. On te donne une question, un "
    "critere de reussite, et la reponse d'un modele. Note sur 0, 1, 2 :\n"
    "2 = reussite complete (tous les points attendus / resultat exact) ;\n"
    "1 = reussite partielle (bonne approche, elements manquants ou erreur mineure) ;\n"
    "0 = faux, hors-sujet, vide ou refuse.\n"
    "Reponds UNIQUEMENT avec un objet JSON : {\"score\": <0|1|2>, \"raison\": \"<20 mots max>\"}."
)


def corrector_score(question: str, criterion: str, answer: str, cfg: dict) -> int | None:
    payload = {
        "model": cfg["model"],
        "temperature": 0.0,
        "max_tokens": 200,
        "messages": [
            {"role": "system", "content": CORRECTOR_SYSTEM},
            {"role": "user",
             "content": f"QUESTION :\n{question}\n\nCRITERE DE REUSSITE :\n{criterion}\n\n"
                        f"REPONSE A EVALUER :\n{answer[:4000]}"},
        ],
    }
    for attempt, (base, key) in enumerate(cfg["endpoints"]):
        for _ in range(2):  # 1 retry par endpoint sur erreur transitoire
            try:
                data = http_post_json(
                    base, payload, {"Authorization": f"Bearer {key}"}, timeout=90)
                txt = (data["choices"][0]["message"].get("content") or "").strip()
                m = re.search(r"\{[^{}]*\"score\"\s*:\s*([012])[^{}]*\}", txt, re.DOTALL)
                if m:
                    return int(m.group(1))
            except Exception:  # noqa: BLE001 - transitoire : retry puis endpoint suivant
                time.sleep(2 * (attempt + 1))
    return None


# ---------------------------------------------------------------- serveur vLLM

@dataclass
class ServerHandle:
    process: subprocess.Popen | None
    container: str = ""

    def shutdown(self) -> None:
        if self.container:
            subprocess.run(["docker", "stop", self.container], capture_output=True, timeout=120)
        if self.process and self.process.poll() is None:
            self.process.terminate()
            try:
                self.process.wait(timeout=60)
            except subprocess.TimeoutExpired:
                self.process.kill()


def boot_server(mode: str, model_path: Path, port: int, gpu: int,
                 model_name: str, max_model_len: int,
                 gpu_mem_util: float, venv_python: Path | None) -> ServerHandle:
    common = [
        "--model", str(model_path), "--served-model-name", model_name,
        "--max-model-len", str(max_model_len), "--port", str(port if mode == "venv" else 8000),
        "--gpu-memory-utilization", str(gpu_mem_util),
    ]
    if mode == "venv":
        env = os.environ.copy()
        env["CUDA_VISIBLE_DEVICES"] = str(gpu)
        env.pop("VLLM_LOGGING_LEVEL", None)
        proc = subprocess.Popen(
            [str(venv_python), "-m", "vllm.entrypoints.openai.api_server", *common],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=env)
        return ServerHandle(process=proc)
    # mode docker : image officielle vllm/vllm-openai, montage du snapshot
    container = "probe-15099-leg"
    subprocess.run(["docker", "rm", "-f", container], capture_output=True)
    proc = subprocess.Popen([
        "docker", "run", "--rm", "--name", container,
        "--gpus", f"device={gpu}", "--shm-size", "8g",
        "-v", f"{model_path}:/model", "-p", f"{port}:8000",
        "vllm/vllm-openai:latest", *common,
    ], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return ServerHandle(process=proc, container=container)


def wait_ready(port: int, timeout_s: int = 900) -> bool:
    t0 = time.time()
    while time.time() - t0 < timeout_s:
        if http_get_ok(f"http://127.0.0.1:{port}/health"):
            return True
        time.sleep(3)
    return False


# ---------------------------------------------------------------- jambe

@dataclass
class LegReport:
    label: str
    model_path: str
    responses: list[OneResponse] = field(default_factory=list)
    vram_baseline_mib: int | None = None
    vram_peak_mib: int | None = None
    weights_gib: float = 0.0
    chat_template_from_snapshot: bool = False
    boot_s: float = 0.0
    scores: dict[str, float] = field(default_factory=dict)
    tokens_per_s: float = 0.0


def run_leg(label: str, model_path: Path, bench: dict, args, extra_body: dict | None) -> LegReport:
    rep = LegReport(label=label, model_path=str(model_path))
    rep.weights_gib = weights_bytes_on_disk(model_path) / (1024 ** 3)
    rep.chat_template_from_snapshot = chat_template_present(model_path)

    mon = VramMonitor(args.gpu)
    mon.start()
    t0 = time.time()
    srv = boot_server(args.serve_mode, model_path, args.port, args.gpu,
                      "duel", args.max_model_len, args.gpu_mem_util,
                      args.venv_python)
    try:
        if not wait_ready(args.port):
            print(f"[{label}] ERREUR : serveur pas pret en {time.time()-t0:.0f}s", file=sys.stderr)
            return rep
        rep.boot_s = time.time() - t0
        print(f"[{label}] serveur pret en {rep.boot_s:.0f}s, poids {rep.weights_gib:.2f} GiB")

        # echauffement (cuda graphs / compilation) hors mesure
        chat_completion(args.port, "duel", "Dis simplement : pret.",
                        16, bench["sampling"], extra_body, timeout=120)

        items = [(a, it) for a in ("qa", "math", "code") for it in bench[a]]
        if args.limit_per_axis:
            per_axis: dict[str, int] = {}
            kept = []
            for a, it in items:
                per_axis[a] = per_axis.get(a, 0) + 1
                if per_axis[a] <= args.limit_per_axis:
                    kept.append((a, it))
            items = kept

        for i, (axis, item) in enumerate(items, 1):
            r = chat_completion(args.port, "duel", item["q"],
                                bench["sampling"]["max_tokens"][axis],
                                bench["sampling"], extra_body)
            r.item_id, r.axis = item["id"], axis
            rep.responses.append(r)
            if i % 10 == 0 or i == len(items):
                print(f"[{label}] {i}/{len(items)} faits "
                      f"(dernier {r.item_id}, {r.completion_tokens} tok, {r.wall_s:.1f}s)")
    finally:
        srv.shutdown()
        mon.stop()
        rep.vram_baseline_mib, rep.vram_peak_mib = mon.baseline_mib, mon.peak_mib
        time.sleep(5)  # laisser le GPU se vider avant la jambe suivante

    ok = [r for r in rep.responses if not r.error]
    tot_tok = sum(r.completion_tokens for r in ok)
    tot_s = sum(r.wall_s for r in ok)
    rep.tokens_per_s = tot_tok / tot_s if tot_s > 0 else 0.0
    return rep


# ---------------------------------------------------------------- verdict

def score_leg(rep: LegReport, bench: dict, corr_cfg: dict | None) -> dict[str, list[int]]:
    """Scores par item, puis moyenne par axe. Q&A -> correcteur aveugle ;
    math -> deterministe puis correcteur ; code -> execution des tests."""
    detail: dict[str, list[int]] = {"qa": [], "math": [], "code": []}
    by_id = {it["id"]: it for axis in ("qa", "math", "code") for it in bench[axis]}
    for r in rep.responses:
        item = by_id.get(r.item_id)
        if not item:
            continue
        if r.error or not r.text.strip():
            detail[r.axis].append(0)
            continue
        if r.axis == "code":
            detail["code"].append(check_code(item, r.text))
        elif r.axis == "math":
            d = check_math(item.get("golden", ""), r.text)
            if d is None and corr_cfg:
                d = corrector_score(item["q"], f"La reponse exacte attendue est : {item['golden']}",
                                    r.text, corr_cfg)
            detail["math"].append(d if d is not None else 0)
        else:
            keys = " ; ".join(item.get("keys", []))
            s = None
            if corr_cfg:
                s = corrector_score(item["q"], f"Points attendus (tous = 2, partiels = 1) : {keys}",
                                    r.text, corr_cfg)
            detail["qa"].append(s if s is not None else 0)
    return detail


def fmt_table(mini: LegReport, qwen: LegReport,
              d_mini: dict[str, list[int]], d_qwen: dict[str, list[int]]) -> str:
    lines = ["| Metrique | MiniCPM5-2B | Qwen3-4B | ratio mini/qwen |",
             "|---|---|---|---|"]
    for axis, name in (("qa", "Q&A (0-2)"), ("math", "Math (0-2)"), ("code", "Code (0-2)")):
        a = sum(d_mini[axis]) / len(d_mini[axis]) if d_mini[axis] else 0.0
        b = sum(d_qwen[axis]) / len(d_qwen[axis]) if d_qwen[axis] else 0.0
        ratio = a / b if b > 0 else float("inf")
        lines.append(f"| {name} | {a:.3f} | {b:.3f} | {ratio:.3f} |")
    allmini = sum(v for ax in d_mini.values() for v in ax) / max(
        1, sum(len(ax) for ax in d_mini.values()))
    allqwen = sum(v for ax in d_qwen.values() for v in ax) / max(
        1, sum(len(ax) for ax in d_qwen.values()))
    ratio = allmini / allqwen if allqwen > 0 else float("inf")
    lines.append(f"| Global (0-2) | {allmini:.3f} | {allqwen:.3f} | {ratio:.3f} |")
    t_ratio = mini.tokens_per_s / qwen.tokens_per_s if qwen.tokens_per_s > 0 else float("inf")
    lines.append(f"| tokens/s | {mini.tokens_per_s:.1f} | {qwen.tokens_per_s:.1f} | {t_ratio:.3f} |")
    w_ratio = mini.weights_gib / qwen.weights_gib if qwen.weights_gib > 0 else float("inf")
    lines.append(f"| VRAM poids (GiB) | {mini.weights_gib:.2f} | {qwen.weights_gib:.2f} | {w_ratio:.3f} |")
    if mini.vram_peak_mib and qwen.vram_peak_mib:
        p_ratio = (mini.vram_peak_mib - (mini.vram_baseline_mib or 0)) / max(
            1, qwen.vram_peak_mib - (qwen.vram_baseline_mib or 0))
        lines.append(f"| VRAM peak serveur (MiB au-dessus base) | "
                     f"{mini.vram_peak_mib - (mini.vram_baseline_mib or 0)} | "
                     f"{qwen.vram_peak_mib - (qwen.vram_baseline_mib or 0)} | {p_ratio:.3f} |")
    return "\n".join(lines)


def verdict(mini: LegReport, qwen: LegReport,
            d_mini: dict[str, list[int]], d_qwen: dict[str, list[int]]) -> dict:
    axis_parities = {}
    for axis in ("qa", "math", "code"):
        a = sum(d_mini[axis]) / len(d_mini[axis]) if d_mini[axis] else 0.0
        b = sum(d_qwen[axis]) / len(d_qwen[axis]) if d_qwen[axis] else 0.0
        axis_parities[axis] = bool(b > 0 and a >= PARITY_RATIO * b)
    n_axes = sum(axis_parities.values())
    allmini = sum(v for ax in d_mini.values() for v in ax) / max(
        1, sum(len(ax) for ax in d_mini.values()))
    allqwen = sum(v for ax in d_qwen.values() for v in ax) / max(
        1, sum(len(ax) for ax in d_qwen.values()))
    global_parity = bool(allqwen > 0 and allmini >= PARITY_RATIO * allqwen)
    vram_win = bool(qwen.weights_gib > 0 and
                    (qwen.weights_gib - mini.weights_gib) / qwen.weights_gib >= WIN_RATIO)
    tok_win = bool(qwen.tokens_per_s > 0 and
                   (mini.tokens_per_s - qwen.tokens_per_s) / qwen.tokens_per_s >= WIN_RATIO)
    accepted = (n_axes >= 2) or (global_parity and (vram_win or tok_win))
    return {
        "axis_parity": axis_parities, "axes_at_parity": n_axes,
        "global_parity": global_parity, "vram_win_ge_30pct": vram_win,
        "tokens_win_ge_30pct": tok_win, "accepted": accepted,
        "rule": "accepte si >=2 axes/3 en parite, OU parite globale + win >=30% (VRAM ou tokens/s)",
    }


# ---------------------------------------------------------------- main

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--model-mini", type=Path, required=True,
                    help="snapshot local MiniCPM5-2B (dossier HF cache)")
    ap.add_argument("--model-qwen", type=Path, required=True,
                    help="snapshot local Qwen3-4B")
    ap.add_argument("--serve-mode", choices=("auto", "venv", "docker"), default="auto")
    ap.add_argument("--venv-python", type=Path, default=Path("D:/Dev/venvs/vllm-probe/Scripts/python.exe"))
    ap.add_argument("--gpu", type=int, default=DEFAULT_GPU)
    ap.add_argument("--port", type=int, default=DEFAULT_PORT)
    ap.add_argument("--max-model-len", type=int, default=8192)
    ap.add_argument("--gpu-memory-utilization", type=float, default=0.90)
    ap.add_argument("--limit-per-axis", type=int, default=0,
                    help="smoke : limite le banc a N items/axe (0 = banc complet)")
    ap.add_argument("--no-corrector", action="store_true",
                    help="sans correcteur distant (smoke) : Q&A=0, math deterministe seulement")
    ap.add_argument("--corrector-model", default="glm-5.2")
    ap.add_argument("--corrector-fallback-model", default="google/gemini-2.5-flash")
    ap.add_argument("--report", type=Path, required=True, help="chemin du rapport JSON de sortie")
    args = ap.parse_args()

    bench = json.loads(BENCH_PATH.read_text(encoding="utf-8"))
    print(f"Banc : {sum(len(bench[a]) for a in ('qa','math','code'))} items, "
          f"sampling {bench['sampling']}")

    # correcteur : claudish primaire, OpenRouter fallback (noms de cles seulement)
    corr_cfg: dict | None = None
    if not args.no_corrector:
        env = load_master_env(ENV_KEYS_NEEDED)
        endpoints = []
        if env.get("CLAUDISH_PROXY_KEY"):
            endpoints.append(("https://models.myia.io/v1/chat/completions",
                              env["CLAUDISH_PROXY_KEY"]))
        if env.get("OPENROUTER_API_KEY"):
            endpoints.append(("https://openrouter.ai/api/v1/chat/completions",
                              env["OPENROUTER_API_KEY"]))
        if endpoints:
            corr_cfg = {"model": args.corrector_model, "endpoints": endpoints}
            print(f"Correcteur : {endpoints[0][0]} (model {args.corrector_model}), "
                  f"fallback x{len(endpoints)-1}")
        else:
            print("AVERTISSEMENT : aucune cle correcteur, Q&A sera 0", file=sys.stderr)

    # mode serveur : venv si vllm importable, sinon docker
    mode = args.serve_mode
    if mode == "auto":
        probe = subprocess.run(
            [str(args.venv_python), "-c", "import vllm"], capture_output=True)
        mode = "venv" if probe.returncode == 0 else "docker"
    print(f"Serveur vLLM : mode {mode}")

    for p in (args.model_mini, args.model_qwen):
        if not p.is_dir():
            print(f"ERREUR : snapshot absent {p}", file=sys.stderr)
            return 2
        if not chat_template_present(p):
            print(f"ERREUR : pas de chat_template dans {p}/tokenizer_config.json "
                  f"(template doit venir du snapshot, pas du README)", file=sys.stderr)
            return 2

    extra_mini: dict | None = None
    extra_qwen = {"chat_template_kwargs": {"enable_thinking": False}}
    mini = run_leg("MiniCPM5-2B", args.model_mini, bench, args, extra_mini)
    qwen = run_leg("Qwen3-4B", args.model_qwen, bench, args, extra_qwen)

    print("Scoring (deterministe + correcteur)...")
    d_mini = score_leg(mini, bench, corr_cfg)
    d_qwen = score_leg(qwen, bench, corr_cfg)
    v = verdict(mini, qwen, d_mini, d_qwen)

    report = {
        "meta": {"issue": 15099, "probe": "A", "generated_at": now_utc(),
                 "sampling": bench["sampling"], "serve_mode": mode,
                 "gpu": args.gpu, "max_model_len": args.max_model_len,
                 "corrector_model": args.corrector_model if corr_cfg else None,
                 "limit_per_axis": args.limit_per_axis or None},
        "mini": {**{k: v2 for k, v2 in mini.__dict__.items() if k != "responses"},
                 "scores_detail": d_mini},
        "qwen": {**{k: v2 for k, v2 in qwen.__dict__.items() if k != "responses"},
                 "scores_detail": d_qwen},
        "verdict": v,
        "responses_mini": [r.__dict__ for r in mini.responses],
        "responses_qwen": [r.__dict__ for r in qwen.responses],
    }
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, ensure_ascii=False, indent=1), encoding="utf-8")

    print()
    print(fmt_table(mini, qwen, d_mini, d_qwen))
    print()
    print(f"VERDICT : {'ACCEPTE' if v['accepted'] else 'REFUSE'} "
          f"(axes en parite {v['axes_at_parity']}/3, parite globale {v['global_parity']}, "
          f"win VRAM {v['vram_win_ge_30pct']}, win tokens {v['tokens_win_ge_30pct']})")
    print(f"Rapport : {args.report}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
