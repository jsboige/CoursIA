#!/usr/bin/env python
"""Probe de calibration #15294 (tranche 2) : pass@1 zero-shot sur le signal
de recompense, avant tout run GPU RL.

Critere de la note de veille (tranche 1, 29/10) : un corpus est CALIBRE pour
un backbone 0.8-2B si son pass@1 zero-shot tombe dans la bande [~20 %, ~70 %]
-- en dessous la recompense est trop rare pour faire gradient (defaut mesure
de DAPO-Math-17k), au-dessus le corpus est sature et ne mesure plus rien.

Corpus servis :
  - svamp : arithmetique courte (temoin maths, ~1000 items, non gated).
    Reponse attendue = nombre exact ; recompense = match numerique.
  - xlam  : function calling (outils). Le fichier de donnees est GATED
    (HTTP 403 sans acceptation des conditions, mesure 01/11) : le corpus
    n'est servi que si --xlam-file est fourni. Recompense = nom d'outil
    correct (+ match d'arguments rapports separement, cf ToolRL #2504.13958 :
    le match exact d'arguments est une recompense grossiere -- les deux
    taux sont rendus, jamais fusionnes).

Modeles interroges via deux serveurs vLLM (OpenAI-compatible) deja lances
par la regie GPU (docker --gpus device=2) : --port-mini et --port-qwen.

Sortie : JSON (chemen --out, convention probe_*.json du depot) avec les
taux par modele, les items individuels, la graine et les horodatages UTC.
Aucune donnee n'est telechargee ici : les corpus arrivent par --svamp-file /
--xlam-file (fichiers locaux, hors depot).
"""
from __future__ import annotations

import argparse
import json
import random
import re
import sys
import time
import urllib.error
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path

BANDE = (0.20, 0.70)  # fenetre de calibration de la tranche 1


def utcnow() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def http_json(url: str, payload: dict | None = None, timeout: int = 120) -> dict:
    data = json.dumps(payload).encode() if payload is not None else None
    req = urllib.request.Request(
        url, data=data,
        headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.loads(r.read())


def wait_ready(base_url: str, model: str, deadline_s: float = 600.0) -> bool:
    """Borné : attend que /v1/models liste le modele (chargement des poids)."""
    t0 = time.monotonic()
    while time.monotonic() - t0 < deadline_s:
        try:
            got = http_json(f"{base_url}/v1/models", timeout=10)
            if any(m.get("id") == model for m in got.get("data", [])):
                return True
        except Exception:  # noqa: BLE001 - en attente de chargement
            pass
        time.sleep(5.0)
    return False


def chat(base_url: str, model: str, messages: list[dict],
         max_tokens: int, timeout: int = 180) -> str:
    out = http_json(f"{base_url}/v1/chat/completions", {
        "model": model, "messages": messages,
        "temperature": 0.0, "max_tokens": max_tokens,
    }, timeout=timeout)
    return out["choices"][0]["message"].get("content") or ""


# ---------------------------------------------------------------- SVAMP ---

_NUM = re.compile(r"-?\d+(?:[.,]\d+)?")


def _to_float(txt: str) -> float | None:
    try:
        return float(txt.replace(",", "."))
    except (TypeError, ValueError):
        return None


def svamp_prompt(item: dict) -> list[dict]:
    q = f"{item['Body'].strip()} {item['Question'].strip()}"
    return [
        {"role": "user",
         "content": f"{q}\n\nSolve the problem. End your reply with a line "
                    f"of the form 'Answer: <number>' containing only the "
                    f"final numeric answer."},
    ]


def svamp_reward(item: dict, reply: str) -> tuple[int, str]:
    """1 si le DERNIER nombre du passage 'Answer:' matche la reference."""
    gold = float(item["Answer"])
    tail = reply.rsplit("Answer:", 1)[-1] if "Answer:" in reply else reply
    nums = _NUM.findall(tail)
    if not nums:
        return 0, ""
    pred = _to_float(nums[-1])
    ok = pred is not None and abs(pred - gold) < 1e-4
    return int(ok), ("" if pred is None else str(pred))


# ------------------------------------------------------------------ xLAM ---

def xlam_prompt(item: dict) -> list[dict]:
    tools = json.dumps(item.get("tools", []), ensure_ascii=False)
    return [
        {"role": "system",
         "content": "You call tools. Reply with ONE JSON object of the "
                    "chosen tool call: {\"name\": ..., \"arguments\": {...}} "
                    "and nothing else."},
        {"role": "user",
         "content": f"TOOLS:\n{tools}\n\nQUERY:\n{item.get('query', '')}"},
    ]


def _first_json_obj(txt: str) -> dict | None:
    m = re.search(r"\{.*\}", txt, re.DOTALL)
    if not m:
        return None
    try:
        v = json.loads(m.group(0))
        return v if isinstance(v, dict) else None
    except json.JSONDecodeError:
        return None


def _norm(v):
    if isinstance(v, dict):
        return {k: _norm(x) for k, x in sorted(v.items())}
    if isinstance(v, list):
        return [_norm(x) for x in v]
    if isinstance(v, str):
        return v.strip().lower()
    return v


def xlam_reward(item: dict, reply: str) -> tuple[int, int, str]:
    """(name_ok, name_and_args_ok, pred_name) -- jamais fusionnes (#2504.13958)."""
    gold_calls = item.get("answers") or []
    if not gold_calls:
        return 0, 0, ""
    gold = gold_calls[0]
    gold_name = gold.get("name") or gold.get("function_name") or ""
    gold_args = _norm(gold.get("arguments") or gold.get("parameters") or {})
    pred = _first_json_obj(reply)
    if not pred:
        return 0, 0, ""
    if "name" not in pred and "function" in pred:  # format chat-completion
        fn = pred["function"]
        pred = {"name": fn.get("name", ""), "arguments": fn.get("arguments", {})}
    p_name = str(pred.get("name", ""))
    p_args = _norm(pred.get("arguments") or {})
    name_ok = int(p_name.strip().lower() == str(gold_name).strip().lower())
    args_ok = int(name_ok and p_args == gold_args)
    return name_ok, args_ok, p_name


# ------------------------------------------------------------------ run ---

def run_svamp(base: str, model: str, items: list[dict],
              concurrency: int = 8) -> dict:
    t0 = time.monotonic()

    def _one(it: dict) -> dict:
        try:
            reply = chat(base, model, svamp_prompt(it), max_tokens=300)
            ok, pred = svamp_reward(it, reply)
            err = ""
        except Exception as exc:  # noqa: BLE001 - item servi en echec, pas d'arret
            reply, ok, pred, err = "", 0, "", f"{type(exc).__name__}"
        return {"id": it.get("ID"), "gold": it.get("Answer"),
                "pred": pred, "ok": ok, "err": err,
                "raw": reply[-90:]}

    # vLLM batche les requetes concurrentes ; ex.map garde l'ordre d'entree
    # (rapport deterministe) sans lier la collecte a l'ordre de completion.
    with ThreadPoolExecutor(max_workers=concurrency) as ex:
        rows = list(ex.map(_one, items))
    good = sum(r["ok"] for r in rows)
    return {"corpus": "svamp", "model": model, "n": len(rows),
            "pass1": round(good / max(len(rows), 1), 4),
            "errors": sum(1 for r in rows if r["err"]),
            "wall_s": round(time.monotonic() - t0, 1),
            "items": rows}


def run_xlam(base: str, model: str, items: list[dict],
             concurrency: int = 8) -> dict:
    t0 = time.monotonic()

    def _one(it: dict) -> dict:
        try:
            reply = chat(base, model, xlam_prompt(it), max_tokens=400)
            name_ok, args_ok, p_name = xlam_reward(it, reply)
            err = ""
        except Exception as exc:  # noqa: BLE001
            reply, name_ok, args_ok, p_name, err = "", 0, 0, "", f"{type(exc).__name__}"
        return {"id": it.get("id"), "ok_name": name_ok,
                "ok_args": args_ok, "pred_name": p_name, "err": err,
                "raw": reply[-90:]}

    with ThreadPoolExecutor(max_workers=concurrency) as ex:
        rows = list(ex.map(_one, items))
    n = max(len(rows), 1)
    return {"corpus": "xlam", "model": model, "n": len(rows),
            "pass1_name": round(sum(r["ok_name"] for r in rows) / n, 4),
            "pass1_name_args": round(sum(r["ok_args"] for r in rows) / n, 4),
            "errors": sum(1 for r in rows if r["err"]),
            "wall_s": round(time.monotonic() - t0, 1),
            "items": rows}


def verdict(pass1: float) -> str:
    if pass1 < BANDE[0]:
        return "SOUS_LA_BANDE (trop dur : recompense trop rare pour RL)"
    if pass1 > BANDE[1]:
        return "SUR_LA_BANDE (sature : le classement ne mesure plus rien)"
    return "DANS_LA_BANDE (calibre)"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--svamp-file", type=Path)
    ap.add_argument("--xlam-file", type=Path)
    ap.add_argument("--items", type=int, default=100)
    ap.add_argument("--seed", type=int, default=13)
    ap.add_argument("--concurrency", type=int, default=8,
                    help="requetes en vol par modele (le serveur vLLM batche)")
    ap.add_argument("--port-mini", type=int, default=8201)
    ap.add_argument("--port-qwen", type=int, default=8202)
    ap.add_argument("--model-mini", default="openbmb/MiniCPM5-2B")
    ap.add_argument("--model-qwen", default="Qwen/Qwen3.5-0.8B")
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args(argv)
    if not args.svamp_file and not args.xlam_file:
        ap.error("--svamp-file ou --xlam-file requis")

    rng = random.Random(args.seed)
    targets = [("mini", f"http://127.0.0.1:{args.port_mini}", args.model_mini),
               ("qwen", f"http://127.0.0.1:{args.port_qwen}", args.model_qwen)]
    for _, base, model in targets:
        if not wait_ready(base, model):
            print(f"[calib] serveur pas pret: {base} ({model})", file=sys.stderr)
            return 2

    report: dict = {"probe": "calib_pass1", "issue": 15294,
                    "bande": list(BANDE), "seed": args.seed,
                    "items": args.items, "concurrency": args.concurrency,
                    "started_utc": utcnow(), "runs": []}

    if args.svamp_file:
        pool = json.loads(args.svamp_file.read_text(encoding="utf-8"))
        sample = rng.sample(pool, min(args.items, len(pool)))
        for tag, base, model in targets:
            r = run_svamp(base, model, sample, args.concurrency)
            r["model_tag"] = tag
            r["verdict"] = verdict(r["pass1"])
            report["runs"].append(r)

    if args.xlam_file:
        pool = json.loads(args.xlam_file.read_text(encoding="utf-8"))
        sample = rng.sample(pool, min(args.items, len(pool)))
        for tag, base, model in targets:
            r = run_xlam(base, model, sample, args.concurrency)
            r["model_tag"] = tag
            r["verdict_name"] = verdict(r["pass1_name"])
            r["verdict_name_args"] = verdict(r["pass1_name_args"])
            report["runs"].append(r)

    report["finished_utc"] = utcnow()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(
        json.dumps(report, ensure_ascii=False, indent=1), encoding="utf-8")
    for r in report["runs"]:
        keys = ("pass1" if "pass1" in r else "pass1_name/pass1_name_args")
        val = (f"{r['pass1']:.1%}" if "pass1" in r
               else f"{r['pass1_name']:.1%} / {r['pass1_name_args']:.1%}")
        v = r.get("verdict") or f"{r.get('verdict_name')} / {r.get('verdict_name_args')}"
        print(f"[calib] {r['corpus']:6s} {r['model_tag']:5s} {keys}={val}  -> {v}")
    print(f"[calib] rapport: {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
