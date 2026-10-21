#!/usr/bin/env python3
"""Pre-tri des fils de commentaires d'une pull request (revue B.0).

L'organe ne rend aucun verdict : il delegue a un petit modele de flotte le
recensement des commentaires, avec un ROLE par commentaire

    dossier | traite_reserve | reserve | signal | info

et l'extrait qui le prouve. La decision reste a l'organe B.0 et a l'agent.

Les commentaires de bot (CI) sont COMPTES, pas transcrits : ils sont du bruit
pour une revue de reserves, et leur volume fait deriver les petits modeles.

Le volume brut (corps de PR, commentaires) reste sur disque : il ne passe
jamais par le contexte de l'agent appelant.

Usage :

    python scripts/coordination/pr_comment_threads.py 21352 21579
    python scripts/coordination/pr_comment_threads.py --dry-run 21352

Variables d'environnement :
    FROGNANO_HUB    base URL du hub OpenAI-compatible (defaut http://192.168.0.50:3000/v1)
    FROGNANO_MODEL  modele appele (defaut frognano-4b)
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

DEFAULT_HUB = "http://192.168.0.50:3000/v1"
DEFAULT_MODEL = "frognano-4b"
DEFAULT_OUT_DIR = Path(".tmp/fn_threads")

SYSTEM = (
    "Tu es un analyste de fils de discussion GitHub. Tu recenses, tu ne "
    "juges pas : tu ne rendus jamais de verdict sur la qualite d'une pull "
    "request, uniquement le role de chaque commentaire. Reponds "
    "uniquement par un JSON valide."
)

TEMPLATE = """Voici une pull request GitHub et les commentaires HUMAINS de son fil.
(Les commentaires de bot sont hors de ce texte : ils ne sont pas reserves.)

=== PR ===
#{num} {titre}
{body}

=== COMMENTAIRES HUMAINS ===
{commentaires}
=== FIN ===

TA TASK : recenser les COMMENTAIRES, pas de rendre de verdict sur la PR.

Pour chaque commentaire, donne son role :
- "dossier"      : le commentaire est un bloc de dossier [ADJOINT PREFLIGHT]
                    ou [CLOSURE PREFLIGHT] (une attestation tierce).
- "traite_reserve": le commentaire repond a une reserve posee plus tot
                    (il la nomme et y repond).
- "reserve"      : le commentaire pose lui-meme un point bloquant.
- "signal"       : le commentaire est un signal de proces (CI, DWELL, ripe,
                    merge, relance de job) sans point bloquant.
- "info"         : commentaire purement informatif.

Un commentaire qui repond a une reserve n'est PAS une reserve : classe-le
"traite_reserve", meme s'il contient un mot severe. A l'inverse, une reserve
posee par un tiers reste "reserve" meme si elle est formulee poliment. Un
bloc de dossier qui porte "domain: fail" ou "checks: ..." reste "dossier" :
c'est son contenu qu'il faut lire, pas une reserve nouvelle.

Un seul extrait par commentaire, recopie fidelement, sur UNE ligne, sans
saut de ligne ni repetition de barrets : max 100 caracteres.
Rends un JSON de la forme :
{{"commentaires": [
   {{"n": <numero du commentaire, dans l'ordre donne>,
     "role": "dossier|traite_reserve|reserve|signal|info",
     "auteur": "<login>", "date": "<YYYY-MM-DD>",
     "extrait": "...",
     "point": "<si role=reserve : le point bloque, une phrase ; sinon null>"}}
 ]}}
et rien d'autre."""


def gh_json(args: list[str]) -> dict:
    """Lit un objet JSON via `gh`, avec le jeton `jsboige` epingle par commande."""
    tok = subprocess.run(
        ["gh", "auth", "token", "--user", "jsboige", "--hostname", "github.com"],
        capture_output=True,
        text=True,
    ).stdout.strip()
    env = {**os.environ, "GH_TOKEN": tok}
    r = subprocess.run(["gh", *args], capture_output=True, text=True, env=env)
    if r.returncode != 0:
        raise RuntimeError(f"gh {' '.join(args)} -> {r.stderr[:400]}")
    return json.loads(r.stdout)


def is_bot(login: str) -> bool:
    low = (login or "").lower()
    return low.endswith("[bot]") or "bot" in low or low == "github-actions"


def proxy_key() -> str | None:
    """Cle du proxy claudish, lue a l'execution -- jamais ecrite dans le depot."""
    raw = subprocess.run(
        ["docker", "inspect", "claudish-proxy", "--format", "{{json .Config.Env}}"],
        capture_output=True,
        text=True,
        timeout=30,
    ).stdout.strip()
    if not raw:
        return None
    try:
        env = json.loads(raw)
    except json.JSONDecodeError:
        return None
    for e in env:
        if e.startswith("CLAUDISH_PROXY_KEY="):
            return e.split("=", 1)[1]
    return None


def call_hub(hub: str, model: str, prompt: str, out: Path, max_tokens: int) -> dict:
    payload = {
        "model": model,
        "messages": [
            {"role": "system", "content": SYSTEM},
            {"role": "user", "content": prompt},
        ],
        "max_tokens": max_tokens,
        "temperature": 0.0,
        "stream": False,
    }
    headers = {"Content-Type": "application/json"}
    key = proxy_key()
    if key:
        headers["Authorization"] = f"Bearer {key}"
    req = urllib.request.Request(
        f"{hub}/chat/completions",
        data=json.dumps(payload).encode("utf-8"),
        headers=headers,
        method="POST",
    )
    t0 = time.perf_counter()
    try:
        with urllib.request.urlopen(req, timeout=300) as resp:
            raw = resp.read().decode("utf-8")
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", "replace")
        out.write_text(f"HTTP {exc.code}\n{detail}", encoding="utf-8")
        return {"http": exc.code, "latence": round(time.perf_counter() - t0, 2)}
    except urllib.error.URLError as exc:
        out.write_text(f"URLEERROR {exc.reason}", encoding="utf-8")
        return {"http": None, "latence": round(time.perf_counter() - t0, 2)}
    dt = time.perf_counter() - t0
    data = json.loads(raw)
    text = ((((data.get("choices") or [{}])[0]).get("message") or {}).get("content")) or ""
    out.write_text(text, encoding="utf-8")
    usage = data.get("usage") or {}
    return {
        "http": 200,
        "latence": round(dt, 2),
        "tokens_in": usage.get("prompt_tokens"),
        "tokens_out": usage.get("completion_tokens"),
        "car_sortie": len(text),
    }


def strip_fences(text: str) -> str:
    t = text.strip()
    t = re.sub(r"^```(?:json)?\s*", "", t)
    t = re.sub(r"\s*```$", "", t)
    return t.strip()


def parse_lenient(text: str) -> dict:
    """JSON strict, puis repli : on coupe au dernier objet complet."""
    t = strip_fences(text)
    try:
        return json.loads(t)
    except json.JSONDecodeError:
        pass
    for cut in range(len(t), 0, -1):
        chunk = t[:cut].rstrip().rstrip(",")
        if not chunk.endswith("}"):
            chunk += "}"
        try:
            return json.loads(chunk)
        except json.JSONDecodeError:
            continue
    raise ValueError("JSON irrecoverable")


def build_prompt(pr: dict, humains: list[dict], body_chars: int, comment_chars: int) -> str:
    lignes = []
    for i, c in enumerate(humains, 1):
        lignes.append(
            f"--- commentaire {i} ({c['author']['login']}, {c['createdAt'][:10]}) ---\n"
            f"{(c.get('body') or '')[:comment_chars]}"
        )
    return TEMPLATE.format(
        num=pr.get("number", "?"),
        titre=pr.get("title", ""),
        body=(pr.get("body") or "")[:body_chars] or "(vide)",
        commentaires="\n\n".join(lignes) or "(aucun)",
    )


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("pr", nargs="+", help="numeros de pull request")
    ap.add_argument("--model", default=os.environ.get("FROGNANO_MODEL", DEFAULT_MODEL))
    ap.add_argument("--hub", default=os.environ.get("FROGNANO_HUB", DEFAULT_HUB))
    ap.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    ap.add_argument("--body-chars", type=int, default=1200)
    ap.add_argument("--comment-chars", type=int, default=1500)
    ap.add_argument("--max-tokens", type=int, default=3000)
    ap.add_argument(
        "--dry-run",
        action="store_true",
        help="construit le prompt et compte les commentaires sans appeler le hub",
    )
    args = ap.parse_args(argv)

    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except (AttributeError, OSError):
        pass

    args.out_dir.mkdir(parents=True, exist_ok=True)
    total_in = 0
    for raw_num in args.pr:
        num = raw_num.lstrip("#")
        pr = gh_json(["pr", "view", num, "--json", "number,title,body,comments,state,headRefOid"])
        comments = pr.get("comments") or []
        humains = [c for c in comments if not is_bot((c.get("author") or {}).get("login"))]
        bots = len(comments) - len(humains)
        prompt = build_prompt(pr, humains, args.body_chars, args.comment_chars)

        if args.dry_run:
            print(
                f"[PR #{num}] commentaires={len(comments)} (humains={len(humains)} bots={bots}) "
                f"car_brut={len(prompt)} -- dry-run, aucun appel hub"
            )
            out = args.out_dir / f"fn_threads_{num}.prompt.txt"
            out.write_text(prompt, encoding="utf-8")
            print(f"    prompt -> {out}")
            continue

        out = args.out_dir / f"fn_threads_{num}.json"
        r = call_hub(args.hub, args.model, prompt, out, args.max_tokens)
        total_in += r.get("tokens_in") or 0
        print(
            f"[PR #{num}] commentaires={len(comments)} (humains={len(humains)} bots={bots}) "
            f"car_brut={len(prompt)} http={r.get('http')} latence={r.get('latence')}s "
            f"tokens_in={r.get('tokens_in')} tokens_out={r.get('tokens_out')} "
            f"car_sortie={r.get('car_sortie')} -> {out}"
        )
        if r.get("http") != 200:
            print(f"    HUB INJOIGNABLE ou en erreur : voir {out}")
            continue
        try:
            parsed = parse_lenient(out.read_text(encoding="utf-8"))
        except ValueError as exc:
            print(f"    JSON INVALIDE : {exc}")
            continue
        for c in parsed.get("commentaires", []):
            marque = "  <<< RESERVE" if c.get("role") == "reserve" else ""
            extrait = re.sub(r"\s+", " ", str(c.get("extrait") or ""))[:100]
            print(
                f"    {c.get('n')}. [{c.get('role')}] {c.get('auteur')} {c.get('date')} "
                f"| {extrait}{marque}"
            )
            if c.get("point"):
                print(f"        point: {str(c.get('point'))[:160]}")
    if not args.dry_run:
        print(f"total tokens_in = {total_in}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
