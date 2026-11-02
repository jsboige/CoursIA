#!/usr/bin/env python3
"""Pre-tri des fils de commentaires d'une PR par un modele de lecture externe.

L'organe B.0 (`scripts/check_unaddressed_nits.py`) marque certains commentaires
« A RELIRE » : ils portent une reserve non levee, levee, ou un point a
trancher. Lire ces fils dans le contexte de l'agent coute plusieurs milliers de
tokens par PR, alors que 7 a 9 commentaires sur 10 sont des bots (CI) qui ne
portent aucune reserve.

Cet organe fait quatre choses, et rien d'autre :

1. il ne transcrit PAS les commentaires de bot : ils sont comptes, pas passes
   au modele (mesure : le volume de bot fait deriver le petit modele en boucle
   de repetition sur les paves de rapport CI) ;
2. il fait attribuer a chaque commentaire HUMAIN un role, avec l'extrait qui le
   prouve ;
3. il ecrit le volume brut et la reponse dans des FICHIERS : rien ne transite
   par le contexte de l'agent appelant ;
4. il COMPTE les reviews formelles non-bot (`pulls/N/reviews`) et le signale
   dans le resume. Sur ce depot, c'est le canal qui porte les reserves : une
   reserve posee en review n'apparait jamais dans `comments`, donc un fil de
   commentaires seuls peut etre lu comme « aucune reserve humaine » alors qu'il
   y en a une. L'organe ne les transcrit pas, il les compte.

Il ne rend aucun verdict et ne leve aucune reserve : la decision reste a
l'organe B.0 et a l'agent qui lit la sortie.

Usage :
    python scripts/coordination/pr_comment_pretriage.py <pr> [<pr> ...]
    python scripts/coordination/pr_comment_pretriage.py --model frognano-4b --pr 20730

Sortie : `.tmp/fn_threads_<pr>.json` (une entree par PR), plus un resume court
sur stdout (role, auteur, extrait, point bloquant).
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

HUB = os.environ.get("FROGNANO_HUB", "http://192.168.0.50:3000/v1")
MODEL_DEFAULT = "frognano-4b"
TMP = Path(".tmp")
MAX_BODY = 1500
MAX_PR_BODY = 1200

SYSTEM = (
    "Tu es un analyste de fils de discussion GitHub. Tu ne rends aucun "
    "verdict sur la pull request, tu n'inventes rien, tu ne commentes pas. "
    "Tu reponds uniquement en JSON valide, sans texte autour."
)

TEMPLATE = """Voici une pull request GitHub et les commentaires HUMAINS de son fil.
(Les commentaires de bot sont hors de ce texte : ils ne sont pas des reserves.)

=== PR ===
#{num} {titre}
{body}

=== COMMENTAIRES HUMAINS ===
{commentaires}
=== FIN ===

TA TASK : recenser les COMMENTAIRES, pas de rendre de verdict sur la PR.

Pour chaque commentaire, donne son role :
- "dossier"       : le commentaire est un bloc de dossier [ADJOINT PREFLIGHT]
                    ou [CLOSURE PREFLIGHT] (une attestation tierce).
- "traite_reserve": le commentaire repond a une reserve posee plus tot
                    (il la nomme et y repond).
- "reserve"       : le commentaire pose lui-meme un point bloquant.
- "signal"        : le commentaire est un signal de processus (CI, DWELL, ripe,
                    merge, relance de job) sans point bloquant.
- "info"          : commentaire purement informatif.

Un commentaire qui repond a une reserve n'est PAS une reserve : classe-le
"traite_reserve", meme s'il contient un mot severe. A l'inverse, une reserve
posee par un tiers reste "reserve" meme si elle est formulee poliment. Un
bloc de dossier qui porte "domain: fail" ou "checks: ..." reste "dossier" :
c'est son contenu qu'il faut lire, pas une reserve nouvelle.

Un seul extrait par commentaire, recopie fidelement, sur UNE ligne, sans
saut de ligne ni repetition de barres : max 100 caracteres.
Rends un JSON de la forme :
{{"commentaires": [
   {{"n": <numero du commentaire, dans l'ordre donne>,
     "role": "dossier|traite_reserve|reserve|signal|info",
     "auteur": "<login>", "date": "<YYYY-MM-DD>",
     "extrait": "...",
     "point": "<si role=reserve : le point bloque, une phrase ; sinon null>"}}
 ]}}
et rien d'autre."""

BOT_LOGINS = {"github-actions", "github-actions[bot]", "dependabot", "dependabot[bot]"}


def gh(args: list[str]) -> str:
    """Appel gh avec le jeton ambiant s'il y en a un (pas de bascule de compte)."""
    env = dict(os.environ)
    if not env.get("GH_TOKEN") and not env.get("GITHUB_TOKEN"):
        tok = subprocess.run(
            ["gh", "auth", "token", "--user", "jsboige", "--hostname", "github.com"],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
        ).stdout.strip()
        if tok:
            env["GH_TOKEN"] = tok
    p = subprocess.run(["gh", *args], capture_output=True, text=True,
                       encoding="utf-8", errors="replace", env=env)
    if p.returncode != 0:
        raise RuntimeError(f"gh {' '.join(args)} -> {p.stderr[:400]}")
    return p.stdout


def proxy_key() -> str | None:
    """Cle du hub, lue dans l'environnement du proxy local si elle y est."""
    env_key = os.environ.get("CLAUDISH_PROXY_KEY")
    if env_key:
        return env_key
    try:
        raw = subprocess.run(
            ["docker", "inspect", "claudish-proxy", "--format", "{{json .Config.Env}}"],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            timeout=30,
        ).stdout
    except (OSError, subprocess.SubprocessError):
        return None
    try:
        entries = json.loads(raw)
    except json.JSONDecodeError:
        return None
    for e in entries:
        if e.startswith("CLAUDISH_PROXY_KEY="):
            return e.split("=", 1)[1]
    return None


def call_model(model: str, system: str, user: str, out: Path,
               max_tokens: int = 3000) -> dict:
    """Appelle le hub en chat/completions et ecrit la reponse brute dans `out`."""
    payload = {
        "model": model,
        "messages": [{"role": "system", "content": system},
                     {"role": "user", "content": user}],
        "max_tokens": max_tokens,
        "temperature": 0.0,
        "stream": False,
    }
    headers = {"Content-Type": "application/json"}
    key = proxy_key()
    if key:
        headers["Authorization"] = f"Bearer {key}"
    req = urllib.request.Request(
        f"{HUB}/chat/completions",
        data=json.dumps(payload).encode("utf-8"),
        headers=headers,
        method="POST",
    )
    t0 = time.perf_counter()
    try:
        with urllib.request.urlopen(req, timeout=300) as resp:
            raw = resp.read().decode("utf-8")
    except urllib.error.HTTPError as exc:
        out.write_text(f"HTTPError {exc.code}\n{exc.read().decode('utf-8', 'replace')}\n",
                       encoding="utf-8")
        return {"http": exc.code, "latence": round(time.perf_counter() - t0, 2)}
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
    """Retire une enveloppe de code markdown, si presente."""
    t = text.strip()
    if t.startswith("```"):
        t = re.sub(r"^```[a-zA-Z]*\n?", "", t)
        t = re.sub(r"\n?```$", "", t)
    return t.strip()


def parse_lenient(text: str) -> dict:
    """JSON strict, puis repli : on isole l'objet, puis on coupe au dernier complet."""
    t = strip_fences(text)
    start, end = t.find("{"), t.rfind("}")
    if start != -1 and end > start:
        t = t[start:end + 1]
    try:
        return json.loads(t)
    except json.JSONDecodeError:
        pass
    for cut in range(len(t), 0, -1):
        chunk = t[:cut].rstrip().rstrip(",")
        for closers in ("", "}", "]", "}]", "}}", "]}", "}]}", "}}]"):
            try:
                found = json.loads(chunk + closers)
            except json.JSONDecodeError:
                continue
            if isinstance(found, dict) and found:
                return found
    raise ValueError("JSON irrecoverable")


def is_bot(login: str) -> bool:
    low = (login or "").lower()
    return low in BOT_LOGINS or low.endswith("[bot]") or low == "github-actions"


def pretriage(pr: int, model: str, dry_run: bool = False) -> dict:
    data = json.loads(gh(["pr", "view", str(pr), "--json",
                          "title,body,comments,state,headRefOid,reviews"]))
    comments = data.get("comments") or []
    humans = [c for c in comments if not is_bot(c.get("author", {}).get("login", ""))]
    # Le canal qui porte les reserves sur ce depot est `reviews`, pas `comments` :
    # une reserve posee en review formelle n'apparait jamais dans `comments`.
    # On les compte (sans les transcrire) pour que le fil rendu ne soit pas lu
    # comme « aucune reserve humaine » (review Hermes #21885, point 1).
    reviews = data.get("reviews") or []
    reviews_nonbot = [
        (rv.get("author", {}).get("login", ""), rv.get("state", ""))
        for rv in reviews
        if not is_bot(rv.get("author", {}).get("login", ""))
    ]
    lines = [
        f"--- commentaire {i} ({c['author']['login']}, {c['createdAt'][:10]}) ---\n"
        f"{(c.get('body') or '')[:MAX_BODY]}"
        for i, c in enumerate(humans, 1)
    ]
    prompt = TEMPLATE.format(
        num=pr,
        titre=data.get("title", ""),
        body=(data.get("body") or "")[:MAX_PR_BODY] or "(vide)",
        commentaires="\n\n".join(lines) or "(aucun)",
    )
    TMP.mkdir(parents=True, exist_ok=True)
    if dry_run:
        out = TMP / f"fn_threads_{pr}.prompt.txt"
        out.write_text(prompt, encoding="utf-8")
        return {
            "pr": pr,
            "head": data.get("headRefOid"),
            "state": data.get("state"),
            "commentaires": len(comments),
            "humains": len(humans),
            "bots": len(comments) - len(humans),
            "reviews_nonbot": len(reviews_nonbot),
            "reviews_nonbot_detail": reviews_nonbot,
            "car_prompt": len(prompt),
            "sortie": str(out),
            "http": None,
            "dry_run": True,
        }
    out = TMP / f"fn_threads_{pr}.json"
    r = call_model(model, SYSTEM, prompt, out)
    return {
        "pr": pr,
        "head": data.get("headRefOid"),
        "state": data.get("state"),
        "commentaires": len(comments),
        "humains": len(humans),
        "bots": len(comments) - len(humans),
        "reviews_nonbot": len(reviews_nonbot),
        "reviews_nonbot_detail": reviews_nonbot,
        "car_prompt": len(prompt),
        "sortie": str(out),
        **r,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("prs", nargs="*", type=int, help="numeros de PR a pre-tri")
    ap.add_argument("--pr", type=int, action="append", default=[],
                    help="meme chose, une PR par option")
    ap.add_argument("--model", default=MODEL_DEFAULT)
    ap.add_argument(
        "--dry-run",
        action="store_true",
        help="compte les commentaires et ecrit le prompt, sans appel au hub",
    )
    args = ap.parse_args()
    nums = args.prs + args.pr
    if not nums:
        ap.error("aucun numero de PR")

    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except (AttributeError, OSError):
        pass

    total_in = 0
    truncated = False
    for pr in nums:
        r = pretriage(pr, args.model, dry_run=args.dry_run)
        total_in += r.get("tokens_in") or 0
        print(f"[PR #{pr}] commentaires={r['commentaires']} (humains={r['humains']} "
              f"bots={r['bots']}) car_brut={r['car_prompt']} http={r.get('http')} "
              f"latence={r.get('latence')}s tokens_in={r.get('tokens_in')} "
              f"tokens_out={r.get('tokens_out')} car_sortie={r.get('car_sortie')} "
              f"-> {r['sortie']}", flush=True)
        rnb = r.get("reviews_nonbot", 0)
        if rnb:
            detail = ", ".join(f"{a}/{s}" for a, s in r.get("reviews_nonbot_detail", []))
            print(f"    reviews non-bot : {rnb} ({detail}) -- le fil ci-dessus ne les "
                  f"couvre PAS (canal des reserves)", flush=True)
        else:
            print("    reviews non-bot : 0", flush=True)
        if args.dry_run:
            continue
        try:
            parsed = parse_lenient(Path(r["sortie"]).read_text(encoding="utf-8"))
        except (OSError, ValueError) as exc:
            print(f"    JSON INVALIDE : {exc}", flush=True)
            continue
        n_rendus = len(parsed.get("commentaires", []))
        if n_rendus < r["humains"]:
            truncated = True
            print(f"    AVERTISSEMENT : {n_rendus}/{r['humains']} commentaires "
                  f"restitues -- sortie du modele tronquee, pre-tri INCOMPLET",
                  flush=True)
        for c in parsed.get("commentaires", []):
            extrait = re.sub(r"\s+", " ", str(c.get("extrait") or ""))[:100]
            marque = "  <<< RESERVE" if c.get("role") == "reserve" else ""
            print(f"    {c.get('n')}. [{c.get('role')}] {c.get('auteur')} "
                  f"{c.get('date')} | {extrait}{marque}", flush=True)
            if c.get("point"):
                print(f"        point: {str(c['point'])[:160]}", flush=True)
    print(f"total tokens_in = {total_in}", flush=True)
    return 1 if truncated else 0


if __name__ == "__main__":
    sys.exit(main())
