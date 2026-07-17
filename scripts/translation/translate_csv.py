#!/usr/bin/env python3
"""T3 — Moteur de traduction des cellules de notebooks (FR source -> 7 langues cibles).

FORK depuis Argumentum `tools/dnn_i18n/translate_game_rules.py` (gpt-5.5, 193 LOC,
commit submodule 7e72f3e5d), adapte au schéma CSV CoursIA (Epic #4957 / #1650).
Voir issue #6949 (PR #2/2) pour le mapping Argumentum -> CoursIA et la motivation
(arrêt des resync CSV "dans le vide" : sans ce moteur, les PRs de drift T1/T2
produisent 0 cellule traduite en 7 langues cibles).

Couches : T1 (extract_cells_to_csv.py) + T2 (check_translation_sync.py) sont
livrées ; ce script est la couche T3 (gated). Il lit un CSV `translations/<famille>/
<série>.csv`, traduit les cellules `text_fr` vers les langues cibles dont la colonne
`text_<lang>` est vide, et réécrit le CSV avec `text_<lang>` + `hash_<lang>` cohérent
avec T2 (hash_<lang> = cell_hash(text_<lang>), même normalize que T1/T2).

Sécurité (HARD) :
  - `ENABLED = False` par défaut. Même avec `--apply`, le moteur refuse d'appeler
    l'API tant que `ENABLED` n'est pas passé à `True` dans la source (GO user,
    #6949 moyen terme). Triple gate : edit source + --apply + clé env.
  - `--dry-run` est le mode défaut (no API, no mutation) : imprime le plan de
    traduction (cellules markdown x langues = N appels).
  - Les clés API viennent UNIQUEMENT de l'environnement (`OPENAI_API_KEY`,
    `OPENROUTER_API_KEY` optionnel). Aucun littéral, aucun fichier `.keys/`,
    aucun `os.getenv("KEY", "<défaut>")` (secrets-hygiene.md règle 1-3).

gpt-5.5 specifics (verified Argumentum #499 pilot, 2026-06-16) :
  - Pas de `temperature` (HTTP 400 sur reasoning models).
  - `max_completion_tokens` (PAS `max_tokens`), floor 1500 / cap 8000, sized au
    champ. `reasoning_effort=low`.
  - OpenAI direct en primaire, OpenRouter en fallback 401/429.

Usage :
  python translate_csv.py --csv translations/iit/iit.csv                  # dry-run plan
  python translate_csv.py --csv x.csv --smoke                              # dry-run 1 cell x 7 langs
  python translate_csv.py --csv x.csv --lang en                            # dry-run 1 langue
  python translate_csv.py --csv x.csv --apply                              # GATED (ENABLED=False) -> no-op
  # (activation : éditer ENABLED=True + OPENAI_API_KEY env + --apply)
"""
import argparse
import csv
import hashlib
import json
import os
import sys
import time
import urllib.error
import urllib.request

# ----------------------------------------------------------------------------
# Gate de sécurité (HARD). `False` = le moteur est inactif même avec --apply.
# Passer à `True` uniquement après GO user (#6949 moyen terme, #1650 Phase 1).
# ----------------------------------------------------------------------------
ENABLED = False

TARGETS = ["en", "ru", "pt", "es", "ar", "fa", "zh"]
LANG_NAMES = {
    "en": "English",
    "ru": "Russian",
    "pt": "Portuguese",
    "es": "Spanish",
    "ar": "Arabic",
    "fa": "Persian",
    "zh": "Chinese (Simplified)",
}

# Modèle + endpoints par défaut (overridable via --model / --base-url / env).
DEFAULT_MODEL = os.environ.get("TRANSLATE_MODEL", "gpt-5.5")
DEFAULT_BASE_URL = os.environ.get("OPENAI_BASE_URL", "https://api.openai.com/v1")
OPENROUTER_BASE_URL = "https://openrouter.ai/api/v1"
OPENROUTER_MODEL = os.environ.get("TRANSLATE_MODEL_OPENROUTER", "openai/gpt-5.5")


# ----------------------------------------------------------------------------
# Hash contract — identique à T1 (extract_cells_to_csv.py) et T2
# (check_translation_sync.py). Maintenir la cohérence : hash_<lang> posé par T3
# doit matcher ce que T2 recompute. NE PAS diverger.
# ----------------------------------------------------------------------------
def normalize(text: str) -> str:
    """Normalisation du drift-detection : rstrip chaque ligne + strip newline final.

    Évite les faux-drift cosmétiques (trailing whitespace / CRLF vs LF) tout en
    préservant le contenu sémantique. Byte-identique à T1/T2.
    """
    lines = [line.rstrip() for line in text.splitlines()]
    return "\n".join(lines).strip("\n")


def cell_hash(text: str) -> str:
    """sha256 (16 hex) du texte normalisé — invariant drift-detection intradépôt."""
    return hashlib.sha256(normalize(text).encode("utf-8")).hexdigest()[:16]


# ----------------------------------------------------------------------------
# I/O CSV — RFC 4180, utf-8 BOM toléré en lecture, LF en écriture.
# ----------------------------------------------------------------------------
CSV_COLUMNS = [
    "notebook", "cell_id", "cell_type", "src_lang", "src_hash",
    "text_fr", "text_en", "text_es", "text_ar", "text_fa", "text_zh", "text_ru", "text_pt",
    "hash_fr", "hash_en", "hash_es", "hash_ar", "hash_fa", "hash_zh", "hash_ru", "hash_pt",
]


def load_csv(path: str) -> list[dict]:
    with open(path, encoding="utf-8-sig", newline="") as f:
        return list(csv.DictReader(f))


def write_csv(path: str, rows: list[dict]) -> None:
    """Réécrit le CSV en préservant l'ordre des colonnes canonique (LF endings)."""
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        w = csv.DictWriter(f, fieldnames=CSV_COLUMNS, lineterminator="\n")
        w.writeheader()
        for row in rows:
            # Garde-fou : ne perdre aucune colonne canonique, ignore les extras.
            w.writerow({col: row.get(col, "") for col in CSV_COLUMNS})


# ----------------------------------------------------------------------------
# Appel LLM — fork de Argumentum call_chat. Clés env uniquement.
# ----------------------------------------------------------------------------
def _provider_keys() -> list[tuple[str, str, str]]:
    """Construit la liste des providers (model, key, base_url) depuis l'environnement.

    Primaire OpenAI (OPENAI_API_KEY). Fallback OpenRouter (OPENROUTER_API_KEY)
    si présent. Aucune clé -> liste vide (l'appelant lèvera une erreur claire).
    """
    providers = []
    k = os.getenv("OPENAI_API_KEY")
    if k:
        providers.append((DEFAULT_MODEL, k, DEFAULT_BASE_URL))
    k2 = os.getenv("OPENROUTER_API_KEY")
    if k2:
        providers.append((OPENROUTER_MODEL, k2, OPENROUTER_BASE_URL))
    return providers


def call_chat(messages, model, key, base_url, max_tokens, reasoning_effort="low", timeout=240):
    """Appel Chat Completions. Retourne (content, dt, reasoning_tokens).

    gpt-5.5 : pas de `temperature`, `max_completion_tokens` (pas `max_tokens`),
    `reasoning_effort=low`. Fork direct de Argumentum (verified #499 pilot).
    """
    body = {"model": model, "messages": messages, "max_completion_tokens": max_tokens}
    if reasoning_effort:
        body["reasoning_effort"] = reasoning_effort
    data = json.dumps(body).encode("utf-8")
    req = urllib.request.Request(
        base_url.rstrip("/") + "/chat/completions",
        data=data,
        headers={"Authorization": "Bearer " + key, "Content-Type": "application/json"},
    )
    t0 = time.time()
    with urllib.request.urlopen(req, timeout=timeout) as r:
        resp = json.loads(r.read())
    dt = time.time() - t0
    content = resp["choices"][0]["message"]["content"]
    rt = resp.get("usage", {}).get("completion_tokens_details", {}).get("reasoning_tokens", 0)
    return content, dt, rt


def translate_markdown(fr_text, target_lang, model, key, base_url,
                       max_tokens_cap=8000, max_tokens_floor=1500):
    """Traduit une cellule markdown FR vers une langue cible. Retourne (html, dt, rt).

    Prompt adapté d'Argumentum (HTML prose) -> markdown pédagogique CoursIA :
    préserve fences de code, inline code, math ($...$), structure markdown
    (headings, listes, liens). Rendu natif dans la langue cible (Cyrillic / CJK /
    arabe). Le code lui-même n'est PAS traduit (seul le prose markdown l'est).
    """
    approx_in = len(fr_text) / 4
    max_tokens = max(max_tokens_floor, min(max_tokens_cap, int(approx_in * 1.6) + 800))
    lang_name = LANG_NAMES[target_lang]
    sys_msg = (
        "You are a professional translator for CoursIA, a French educational repository "
        "of AI notebooks (machine learning, symbolic AI, probabilistic programming). "
        "You translate pedagogical Markdown content from French.")
    user_msg = (
        f"Translate the following French Markdown into {lang_name}.\n"
        "STRICT RULES:\n"
        "- Preserve ALL fenced code blocks (```...```), inline code (`...`), and math "
        "($...$, $$...$$) EXACTLY as-is. Never translate code or formulas — only the "
        "prose around them.\n"
        "- Preserve Markdown structure (headings #, lists -/*, links [text](url), "
        "blockquotes >, tables). Keep the same number and order of structural elements.\n"
        "- Keep proper nouns, library/API names, and identifiers consistent.\n"
        "- Write in the target language's native script (Cyrillic for Russian, CJK for "
        "Chinese, Arabic script for Arabic/Persian).\n"
        "- Return ONLY the translated Markdown. No explanation, no fences around the "
        "whole output, no preamble.\n\n"
        f"FRENCH MARKDOWN TO TRANSLATE:\n{fr_text}")
    msgs = [{"role": "system", "content": sys_msg}, {"role": "user", "content": user_msg}]
    return call_chat(msgs, model, key, base_url, max_tokens)


# ----------------------------------------------------------------------------
# Plan de traduction — cellules éligibles.
# ----------------------------------------------------------------------------
def translation_plan(rows, langs, include_code=False):
    """Yield (row_index, lang) pour chaque cellule markdown éligible x langue cible vide.

    Éligibilité : cell_type == 'markdown' (ou 'code' si include_code), text_fr non
    vide, text_<lang> vide (non déjà traduit — sert aussi de cache/resume).
    """
    for i, row in enumerate(rows):
        ctype = row.get("cell_type", "")
        if ctype == "code" and not include_code:
            continue
        if ctype not in ("markdown", "code"):
            continue
        fr = row.get("text_fr", "")
        if not fr.strip():
            continue
        for lang in langs:
            if not row.get(f"text_{lang}", "").strip():
                yield i, lang


def run_translations(rows, langs, include_code, out_path, smoke):
    """Exécute les traductions live (ENABLED doit être True). Mutate rows in place.

    Écrit le CSV incrémentalement après chaque cellule (resume-safe : un run
    interrompu reprend où il s'est arrêté grâce au cache text_<lang>).
    """
    providers = _provider_keys()
    if not providers:
        raise ValueError(
            "Aucune clé API trouvée. Définir OPENAI_API_KEY (et optionnellement "
            "OPENROUTER_API_KEY) dans l'environnement. Jamais de littéral inline "
            "(secrets-hygiene.md).")

    plan = list(translation_plan(rows, langs, include_code))
    if smoke:
        # 1 cellule x toutes les langues demandées (premier markdown trouvé).
        first_idx = next((i for i, _ in plan), None)
        plan = [(i, lang) for i, lang in plan if i == first_idx] if first_idx is not None else []
    total = len(plan)
    print(f"[plan] {total} traductions à produire ({len(langs)} langue(s))", file=sys.stderr)

    done = fails = 0
    for idx, lang in plan:
        fr = rows[idx]["text_fr"]
        ok = False
        for attempt, (model, key, base) in enumerate(providers):
            try:
                out, dt, rt = translate_markdown(fr, lang, model, key, base)
                rows[idx][f"text_{lang}"] = out.strip()
                rows[idx][f"hash_{lang}"] = cell_hash(rows[idx][f"text_{lang}"])
                ok = True
                done += 1
                nb = rows[idx]["notebook"].split("/")[-1]
                cid = rows[idx]["cell_id"][:8]
                print(f"  [{done}/{total}] {nb} {cid}->{lang} "
                      f"({len(out)}c, {dt:.1f}s, rt={rt}) via {model}", file=sys.stderr)
                break
            except urllib.error.HTTPError as e:
                body = e.read().decode("utf-8", "replace")[:200]
                print(f"  [warn] {nb if 'nb' in dir() else idx} {lang} {model} "
                      f"HTTP {e.code}: {body}", file=sys.stderr)
                if e.code in (401, 429) and attempt < len(providers) - 1:
                    print("  [fallback] switching provider", file=sys.stderr)
                    continue
                time.sleep(3)
            except Exception as e:  # noqa: BLE001 - réseau, robustesse avant tout
                print(f"  [warn] cell[{idx}] ->{lang} {model} ERR "
                      f"{type(e).__name__}: {e}", file=sys.stderr)
                time.sleep(3)
        if not ok:
            fails += 1
            print(f"  [FAIL] cell[{idx}]->{lang} all providers exhausted", file=sys.stderr)
        write_csv(out_path, rows)  # resume-safe : persiste après chaque cellule
        time.sleep(0.5)

    print(f"\n[done] {done} traduites, {fails} échecs -> {out_path}", file=sys.stderr)
    return done, fails


def main() -> int:
    ap = argparse.ArgumentParser(description="T3 moteur traduction CSV (fork Argumentum, #6949)")
    ap.add_argument("--csv", required=True, help="CSV translations à traduire")
    ap.add_argument("--out", help="CSV de sortie (défaut = --csv, in-place)")
    ap.add_argument("--lang", help="une seule langue cible (sinon les 7)")
    ap.add_argument("--all", action="store_true", help="toutes les langues cibles")
    ap.add_argument("--smoke", action="store_true", help="1 cellule x langues (POC)")
    ap.add_argument("--apply", action="store_true",
                    help="applique réellement (défaut = dry-run plan seul)")
    ap.add_argument("--include-code", action="store_true",
                    help="traduit aussi les cellules code (défaut = markdown seul ; "
                         "la traduction des commentaires de code est un refinement T3)")
    ap.add_argument("--model", default=DEFAULT_MODEL, help=f"modèle primaire (défaut {DEFAULT_MODEL})")
    ap.add_argument("--base-url", default=DEFAULT_BASE_URL, help="endpoint primaire")
    args = ap.parse_args()

    out_path = args.out or args.csv
    rows = load_csv(args.csv)
    n_md = sum(1 for r in rows if r.get("cell_type") == "markdown")
    n_code = sum(1 for r in rows if r.get("cell_type") == "code")
    print(f"[load] {len(rows)} lignes ({n_md} markdown, {n_code} code)", file=sys.stderr)

    if args.lang:
        langs = [args.lang]
    elif args.all or args.smoke:
        langs = list(TARGETS)
    else:
        langs = list(TARGETS)  # dry-run default = plan complet sur les 7 langues

    plan = list(translation_plan(rows, langs, args.include_code))
    if args.smoke:
        first_idx = next((i for i, _ in plan), None)
        plan = [(i, lang) for i, lang in plan if i == first_idx] if first_idx is not None else []

    print(f"[plan] {len(plan)} traductions nécessaires "
          f"({len(langs)} langue(s), include_code={args.include_code})", file=sys.stderr)

    if not args.apply:
        print("[dry-run] aucune mutation, aucun appel API. Passe --apply pour exécuter "
              "(gated par ENABLED).", file=sys.stderr)
        # Détaille un échantillon du plan (5 premières cellules).
        sample = plan[:5]
        for i, lang in sample:
            nb = rows[i]["notebook"].split("/")[-1]
            print(f"  - {nb} cell[{rows[i]['cell_id'][:8]}] ->{lang} "
                  f"({len(rows[i]['text_fr'])}c FR)", file=sys.stderr)
        if len(plan) > 5:
            print(f"  ... +{len(plan) - 5} autres", file=sys.stderr)
        return 0

    # --apply : gate de sécurité ENABLED.
    if not ENABLED:
        print("[GATED] ENABLED=False dans translate_csv.py. Le moteur T3 est inactif : "
              "aucun appel API, aucune mutation. Pour activer (après GO user, #6949 "
              "moyen terme / #1650 Phase 1) : éditer ENABLED=True + définir "
              "OPENAI_API_KEY env + re-passer --apply.", file=sys.stderr)
        return 0

    return 0 if run_translations(rows, langs, args.include_code, out_path, args.smoke)[1] == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
