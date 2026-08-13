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
  - `ENABLED` contrôlé par la variable d'environnement `TRANSLATE_ENABLED`
    (`1`/`true`/`yes`/`on`). Défaut : inactif. Même avec `--apply`, le moteur
    refuse d'appeler l'API tant que `TRANSLATE_ENABLED` n'est pas activé. Triple
    gate : `TRANSLATE_ENABLED=1` (env, CI-callable sans monkeypatch — grain D
    #10043) + --apply + clé env. Fini l'activation in-memory par importlib (#10032).
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
  python translate_csv.py --csv x.csv --apply                              # GATED (TRANSLATE_ENABLED inactif) -> no-op
  # (activation : TRANSLATE_ENABLED=1 + OPENAI_API_KEY env + --apply ; CI-callable)
  python translate_csv.py --csv x.csv --apply --max-cells 50               # cap dur : 50 traductions max/passe
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
from pathlib import Path

# Sibling import: ``check_perimeter`` owns the SINGLE source of truth for the
# ordered target-language universe (#10109). This script's directory is on
# ``sys.path`` when run as ``python scripts/translation/translate_csv.py``;
# the explicit insert also covers ``python -m`` and pytest invocation.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_perimeter import TARGET_LANGS  # noqa: E402

# ----------------------------------------------------------------------------
# Gate de sécurité (HARD). Inactif par défaut ; activé par la variable
# d'environnement TRANSLATE_ENABLED (grain D #10043). CI-callable sans
# monkeypatch : `TRANSLATE_ENABLED=1 python translate_csv.py --csv x --apply`.
# Triple gate : env flag + --apply + clé API env. GO user = umbrella #10038.
# ----------------------------------------------------------------------------
_TRUTHY = ("1", "true", "yes", "on")


def _enabled_from_env() -> bool:
    """Lit la gate d'activation depuis l'env (TRANSLATE_ENABLED). Défaut : off.

    Résout le cran de sûreté posé pendant le développement (ENABLED=False en
    source) en une activation CI-callable sans monkeypatch : la CI positionne
    ``TRANSLATE_ENABLED=1`` dans son env, au lieu d'éditer la source en mémoire
    via ``importlib`` (workaround de #10032, désormais inutile).
    """
    return os.getenv("TRANSLATE_ENABLED", "").strip().lower() in _TRUTHY


ENABLED = _enabled_from_env()

# The 7 target languages, in the canonical order owned by ``check_perimeter``
# (#10109). A local divergent copy previously listed ``en ru pt es ar fa zh``
# -- a permutation that silently swaps translations the moment any positional
# access traverses it. Consume the single source instead.
TARGETS = list(TARGET_LANGS)
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
    # translate_policy (#10326): per-row translation policy. Empty = default
    # (translate if target empty or drifted). ``verbatim`` = never translate,
    # ``text_<lang> := text_fr`` is preserved as-is (no LLM call) -- for cells
    # whose pedagogical value is the source text itself (literary citation,
    # idiomatic example, prompt/completion to reproduce verbatim). Declared on
    # the source notebook cell (metadata) and carried through T1 --update; T3
    # short-circuits before the eligibility test so an empty target on a
    # verbatim row is never sent to the LLM. Backward compatible: a CSV without
    # the column reads as empty (DictReader) = default translate.
    "translate_policy",
]

# Recognised translate_policy values (#10326). ``verbatim`` is honored by T3 in
# this slice; ``verbatim-with-gloss`` (preserve FR + add a translated note) is a
# follow-up (needs T4 renderer changes) and currently falls back to default.
VERBATIM_POLICY = "verbatim"


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
def translation_plan(rows, langs, include_code=False, drifted=None):
    """Yield (row_index, lang) pour chaque cellule éligible x langue cible.

    Éligibilité (filtres cumulatifs) :
      - cell_type == 'markdown' (ou 'code' si include_code) ;
      - text_fr non vide ;
      - **soit** ``text_<lang>`` vide (cible à produire — sert aussi de cache/resume),
        **soit** ``(row_index, lang) in drifted`` (source FR modifiée depuis
        l'extraction CSV, le contenu cible existant est périmé et doit être
        régénéré — goulot d'intégration T3 ↔ T2 #10287).

    Args:
        rows: lignes CSV chargées (DictReader).
        langs: liste des langues cibles.
        include_code: inclure les cellules ``code`` (defaut False).
        drifted: ``None`` (comportement legacy : cible vide uniquement) ou
            ``set[(int, str)]`` de paires ``(row_index, lang)`` dont la source
            FR a dérivé. Computé par l'appelant (qui a accès au disque) via
            ``compute_drift_from_notebooks()`` — la fonction reste **pure**,
            pas d'I/O notebook ici (acceptance #10287 critère 2).

    Yields:
        ``(row_index, lang)`` — tuples éligibles.
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
        # #10326 preserve-verbatim: a row marked ``verbatim`` is never eligible,
        # even if its target is empty -- the source FR IS the deliverable for
        # every lang (literary citation, idiomatic example, prompt to reproduce).
        # Short-circuit BEFORE the target_empty/drifted test so an empty verbatim
        # target is not sent to the LLM on the first pass.
        if row.get("translate_policy", "").strip() == VERBATIM_POLICY:
            continue
        for lang in langs:
            target_empty = not row.get(f"text_{lang}", "").strip()
            if target_empty:
                yield i, lang
                continue
            if drifted is not None and (i, lang) in drifted:
                yield i, lang


def compute_drift_from_notebooks(rows, repo_root=None):
    """Identifie les row indices dont le ``src_hash`` ne match plus la source FR courante.

    Lit les ``.ipynb`` référencés par les lignes du CSV, compare
    ``cell_hash(cell_source_fr_actual)`` au ``row["src_hash"]`` extrait. Retourne
    les indices dont le hash diffère (= « SRC_DRIFT » au sens T2). Une lecture
    manquante ou un JSON cassé est traitée comme **non-drift** (skip défensif,
    comme ``check_translation_sync.py`` T2) — la vérité disque prime, l'absence
    d'info ne déclare pas un drift.

    Args:
        rows: lignes CSV chargées.
        repo_root: racine du dépôt. ``None`` → auto-détection via le chemin
            CSV (le repo contient ``scripts/translation/translate_csv.py``).

    Returns:
        ``set[int]`` — indices des lignes dont la source FR a dérivé.
    """
    if repo_root is None:
        repo_root = _detect_repo_root(rows)
    if repo_root is None:
        return set()

    # Cache (path, cell_id) -> source FR pour éviter de relire N fois le même notebook.
    notebook_cache: dict[tuple[str, str], str | None] = {}

    drifted_indices: set[int] = set()
    for i, row in enumerate(rows):
        csv_src_hash = row.get("src_hash", "").strip()
        if not csv_src_hash:
            # Pas de hash d'extraction → T2 ne peut pas conclure, on ne déclare pas drift.
            continue
        nb_rel = row.get("notebook", "").strip()
        cell_id = row.get("cell_id", "").strip()
        if not nb_rel or not cell_id:
            continue
        key = (nb_rel, cell_id)
        if key not in notebook_cache:
            notebook_cache[key] = _read_cell_source(nb_rel, cell_id, repo_root)
        actual = notebook_cache[key]
        if actual is None:
            continue  # cellule introuvable → skip défensif, pas drift
        if cell_hash(actual) != csv_src_hash:
            drifted_indices.add(i)
    return drifted_indices


def _detect_repo_root(rows) -> Path | None:
    """Détecte la racine du dépôt (contenant ``scripts/translation/``).

    On cherche d'abord depuis ``cwd``, puis en remontant les ancêtres (cas
    worktree où ``cwd`` peut être n'importe où). ``rows`` est conservé dans la
    signature pour permettre un affinement futur (chemin absolu d'un notebook
    comme heuristique) — aujourd'hui cwd suffit.
    """
    del rows  # noqa: F811 - unused parameter kept for future heuristic
    cwd = Path.cwd()
    if (cwd / "scripts" / "translation").is_dir():
        return cwd
    for ancestor in cwd.parents:
        if (ancestor / "scripts" / "translation").is_dir():
            return ancestor
    return None


def _read_cell_source(notebook_rel: str, cell_id: str, repo_root: Path) -> str | None:
    """Lit le source FR actuel d'une cellule depuis son notebook. None si KO.

    Lecture défensive : notebook introuvable, JSON cassé, cellule absente → None.
    On **ne lève pas** : T2 a le même comportement et l'absence d'info ne déclare
    pas un drift (cf acceptance #10287 — pas d'effet de bord silencieux sur
    ``text_<lang>``).
    """
    nb_path = repo_root / notebook_rel
    try:
        with open(nb_path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError):
        return None
    for cell in nb.get("cells", []):
        if cell.get("id") == cell_id:
            src = cell.get("source", "")
            if isinstance(src, list):
                return "".join(src)
            return src or ""
    return None


def run_translations(rows, langs, include_code, out_path, smoke, limit=None, drifted=None):
    """Exécute les traductions live (ENABLED doit être True). Mutate rows in place.

    Écrit le CSV incrémentalement après chaque cellule (resume-safe : un run
    interrompu reprend où il s'est arrêté grâce au cache text_<lang>).

    Args:
        drifted: ``set[(int, str)]`` — paires éligibles dont la source FR a
            dérivé. Si ``None``, comportement legacy (cible vide uniquement).
            Computé upstream dans ``main()`` via ``compute_drift_from_notebooks()``
            — ``run_translations`` reste pure sur le CSV (acceptance #10287).
    """
    providers = _provider_keys()
    if not providers:
        raise ValueError(
            "Aucune clé API trouvée. Définir OPENAI_API_KEY (et optionnellement "
            "OPENROUTER_API_KEY) dans l'environnement. Jamais de littéral inline "
            "(secrets-hygiene.md).")

    plan = list(translation_plan(rows, langs, include_code, drifted=drifted))
    if smoke:
        # 1 cellule x toutes les langues demandées (premier markdown trouvé).
        first_idx = next((i for i, _ in plan), None)
        plan = [(i, lang) for i, lang in plan if i == first_idx] if first_idx is not None else []
    if limit:
        plan = plan[:limit]
    total = len(plan)
    print(f"[plan] {total} traductions à produire ({len(langs)} langue(s))", file=sys.stderr)

    # #10326 preserve-verbatim (acceptance crit 1 + 5): a row marked ``verbatim``
    # is never sent to the LLM. T3's contract for it is ``text_<lang> := text_fr``
    # -- the source FR IS the deliverable for every lang (literary citation,
    # idiomatic example, prompt to reproduce). We copy FR into each target here
    # (no LLM call) and log every preserved cell so the count is visible, never
    # silent. Safe at the CSV layer: parity (FR_CONTAM) runs on RENDERED _en
    # notebooks (T4 pipeline, follow-up) not on the raw CSV, and sync drift is
    # keyed on src_hash (unchanged). The rows were excluded from the plan above.
    verbatim = [r for r in rows if r.get("translate_policy", "").strip() == VERBATIM_POLICY]
    for r in verbatim:
        fr_text = r.get("text_fr", "")
        fr_hash = r.get("hash_fr") or cell_hash(fr_text)
        for lang in langs:
            r[f"text_{lang}"] = fr_text
            r[f"hash_{lang}"] = fr_hash
        print(f"[verbatim] {r.get('notebook','').split('/')[-1]} "
              f"{r.get('cell_id','')[:8]} preserved (translate_policy=verbatim, "
              f"text_<lang> := text_fr, no LLM call)", file=sys.stderr)
    if verbatim:
        print(f"[verbatim] {len(verbatim)} cellule(s) préservée(s) — "
              f"aucune traduction (#10326)", file=sys.stderr)
        # Persist the text_<lang> := text_fr copies even when the plan is empty
        # (all cells verbatim): the resume-safe write_csv inside the plan loop
        # never runs in that case, so the copies would stay in memory only.
        write_csv(out_path, rows)

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
    ap.add_argument("--max-cells", type=int, default=300,
                    help="cap dur du nombre de traductions par exécution (défaut 300, grain D "
                         "#10043) : borne le coût d'une passe et protège contre un bug de hash "
                         "qui déclencherait une passe complète (24 470 cellules). Neutre sur la gate.")
    ap.add_argument("--limit", type=int, default=None,
                    help="[deprecated, alias de --max-cells] surcharge le cap si donné (backward "
                         "compat #10032). Préférer --max-cells.")
    args = ap.parse_args()

    # Cap effectif : --limit (deprecated alias) surcharge --max-cells sinon (grain D #10043).
    effective_cap = args.limit if args.limit is not None else args.max_cells

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

    # Compute drift depuis les notebooks (cf #10287) — la dérive est injectée
    # dans translation_plan() pour qu'une cellule ``text_<lang>`` non-vide
    # dont la source FR a changé devienne éligible à retraduction.
    # Erreurs de lecture (notebook introuvable, JSON cassé) → skip défensif.
    drifted_indices = compute_drift_from_notebooks(rows)
    drifted_pairs = {(i, lang) for i in drifted_indices for lang in langs}
    if drifted_pairs:
        print(f"[drift] {len(drifted_indices)} cellule(s) FR modifiée(s) "
              f"depuis l'extraction CSV ({len(drifted_pairs)} paires "
              f"cel. x langue éligibles à retraduction) — #10287", file=sys.stderr)

    plan = list(translation_plan(rows, langs, args.include_code, drifted=drifted_pairs))
    if args.smoke:
        first_idx = next((i for i, _ in plan), None)
        plan = [(i, lang) for i, lang in plan if i == first_idx] if first_idx is not None else []

    # dry-run : plan COMPLET (informatif) + cap appliqué en --apply (grain D #10043).
    print(f"[plan] {len(plan)} traductions nécessaires "
          f"({len(langs)} langue(s), include_code={args.include_code})", file=sys.stderr)
    if len(plan) > effective_cap and not args.smoke:
        print(f"[cap] --apply sera borné à {effective_cap} traductions (--max-cells) ; "
              f"{len(plan) - effective_cap} attendront une passe ultérieure.", file=sys.stderr)

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

    # --apply : gate de sécurité ENABLED (env TRANSLATE_ENABLED, grain D #10043).
    if not ENABLED:
        print("[GATED] TRANSLATE_ENABLED inactif. Le moteur T3 n'appelle pas l'API, "
              "ne mute rien. Activation CI-callable (sans monkeypatch) : "
              "`TRANSLATE_ENABLED=1 python translate_csv.py --csv x --apply` + clé "
              "OPENAI_API_KEY env. GO user = umbrella #10038.", file=sys.stderr)
        return 0

    return 0 if run_translations(rows, langs, args.include_code, out_path, args.smoke, effective_cap, drifted=drifted_pairs)[1] == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
