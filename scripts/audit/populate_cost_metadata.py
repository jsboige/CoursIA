#!/usr/bin/env python3
"""
populate_cost_metadata.py — Peuple `nb.metadata['cost']` pour les notebooks sans matrice de coût.

Issue #8056 — matrice coût/ressource par notebook. Issue #8587 (MERGED) a ajouté le
champ `qcc_tokens_est` au schema + validator (Litmus 7) + tests. Ce qui reste :
~69 notebooks QuantConnect (QuantBook) SANS aucune `metadata.cost` — donc présentés
comme « gratuits » (Litmus 7 flag). Les 10 PR de migration précédentes (#8418..#8585)
étaient des hand-edits par notebook ; ce script déterministe clôt le gap en une passe.

But : pour chaque notebook QuantConnect utilisant `QuantBook()` et dépourvu de
`metadata['cost']`, insérer le bloc de coût canonique (profile `quantbook`) dérivé :
  - `qcc_tokens_est` via l'heuristic documentée `max(400, n_code_cells × 70)`
    (cf docs/notebook-metadata/cost-matrix.md §"Coût QCC / QuantConnect", #8056)
  - les champs obligatoires (schema cost-matrix.md) aux valeurs de consensus des
    13 quantbooks déjà migrés (#8585) ou aux défauts du schema
  - `null` pour les champs notebook-specific (`reduced_pedagogical`,
    `free_alternative`) qui exigent un jugement humain — jamais fabriqués

Idempotent : JAMAIS écrase un bloc `cost` existant (un notebook déjà peuplé est
skippé). Litmus anti-LIGHT : ce script APPLIQUE une transformation documentée et
déterministe ; le verdict final (la metadata est-elle *juste* ?) = revue humaine.
Cf `check_cost_metadata.py` (le vérificateur), `docs/notebook-metadata/cost-matrix.md`.

Usage :
  # Audit (dry-run) — liste ce qui serait peuplé, n'écrit rien
  python scripts/audit/populate_cost_metadata.py <notebook-ou-dossier>.ipynb --profile quantbook

  # Appliquer
  python scripts/audit/populate_cost_metadata.py <notebook-ou-dossier> --profile quantbook \\
      --by myia-po-2024:CoursIA-2 --apply
"""

import argparse
import datetime as _dt
import json
import re
import sys
from pathlib import Path


QUANTBOOK_RE = re.compile(r"QuantBook\(\)|self\.QuantBook")

# Champ obligatoires + defaults pour le profile `quantbook`.
# Valeurs : consensus des 13 quantbooks migrés (#8585) > défaut schema (cost-matrix.md
# §mandatory) > null honest pour les champs notebook-specific.
# NOTE doc-vs-practice : le template doc (cost-matrix.md §"QC / QuantConnect") montre
# `api_provider: qc_cloud` / `external_account: qc`, mais la PRATIQUE migrée (13/13)
# utilise `api_provider: none` / `external_account: quantconnect-organization`. On suit
# la pratique migrée (consistance intra-famille QC) ; l'écart est documenté ici, pas caché.


def _count_code_cells(nb: dict) -> int:
    """Nombre de cellules code non-vides (source non-whitespace)."""
    n = 0
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        src = "".join(cell.get("source", []))
        if src.strip():
            n += 1
    return n


def _uses_quantbook(nb: dict) -> bool:
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        if QUANTBOOK_RE.search("".join(cell.get("source", []))):
            return True
    return False


def qcc_tokens_estimate(n_code_cells: int) -> int:
    """Heuristic QCC documentée (cost-matrix.md §"Coût QCC / QuantConnect", #8056) :
    ~70 QCC par cellule code, plancher 400. Estimation (suffixe `_est`), pas mesure."""
    return max(400, n_code_cells * 70)


def build_quantbook_cost(nb: dict, by: str, today: str) -> dict:
    """Construit le bloc `metadata['cost']` canonique pour un quantbook.

    Champs dérivés : `qcc_tokens_est` (heuristic), `last_validated` (date de création
    de la metadata — pas date d'exécution QC Cloud ; `validator: qc_cloud` nomme la
    MÉTHODE canonique de validation, pas une exécution récente).
    Champs notebook-specific (`reduced_pedagogical`, `free_alternative`) : null
    (jugement humain ; QuantBook = QC uniquement → pas d'alternative locale).
    """
    n_code = _count_code_cells(nb)
    return {
        "api_usd_est": 0.0,  # QCC = quota non-USD (schema default 0)
        "api_provider": "none",  # 13/13 migrés ; schema default "none"
        "qcc_tokens_est": qcc_tokens_estimate(n_code),  # heuristic max(400, n×70)
        "cpu_min": 0,  # QC s'exécute sur le cloud (QCC) ; CPU local = 0 (schema default)
        "gpu_required": False,  # quantbook de recherche, pas de GPU local
        "network": True,  # API QuantConnect obligatoire (HTTPS) (13/13 migrés)
        "external_account": "quantconnect-organization",  # 12/13 migrés (QC user + token)
        "free_alternative": None,  # QuantBook = QC uniquement, pas d'alternative locale
        "reduced_pedagogical": None,  # notebook-specific (jugement humain) ; null = honnête
        "reproducibility": "MED",  # single-run backtest stochastique (doc template)
        "last_validated": today,  # date d'établissement de la metadata (script)
        "validator": "qc_cloud",  # Litmus 5 : qc_cloud pour QuantBook (13/13)
    }


# --- Profile search-cpu : notebooks CPU-purs déterministes (Search, etc.) -------
# Issue #8056 (P1) — rollout family-partitionné. Le profile `search-cpu` couvre les
# notebooks d'algorithmes CPU-purs déterministes (Search/Part1-Foundations, etc.) :
# gratuit, pas d'API/GPU/compte externe, reproductibilité HIGH. Réutilisable pour
# les tranches futures (résiduel ~105 notebooks Search).

# Signaux d'usage non-CPU-pure — si PRÉSENTS, le notebook n'est PAS éligible au
# profile `search-cpu` (coût non-nul) → skip (ne pas fabriquer un cost « 0/CPU » faux).
_API_RE = re.compile(
    # `mistralai` couvre le SDK officiel Mistral (`from mistralai import Mistral`),
    # que `mistral\.[a-z]` rate (pas de `.` après mistral). Concern #1 Hermes (po-2026).
    r"openai|anthropic|mistral\.[a-z]|\bmistralai\b|ChatCompletion|replicate\.|gpt-image|dall-?e",
    re.I,
)
_GPU_RE = re.compile(
    r"\.cuda\(|torch\.cuda|device_lib|jax\.devices|tf\.config.*gpu"
)
_ACCOUNT_RE = re.compile(
    r"HF_TOKEN|OPENAI_API_KEY|ANTHROPIC_API_KEY|MISTRAL_API_KEY|"
    r"os\.getenv\(\s*[\"']\w*(_KEY|_TOKEN|API)",
)
# Libs HTTP génériques = réseau requis (un requests.get/httpx/urllib n'est pas
# CPU-pur). On matche les imports ET les appels typiques pour éviter le FP sur le
# mot isolé « requests » en prose (cf G.1, concern #2 Hermes po-2026 sur #8660) ;
# mieux vaut FP-skip (gate conservatrice) que miss un notebook API payant.
_HTTP_LIB_RE = re.compile(
    r"\b(?:import|from)\s+(?:requests|httpx|aiohttp|urllib)\b"
    r"|(?:requests|httpx)\.(?:get|post|put|delete|patch|head|request)\s*\("
    r"|urllib\.request\b",
    re.I,
)
# Restore NuGet au runtime = réseau requis (packages .NET téléchargés à l'exécution).
# ATTENTION : ne PAS matcher le mot isolé « NuGet » (FP sur la prose, ex. « Aucune
# dépendance NuGet ») — exiger un vrai préfixe de directive (#r "nuget: …) ou commande
# dotnet. Cf G.1 (vérifier les signaux sur la source exacte, pas un proxy).
_NUGET_RE = re.compile(r"#r\s+[\"']?nuget|!dotnet add package|!dotnet restore")


def _source_text(nb: dict) -> str:
    """Concatène le source de toutes les cellules (pour scan de signaux)."""
    parts = []
    for cell in nb.get("cells", []):
        s = cell.get("source", "")
        parts.append("".join(s) if isinstance(s, list) else s)
    return "\n".join(parts)


def is_cpu_pure(nb: dict) -> bool:
    """True si le notebook n'a AUCUN signal API/GPU/compte/HTTP-lib/QuantBook.

    Gate de sécurité du profile `search-cpu` : un notebook qui appelle une API
    (provider nommé OU SDK officiel comme `mistralai`), le GPU, ou une lib HTTP
    générique (`requests`/`httpx`/`urllib`) n'est PAS gratuit-CPU → le profile est
    inadéquat → skip. Évite de fabriquer un cost « 0 USD / CPU-only » sur un
    notebook payant (Litmus anti-LIGHT). Trade-off assumé : conservateur (FP-skip)
    plutôt que miss — un notebook skip à tort reste sans cost-matrix, jamais
    marqué faux-gratuit.
    """
    if _uses_quantbook(nb):
        return False
    src = _source_text(nb)
    return not (
        _API_RE.search(src)
        or _GPU_RE.search(src)
        or _ACCOUNT_RE.search(src)
        or _HTTP_LIB_RE.search(src)
    )


def _cpu_min_estimate(n_code: int) -> int:
    """Heuristic cpu_min (minutes, estimé) : ≤15 cellules code → 1, 16-25 → 2, >25 → 3."""
    if n_code <= 15:
        return 1
    if n_code <= 25:
        return 2
    return 3


def build_search_cpu_cost(nb: dict, by: str, today: str) -> dict:
    """Bloc `metadata['cost']` canonique pour un notebook CPU-pur déterministe.

    Champs dérivés (honnêtes, pas fabriqués) :
      - `cpu_min` : heuristic via _count_code_cells (estimation, suffixe non-_est car
        champ entier conventionnel).
      - `network` : True si restore NuGet détecté au runtime, False sinon.
    `validator: manual` = matrice coût établie par inspection du source (pas une
    re-exécution machine claimée). `free_alternative: self` = sentinelle canonique
    (le notebook est DÉJÀ gratuit/CPU). `reduced_pedagogical: null` = honnête (ces
    notebooks ne sont pas des sous-ensembles les uns des autres).
    """
    n_code = _count_code_cells(nb)
    network = bool(_NUGET_RE.search(_source_text(nb)))
    return {
        "api_usd_est": 0.0,  # gratuit
        "api_provider": "none",
        "qcc_tokens_est": 0,  # non-QC
        "cpu_min": _cpu_min_estimate(n_code),  # heuristic
        "gpu_min": 0,
        "gpu_required": False,
        "vram_gb": 0,
        "vram_tier": "NONE",
        "network": network,  # True si NuGet restore au runtime
        "external_account": "none",
        "free_alternative": "self",  # sentinelle canonique : déjà gratuit
        "reduced_pedagogical": None,  # notebook-specific (jugement humain) ; null = honnête
        "reproducibility": "HIGH",  # algorithmes déterministes
        "last_validated": today,  # date d'établissement de la metadata (inspection source)
        "validator": "manual",  # inspection source, pas re-exécution machine claimée
    }


# --- Dispatch par profile -------------------------------------------------------
# Chaque profile : (gate d'éligibilité, builder de cost, raison de skip si inéligible).
PROFILES = {
    "quantbook": {
        "eligible": _uses_quantbook,
        "build": build_quantbook_cost,
        "skip_reason": "skipped-no-quantbook",
    },
    "search-cpu": {
        "eligible": is_cpu_pure,
        "build": build_search_cpu_cost,
        "skip_reason": "skipped-not-cpu-pure",
    },
}


def populate_notebook(path: Path, profile: str, by: str, today: str, apply: bool) -> str:
    """Peuple metadata.cost pour le profile donné, si éligible + absent.

    Returns: 'populated' | 'skipped-has-cost' | '<profile skip_reason>' | 'error: ...'.
    """
    prof = PROFILES[profile]
    try:
        raw = path.read_text(encoding="utf-8")
        nb = json.loads(raw)
    except Exception as e:
        return f"error: {e}"

    if not prof["eligible"](nb):
        return prof["skip_reason"]

    meta = nb.setdefault("metadata", {})
    if "cost" in meta:  # idempotent : ne JAMAIS écraser un bloc existant
        return "skipped-has-cost"

    cost = prof["build"](nb, by=by, today=today)
    if not apply:
        return "populated"  # dry-run : on rapporte, on n'écrit pas

    meta["cost"] = cost
    # Round-trip json indent=1 (convention repo), sort_keys=False (préserve l'ordre
    # d'insertion original des notebooks non sérialisés avec sort_keys), LF-only.
    # Préserve le trailing-newline original (byte-surgical : ne churn pas les
    # notebooks qui n'en ont pas — C913-L).
    had_trailing_nl = raw.endswith("\n")
    out = json.dumps(nb, indent=1, ensure_ascii=False, sort_keys=False)
    if had_trailing_nl:
        out += "\n"
    path.write_text(out, encoding="utf-8", newline="\n")
    return "populated"


def iter_notebooks(target: Path):
    """Énumère les .ipynb sous target (fichier unique ou dossier récursif),
    en excluant _output.ipynb, .ipynb_checkpoints/, /backtests/."""
    if target.is_file():
        yield target
        return
    for p in sorted(target.rglob("*.ipynb")):
        s = str(p).replace("\\", "/")
        if "_output" in p.name:
            continue
        if ".ipynb_checkpoints" in s:
            continue
        if "/backtests/" in s:
            continue
        yield p


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("target", type=Path, help="Notebook .ipynb ou dossier à peupler")
    ap.add_argument("--profile", choices=list(PROFILES), default="quantbook",
                    help=f"Profile de coût (implémentés : {', '.join(PROFILES)})")
    ap.add_argument("--by", default="anonymous",
                    help="machine:workspace (provenance, pour le rapport)")
    ap.add_argument("--apply", action="store_true",
                    help="Écrire les modifications (défaut : dry-run)")
    ap.add_argument("--today", default=None,
                    help="Date ISO pour last_validated (défaut : aujourd'hui)")
    args = ap.parse_args(argv)

    if not args.target.exists():
        print(f"ERROR: {args.target} n'existe pas", file=sys.stderr)
        return 2

    today = args.today or _dt.date.today().isoformat()
    skip_key = PROFILES[args.profile]["skip_reason"]
    counts = {"populated": 0, "skipped-has-cost": 0, skip_key: 0}
    errors = []

    for nb_path in iter_notebooks(args.target):
        status = populate_notebook(nb_path, profile=args.profile,
                                   by=args.by, today=today, apply=args.apply)
        if status.startswith("error"):
            errors.append((nb_path, status))
        elif status in counts:
            counts[status] += 1
            if status == "populated":
                print(f"  {'WRITE' if args.apply else 'DRY-RUN'}  {nb_path}")
        else:
            errors.append((nb_path, f"unexpected: {status}"))

    mode = "APPLY" if args.apply else "DRY-RUN"
    print(f"\n[{mode}] profile={args.profile} by={args.by} today={today}")
    print(f"  populated (sans cost, éligible) : {counts['populated']}")
    print(f"  skipped-has-cost (déjà peuplé)   : {counts['skipped-has-cost']}")
    print(f"  {skip_key:<35} : {counts[skip_key]}")
    if errors:
        print(f"  errors                           : {len(errors)}", file=sys.stderr)
        for p, e in errors:
            print(f"    {p}: {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
