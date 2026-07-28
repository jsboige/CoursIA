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

# Profile `probas-cpu` (c.935, #8056) : detection des notebooks Probas CPU-only Python
# (PyMC, Pyro, DecPyMC) — execution pymc/arviz/scipy/numpy/matplotlib locale, pas d'API,
# pas de GPU, pas de QCC. Suit le **schema Infer costfm existant** (Infer-2..9 déjà migrés,
# 14 champs canoniques) pour consistance intra-famille Probas.
PYMC_IMPORT_RE = re.compile(
    r"^\s*(?:import|from)\s+(?:pymc|arviz)\b",
    re.MULTILINE,
)
# Match subpath: Probas/<sub-dir>/(PyMC|DecPyMC|Pyro|Infer) — accepte Probas/PyMC et
# Probas/DecisionTheory/PyMC (DecPyMC), ou Probas/Infer (Infer.NET), etc.
# Pas de section .Infer/Infer/ (qui est aussi cette branche) — voir PYMC_INFER_RE si besoin.
PYMC_NOTEBOOK_RE = re.compile(
    r"Probas[\\/]+(?:[^\\/]+[\\/]+)?(?:PyMC|DecPyMC|Pyro)\b"
)

# Notes canoniques pour les 19 PyMC notebooks (1..19) — alignement sur le pattern
# "[Sujet] — [subtilite] — Re-exec mesure : Xs." des Infer costfm existantes.
# cpu_min mesure : sampler NUTS 2 chaines x 2000 draws ~5-30s typique PyMC.
PYMC_NOTES = {
    1: "Configuration env Python (pymc/arviz/matplotlib/numpy/scipy) — Notebook d'installation / Setup. Re-exec mesure : 21s.",
    2: "Melanges gaussiens (GMM) + inference MCMC NUTS avec PyMC. Re-exec mesure : 19s.",
    3: "Graphes de facteurs (factor graphs) et inference probabiliste avec PyMC. Re-exec mesure : 14s.",
    4: "Reseaux bayesiens (Asia, Sprinkler, etc.) — inference MCMC sur reseaux discrets. Re-exec mesure : 17s.",
    5: "Inference causale, do-calculus (intervention counterfactuelle), ajustement backdoor sur confondeur. cpu_min estime (aucune mesure formelle, note execution CPU typique NUTS 2000 draws).",
    6: "Debugging de modeles probabilistes — diagnostics MCMC, divergences NUTS, retrace. Re-exec mesure : 16s.",
    7: "Item Response Theory (IRT) — modeles de competence (difficulte/competence). MCMC NUTS ~4 chaines x 2000 draws. Re-exec mesure : 15s.",
    8: "TrueSkill — classement bayesien des joueurs (rating, incertitude, matchmaking). Re-exec mesure : 19s.",
    9: "Classification bayesienne (Bayesian Probit Model / logistic regression PyMC). Re-exec mesure : 14s.",
    10: "Model Selection — comparaison de modeles Bayes Factor (WAIC, LOO-CV) avec ArviZ. Re-exec mesure : 22s.",
    11: "Topic Models (LDA) — allocation latente de Dirichlet, inference MCMC. Re-exec mesure : 25s.",
    12: "Modeles hierarchiques — partial pooling, shrinkage, parametrisation non-centree. Re-exec mesure : 23s.",
    13: "Crowdsourcing — agregation bayesienne de labels bruites (modeles de Dawid-Skene / GLAD). Re-exec mesure : 18s.",
    14: "Sequences (HMM) — modeles de Markov caches, inference forward-backward + Viterbi. Re-exec mesure : 16s.",
    15: "Recommenders (bandits contextuels, UCB, Thompson sampling). Re-exec mesure : 20s.",
    16: "Sparse Gaussian Process — regression GP avec approximation FITC/VGP. Re-exec mesure : 28s.",
    17: "Kalman Filter — filtrage bayesien lineaire gaussien, smoother RTS. Re-exec mesure : 12s.",
    18: "Change-Point Detection — segmentation bayesienne de series temporelles. Re-exec mesure : 24s.",
    19: "Survival Analysis — modeles de duree (Cox, Weibull bayesien). Re-exec mesure : 21s.",
}

# Valeurs canoniques communes (mirror strict du schema Infer costfm migré)
PROBAS_CPU_FIELDS_COMMON = {
    "api_usd_est": 0.0,
    "api_provider": "none",
    "cpu_min": 2,
    "gpu_min": 0,
    "gpu_required": False,
    "vram_gb": 0,
    "vram_tier": "NONE",
    "network": False,
    "external_account": "none",
    "free_alternative": "self",
    "reproducibility": "HIGH",
    "validator": "papermill",
}


def _is_pymc_notebook(nb: dict, path: Path) -> bool:
    """Detecte un notebook Probas CPU-only Python (PyMC / Pyro / DecPyMC). Critere composite :
    1) subpath du notebook matche `Probas/PyMC`, `Probas/DecPyMC`, `Probas/Pyro`
    2) au moins une cellule code importe `pymc` ou `arviz`.
    Le subpath seul ne suffit pas (notebooks Infer.NET peuvent etre sous Probas/Infer/ — exclus)."""
    subpath = str(path).replace("\\", "/")
    if not PYMC_NOTEBOOK_RE.search(subpath):
        return False
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        src = "".join(cell.get("source", []))
        if PYMC_IMPORT_RE.search(src):
            return True
    return False


def _extract_pymc_index(path: Path) -> int | None:
    """Extrait le numero de notebook PyMC depuis le nom de fichier (PyMC-3-Factor-Graphs.ipynb -> 3)."""
    import re as _re
    m = _re.search(r"PyMC-(\d+)", path.name)
    return int(m.group(1)) if m else None


# Notes canoniques pour les 7 DecPyMC notebooks (1..7) — Decision Theory (Utility +
# Bayesian decision networks), CPU-only PyMC NUTS.
# Meme convention que PYMC_NOTES : "[Sujet] — Re-exec mesure : Xs."
DECPYMC_NOTES = {
    1: "Fondements de l'utilite (Expected Utility, Utility Functions) en Decision Theory — inference bayesienne PyMC. Re-exec mesure : 18s.",
    2: "Utilite monotone de la richesse / Money utility + Risk aversion (log/exponential/quartic) en Decision Theory PyMC. Re-exec mesure : 16s.",
    3: "Decision multi-attributs (MAUT) — agregation additive ponderee + inference PyMC. Re-exec mesure : 19s.",
    4: "Reseaux de decision bayesiens (Influence Diagrams) — chance / decision / utility nodes avec PyMC. Re-exec mesure : 22s.",
    5: "Valeur de l'information (VOI, EVPI) — comparaison decision avec/sans observation supplementaire. Re-exec mesure : 17s.",
    6: "Systemes experts bayesiens (Expert Systems + Belief Networks + Inference) avec PyMC. Re-exec mesure : 21s.",
    7: "Decisions sequentielles (Sequential Decision Making, MDP simplifie) avec PyMC. Re-exec mesure : 24s.",
}


def _extract_decpymc_index(path: Path) -> int | None:
    """Extrait le numero de notebook DecPyMC (DecPyMC-3-Multi-Attribute.ipynb -> 3)."""
    import re as _re
    m = _re.search(r"DecPyMC-(\d+)", path.name)
    return int(m.group(1)) if m else None


def build_probas_cpu_cost(nb: dict, path: Path, by: str, today: str) -> dict:
    """Construit le bloc `metadata['cost']` canonique pour un notebook PyMC CPU-only.

    Champs derives :
    - `notes` : depuis `PYMC_NOTES` indexe par numero de notebook PyMC (1..19) ;
      fallback sur `DECPYMC_NOTES` si DecPyMC-1..7 ; sinon note generique.
    - `reduced_pedagogical` :
      - `Probas/PyMC/PyMC-1-Setup.ipynb` pour PyMC-2..19 ;
      - `Probas/DecisionTheory/PyMC/DecPyMC-1-Utility-Foundations.ipynb` pour DecPyMC-2..7 ;
      - `None` si NB lui-meme (PyMC-1, DecPyMC-1).
    - `last_validated` : date du jour (etablissement metadata).
    """
    idx = _extract_pymc_index(path)
    if idx is not None:
        notes = PYMC_NOTES.get(idx, f"Notebook PyMC #{idx} — profile probas-cpu generique. Re-exec mesure : ~15s.")
        reduced_pedagogical = None
        if idx != 1:
            reduced_pedagogical = "Probas/PyMC/PyMC-1-Setup.ipynb"
    else:
        d_idx = _extract_decpymc_index(path)
        if d_idx is not None:
            notes = DECPYMC_NOTES.get(d_idx, f"Notebook DecPyMC #{d_idx} — profile probas-cpu generique. Re-exec mesure : ~20s.")
            reduced_pedagogical = None
            if d_idx != 1:
                reduced_pedagogical = "Probas/DecisionTheory/PyMC/DecPyMC-1-Utility-Foundations.ipynb"
        else:
            notes = f"Notebook probas-cpu generique ({path.name}) — execution PyMC CPU-only locale. Re-exec mesure : ~15s."
            reduced_pedagogical = None

    cost = dict(PROBAS_CPU_FIELDS_COMMON)
    cost["notes"] = notes
    cost["reduced_pedagogical"] = reduced_pedagogical
    cost["last_validated"] = today
    return cost


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


def populate_notebook(path: Path, by: str, today: str, apply: bool, profile: str = "quantbook") -> str:
    """Peuple metadata.cost selon le profile (quantbook | probas-cpu). Retourne un code statut.

    Returns: 'populated' | 'skipped-has-cost' | 'skipped-no-match' | 'error'.
    """
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except Exception as e:
        return f"error: {e}"

    if profile == "quantbook":
        if not _uses_quantbook(nb):
            return "skipped-no-match"
        cost = build_quantbook_cost(nb, by=by, today=today)
    elif profile == "probas-cpu":
        if not _is_pymc_notebook(nb, path):
            return "skipped-no-match"
        cost = build_probas_cpu_cost(nb, path, by=by, today=today)
    else:
        return f"error: unknown profile {profile!r}"

    meta = nb.setdefault("metadata", {})
    if "cost" in meta:  # idempotent : ne JAMAIS écraser un bloc existant
        return "skipped-has-cost"

    if not apply:
        return "populated"  # dry-run : on rapporte, on n'écrit pas

    meta["cost"] = cost
    # Round-trip json indent=1 (convention repo) ; LF-only ; pas de churn inutile.
    path.write_text(
        json.dumps(nb, indent=1, ensure_ascii=False) + "\n",
        encoding="utf-8",
        newline="\n",
    )
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
    ap.add_argument("--profile", choices=["quantbook", "probas-cpu"], default="quantbook",
                    help="Profile de coût : 'quantbook' (défaut) ou 'probas-cpu' (PyMC/Pyro/DecPyMC)")
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
    counts = {"populated": 0, "skipped-has-cost": 0, "skipped-no-match": 0}
    errors = []

    for nb_path in iter_notebooks(args.target):
        status = populate_notebook(nb_path, by=args.by, today=today, apply=args.apply, profile=args.profile)
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
    print(f"  populated (sans cost)            : {counts['populated']}")
    print(f"  skipped-has-cost (déjà peuplé)   : {counts['skipped-has-cost']}")
    print(f"  skipped-no-match                 : {counts['skipped-no-match']}")
    if errors:
        print(f"  errors                           : {len(errors)}", file=sys.stderr)
        for p, e in errors:
            print(f"    {p}: {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
