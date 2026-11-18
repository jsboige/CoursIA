"""Mesureur de la restitution en 3 actes (Distillation D5, veine E).

Source : Ashley, Herrmann, Friggstad, Schmidhuber — *On Narrative Information
and the Distillation of Stories* (arXiv:2211.12423v2, atelier NeurIPS 2022 /
etendu IEEE TPAMI 2024). PDF archive dans le gisement canonique sous
`Bibliographie IA/Argumentation/Rhetoric, Discourse & Persuasion/`.

Adaptation documentee dans la docstring du module
---------------------------------------------
Le papier definit l'information narrative comme
    I({f(x) | x in c} ; o(c))
ou f est une feature (essence narrative), c une collection d'atomes, et
o(c) l'ordre original de la collection. L'essence narrative maximise cette
information mutuelle ; elle est apprise contrastivement (InfoNCE modifie,
Eq. 2 du papier).

L'organe transpose la notion : on ne dispose pas d'un extracteur f_theta
bi-LSTM pre-entraine (pas dans le depot), et l'adaptation a un probleme
d'ordre entre une **trace d'analyse** (producteur, 6 axes + roles probatoires)
et une **restitution en 3 actes** (consommateur, R6). La transposition est :

    coverage       = |src ∩ rest| / |src|              # recall
    order_preserv  = Kendall-tau-style sur atomes partages
    score          = moyenne harmonique (coverage, order_preserv)

Justification : la distance de Levenshtein pure penalise les restitutions
qui ajoutent du **boilerplate** (preambule, recommandations) ; ce n'est pas
la semantique que le papier vise. La couverture mesure ce qui survit, l'ordre
mesure si l'ordre des atomes partages est respecte. Les deux ensemble
capturent `I(atomes ; ordre)` du papier sans extracteur bi-LSTM.

Instruments empruntables au papier :
- essence scalaire (Table 1) comme boussole de dimensionalite (non
  exploitable ici : pas d'extracteur bi-LSTM dans le scope)
- borne InfoNCE Eq. 2 comme garde-fou sur N

Divergence asummee : on transpose MI(atomes ; ordre) en preservation de
l'ordre de la trace vers la restitution, par couverture + Kendall-tau. C'est
une lecture possible, pas la seule. Voir issue #19603, section "Organe".
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# Verdict thresholds, sur le score composite (moyenne harmonique
# coverage * kendall-tau). Voir docstring du module pour la justification.
PRESERVES_HIGH = 0.80  # > 80 % : renderer preserve l'ordre ET la substance
PRESERVES_MID = 0.50   # 50 - 80 % : substance survit mais l'ordre casse


def levenshtein(a: List[str], b: List[str]) -> int:
    """Distance de Levenshtein classique sur deux sequences de tokens.

    Implementation iterative, O(len(a) * len(b)) memoire. Pas
    d'optimisation banded : on traite des corpus de < 64 atomes (N borne
    par la structure RestitutionActs = 3 actes avec sous-atomes finis).
    """
    if not a:
        return len(b)
    if not b:
        return len(a)
    n, m = len(a), len(b)
    # Rolling row pour economiser la memoire
    prev = list(range(m + 1))
    curr = [0] * (m + 1)
    for i in range(1, n + 1):
        curr[0] = i
        for j in range(1, m + 1):
            cost = 0 if a[i - 1] == b[j - 1] else 1
            curr[j] = min(
                curr[j - 1] + 1,        # insertion
                prev[j] + 1,            # deletion
                prev[j - 1] + cost,     # substitution
            )
        prev, curr = curr, prev
    return prev[m]


def normalised_order_score(source: List[str], restitution: List[str]) -> float:
    """Score de preservation de l'ordre (Levenshtein normalise), dans [0, 1].

    Conserve pour les tests unitaires ; le score canonique utilise la
    composition (couverture + Kendall-tau). Levenshtein penalise les
    sequences de longueurs tres differentes, ce qui est le cas source vs
    restitution (la restitution ajoute du boilerplate).

    Si les deux listes sont vides -> 1.0 (degenere) ; si l'une vide et
    l'autre non -> 0.0 (rien a comparer).
    """
    if not source and not restitution:
        return 1.0
    if not source or not restitution:
        return 0.0
    d = levenshtein(source, restitution)
    return 1.0 - d / max(len(source), len(restitution))


def coverage_score(source: List[str], restitution: List[str]) -> float:
    """Couverture = fraction des atomes source qui survivent dans restitution.

    Si la source est vide -> 1.0 (degenere). Si la restitution est vide
    mais la source non -> 0.0 (rien ne survit).

    C'est le **recall** du renderer : combien d'atomes de l'analyse
    arrivent au consommateur. Complementaire au Kendall-tau (precision
    sur l'ordre).
    """
    if not source:
        return 1.0
    src_set = set(source)
    rest_set = set(restitution)
    survived = src_set & rest_set
    return len(survived) / len(src_set)


def _dedup_preserve_order(seq: List[str]) -> List[str]:
    """Deduplique une liste en gardant l'ordre de premiere apparition."""
    seen = set()
    out: List[str] = []
    for a in seq:
        if a not in seen:
            seen.add(a)
            out.append(a)
    return out


def kendall_tau_on_shared(
    source: List[str], restitution: List[str]
) -> float:
    """Kendall-tau-style sur les atomes partages (ordre de 1ere apparition).

    On extrait la sous-liste dedupliquee des atomes de `source` qui
    survivent dans `restitution` (ordre = 1ere apparition dans `source`),
    puis la meme sous-liste dans `restitution` (ordre = 1ere apparition
    dans `restitution`). Si identiques -> 1.0 ; si inversees -> proche de
    0 ; sinon -> 1 - Levenshtein normalisee.

    Renvoie 1.0 si la liste partagee est vide ou de longueur 1 (degenere).
    """
    src_set = set(source)
    rest_set = set(restitution)
    shared = src_set & rest_set
    if len(shared) <= 1:
        return 1.0

    sub_src = _dedup_preserve_order([a for a in source if a in shared])
    sub_rest = _dedup_preserve_order([a for a in restitution if a in shared])

    d = levenshtein(sub_src, sub_rest)
    return 1.0 - d / max(len(sub_src), len(sub_rest))


def composite_preservation_score(
    source: List[str], restitution: List[str]
) -> float:
    """Score composite = moyenne harmonique (coverage, kendall_tau).

    La moyenne harmonique penalise les scores faibles : un corpus avec
    couverture 1.0 mais ordre 0.0 -> score 0.0 (le renderer a tout
    restitue mais dans le desordre, ce qui est une degradation semantique
    pour le lecteur). Symetriquement pour couverture 0.0.

    Renvoie 1.0 si les deux listes sont vides (degenere).
    """
    if not source and not restitution:
        return 1.0
    cov = coverage_score(source, restitution)
    tau = kendall_tau_on_shared(source, restitution)
    if cov == 0.0 or tau == 0.0:
        return 0.0
    return 2.0 * cov * tau / (cov + tau)


def infonce_lower_bound(num_atoms: float) -> float:
    """Borne inferieureuse de l'I narrative Eq. 2 du papier : log(N) - L_N.

    Ici on approxime L_N par 1 (borne triviale) pour N >= 1. Pour N < 1
    (degenerate), retourne 0.
    """
    import math
    if num_atoms < 1:
        return 0.0
    return math.log(num_atoms) - 1.0


@dataclass
class PreservationReport:
    corpus: str
    n_source: int
    n_restitution: int
    coverage: float
    order_preservation: float
    order_score: float  # score composite (moyenne harmonique coverage * tau)
    infonce_lower_bound: float
    verdict: str

    def as_dict(self) -> Dict[str, object]:
        return {
            "corpus": self.corpus,
            "n_source": self.n_source,
            "n_restitution": self.n_restitution,
            "coverage": round(self.coverage, 4),
            "order_preservation": round(self.order_preservation, 4),
            "order_score": round(self.order_score, 4),
            "infonce_lower_bound": round(self.infonce_lower_bound, 4),
            "verdict": self.verdict,
        }


def verdict_from_score(score: float) -> str:
    if score > PRESERVES_HIGH:
        return "PRESERVES >80%"
    if score >= PRESERVES_MID:
        return "PRESERVES 50-80%"
    return "LOSSY <50%"


# ---------------------------------------------------------------------------
# Extracteurs d'atomes
# ---------------------------------------------------------------------------

# Mots vides francais / anglais, ne portent pas d'information d'ordre
_STOPWORDS = frozenset({
    "le", "la", "les", "de", "du", "des", "un", "une", "et", "ou", "en",
    "a", "au", "aux", "ce", "ces", "cette", "il", "elle", "on", "nous",
    "vous", "ils", "elles", "leur", "leurs", "son", "sa", "ses", "mon",
    "ma", "mes", "ton", "ta", "tes", "notre", "votre", "que", "qui",
    "quoi", "dont", "ou", "ne", "pas", "plus", "moins", "tres", "trop",
    "peu", "car", "donc", "mais", "puis", "alors", "si", "comme", "the",
    "a", "an", "and", "or", "of", "to", "in", "on", "for", "is", "are",
    "was", "were", "be", "been", "this", "that", "these", "those", "it",
    "its", "with", "as", "by", "at", "from", "but", "not", "no",
})


_TOKEN_RE = re.compile(r"[\w]{4,}", re.UNICODE)


def extract_atomes_from_text(text: str, max_atoms: int = 64) -> List[str]:
    """Extrait une liste ordonnee d'atomes (mots significatifs) depuis un texte.

    Strategie : on tokenise, on filtre les stopwords et les mots < 4
    caracteres, on garde l'ordre de premiere apparition. `max_atoms` borne
    la sortie (cf. RestitutionActs = 3 actes avec sous-atomes finis, un
    corpus real depasse rarement 64 atomes distincts).

    C'est un proxy : le papier utilise un extracteur bi-LSTM contraste ;
    on n'a pas cet extracteur dans le scope de l'organe. La liste
    obtenue est utilisable pour la mesure d'ordre (Levenshtein), pas pour
    une mesure d'information mutuelle a la lettre.
    """
    seen = set()
    atoms: List[str] = []
    for m in _TOKEN_RE.finditer(text):
        w = m.group(0).lower()
        if w in _STOPWORDS:
            continue
        if w in seen:
            continue
        seen.add(w)
        atoms.append(w)
        if len(atoms) >= max_atoms:
            break
    return atoms


# ---------------------------------------------------------------------------
# Extraction depuis le format RestitutionActs (etat d'analyse)
# ---------------------------------------------------------------------------

# Les 6 axes analytiques du depot, source pour le scaffold RestitutionActs
_AXES = ["fallacies", "quality", "counter_arguments", "formal_pl",
         "formal_fol", "dung"]


def extract_atomes_from_state(state: Dict[str, object]) -> List[str]:
    """Extrait une liste ordonnee d'atomes depuis un etat d'analyse Argument.

    Convention : on itere les axes dans l'ordre AXES (defini dans 08d),
    et pour chaque axe on extrait les valeurs (pas les cles JSON
    structurelles comme 'name', 'text', 'score'). L'ordre resultant
    reflete l'ordre de l'analyse.

    Format de state attendu (cf. Argumentation-08d cell.9 ETAT de
    reference) : dict par axe, chaque axe contient une liste d'elements
    dont les valeurs portent les labels semantiques (name, text, etc.).

    Tolerance : si un axe est absent ou vide, on l'ignore. Si le format
    est inattendu (pas un dict), on extrait depuis la
    representation str de l'etat.
    """
    # Cles JSON structurelles a ignorer (pas de contenu semantique)
    _STRUCTURAL_KEYS = frozenset({
        "name", "text", "score", "value", "type", "id", "index",
        "level", "kind", "category",
    })
    if not isinstance(state, dict):
        return extract_atomes_from_text(str(state))
    atoms: List[str] = []
    for axe in _AXES:
        bucket = state.get(axe)
        if bucket is None:
            continue
        if isinstance(bucket, list):
            for item in bucket:
                if isinstance(item, dict):
                    for k, v in item.items():
                        if k in _STRUCTURAL_KEYS:
                            atoms.extend(extract_atomes_from_text(str(v)))
                        else:
                            # cle non-structurelle : cle + valeur
                            atoms.extend(extract_atomes_from_text(str(v)))
                else:
                    atoms.extend(extract_atomes_from_text(repr(item)))
        elif isinstance(bucket, dict):
            for k, v in bucket.items():
                atoms.extend(extract_atomes_from_text(repr(v)))
        else:
            atoms.extend(extract_atomes_from_text(repr(bucket)))
    return atoms


# ---------------------------------------------------------------------------
# Extraction depuis une restitution 3 actes (markdown)
# ---------------------------------------------------------------------------

_ACTE_SPLIT_RE = re.compile(
    r"(?:^|\n)\s*(?:#{1,6}\s+)?(?:Acte\s+[IVX]+\b|"
    r"Act\s+[IVX]+\b|"
    r"##\s+Acte\s+[IVX]+|"
    r"##\s+Act\s+[IVX]+)",
    re.IGNORECASE,
)


def extract_atomes_from_restitution(restitution_md: str) -> List[str]:
    """Extrait une liste ordonnee d'atomes depuis la restitution 3 actes.

    Strategie : on splitte par "Acte I/II/III" (regex permissive), on
    garde l'ordre des actes, et pour chaque acte on extrait les atomes
    dans l'ordre d'apparition. La liste resultante est l'ordre dans
    lequel le consommateur (renderer R6) presente l'information au
    lecteur.
    """
    parts = _ACTE_SPLIT_RE.split(restitution_md)
    # parts[0] est le preambule, on l'inclut s'il porte de l'info
    atoms: List[str] = []
    for part in parts:
        atoms.extend(extract_atomes_from_text(part))
    return atoms


# ---------------------------------------------------------------------------
# Mesure principale
# ---------------------------------------------------------------------------

def measure_preservation(
    corpus: str,
    source: List[str],
    restitution: List[str],
) -> PreservationReport:
    """Mesure la preservation de l'ordre entre une trace et sa restitution.

    Renvoie un PreservationReport avec verdict :
    - PRESERVES >80% si order_score > 0.80
    - PRESERVES 50-80% si 0.50 <= order_score <= 0.80
    - LOSSY <50% si order_score < 0.50

    Le score canonique est la moyenne harmonique (couverture, kendall-tau
    sur atomes partages). Voir docstring du module.
    """
    cov = coverage_score(source, restitution)
    tau = kendall_tau_on_shared(source, restitution)
    score = composite_preservation_score(source, restitution)
    n = max(len(source), len(restitution))
    lower_bound = infonce_lower_bound(float(n))
    verdict = verdict_from_score(score)
    return PreservationReport(
        corpus=corpus,
        n_source=len(source),
        n_restitution=len(restitution),
        coverage=cov,
        order_preservation=tau,
        order_score=score,
        infonce_lower_bound=lower_bound,
        verdict=verdict,
    )


def measure_from_files(
    corpus: str,
    source_path: Path,
    restitution_path: Path,
) -> PreservationReport:
    """Mesure la preservation depuis deux fichiers (JSON state + MD restitution)."""
    source_data = json.loads(source_path.read_text(encoding="utf-8"))
    if isinstance(source_data, dict) and "state" in source_data:
        source_data = source_data["state"]
    source_atoms = extract_atomes_from_state(source_data)
    rest_md = restitution_path.read_text(encoding="utf-8")
    rest_atoms = extract_atomes_from_restitution(rest_md)
    return measure_preservation(corpus, source_atoms, rest_atoms)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _build_argparser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="narrative_information",
        description="Mesureur de preservation de l'ordre (Distillation D5).",
    )
    p.add_argument(
        "--source",
        type=Path,
        required=True,
        help="Chemin vers l'etat d'analyse (JSON)",
    )
    p.add_argument(
        "--restitution",
        type=Path,
        required=True,
        help="Chemin vers la restitution 3 actes (markdown)",
    )
    p.add_argument(
        "--corpus",
        default="",
        help="Nom du corpus (pour le rapport)",
    )
    p.add_argument(
        "--json",
        action="store_true",
        help="Sortie JSON",
    )
    return p


def main(argv: Optional[List[str]] = None) -> int:
    args = _build_argparser().parse_args(argv)
    corpus = args.corpus or args.source.stem
    report = measure_from_files(corpus, args.source, args.restitution)
    if args.json:
        print(json.dumps(report.as_dict(), ensure_ascii=False, indent=2))
    else:
        d = report.as_dict()
        print(f"Mesureur de preservation D5 (Ashley et al., arXiv 2211.12423)")
        print(f"  corpus         : {d['corpus']}")
        print(f"  source atomes  : {d['n_source']}")
        print(f"  restitu atomes : {d['n_restitution']}")
        print(f"  order_score    : {d['order_score']:.4f}")
        print(f"  infonce bound  : {d['infonce_lower_bound']:.4f} (log(N)-1)")
        print(f"  verdict        : {d['verdict']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())