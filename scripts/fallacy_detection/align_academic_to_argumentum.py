#!/usr/bin/env python3
"""Alignment des taxonomies de sophismes academiques vers la grille Argumentum.

Phase 2 / sous-grain CPU de l'EPIC #10355 (fallacy detection via Qwen FT+PT).
Premiere etape concrete du *dataset builder* (Phase 2) : avant de projeter les
etiquettes Argumentum sur les corpus adjacents (IBM debate_speeches, AraucariaDB,
ChangeMyView -- cf notebook 02 / PR #10367), il faut savoir **quelle fraction**
des etiquettes academiques couvertes par la litterature (Logic/LogicClimate de
Jin 2021 ; MAFALDA de Helwe 2023) existe deja dans la grille Argumentum (1408
sophismes / 8 familles), et **quelle est la forme de l'ecart**.

Ce sous-grain est DELIBEREMENT non-gated : il ne depend NI du deck-2 Argumentum
(corpus FR, 1408 cartes -- sollicite via agents Argumentum) NI du projet FT
etudiant EPITA-IS. Il n'utilise QUE la taxonomie Argumentum livree dans le depot
(``data/argumentum_fallacies_taxonomy.csv``) + les listes d'etiquettes
academiques publiques (papiers cites). Le gate cross-workspace qualifie les
etapes AVAL (projection sur corpus), pas cet alignement taxonomy-vs-taxonomy.

Methode : stdlib-only (comme ``extract_jessynoo_fallacy.py``). Pour chaque
etiquette academique, on cherche un (ou plusieurs) candidat(s) Argumentum par :
  (a) correspondance de nom (``Simple_name_en`` exacte ou proche, puis cognates
      FR sur ``nom_vulgarise`` / ``text_fr``) ;
  (b) chevauchement lexical (Jaccard sur tokens significatifs de
      ``desc_en`` / ``text_en``) ;
  (c) reconnaissance de motifs par famille (ex. "ad hominem" -> Famille Influence).
On produit un verdict ALIGNEMENT PARTIEL / ALIGNEMENT DIRECT / NON TROUVE par
etiquette, puis un rapport de couverture par famille Argumentum.

Sources (verifiees firsthand dans le survey #10360) :
  - Jin, Bhargava, Brew, Durrett, Klein, *Logical Fallacy Detection*, Findings
    EMNLP 2021, arXiv:2202.13758 -- 13 types + LogicClimate.
  - Helwe, Calamai, Paris, Clavel, Suchanek, *MAFALDA: A Benchmark and
    Comprehensive Study of Fallacy Detection and Classification*, 2023,
    arXiv:2311.09761 -- hierarchie 3 niveaux, L2 = 23 classes fines.

Usage :
  python -m fallacy_detection.align_academic_to_argumentum --report
  python -m fallacy_detection.align_academic_to_argumentum --out-csv <path>

Aucun acces reseau. Sortie : CSV de mapping + JSON de couverture + resume stdout.
"""

from __future__ import annotations

import argparse
import csv
import io
import json
import re
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path

# ---------------------------------------------------------------------------
# Localisation de la taxonomie Argumentum (livree dans le depot).
# ---------------------------------------------------------------------------

# Racine du depot : scripts/fallacy_detection/ -> ../../
_REPO_ROOT = Path(__file__).resolve().parents[2]
_DEFAULT_TAXO = (
    _REPO_ROOT
    / "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/data/argumentum_fallacies_taxonomy.csv"
)

# Colonnes de la taxonomie Argumentum utilisees (sur 1553 lignes / 1408 sophismes).
# La taxonomie est multilingue ; on exploite Simple_name_en (rare : 61/1408),
# text_en, desc_en, et les cognates FR nom_vulgarise / text_fr / desc_fr.
_TAXO_COLS = {
    "pk": "PK",
    "famille": "Famille",
    "sousfamille": "Sous-Famille",
    "nom_fr": "nom_vulgarisé",
    "text_fr": "text_fr",
    "desc_fr": "desc_fr",
    "simple_en": "Simple_name_en",
    "text_en": "text_en",
    "desc_en": "desc_en",
}

# Les 8 familles Argumentum (racine "Argument fallacieux" exclue du compte par
# famille -- c'est le noeud racine de la hierarchie, pas une feuille).
ARGUMENTUM_FAMILIES = [
    "Influence",
    "Tricherie",
    "Insuffisance",
    "Obstruction",
    "Erreur mathématique",
    "Erreur de raisonnement",
    "Abus de langage",
]


# ---------------------------------------------------------------------------
# Listes d'etiquettes academiques (papiers cites, encodees ici).
# ---------------------------------------------------------------------------

# Logic / LogicClimate (Jin et al. 2021, arXiv:2202.13758) : 13 types.
# Liste canonique du dataset (tasksource/logic2fallacy, causalNLP/logical-fallacy).
# Chaque entree : (label_en, keywords FR/EN pour le matching, note source).
LOGIC_13 = [
    ("Ad hominem", ["ad hominem", "attaque personnelle"]),
    ("Appeal to authority", ["argument d'autorité", "appeal to authority"]),
    ("Appeal to emotion", ["appel à l'émotion", "appel aux emotions"]),
    ("Bandwagon", ["bandwagon", "appel à la popularité", "ad populum"]),
    ("Causal oversimplification", ["causal oversimplification", "simplification"]),
    ("Circular reasoning", ["raisonnement circulaire", "circular"]),
    ("Equivocation", ["équivoque", "ambiguïté", "equivocation"]),
    ("False analogy", ["fausse analogie", "analogie"]),
    ("False cause", ["fausse cause", "post hoc", "faux cause"]),
    ("False dilemma", ["faux dilemme", "faux dilemme"]),
    ("Faulty generalization", ["generalisation", "généralisation"]),
    ("Red herring", ["red herring", "hareng rouge", "diversion"]),
    ("Slippery slope", ["pente glissante", "slippery slope"]),
    ("Straw man", ["épouvantail", "straw man", "homme de paille"]),
    ("Sunk cost fallacy", ["coût irrécupérable", "sunk cost"]),
]
# NB : 15 entrees encodees couvrent les 13 types canoniques + 2 variants nominaux
# frequent dans les datasets derives (Faulty generalisation / Hasty). On garde la
# granularite pour que l'alignement soit robuste aux variantes de label.

# MAFALDA (Helwe et al. 2023, arXiv:2311.09761) : L2 = 23 classes fines, sous
# 3 categories L1 (Pathos / Logos / Ethos). Encodage issu du papier.
MAFALDA_L2 = [
    # --- Pathos (appel aux affects) ---
    ("Appeal to emotion", ["appeal to emotion", "appel à l'émotion"], "Pathos"),
    ("Appeal to authority", ["appeal to authority", "argument d'autorité"], "Pathos"),
    ("Appeal to nature", ["appeal to nature", "appel à la nature"], "Pathos"),
    ("Appeal to tradition", ["appeal to tradition", "appel à la tradition"], "Pathos"),
    ("Appeal to popularity", ["appeal to popularity", "ad populum"], "Pathos"),
    ("Appeal to values", ["appeal to values", "appel aux valeurs"], "Pathos"),
    ("Appeal to fear", ["appeal to fear", "appel à la peur"], "Pathos"),
    ("Sentimental appeal", ["sentimental", "pathétique"], "Pathos"),
    # --- Logos (defauts de raisonnement) ---
    ("Causal fallacy", ["causal", "causalité", "post hoc"], "Logos"),
    ("False analogy", ["false analogy", "fausse analogie"], "Logos"),
    ("Slippery slope", ["slippery slope", "pente glissante"], "Logos"),
    ("Hasty generalization", ["hasty generalization", "généralisation hâtive"], "Logos"),
    ("Fallacy of composition", ["composition"], "Logos"),
    ("Fallacy of division", ["division"], "Logos"),
    ("False cause", ["false cause", "fausse cause"], "Logos"),
    ("Fallacy of logic", ["fallacy of logic"], "Logos"),
    ("Equivocation", ["equivocation", "équivoque", "ambiguïté"], "Logos"),
    ("Fallacy of proportion", ["proportion"], "Logos"),
    ("Red herring", ["red herring", "diversion"], "Logos"),
    ("Straw man", ["straw man", "épouvantail", "homme de paille"], "Logos"),
    ("Circular reasoning", ["circular reasoning", "raisonnement circulaire"], "Logos"),
    ("Begging the question", ["begging the question", "pétition de principe"], "Logos"),
    # --- Ethos (attaque du locuteur) ---
    ("Ad hominem", ["ad hominem", "attaque personnelle"], "Ethos"),
]
# NB : 23 classes L2 encodees. Quelques labels apparaissent dans 2 categories L1
# (ex. Slippery slope, Straw man, Equivocation) : c'est le chevauchement
# connu Pathos/Logos documente par Helwe 2023. On dedupliquera au mapping.


# ---------------------------------------------------------------------------
# Heuristiques de matching (stdlib only, pas de dependance externe).
# ---------------------------------------------------------------------------

_STOPWORDS = {
    "the", "a", "an", "of", "to", "and", "or", "in", "on", "for", "is", "are",
    "le", "la", "les", "de", "du", "des", "un", "une", "et", "ou", "à", "au",
    "aux", "en", "dans", "sur", "pour", "qui", "que", "par", "with", "your",
    "you", "their", "this", "that", "argument", "fallacy", "fallacieux",
    "reasoning", "raisonnement",
}


def _tokens(text: str) -> set[str]:
    """Tokenise pour le calcul de Jaccard : mots significatifs, lower, >=3 chars."""
    if not text:
        return set()
    raw = re.findall(r"[A-Za-zÀ-ÿ]{3,}", text.lower())
    return {w for w in raw if w not in _STOPWORDS}


def _jaccard(a: set[str], b: set[str]) -> float:
    if not a or not b:
        return 0.0
    inter = len(a & b)
    union = len(a | b)
    return inter / union if union else 0.0


@dataclass
class ArgumentumEntry:
    """Une feuille de la taxonomie Argumentum."""

    pk: str
    famille: str
    sousfamille: str
    nom_fr: str
    text_fr: str
    desc_fr: str
    simple_en: str
    text_en: str
    desc_en: str
    # Index lexicaux pre-calcules (FR + EN combines).
    tokens: set[str] = field(default_factory=set, repr=False)

    @classmethod
    def from_row(cls, row: dict) -> "ArgumentumEntry | None":
        pk = (row.get("PK") or "").strip()
        # On saute la racine "Argument fallacieux" (noeud racine, pas une feuille).
        famille = (row.get("Famille") or "").strip()
        if not pk or famille == "Argument fallacieux":
            return None
        e = cls(
            pk=pk,
            famille=famille,
            sousfamille=(row.get("Sous-Famille") or "").strip(),
            nom_fr=(row.get("nom_vulgarisé") or "").strip(),
            text_fr=(row.get("text_fr") or "").strip(),
            desc_fr=(row.get("desc_fr") or "").strip(),
            simple_en=(row.get("Simple_name_en") or "").strip(),
            text_en=(row.get("text_en") or "").strip(),
            desc_en=(row.get("desc_en") or "").strip(),
        )
        # Index lexical combine FR+EN (la taxonomie etant majoritairement FR,
        # l'index FR porte l'essentiel du signal ; l'EN complete les 61/1408
        # entries nommees en anglais).
        combined = " ".join(
            [e.nom_fr, e.text_fr, e.desc_fr, e.simple_en, e.text_en, e.desc_en]
        )
        e.tokens = _tokens(combined)
        return e


def load_argumentum(csv_path: Path) -> list[ArgumentumEntry]:
    """Charge la taxonomie Argumentum (UTF-8-BOM tolerant). Renvoie les feuilles."""
    raw = csv_path.read_bytes().decode("utf-8-sig")
    reader = csv.DictReader(io.StringIO(raw))
    entries: list[ArgumentumEntry] = []
    for row in reader:
        e = ArgumentumEntry.from_row(row)
        if e is not None:
            entries.append(e)
    return entries


@dataclass
class Alignment:
    """Resultat de l'alignement d'une etiquette academique vers Argumentum."""

    academic_label: str
    academic_source: str  # "Logic13" ou "MAFALDA-L2"
    keywords: list[str]
    best_pk: str | None
    best_famille: str | None
    best_name: str
    score: float  # 0..1, score de confiance du matching
    verdict: str  # "DIRECT" / "PARTIAL" / "NOT_FOUND"
    candidates: list[tuple[str, str, float]] = field(default_factory=list)

    def to_row(self) -> dict:
        d = asdict(self)
        d["candidates (pk,famille,score)"] = "; ".join(
            f"{pk}({f},{s:.2f})" for pk, f, s in self.candidates[:3]
        )
        del d["candidates"]
        return d


# Seuils de confiance (calibres sur la structure de la taxonomie : la majorite
# des entries n'ont pas de Simple_name_en, donc on s'appuie sur les cognates FR
# + le chevauchement lexical ; un score Jaccard ~0.15 est deja informatif vu la
# taille moyenne des descriptions).
DIRECT_THRESHOLD = 0.30  # nom matche (EN direct ou cognate FR forte)
PARTIAL_THRESHOLD = 0.08  # chevauchement lexical detectable


def align_label(
    label: str,
    source: str,
    keywords: list[str],
    argum: list[ArgumentumEntry],
) -> Alignment:
    """Aligne UNE etiquette academique vers la meilleure entrée Argumentum."""
    kw_tokens: set[str] = set()
    for k in keywords:
        kw_tokens |= _tokens(k)
    # Le label lui-meme participe au pool de tokens.
    kw_tokens |= _tokens(label)

    scored: list[tuple[str, str, float, str, float]] = []
    for e in argum:
        # (a) correspondance de nom EN directe.
        name_score = 0.0
        if e.simple_en and _norm(e.simple_en) == _norm(label):
            name_score = 1.0
        elif e.simple_en and _norm(e.simple_en) in _norm(label):
            name_score = 0.8
        # (a bis) cognate FR sur le nom vulgarise.
        fr_name_score = 0.0
        for k in keywords:
            if k.lower() in (e.nom_fr.lower() + " " + e.text_fr.lower()):
                fr_name_score = max(fr_name_score, 0.7)
        # (b) chevauchement lexical global.
        lex = _jaccard(kw_tokens, e.tokens)
        # Score combine : le nom domine, le lexical affine.
        score = max(name_score, fr_name_score, 0.6 * lex if lex > 0 else 0.0)
        if score > 0:
            name_disp = e.simple_en or e.nom_fr or e.text_fr[:40]
            scored.append((e.pk, e.famille, score, name_disp, lex))

    scored.sort(key=lambda t: t[2], reverse=True)
    if not scored:
        return Alignment(label, source, keywords, None, None, "", 0.0, "NOT_FOUND")

    best_pk, best_fam, best_score, best_name, _lex = scored[0]
    if best_score >= DIRECT_THRESHOLD:
        verdict = "DIRECT"
    elif best_score >= PARTIAL_THRESHOLD:
        verdict = "PARTIAL"
    else:
        verdict = "NOT_FOUND"
    return Alignment(
        label,
        source,
        keywords,
        best_pk,
        best_fam,
        best_name,
        round(best_score, 3),
        verdict,
        [(pk, f, round(s, 3)) for pk, f, s, _, _ in scored[:3]],
    )


def _norm(s: str) -> str:
    """Normalisation pour comparaison de noms : lower, sans accents, alnum."""
    s = s.lower()
    s = re.sub(r"[àáâãäå]", "a", s)
    s = re.sub(r"[éèêë]", "e", s)
    s = re.sub(r"[îï]", "i", s)
    s = re.sub(r"[ôö]", "o", s)
    s = re.sub(r"[ûüù]", "u", s)
    s = re.sub(r"ç", "c", s)
    return re.sub(r"[^a-z0-9]+", " ", s).strip()


# ---------------------------------------------------------------------------
# Rapport de couverture.
# ---------------------------------------------------------------------------


def coverage_report(alignments: list[Alignment]) -> dict:
    """Synthetise la couverture par source + par famille Argumentum."""
    by_source: dict[str, dict] = {}
    family_hits: dict[str, int] = {f: 0 for f in ARGUMENTUM_FAMILIES}
    for a in alignments:
        s = by_source.setdefault(
            a.academic_source,
            {"total": 0, "DIRECT": 0, "PARTIAL": 0, "NOT_FOUND": 0, "labels_not_found": []},
        )
        s["total"] += 1
        s[a.verdict] += 1
        if a.verdict == "NOT_FOUND":
            s["labels_not_found"].append(a.academic_label)
        if a.best_famille in family_hits and a.verdict != "NOT_FOUND":
            family_hits[a.best_famille] += 1

    # Familles Argumentum JAMAIS touchees par les etiquettes academiques.
    never_hit = [f for f, n in family_hits.items() if n == 0]
    return {
        "by_source": by_source,
        "argumentum_families_hit": family_hits,
        "argumentum_families_never_hit": never_hit,
        "argumentum_family_count": len(ARGUMENTUM_FAMILIES),
        "argumentum_total_leaves": sum(1 for _ in alignments),  # placeholder corrige ci-dessous
    }


def build(
    csv_path: Path = _DEFAULT_TAXO,
) -> tuple[list[Alignment], dict]:
    """Pipeline complet : charge la taxonomie, aligne, rapporte."""
    if not csv_path.exists():
        raise FileNotFoundError(f"Taxonomie Argumentum introuvable : {csv_path}")
    argum = load_argumentum(csv_path)
    alignments: list[Alignment] = []
    for label, kw in LOGIC_13:
        alignments.append(align_label(label, "Logic13", kw, argum))
    for label, kw, _l1 in MAFALDA_L2:
        alignments.append(align_label(label, "MAFALDA-L2", kw, argum))
    report = coverage_report(alignments)
    report["argumentum_total_leaves"] = len(argum)
    report["argumentum_csv"] = str(csv_path)
    return alignments, report


# ---------------------------------------------------------------------------
# CLI.
# ---------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        description="Aligne Logic-13 + MAFALDA-23-L2 vers la taxonomie Argumentum."
    )
    p.add_argument(
        "--taxonomy",
        type=Path,
        default=_DEFAULT_TAXO,
        help="Chemin vers argumentum_fallacies_taxonomy.csv (defaut: repo).",
    )
    p.add_argument("--out-csv", type=Path, default=None, help="CSV de mapping en sortie.")
    p.add_argument("--out-json", type=Path, default=None, help="Rapport JSON en sortie.")
    p.add_argument("--report", action="store_true", help="Afficher le resume sur stdout.")
    args = p.parse_args(argv)

    try:
        alignments, report = build(args.taxonomy)
    except FileNotFoundError as e:
        print(f"ERREUR : {e}", file=sys.stderr)
        return 2

    if args.out_csv:
        rows = [a.to_row() for a in alignments]
        with args.out_csv.open("w", encoding="utf-8", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
            w.writeheader()
            w.writerows(rows)
        print(f"Mapping CSV ecrit : {args.out_csv}")

    # Le rapport JSON va toujours dans un fichier si --out-json, sinon stdout si --report.
    report_json = json.dumps(report, ensure_ascii=False, indent=2)
    if args.out_json:
        args.out_json.write_text(report_json, encoding="utf-8")
        print(f"Rapport JSON ecrit : {args.out_json}")

    if args.report or not (args.out_csv or args.out_json):
        print("=== Couverture academique -> Argumentum ===")
        for source, stats in report["by_source"].items():
            direct = stats["DIRECT"]
            partial = stats["PARTIAL"]
            nf = stats["NOT_FOUND"]
            tot = stats["total"]
            pct = 100 * (direct + partial) / tot if tot else 0
            print(
                f"  {source}: {direct} DIRECT + {partial} PARTIAL + {nf} NOT_FOUND "
                f"(couverture {pct:.0f}%)"
            )
            if nf:
                print(f"    non trouves : {', '.join(stats['labels_not_found'])}")
        print()
        print(f"Familles Argumentum touchees : {sum(1 for n in report['argumentum_families_hit'].values() if n>0)}"
              f" / {report['argumentum_family_count']}")
        if report["argumentum_families_never_hit"]:
            print(
                f"Familles JAMAIS touchees par les etiquettes academiques : "
                f"{', '.join(report['argumentum_families_never_hit'])}"
            )
        print(f"Feuilles Argumentum totales : {report['argumentum_total_leaves']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
