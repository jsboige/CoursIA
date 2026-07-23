# Audit cross-source distillation — méthode 4 étapes + 4 verdicts

**S'applique à** : tout agent du cluster auditant une **distillation** entre une **source canonique** (MBML, papier NeurIPS/arXiv, doc SOTA) et un **portage** (Infer.NET, PyMC, Lean, QC, etc.). Pilote = quatuor MBML (Probas) c.8081/84/85/86 — promu c.8092 [L772 + L789 + L790 + L791]. Voir topic files :

- [`cycle-c8081-probas-distillation-audit`](../memory/cycle-c8081-probas-distillation-audit.md) — fondateur méthode (TrueSkill)
- [`cycle-c8084-murder-mystery-audit`](../memory/cycle-c8084-murder-mystery-audit.md) — L789 (Ch.1 attribution)
- [`cycle-c8085-studentskills-irt-audit`](../memory/cycle-c8085-studentskills-irt-audit.md) — L790 (Ch.2 IRT divergence)
- [`cycle-c8086-crowdsourcing-audit`](../memory/cycle-c8086-crowdsourcing-audit.md) — L791 (Ch.7 Dawid-Skene)

## Étape 1 — Identifier la source canonique

| Question | Action concrète |
|---|---|
| Quel chapitre MBML / papier / doc canonique est distillé ? | `grep -in "<mot-clé>" README.md` + lecture lineage cross-références |
| Quel notebook Infer.NET (numéro N) ? | `ls MyIA.AI.Notebooks/Probas/Infer/Infer-N-*.ipynb` |
| Quel notebook PyMC miroir (numéro M) ? | `ls MyIA.AI.Notebooks/Probas/PyMC/PyMC-M-*.ipynb` |

## Étape 2 — Lire la source originale (firsthand)

| Source | Action |
|---|---|
| MBML chapter | https://mbmlbook.com/<Chapter>.html + sous-sections |
| MBML code | https://github.com/dotnet/mbmlbook `Examples/*.cs` |
| Papier de référence | NeurIPS/arXiv DOI + version PDF |

**Why firsthand** : G.9 culture du doute + L915 — un pitch plausible non mesuré = fabrication. Lire les **sous-sections** du chapitre MBML (pas seulement l'intro), lire les **examples chiffrés** (pas seulement la prose), confronter verdict au label (cf [verify-before-claiming.md](verify-before-claiming.md)).

## Étape 3 — Comparer axe par axe

| Axe | Critère vérifiable |
|---|---|
| **Concepts** | Toutes sous-sections MBML présentes ? Modèle formel correct ? |
| **Dérivation** | Étapes mathématiques reproduites ? EP/V(t)/W(t) détaillées ? |
| **Exemples chiffrés** | ≥1 exemple comparable aux MBML Examples/*.cs ? |
| **Visualisations** | ≥1 figure sémantiquement alignée ? |
| **Exercices** | ≥3 exercices originaux (cf [three-exercises-per-notebook.md](three-exercises-per-notebook.md)) ? |
| **Attribution** | Citation MBML explicite dans cellules notebook ? (≠ README seul) |

## Étape 4 — Verdict par axe + verdict global

| Verdict | Critère vérifiable |
|---|---|
| **FIDÈLE** | Toutes sous-sections MBML présentes + ≥1 exemple chiffré + ≥1 exercice |
| **PERTE DOCUMENTÉE** | ≥1 axe manquant mais explicite (section "Limites" ou renvoi externe) |
| **PERTE PAR COMPLAISANCE** | ≥1 axe manquant **sans mention explicite** |
| **DIVERGENCE POSITIVE** | Exercices originaux ≠ copier-coller MBML (≠ régression, ≠ enrichissement frauduleux) |

### Verdict global (synthèse)

`FIDÈLE X% / PERTE DOCUMENTÉE Y% / PERTE PAR COMPLAISANCE Z% / DIVERGENCE POSITIVE W%` — `X+Y+Z+W = 100%`. Calcul sur les 6 axes pondérés également.

## Reconductibilité cross-famille

| Famille | Audit cross-source potentiel |
|---|---|
| **Probas/Infer.NET + PyMC vs MBML** | Pilote c.8081/84/85/86 — 4 chapitres audités (TrueSkill, Murder Mystery, StudentSkills, Crowdsourcing) |
| **DecisionTheory/DecInfer + DecPyMC vs MBML Decision Making** | Recommandation c.8081 §4 — pas de filiation MBML explicite, audit séparé à mener |
| **GameTheory Lean vs ?** | Lean = langage formel, pas de « source canonique » externe à comparer (sauf Mathlib) — pattern non applicable |
| **Search/CSP vs ?** | Pas de distillation MBML/SOTA externe identifiée — pattern non applicable |
| **QuantConnect vs ?** | Pas de distillation MBML/SOTA externe identifiée — pattern non applicable |

## Patterns proches (distincts, ne pas confondre)

- **L770 ★** MED/doc-honesty axe-2 sweep EPIC #3801 — markdown claim N vs committed output M, +1/-1 atomic, See #N partial. **Même méthodologie de lecture firsthand** mais scope différent (markdown d'un notebook vs lineage cross-source d'un corpus).
- **c.793 #8068** : protocole d'échantillonnage sémantique cross-famille — pattern inventaire (≠ audit distillation).
- **c.761 #8070** : dénominateurs forensic/catalogue/disque — pattern réconciliation 3 sources (≠ audit 1 source vs N notebooks).
- **c.449 (fondateur EPIC #5780)** : vision-QA MiniMax M3 + PIL RGB stats — pattern audit visuel (≠ audit textuel distillation).

## Pourquoi cette rule (sub-grain méthodologique épic #8081)

| Tranche | PR | Leçons promues | Substance | Status |
|---------|-----|----------------|-----------|--------|
| c.8081 (pilote) | #8085 MERGED | (audit seul) | quantifier distillation TrueSkill vs MBML Ch.3 | MERGED 2026-07-23 |
| c.8084 | #8088 MERGED | (audit seul) | Murder Mystery Ch.1 | MERGED 2026-07-23 |
| c.8085 | #8091 MERGED | (audit seul) | StudentSkills Ch.2 IRT/DINA | MERGED 2026-07-23 |
| c.8086 | #8094 MERGED | (audit seul) | Crowdsourcing Ch.7 | MERGED 2026-07-23 |
| **c.8092 (cette rule)** | (à créer) | **L772 + L789 + L790 + L791** | méthode 4 étapes + 4 verdicts + reconductibilité cross-famille | grain en livraison |

**Règle d'or c.8081** : « audit = contribution méthodologique, promouvoir leçon L-NNN dans rule cible AVANT clôture audit ». **Boucle close** par c.8092 : 4 leçons cross-source consolidées en 1 rule méthodologique, prêt à servir de pattern pour DecisionTheory (recommandation c.8081 §4).

## Voir aussi

- [harness-hygiene.md](harness-hygiene.md) — 3 tiers information (sub-grain méthodologique parent)
- [proactive-coordination.md](proactive-coordination.md) — sub-grain méthodologique, R5 pool global cross-famille
- [audit-reassessment.md](audit-reassessment.md) — 4 étapes audit (NanoClaw pattern, distinct mais compatible)
- [verify-before-claiming.md](verify-before-claiming.md) — cross-check G.1, ne pas propager un claim non vérifié
- [anti-regression.md](anti-regression.md) — ne pas stripper le code réel (≠ ne pas auditer une distillation)
