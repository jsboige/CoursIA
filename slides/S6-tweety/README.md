# S6-tweety — Deck Slidev TweetyProject

Deck de presentation pour la serie de 10 notebooks **TweetyProject** (`SymbolicAI/Tweety/`).

## Contenu

17 slides couvrant :
- Configuration et ecosysteme JPype/Java
- Logiques formelles (PL, FOL, DL, modale, QBF)
- Revision de croyances et incoherence (AGM, MUS, MaxSAT)
- Argumentation abstraite (frameworks de Dung, CF2)
- Argumentation structuree (ASPIC+, DeLP, ABA)
- Frameworks etendus (ADF, bipolaire, pondere)
- Ranking semantics et argumentation probabiliste
- Agents dialogiques (persuasion, negociation)
- Preferences et theorie du vote

## Utilisation

```bash
# Depuis le dossier slides/
./node_modules/.bin/slidev S6-tweety/slides.md --port 3046 --no-open
```

## Notebooks correspondants

`MyIA.AI.Notebooks/SymbolicAI/Tweety/` — 10 notebooks, ~7h

| Notebook | Theme |
|----------|-------|
| Tweety-1-Setup | Configuration JVM + JARs |
| Tweety-2-Basic-Logics | PL + FOL |
| Tweety-3-Advanced-Logics | DL, Modale, QBF |
| Tweety-4-Belief-Revision | AGM, MUS, MaxSAT |
| Tweety-5-Abstract-Argumentation | Frameworks de Dung |
| Tweety-6-Structured-Argumentation | ASPIC+, DeLP, ABA |
| Tweety-7a-Extended-Frameworks | ADF, Bipolar, WAF |
| Tweety-7b-Ranking-Probabilistic | Ranking + Probabiliste |
| Tweety-8-Agent-Dialogues | Agents et dialogues |
| Tweety-9-Preferences | Preferences et vote |

## References

- Epic #1240 (refonte slides IA 101)
- Issue #1242 (creation decks S6-tweety + S7-lean)
