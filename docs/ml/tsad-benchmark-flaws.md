# Flaws des benchmarks TSAD et place du Matrix Profile

Note de référence compagnon pour les notebooks **ML-10** (critique
méthodologique des benchmarks de détection d'anomalies temporelles) et
**ML-11** (Matrix Profile multidimensionnel, méthode non-apprentissage
qui résiste à la critique). Cette note consolide le cadre méthodologique
pour que le lectorat situe la série **ML-9 → ML-10 → ML-11** et
comprenne *pourquoi* elle progresse dans cet ordre.

## La triade de sources

Trois textes éclairent la détection d'anomalies temporelles (TSAD) sous
des angles complémentaires.

### Wu & Keogh 2020 — le diagnostic fondateur

**Wu, R. & Keogh, E. (2020).** *Current Time Series Anomaly Detection
Benchmarks are Flawed and are Creating the Illusion of Progress.*
arXiv:2009.13807, IEEE TKDE 2021.
[arxiv.org/abs/2009.13807](https://arxiv.org/abs/2009.13807)

Le papier identifie **quatre flaws** dans les benchmarks classiques
(Yahoo, Numenta, NASA, OMNI) :

1. **Trivialité** — un problème est trivial si une seule ligne de code
   (primitives vectorisées : `mean`, `max`, `std`, `diff`) le résout.
   Une fraction significative des benchmarks y cède.
2. **Densité d'anomalies irréaliste** — plus de la moitié de la série
   marquée anormale, ou 21 anomalies dans un court segment, ou
   anomalies collées.
3. **Ground truth mal étiqueté** — faux positifs et faux négatifs
   avérés (ex : Yahoo).
4. **Run-to-failure bias** — les séries proviennent presque toutes de
   scénarios où la machine a déjà cassé, et l'anomalie est triviale à
   détecter *a posteriori*.

L'**UCR Archive** (367 séries, Eamonn Keogh) sert de contre-épreuve :
sur ce corpus, les SOTA publiés s'effondrent à des niveaux proches de
l'aléatoire.

### Keogh 2025 — la baseline SPC bat le SOTA

**Keogh, E. (2025).** Post Reddit sur TSB-AD-M (NeurIPS 2024) :
l'application directe de la **règle SPC** (*Statistical Process
Control*, Shewhart 1924) — `M + 3*S` — surpasse la majorité des
méthodes SOTA publiées, sans apprentissage, sans ajustement.

L'introspection communautaire n'est pas terminée. Le baseline trivial
bat le SOTA sur le benchmark de référence.

### Yeh et al. 2024 — Matrix Profile multidimensionnel

**Yeh, C.-C. M. et al. (2024).** *Matrix Profile for Anomaly Detection
on Multidimensional Time Series.* arXiv:2409.09298.
[arxiv.org/abs/2409.09298](https://arxiv.org/abs/2409.09298)

Le **Matrix Profile (MP)** d'une série univariée à n sous-séquences
est le vecteur des distances au plus proche voisin non-trivial de
chaque sous-séquence — un profil de similarité locale. C'est une
méthode **non-apprentissage** : pas de paramètre à apprendre, pas de
risque de surapprendre un benchmark trivial.

L'extension multidimensionnelle (Matrix Profile sur n dimensions)
préserve la propriété discriminante sur **119 datasets × 3 setups**
(non-supervisé, supervisé, semi-supervisé), seule méthode constante
sur tous les benchmarks.

### Fu et al. ICLR 2025 — hybridation MP + autoencodeur

**Fu, Y. et al. (ICLR 2025, soumission).** *FMP-AE: A Hybrid Approach
to Time Series Anomaly Detection.* OpenReview fErm1seIom.
[openreview.net/forum?id=fErm1seIom](https://openreview.net/forum?id=fErm1seIom)

L'autoencodeur apprend la représentation ; le **Matrix Profile sert
de loss structurée hybride** — la reconstruction n'est pas la seule
contrainte, la cohérence avec les plus proches voisins l'est aussi.
Le MP reste pertinent à l'ère du deep learning, comme **régulateur
structurel**.

Code public : [github.com/FyingE/FMP-AE](https://github.com/FyingE/FMP-AE).

## Fil pedagogique : ML-9 → ML-10 → ML-11

La série ML construit le regard critique *avant* l'outil SOTA, sinon
on enseigne un algorithme sans le cadre qui le rend légitime.

- **ML-9** — Détection d'anomalies par **ACP** sur jeu synthétique
  capteurs. Pédagogiquement sain pour introduire l'algorithme, mais
  sans regard critique sur *comment on évalue* un détecteur.
- **ML-10** — La critique des benchmarks (Wu-Keogh + SPC) : avant
  d'enseigner un SOTA, montrer qu'un baseline trivial peut le battre,
  que les benchmarks ont des flaws structurels, que l'illusion de
  progression est un piège.
- **ML-11** — Le Matrix Profile, méthode non-apprentissage qui
  *résiste* à la critique : pas de surapprentissage possible (pas
  d'apprentissage), constant sur 119 datasets, étendable en
  multidimensionnel.

Sans ML-10, ML-11 enseignerait un algorithme sans le regard critique
qui le met en valeur. Sans ML-9, ML-10 manquerait de substrat
pédagogique pour introduire la notion de détecteur.

## Pointeurs

### Notebooks

- [ML-9-Anomaly-Detection-Python.ipynb](../../MyIA.AI.Notebooks/ML/ML.Net/ML-9-Anomaly-Detection-Python.ipynb) — détection par ACP, Python.
- [ML-9-Anomaly-Detection.ipynb](../../MyIA.AI.Notebooks/ML/ML.Net/ML-9-Anomaly-Detection.ipynb) — jumeau .NET Interactive.

### Depots de code

- [stumpy](https://github.com/stumpy-dev/stumpy) — implémentation de
  référence du Matrix Profile en Python.
- [mmpad_tsb](https://github.com/TheDatumOrg/mmpad_tsb) — Matrix
  Profile multidimensionnel (paquet officiel des auteurs Yeh et al.).
- [FMP-AE](https://github.com/FyingE/FMP-AE) — hybridation MP +
  autoencodeur (Fu et al. ICLR 2025).

### Donnees

- [UCR Archive](https://www.cs.ucr.edu/~eamonn/time_series_data_2018/) —
  367 séries temporelles labellisées, contre-épreuve des benchmarks
  trivialement résolus.
- [TSB-AD](https://github.com/TheDatumOrg/TSB-AD) — TSB-AD-M (NeurIPS
  2024), benchmark moderne où SPC bat le SOTA publié.

## References

- Wu, R. & Keogh, E. (2020). *Current Time Series Anomaly Detection
  Benchmarks are Flawed and are Creating the Illusion of Progress.*
  arXiv:2009.13807.
- Keogh, E. (2025). Post communautaire sur TSB-AD-M. Reddit r/MachineLearning.
- Yeh, C.-C. M. et al. (2024). *Matrix Profile for Anomaly Detection
  on Multidimensional Time Series.* arXiv:2409.09298.
- Fu, Y. et al. (ICLR 2025, soumission). *FMP-AE: A Hybrid Approach to
  Time Series Anomaly Detection.* OpenReview fErm1seIom.

## Voir aussi

- Issue #13991 — Notebook ML-10 (critique méthodologique).
- Issue #13992 — Notebook ML-11 (Matrix Profile multidimensionnel).
