# Cas 27 — Tegmark 2015, perceptronium : pre-enregistrement du banc

**Scelle le 2026-11-21 avant toute mesure** (commit dedie, avant le code du banc).
Claim : [issue #8182, c.7067798863](https://github.com/jsboige/CoursIA/issues/8182#issuecomment-7067798863) — lane `myia-po-2027:CoursIA`. See #8182, Part of #4588.

**Source primaire archivee** (gisement `G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\`) :
`2015 - Tegmark - Consciousness as a State of Matter - Perceptronium (arXiv 1401.1219v3, CSF accepted).pdf` —
identite verifiee p.1 (Max Tegmark, MIT Kavli ; accepte CSF 17/03/2015 ; DOI 10.1016/j.chaos.2015.03.014 ;
journal ref Chaos, Solitons & Fractals 76 (2015) 238-270). Toutes les equations ci-dessous sont citees
depuis cette copie, jamais de memoire.

## Ce que la theorie predit (lectures firsthand, pages de la copie archivee)

| # | Prediction | Localisation | Enonce quantitatif |
|---|---|---|---|
| P1 | Coherence energetique d'un etat propre de position sur spectre equidistant | eq. 58-61 (p.21) | `delta_H = hbar.omega.sqrt((n^2-1)/12)` pour `E_k = (k-(n-1)/2).hbar.omega` |
| P2 | Fidelite de l'etat de position apres evolution | eq. 63 (p.21) | `f_n(phi) = sin(n.phi)/(n.sin phi)`, zeros en `phi = k.pi/n` |
| P3 | Production d'entropie au second ordre | eq. 80-81 (p.23) | `dS_lin/dt(0) = 0` ; `d2S_lin/dt2` ne depend que de `H_3` (quadratique), formule exacte eq. 81 |
| P4 | Decroissance de l'entropie lineaire avec la taille | Fig. 14 + texte (p.24) | `S_lin,1(T) ~ 2^{-4b}` asymptotiquement (T = periode orbitale 2pi/omega) |
| P5 | Croissance de l'autonomie avec la taille | eq. 82-86 + texte (p.24) | `A = tau_ind/tau_dyn ~ 2^{3b}` ; le texte : « asymptotically increasing as A ~ 2^{2b}/2^{-b} = 2^{3b} » |
| P6 | Genercite de la loi d'echelle | texte (p.24) | « we expect this exponential scaling to be quite generic, independent of interaction details » |
| P7 | Plafond d'information integree quantique | section II.D (p.19) + footnote 9 | en n=4 (2 qubits, coupe 2+2), max `Phi = log(27/16)/log 8 ~ 0.2516` bit, atteint pour le spectre `{1/3, 1/3, 1/3, 0}` ; aucun etat quantique de quelque taille ne depasse ~0.25 bit |

Le paradoxe de Zenon quantique (section III.L) et la robustesse d'objet ≥ 10 (section II) sont qualitatifs
ou repris indirectly par P4/P5 : ils ne forment pas des hypotheses separees mesurables ici.

## Banc (parametres scelles)

Unites : `hbar = omega = 1` (adimensionne ; les lois d'echelle n'en dependent pas).

- **Sous-systeme** : b qubits, dimension n = 2^b, Hamiltonien equidistant
  `H1 = diag(E_0..E_{n-1})`, `E_k = (k - (n-1)/2)` (eq. 58).
- **Etats de position** : transformee de Fourier des etats d'energie,
  `|x_j> = (1/sqrt(n)) . sum_k exp(2i.pi.j.k/n) |E_k>` ; etat initial `|x_1>`.
- **Operateur position** : `x = diag(0, 1, ..., n-1)` dans la base de position
  (le recentrage ne decale que des phases, sans effet sur les exposants).
- **Environnement** : 1 qubit, `rho2 = |up><up|`, `H2 = sigma_x` (omega_2 = 1, scelle).
- **Interaction** (eq. 83) : `H3 = V(x) . kron sigma_x`, potentiel de base
  `V0(x) = sin(2.pi.x/n)` (amplitude 1, regime du papier ou `||H1|| >> ||H3||` aux grandes tailles).
- **Hamiltonien complet** : `H = kron(H1, I2) + kron(In, H2) + H3` ; evolution exacte
  `U = expm(-i.H.t)`, entropie lineaire du sous-systeme `S_lin,1 = 1 - tr(rho1^2)` apres
  trace partielle sur l'environnement.
- **Tailles** : b dans {2..9} (n = 4..512, espace total ≤ 1024 — dense expm faisable).
- **Mesures par b** : `delta_H(|x_1>)`, courbe `f_n(phi)`, `S_lin,1(t=0..T)` (T = 2.pi),
  derivees 0/2 via differences finies et via eq. 81, `tau_dyn = 1/delta_H`,
  `tau_ind = [d2S_lin/dt2(0)]^{-1/2}`, `A = tau_ind/tau_dyn`.

### Potentiels multi-seed (role des seeds, P6)

Pour s dans {0, 1, 7, 42, 99} : `V_s(x) = sum_{m=1..3} a_m . sin(2.pi.m.x/n + phase_m)`,
`(a_m, phase_m)` tires du generateur `numpy.random.default_rng(s)`, puis `V_s` normalise pour
`||V_s||_op = ||V0||_op` (meme force de couplage, seule la forme change). Le potentiel de base `V0`
est le sixieme tirage (deterministe, celui du papier).

### Integration (P7)

`Phi(rho)` selon la definition du papier (section II.C-II.D, theoreme rhoDC de Jevtic-Jennings-Rudolph) :
diagonaliser rho (n = 4), repartir les 4 valeurs propres en matrice 2x2, information mutuelle en bits
`I = H(ligne) + H(colonne) - H(matrice)` minimisee sur les 4! = 24 permutations.
Perimetre scelle : n = 4 exhaustif ; recherche aleatoire 10 000 etats purs Haar + 10 000 spectrales
aleatoires par seed (5 seeds) ; la tendance a la baisse en nombre de qubits (footnote 9 :
0.252, 0.171, 0.128... pour 2, 4, 6... qubits) est citee mais HORS banc (coupe a 256 qubits :
256! permutations) — declare tel, non mesure.

### Controle negatif

`H3 = 0` : `S_lin,1(t) = 0` exactement pour tout t (verif machine), `d2S_lin/dt2 = 0` par eq. 81 —
l'entropie mesuree vient bien de l'interaction, pas de la numerique.

## Hypotheses scellees et seuils (fixes avant mesure)

| # | Hypothese | CONFIRMEE si | REFUTEE si | Sinon |
|---|---|---|---|---|
| H1 | `delta_H` de l'etat `x_1` egal a `sqrt((n^2-1)/12)` | erreur relative max < 1e-12 sur n dans {2..64} | erreur > 1e-6 | NON_CONCLUANT |
| H2 | module du recouvrement `<x_1/U(phi)/x_1>` egal a `sin(n.phi)/(n.sin phi)` en module | erreur absolue max < 1e-12 sur n dans {2..64}, grille phi dans (0, pi), et zeros a k.pi/n a 1e-12 pres | erreur > 1e-6 | NON_CONCLUANT |
| H3 | eq. 80-81 : derivee premiere nulle, derivee seconde exacte | valeur absolue de dS/dt(0) < 1e-12 et accord relatif eq. 81 vs differences finies < 1e-6 (a dt = 1e-4), pour b dans {2..6} | accord > 1e-3 | NON_CONCLUANT |
| H4 | `log2 S_lin,1(T)` decroit lineairement en b, pente asymptotique -4 | pente OLS sur b dans {5..9} dans [-5.0, -3.0] | pente > -2.0 (decroissance clairement plus faible) | NON_CONCLUANT |
| H5 | `log2 A(b)` croit lineairement, pente asymptotique +3 | pente OLS sur b dans {5..9} dans [2.0, 4.0] | pente < 1.0 | NON_CONCLUANT |
| H6 | Genercite : memes exposants sous potentiels aleatoires | les 5 seeds chacun dans les bandes H4 et H5 | >= 3 seeds hors bande (meme cote) | NON_CONCLUANT |
| H7 | Plafond `Phi` a l'optimum du papier en n=4 ; optimum au spectre {1/3,1/3,1/3,0} | ecart absolu `Phi(opt) - log(27/16)/log 8` < 1e-6 ET max sur recherche aleatoire (5 seeds) <= 0.26 | un etat aleatoire depasse 0.26 bit | NON_CONCLUANT |

H1, H2, H3 sont des validations d'implementation d'identites mathematiques exactes du papier
(refutation = bug de banc, pas refutation de theorie). H4, H5, H6 testent les lois d'echelle
(Fig. 14). H7 teste le plafond d'integration. **Les seuils ci-dessus sont fixes et ne seront pas
reajustes apres mesure** ; tout ecart sera rapporte tel quel.

## Analyse (scellee)

- Ajustements : OLS degre 1 (`numpy.polyfit`) de `log2 S_lin,1(T)` et `log2 A` sur b ∈ {5..9},
  avec les valeurs brutes par b et par potentiel dans le JSON de resultats.
- Aucune exclusion de donnee ; si un expm echoue a une taille (memoire), la taille est rapportee
  manquante et la regression court sur les tailles restantes, sans reecriture des seuils.
- Verdict par hypothese + verdict global du cas (nomme), rapports dans
  `ict/results/perceptronium_results.json` (brut + verdicts).

## Chemins du grain (claim borne)

- `MyIA.AI.Notebooks/IIT/ICT-Series/ict/perceptronium.py`
- `MyIA.AI.Notebooks/IIT/ICT-Series/ict/tests/test_perceptronium.py`
- `MyIA.AI.Notebooks/IIT/ICT-Series/ict/results/perceptronium_results.json`
- `docs/ict/perceptronium-pre-enregistrement.md`

Chemins partages non touches : README de serie et `docs/ict/dissociations-matrix.md`
(occupes par #27470/#26601) — la ligne de dissociation du cas 27 viendra apres, en PR separee.

## Amendement pre-mesure (2026-11-21, declare avant toute execution du banc)

Erreur de transcription detectee a l'ecriture des tests, AVANT toute mesure : la
ligne H7 fixait « `|Phi(opt) - 0.2516| < 1e-6` », mais `0.2516` est l'arrondi a 4
decimales du papier — la valeur close-form est `Phi_opt = log(27/16)/log(8) =
0.2516292...` (egale a l'information mutuelle en bits `2.H(2/3) - log2(3)`,
verifiee a la main). Le seuil tel que scelle rendait H7 NON_CONCLUANTE par
construction. **Correction** : la cible devient l'expression close-form du papier
`log(27/16)/log 8`, tolerance inchangee (1e-6) ; le plafond de refutation reste
0.26 bit. Aucun autre seuil ne bouge. L'amendement est pre-mesure : aucune donnee
du banc n'avait ete produite au moment de la correction (commit dedie).

**A2 — H3, plancher de bruit de la difference centree.** Le seuil scelle
« valeur absolue de dS/dt(0) < 1e-12 » est sous le plancher de bruit numerique
de l'instrument lui-meme : la difference centree `(S(+eps)-S(-eps))/2.eps` porte
un bruit ~ bruit(S)/eps ~ 1e-15/1e-3 ~ 1e-12, mesure a 1.6e-12..4.4e-12 dans les
tests sur n = 4..32. Une derivee premiere reellement non nulle serait d'ordre
`S''.eps ~ 1e-3` — huit ordres de grandeur au-dessus. **Correction** : seuil H3
derivee premiere porte a **1e-10** ; la derivee seconde se valide en trois points
(voir A3) : residu `|S''(0)| < 1e-12` (l'algebre predit 0 exactement — tout residu
est un bug d'instrument), egalite au double calcul independant `4.Var(V)`, et
**ordre de convergence quadratique** de la difference finie `fd(2dt)/fd(dt)` dans
[3.5, 4.5] quand `fd` est au-dessus du bruit (signature du regime quartique : la
comparaison directe eq81-vs-difference-finie dans le cas nul ne mesure que la
troncature O(dt^2), pas un accord).

**A3 — H5/H6, operacionalisation de tau_ind (finding pre-mesure).** Pour la
construction scellee (etat initial propre de position, potentiel V diagonal en
base de position), l'equation 81 se reduit algebriquement a
`S''(0) = 4.Var_{x1}(V) = 0` exactement — la revendication du papier
« S_lin(t) ~ S''(0).t^2/2 » ne peut pas etre litterale pour un etat propre de
position ; l'entropie produite pendant l'orbite vient des excursions entre
etats propres (Fig. 13 du papier), d'ordre superieur en t. En consequence
`tau_ind = [S''(0)]^{-1/2}` serait infini pour TOUT potentiel diagonal, et
l'autonomie H5 indefinie. **Operacionalisation** : autonomie effective
`A_eff = tau_dyn^{-1... }` non — `A_eff = tau_ind_eff / tau_dyn` avec
`tau_ind_eff = sqrt(T^2 / (2 S_lin,1(T)))` (courbure effective sur une orbite
complete, celle que la Fig. 14 mesure). L'arithmetique du papier est
preservee : si `S_lin(T) ~ 2^{-4b}` (H4) et `delta_H ~ 2^{b}` (H1), alors
`log2 A_eff` a pente `1 + 4/2 = +3` — la bande H5 [2.0, 4.0] et la borne de
refutation +1.0 restent celles scellees. `S''(0)` via eq. 81 reste mesure et
rapporte (valeur attendue : 0 machine — temoin de l'identite A3).
