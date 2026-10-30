# Jauge — l'arc Noether → Yang–Mills sur réseau

Sous-série Physique de la collection [MyIA.AI.Notebooks](../../README.md), ouverte par l'EPIC #23161 (veine V6 de #20428). Le fil « symétries » part de Galois (par la monodromie de `Lean-15e`), continue par les groupes de Lie et le théorème de Noether, puis la jauge locale U(1) et SU(2), et aboutit au réseau de jauge de Wilson.

| Carnet | Ce qu'il démontre | Outils |
|---|---|---|
| [Jauge-01 — Le théorème de Noether en sympy](Jauge-01-Theoreme-Noether-Python.ipynb) | Le courant de Noether d'un flot à δL = 0, construit et vérifié conservé deux fois : symboliquement (substitution des accélérations d'Euler-Lagrange) et numériquement (intégration à tolérance serrée) ; contre-témoin anisotrope qui montre que la conservation disparaît avec la symétrie | sympy, scipy |

## À venir

- **Jauge-02** — de la symétrie U(1) globale à la jauge locale : dérivée covariante, puis SU(2) non abélien où la courbure porte l'auto-interaction ;
- **Jauge-03** — l'action de Wilson sur réseau : théorie de jauge en dimension 2 exactement soluble (moyenne de plaquette en forme fermée de β, vérité plantée confirmée contre la source archivée), puis loi de l'aire en dimension 3-4 par les rapports de Creutz, à hypothèse pré-enregistrée.

Le résultat d'existence Yang–Mills annoncé par OpenAI le 26/10 reste en veille tant que sa publication formelle n'est pas sortie : aucun carnet de cette sous-série ne l'énonce. La veille est tracée dans l'EPIC #23161 ; elle n'a pas encore d'issue dédiée, et le commentaire qui l'a fait apparaître vit sur une issue dont le titre porte un autre sujet.
