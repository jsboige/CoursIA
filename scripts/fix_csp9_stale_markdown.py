"""
Follow-up to PR #578 : update 3 markdown cells of CSP-9-Distributed that still
described the (now-fixed) algorithmic bugs as if they were present.

Cells :
  8  "Analyse de l'implementation ABT"           : remove the bug-as-feature list
  17 "Analyse de l'extension AWC"                : sync table with new code
                                                  (awc_rank, priority_sort_key,
                                                  _on_awc_reorder)
  23 "Interpretation de l'ordonnancement multi-hopital" : rewrite to match
                                                  post-fix output (3 distinct slots)

Cell 20 (privacy-preserving) keeps its current "limitations" wording : the
PrivateConstraint.evaluate / _real_evaluate placeholders are documented scope
limitations, not algorithmic bugs.
"""

import json
from pathlib import Path

NB_PATH = Path("MyIA.AI.Notebooks/Search/Part2-CSP/CSP-9-Distributed.ipynb")


CELL_8_ANALYSE_ABT = '''### Analyse de l'implementation ABT

**Architecture de l'agent ABT** :

| Methode | Responsabilite | Cle pour ABT |
|---------|----------------|--------------|
| `check_consistency()` | Verifie la coherence avec agent_view et nogoods | Coeur de la coherence locale |
| `choose_value()` | Selectionne la premiere valeur du domaine compatible avec agent_view | Heuristique de choix simple |
| `process_ok_message()` | Traite un assignement recu d'un agent de haute priorite | Bootstrap + propagation avant |
| `process_nogood_message()` | Apprend un nogood, eventuellement demande un addlink | Apprentissage + reparation |
| `_backtrack()` | Construit un nogood, retire la cible de la vue, re-essaie | Resolution effective |
| `_send_ok_messages()` | Diffuse la valeur courante aux agents de basse priorite | Communication |

**Architecture du systeme ABT** :

| Methode | Responsabilite |
|---------|----------------|
| `_setup_priority_order()` | Etablit l'ordre de priorite via `priority_sort_key` (statique en ABT pur, dynamique en AWC) |
| `run()` | Boucle FIFO jusqu'a quiescence ; valide la solution avant de la retourner |
| `_check_solution()` | Coherence locale : chaque agent est compatible avec sa vue |
| `_verify_global_constraints()` | Coherence globale : chaque arete du graphe est satisfaite |

**Pourquoi deux verifications de solution ?**

`_check_solution` ne suffit pas a elle seule : si la file contient encore des `ok?`, deux agents
sans relation de priorite mais voisins par contrainte peuvent etre localement coherents avec leur
vue tout en etant globalement incompatibles. La quiescence (file vide) est la condition necessaire
pour que la coherence locale agrege en coherence globale ; `_verify_global_constraints` est la
verification finale qui rejette les faux succes residuels.

**Points pedagogiques** :

- L'algorithme suit fidelement Yokoo et al. (1992) : agents qui s'envoient des `ok?`, apprennent
  des `nogood`, ouvrent des `addlink` quand le voisinage de priorite n'est pas connu.
- L'ordre de priorite est statique pour ABT pur (utiliser `AWCAgent` pour un ordre dynamique).
- La complexite d'execution depend du graphe des contraintes : pour des instances peu denses, la
  convergence se fait en quelques messages ; pour des instances denses, le nombre de nogoods
  appris croit (cf benchmarks plus bas).

> **Note** : la simulation utilise une file FIFO globale, modele *asynchrone fiable + ordre unique*.
> En production, chaque agent aurait sa propre boite de reception et l'ordre de livraison des
> messages depend des canaux (sockets, queue distribuee). Les invariants algorithmiques restent
> les memes : ABT est correct quel que soit l'ordonnanceur, tant que les messages sont livres une
> fois exactement.
'''


CELL_17_ANALYSE_AWC = '''### Analyse de l'extension AWC

**Ajouts par rapport a ABT** :

| Methode/Attribut | Role | Impact |
|------------------|------|--------|
| `self.awc_rank` | Rang dynamique de l'agent (float) | Diminue quand l'agent est promu |
| `self.nogoods_received` | Compteur de nogoods recus depuis la derniere promotion | Detecte les blocages repetes |
| `priority_sort_key()` | Surcharge : trie par `(awc_rank, id)` au lieu de `(id, id)` | Pris en compte par `ABTSystem._setup_priority_order` |
| `_increase_priority()` | Decremente `awc_rank` puis appelle `_system._on_awc_reorder()` | Reordonnancement effectif |
| `process_nogood_message()` | Promotion automatique apres 3 nogoods recus | Adaptation reactive |
| `_backtrack()` | Promotion preventive avant le backtrack | Strategie proactive |

**Strategie de reordonnancement** :

```python
if self.nogoods_received > 3:
    self._increase_priority()
```

Quand un agent recoit beaucoup de nogoods, c'est qu'il bloque les autres. Le promouvoir lui donne
une priorite plus elevee : il choisira en premier et imposera son choix au reste du systeme.

**Pipeline complet d'une promotion** :

1. `agent._increase_priority()` decremente `agent.awc_rank` (ex : 2.0 -> 1.0).
2. `agent._increase_priority()` appelle `system._on_awc_reorder()`.
3. `system._on_awc_reorder()` recalcule `higher_priority` / `lower_priority` pour TOUS les agents
   via `priority_sort_key()`.
4. `system._on_awc_reorder()` rediffuse la valeur courante de chaque agent ayant deja choisi
   (vague de `ok?`) afin que tout le monde reflete la nouvelle hierarchie.
5. La boucle de `system.run()` reprend a partir de cette nouvelle file.

**Avantages d'AWC** :

- **Adaptatif** : l'ordre des agents s'adapte aux blocages observes.
- **Moins de backtracking redondant** : en promouvant les agents bloquants, on evite les cycles
  ou les agents bas remontent encore et encore le meme nogood.
- **Meilleure convergence** : sur les instances denses, AWC produit moins de messages qu'ABT
  (cf benchmark `density=0.7` plus bas, AWC ~125 messages vs ABT ~575).

**Limites** :

- **Cout du reordonnancement** : chaque promotion redeclenche une vague d'`ok?` (cf
  `_on_awc_reorder`). Sur des instances peu denses, ce cout peut effacer le benefice.
- **Tuning du seuil** : ici 3 nogoods recus avant promotion. Un seuil trop bas declenche des
  reordonnancements inutiles, un seuil trop haut perd le benefice de l'adaptation.
- **Pas d'oubli** : les nogoods ne sont jamais oublies. Sur des problemes longs, leur nombre peut
  exploser (heuristiques de forgetting non implementees ici).
'''


CELL_23_INTERP_HOPITAL = '''### Interpretation de l'ordonnancement multi-hopital

**Resultat attendu** : 3 hopitaux, 5 creneaux, contrainte `slot != other_slot` -> chaque hopital
doit recevoir un creneau **distinct**. Le systeme converge vers une telle allocation.

**Pourquoi ca marche** :

1. **Reduction au DisCSP standard** : meme si les hopitaux portent des contraintes privees
   (`PrivacyPreservingAgent`), la contrainte d'unicite des creneaux passe par `constraint_func`
   classique, exactement comme dans le cas coloration de graphe.
2. **Quiescence + verification globale** : avant de retourner la solution, `ABTSystem` attend que
   la file de messages soit vide puis appelle `_verify_global_constraints` qui inspecte chaque
   arete du graphe (ici toutes les paires d'hopitaux). Une affectation `Lundi_AM = Lundi_AM`
   serait rejetee par cette verification finale.
3. **Confidentialite preservee** : les rapports `agents_with_access: []` montrent qu'aucun
   hopital n'a divulgue ses contraintes privees. La resolution se fait uniquement via la
   contrainte publique d'unicite.

**Lecture du rapport de confidentialite** :

| Champ | Signification |
|-------|---------------|
| `privacy_level` | Niveau declare a la construction (`high` ici) |
| `agents_with_access` | Liste des agents a qui on a explicitement donne acces via `reveal_constraint_to` |
| `private_constraints_count` | Nombre de contraintes privees ajoutees a l'agent |

Dans ce scenario simple, aucune contrainte privee n'est ajoutee : c'est l'API qui est illustree,
pas son interaction avec le solveur. Pour aller plus loin, on ajouterait des
`PrivateConstraint` avec une logique d'evaluation reelle (cf section "Limites" plus bas) et on
mesurerait combien d'information chaque hopital doit reveler pour atteindre une solution.

**Points cles** :

- L'orchestration ABT + verification globale rend l'allocation **fiable** : pas de creneau
  partage entre deux hopitaux.
- La couche privacy preserve la confidentialite des contraintes internes mais ne **remplace pas**
  la contrainte publique d'unicite ; elle s'ajoute.
- Pour un usage production (medical, finance), il faudrait completer la couche privacy avec du
  vrai chiffrement (homomorphe) ou un protocole SMPC, comme detaille dans la section suivante.
'''


CELL_PATCHES = {
    "f7e21456": ("markdown", CELL_8_ANALYSE_ABT),
    "070a53e6": ("markdown", CELL_17_ANALYSE_AWC),
    "8f050be3": ("markdown", CELL_23_INTERP_HOPITAL),
}


def to_list(src: str):
    return src.splitlines(keepends=True)


def main():
    nb = json.loads(NB_PATH.read_text(encoding='utf-8'))
    by_id = {c.get("id"): (i, c) for i, c in enumerate(nb["cells"])}
    for cell_id, (cell_type, src) in CELL_PATCHES.items():
        if cell_id not in by_id:
            raise SystemExit(f"missing cell {cell_id}")
        idx, cell = by_id[cell_id]
        if cell["cell_type"] != cell_type:
            raise SystemExit(f"cell {cell_id} type mismatch")
        cell["source"] = to_list(src)
        print(f"Patched cell {idx} ({cell_id}, {cell_type}, {len(cell['source'])} lines)")

    NB_PATH.write_text(json.dumps(nb, indent=1, ensure_ascii=False) + "\n", encoding='utf-8')
    print(f"\nNotebook saved: {NB_PATH}")


if __name__ == "__main__":
    main()
