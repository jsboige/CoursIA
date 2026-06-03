"""
Apply Laqwad's algorithmic fixes (PR #429) to CSP-9-Distributed.ipynb,
without the formatting noise.

Cells modified:
  5  ABTAgent class       (full rewrite : process_ok_message bootstrap,
                           _backtrack with retry, _nogood_applicable,
                           process_nogood_message addlink + replay,
                           priority_sort_key hook for AWC)
  7  ABTSystem class      (run() runs to quiescence then verifies global
                           constraints, addlink replies with current value,
                           _verify_global_constraints, _on_awc_reorder hook)
  16 AWCAgent class       (uses awc_rank + priority_sort_key + _on_awc_reorder)
  25 benchmark_discsp     (factored build_agents helper, AWC actually run)
  11 markdown interp      (rewritten : algorithm now correct)
  14 markdown interp      (rewritten : algorithm now correct)
  26 markdown interp      (rewritten : algorithm now correct)

Outputs are NOT cleared here ; Papermill will refresh them on re-execution.
"""

import json
import sys
from pathlib import Path

NB_PATH = Path("MyIA.AI.Notebooks/Search/Part2-CSP/CSP-9-Distributed.ipynb")


def to_list(src: str) -> list:
    """Convert a multi-line string to list[str] preserving newlines (notebook source format)."""
    lines = src.splitlines(keepends=True)
    return lines


CELL_ABT_AGENT = '''class ABTAgent:
    """
    Agent pour l'algorithme Asynchronous Backtracking.

    Base sur Yokoo et al. (1992).
    """

    def __init__(self, agent_id: int, domain: List[Any],
                 constraint_func, neighbors: List[int]):
        self.id = agent_id
        self.domain = domain
        self.constraint_func = constraint_func  # Fonction de contrainte locale
        self.neighbors = neighbors

        # Etat de l'agent
        self.value = None
        self.agent_view: Dict[int, Any] = {}  # Vue des agents de haute priorite
        self.nogoods: Set[Nogood] = set()     # Nogoods appris
        self.higher_priority: List[int] = []  # Agents de haute priorite
        self.lower_priority: List[int] = []   # Agents de basse priorite

        # File de messages locale (non utilisee par ABTSystem)
        self.message_queue: List[Message] = []

        # Statistiques (nogoods_generated : nogoods emis dans _backtrack, pas recus)
        self.messages_sent = 0
        self.nogoods_generated = 0
        self._system = None  # Renseigne par ABTSystem pour AWC / reordonnancement

    def priority_sort_key(self) -> Tuple[float, int]:
        """Cle de tri pour l'ordre entre agents (ABT pur : identique a l'id)."""
        return (float(self.id), self.id)

    def set_priority_order(self, higher: List[int], lower: List[int]):
        """Definit l'ordre de priorite des agents."""
        self.higher_priority = higher
        self.lower_priority = lower

    def check_consistency(self, value: Any) -> bool:
        """
        Coherence locale : contraintes avec chaque agent deja present dans agent_view
        (en pratique : agents de priorite superieure ayant envoye un ok?).
        Quand la file de messages est vide, la vue contient tous les voisins prioritaires :
        la coherence locale coincide alors avec les aretes du graphe pour cet agent.
        """
        for var_id, val in self.agent_view.items():
            if not self.constraint_func(self.id, value, var_id, val):
                return False

        # Verifier avec les nogoods appris
        for nogood in self.nogoods:
            if self._nogood_applicable(nogood, value):
                return False

        return True

    def _nogood_applicable(self, nogood: Nogood, value: Any) -> bool:
        """Le nogood contient self avec une certaine valeur, et toutes les autres
        variables de priorite superieure doivent coincider avec agent_view."""
        if self.id not in nogood.assignments:
            return False
        if nogood.assignments[self.id] != value:
            return False
        for v, v_val in nogood.assignments.items():
            if v == self.id:
                continue
            if self.agent_view.get(v) != v_val:
                return False
        return True

    def choose_value(self) -> Optional[Any]:
        """Choisit une valeur coherente avec l'agent_view."""
        for val in self.domain:
            if self.check_consistency(val):
                return val
        return None

    def process_ok_message(self, msg: Message) -> List[Message]:
        """Traite un message 'ok?' (assignation d'un agent de haute priorite).

        Si l'agent n'a pas encore choisi de valeur, il en choisit une
        immediatement et la propage. Sans ce cas, un agent recevant son premier
        ok? avant son init resterait silencieux et l'algorithme atteindrait
        une fausse quiescence.
        """
        var_id, value = msg.content
        self.agent_view[var_id] = value

        if self.value is None:
            self.value = self.choose_value()
            if self.value is not None:
                return self._send_ok_messages()
            return self._backtrack()

        if not self.check_consistency(self.value):
            self.value = self.choose_value()
            if self.value is not None:
                return self._send_ok_messages()
            return self._backtrack()
        return []

    def process_nogood_message(self, msg: Message) -> List[Message]:
        """Traite un message 'nogood' (contrainte apprise).

        Si le nogood mentionne un agent inconnu, on l'ajoute a higher_priority
        et on demande un addlink. Si la valeur courante reste valide, on
        renvoie un ok? a l'expediteur (qui a probablement retire self de sa
        vue en backtrackant et a besoin de la valeur a jour).
        """
        nogood = msg.content
        self.nogoods.add(nogood)

        # Liens manquants : tout agent du nogood pas encore dans la vue doit envoyer addlink
        new_links = []
        for var_id in nogood.assignments:
            if var_id != self.id and var_id not in self.agent_view:
                if var_id not in self.higher_priority:
                    self.higher_priority.append(var_id)
                new_links.append(var_id)

        messages: List[Message] = []

        for var_id in new_links:
            messages.append(Message(
                sender=self.id,
                receiver=var_id,
                msg_type='addlink',
                content=self.id
            ))
            self.messages_sent += 1

        # Verifier la valeur courante
        value_changed = False
        if self.value is not None and not self.check_consistency(self.value):
            old_value = self.value
            self.value = self.choose_value()
            value_changed = (self.value != old_value)
            if self.value is not None:
                messages.extend(self._send_ok_messages())
            else:
                messages.extend(self._backtrack())

        # Si la valeur n'a pas change, renvoyer un ok? a l'expediteur :
        # il a probablement retire self de son agent_view en backtrackant et doit
        # recuperer la valeur courante (sinon il peut converger sur un etat global incoherent).
        if not value_changed and self.value is not None and msg.sender != self.id:
            messages.append(Message(
                sender=self.id,
                receiver=msg.sender,
                msg_type='ok?',
                content=(self.id, self.value),
            ))
            self.messages_sent += 1

        return messages

    def _send_ok_messages(self) -> List[Message]:
        """Envoie la valeur courante aux agents de basse priorite."""
        messages = []
        for neighbor in self.lower_priority:
            messages.append(Message(
                sender=self.id,
                receiver=neighbor,
                msg_type='ok?',
                content=(self.id, self.value)
            ))
            self.messages_sent += 1
        return messages

    def _backtrack(self) -> List[Message]:
        """ABT standard : construit un nogood compose des seuls agents de priorite
        superieure (la cible peut les voir), l'envoie au plus prioritaire d'entre eux,
        puis retire la cible de sa vue et re-essaie une affectation locale.
        Si plus aucune valeur n'est compatible, on backtracke recursivement.
        """
        relevant = {v: self.agent_view[v] for v in self.higher_priority if v in self.agent_view}
        if not relevant:
            return [Message(
                sender=self.id,
                receiver=-1,
                msg_type='stop',
                content='no_solution'
            )]

        target = max(relevant.keys())
        nogood = Nogood(relevant)
        messages: List[Message] = [Message(
            sender=self.id,
            receiver=target,
            msg_type='nogood',
            content=nogood,
        )]
        self.messages_sent += 1
        self.nogoods_generated += 1

        self.agent_view.pop(target, None)
        self.value = self.choose_value()
        if self.value is not None:
            messages.extend(self._send_ok_messages())
        else:
            messages.extend(self._backtrack())
        return messages

    def initialize(self) -> List[Message]:
        """Initialise l'agent et envoie les premiers messages."""
        self.value = self.choose_value()
        if self.value is not None:
            return self._send_ok_messages()
        return self._backtrack()
print("Classe ABTAgent definie.")
'''


CELL_ABT_SYSTEM = '''class ABTSystem:
    """
    Systeme de simulation pour l'algorithme ABT.
    Simule la communication asynchrone entre agents via une file FIFO globale.
    """

    def __init__(self, agents: Dict[int, ABTAgent]):
        self.agents = agents
        self.message_queue: List[Message] = []
        self.solution: Optional[Dict[int, Any]] = None
        self.no_solution = False
        self.total_messages = 0
        self.total_nogoods = 0
        self.message_type_counts: Dict[str, int] = {}  # types traites dans la file

        for ag in self.agents.values():
            ag._system = self

        self._setup_priority_order()

    def _setup_priority_order(self):
        """Configure higher/lower selon priority_sort_key() de chaque agent (ABT ou AWC)."""
        agent_ids = sorted(self.agents.keys(), key=lambda i: self.agents[i].priority_sort_key())
        for i, agent_id in enumerate(agent_ids):
            higher = agent_ids[:i]
            lower = agent_ids[i + 1:]
            self.agents[agent_id].set_priority_order(higher, lower)

    def _on_awc_reorder(self):
        """Apres promotion AWC : recalcul des priorites + nouvelle vague de ok?."""
        self._setup_priority_order()
        for ag in self.agents.values():
            if ag.value is not None:
                self.message_queue.extend(ag._send_ok_messages())

    def run(self, max_iterations: int = 10000) -> Optional[Dict[int, Any]]:
        """
        Execute ABT jusqu'a quiescence (file vide), puis valide la solution.
        On ne declare le succes qu'apres vidage de la file : sinon des ok? peuvent
        encore modifier les vues et donner une fausse coherence locale.
        """
        self.message_type_counts = {}
        for agent in self.agents.values():
            messages = agent.initialize()
            self.message_queue.extend(messages)

        iteration = 0
        while iteration < max_iterations:
            if not self.message_queue:
                if self.no_solution:
                    return None
                if self._check_solution() and self._verify_global_constraints():
                    self.solution = {a.id: a.value for a in self.agents.values()}
                    return self.solution
                break

            msg = self.message_queue.pop(0)
            self.total_messages += 1
            self.message_type_counts[msg.msg_type] = self.message_type_counts.get(msg.msg_type, 0) + 1

            if msg.msg_type == 'stop':
                self.no_solution = True
                return None

            receiver = self.agents.get(msg.receiver)
            if receiver:
                if msg.msg_type == 'ok?':
                    new_messages = receiver.process_ok_message(msg)
                elif msg.msg_type == 'nogood':
                    new_messages = receiver.process_nogood_message(msg)
                    self.total_nogoods += 1
                elif msg.msg_type == 'addlink':
                    # L'agent de haute priorite renvoie son assignement courant au demandeur
                    requester = msg.content
                    new_messages = []
                    if receiver.value is not None:
                        new_messages.append(Message(
                            sender=receiver.id,
                            receiver=requester,
                            msg_type='ok?',
                            content=(receiver.id, receiver.value)
                        ))
                        receiver.messages_sent += 1
                else:
                    new_messages = []

                self.message_queue.extend(new_messages)

            iteration += 1

        return None

    def _check_solution(self) -> bool:
        """Tous les agents ont une valeur et sont localement coherents avec leur vue."""
        for agent in self.agents.values():
            if agent.value is None:
                return False
            if not agent.check_consistency(agent.value):
                return False
        return True

    def _verify_global_constraints(self) -> bool:
        """Verifie chaque arete du graphe (via les listes de voisins des agents).
        Une coherence locale chez chaque agent ne suffit pas : deux agents non
        relies par priorite mais relies par contrainte pourraient choisir des
        valeurs incompatibles. Cette passe finale rejette ces faux succes.
        """
        assignment = {a.id: a.value for a in self.agents.values()}
        if any(v is None for v in assignment.values()):
            return False
        seen_edges: Set[Tuple[int, int]] = set()
        for aid, agent in self.agents.items():
            for nb in agent.neighbors:
                edge = tuple(sorted((aid, nb)))
                if edge in seen_edges:
                    continue
                seen_edges.add(edge)
                if not agent.constraint_func(aid, assignment[aid], nb, assignment[nb]):
                    return False
        return True

    def get_statistics(self) -> Dict:
        """Retourne les statistiques d'execution."""
        return {
            'total_messages': self.total_messages,
            'total_nogoods': self.total_nogoods,
            'solution_found': self.solution is not None,
            'solution': self.solution
        }
print("Classe ABTSystem definie.")
'''


CELL_AWC_AGENT = '''class AWCAgent(ABTAgent):
    """
    Couche pedagogique AWC au-dessus d'ABT : rang dynamique awc_rank utilise par
    ABTSystem.priority_sort_key pour reorder higher/lower a la volee. Ce n'est pas
    AWC complet (Yokoo 1995) mais le reordonnancement impacte reellement la simulation.
    """

    def __init__(self, agent_id: int, domain: List[Any],
                 constraint_func, neighbors: List[int]):
        super().__init__(agent_id, domain, constraint_func, neighbors)
        self.awc_rank = float(agent_id)
        self.nogoods_received = 0  # nogoods recus (voir process_nogood_message)

    def priority_sort_key(self) -> Tuple[float, int]:
        return (self.awc_rank, self.id)

    def process_nogood_message(self, msg: Message) -> List[Message]:
        """Apres traitement ABT : compte les nogoods recus, promotion si blocage repete."""
        result = super().process_nogood_message(msg)
        self.nogoods_received += 1
        if self.nogoods_received > 3:
            self._increase_priority()
            self.nogoods_received = 0
        return result

    def _increase_priority(self):
        """Monter dans la hierarchie : diminuer awc_rank, puis synchroniser via le systeme."""
        self.awc_rank -= 1.0
        sys = getattr(self, '_system', None)
        if sys is not None:
            sys._on_awc_reorder()

    def _backtrack(self) -> List[Message]:
        if self.higher_priority:
            self._increase_priority()
        return super()._backtrack()

print("Classe AWCAgent definie.")
'''


CELL_BENCHMARK = '''def benchmark_discsp(n_agents: int, domain_size: int,
                     constraint_density: float, n_runs: int = 5):
    """
    Compare les performances d'ABT et d'AWC sur des instances aleatoires.

    Parameters
    ----------
    n_agents : nombre d'agents
    domain_size : taille du domaine
    constraint_density : probabilite de contrainte entre deux agents
    n_runs : nombre d'executions
    """
    results = {'ABT': [], 'AWC': []}

    for run in range(n_runs):
        domain = list(range(domain_size))
        edges = []
        constraint_funcs = {}

        for i in range(n_agents):
            for j in range(i + 1, n_agents):
                if random.random() < constraint_density:
                    edges.append((i, j))
                    forbidden = (random.randint(0, domain_size - 1),
                                 random.randint(0, domain_size - 1))
                    constraint_funcs[(i, j)] = forbidden

        def build_agents(agent_cls):
            agents = {}
            for i in range(n_agents):
                neighbors = [n for e in edges for n in e if i in e and n != i]
                relevant_constraints = {(min(k[0], k[1]), max(k[0], k[1])): v
                                        for k, v in constraint_funcs.items() if i in k}

                def constraint_func(v1, val1, v2, val2, rc=relevant_constraints):
                    edge = (min(v1, v2), max(v1, v2))
                    if edge in rc:
                        forb = rc[edge]
                        if v1 < v2 and (val1, val2) == forb:
                            return False
                        if v1 > v2 and (val2, val1) == forb:
                            return False
                    return True

                agents[i] = agent_cls(i, domain.copy(), constraint_func, neighbors)
            return agents

        max_it = 10000

        system_abt = ABTSystem(build_agents(ABTAgent))
        start = datetime.now()
        solution_abt = system_abt.run(max_iterations=max_it)
        time_abt = (datetime.now() - start).total_seconds()
        results['ABT'].append({
            'time': time_abt,
            'messages': system_abt.total_messages,
            'nogoods': system_abt.total_nogoods,
            'solved': solution_abt is not None
        })

        system_awc = ABTSystem(build_agents(AWCAgent))
        start = datetime.now()
        solution_awc = system_awc.run(max_iterations=max_it)
        time_awc = (datetime.now() - start).total_seconds()
        results['AWC'].append({
            'time': time_awc,
            'messages': system_awc.total_messages,
            'nogoods': system_awc.total_nogoods,
            'solved': solution_awc is not None
        })

    return results


def _print_bench_summary(name: str, rows: List[dict]):
    print(f"\\nResultats {name}:")
    for i, r in enumerate(rows):
        status = "Resolu" if r['solved'] else "Non resolu"
        print(f"  Run {i+1}: {status}, {r['messages']} messages, "
              f"{r['nogoods']} nogoods, {r['time']:.3f}s")
    avg_m = sum(r['messages'] for r in rows) / len(rows)
    avg_n = sum(r['nogoods'] for r in rows) / len(rows)
    sr = sum(1 for r in rows if r['solved']) / len(rows)
    print(f"\\nMoyennes {name}:")
    print(f"  Messages: {avg_m:.1f}")
    print(f"  Nogoods: {avg_n:.1f}")
    print(f"  Taux de succes: {sr*100:.1f}%")


print("=== Benchmark DisCSP ===")
random.seed(42)
results = benchmark_discsp(n_agents=5, domain_size=3,
                           constraint_density=0.5, n_runs=3)
_print_bench_summary('ABT', results['ABT'])
_print_bench_summary('AWC', results['AWC'])
'''


CELL_INTERP_COLORATION = '''### Interpretation : Analyse de la solution ABT

**Resultat attendu** : la solution retournee par `system.run()` doit satisfaire **toutes** les aretes
du cycle 0-1, 1-2, 2-3, 3-0 ; chaque arete relie deux couleurs differentes.

**Verification automatique** : la cellule precedente verifie chaque arete et imprime `OK` ou `ECHEC`.
Si l'execution affiche autre chose que 4 `OK`, c'est qu'un bug est present (a remonter via une issue).

**Comment l'algorithme y arrive** :

1. Chaque agent commence par choisir la premiere valeur compatible avec sa vue. Comme la vue est
   vide a l'init, l'agent 0 choisit `R`, puis 1 choisit `G` (different de `R`), puis 2 choisit
   la premiere valeur differente de `R` qu'il connaisse (`G`), puis 3 examine sa vue.
2. Si un agent decouvre que sa valeur est en conflit (apres avoir recu un `ok?` qui change sa vue),
   il essaie une autre valeur de son domaine. Si plus aucune valeur n'est compatible, il **backtracke** :
   il envoie un `nogood` a l'agent de plus haute priorite present dans sa vue, retire celui-ci
   de la vue et re-choisit.
3. Le `nogood` est appris par la cible : a sa prochaine evaluation, elle saura que cette combinaison
   de valeurs est interdite.
4. **Apprentissage `addlink`** : si un nogood mentionne un agent inconnu de la cible, celle-ci
   demande un `addlink` pour ouvrir un canal et recevoir sa valeur.
5. Le systeme s'arrete quand la file est vide (quiescence). A ce moment, `_verify_global_constraints`
   parcourt **chaque arete** du graphe pour valider la solution avant de la retourner.

**Note** : `_check_solution` (coherence locale agent par agent) ne suffirait pas a elle seule, car
deux agents non lies par priorite mais lies par contrainte pourraient choisir des valeurs
incompatibles si la file est encore active. La verification globale finale rejette ces faux succes.
'''


CELL_INTERP_VISU = '''### Interpretation de la visualisation

**Graphe de coloration** (gauche) :
- Les noeuds representent les agents 0, 1, 2, 3
- Les couleurs indiquent la valeur choisie par chaque agent **en fin de simulation** (apres quiescence)
- Les aretes montrent les contraintes ; chaque arete doit relier deux couleurs differentes

**Statistiques par agent** (droite) :
- **Messages envoyes** : combien d'`ok?` / `nogood` / `addlink` chaque agent a emis
- **Nogoods generes** : combien de fois cet agent a backtracke (envoye un nogood)

**Lecture du flux ABT** :

1. **Phase d'initialisation** : tous les agents diffusent leur valeur initiale aux agents de
   priorite inferieure (`ok?`). L'agent 0 (priorite la plus haute) emet vers 1, 2, 3 ; l'agent 1
   emet vers 2, 3 ; etc. Le compteur `messages_sent` reflete cette propagation.
2. **Phase de propagation** : chaque agent ajuste sa valeur en fonction des `ok?` recus. Si un
   conflit apparait (la valeur courante n'est plus compatible avec la vue), il choisit une autre
   valeur dans son domaine.
3. **Phase de backtracking** : quand un agent epuise son domaine, il emet un `nogood` vers le plus
   prioritaire des agents de sa vue, qui devra alors changer de valeur. Le compteur
   `nogoods_generated` recense ces emissions.
4. **Quiescence** : la file de messages se vide ; le systeme verifie la coherence globale et
   retourne la solution si toutes les aretes sont satisfaites.

> **A retenir** : les nogoods sont l'outil d'**apprentissage distribue** d'ABT. Plus le graphe est
> dense ou contraint, plus on en accumule. Sur un cycle 4-noeuds avec 3 couleurs, quelques nogoods
> suffisent ; sur des instances plus larges, leur nombre peut exploser et motive AWC ou des
> heuristiques d'oubli.
'''


CELL_INTERP_BENCH = '''### Interpretation des resultats du benchmark

**Lecture** : le benchmark genere `n_runs` instances aleatoires de coloration de graphe avec
`n_agents` agents, un domaine de taille `domain_size`, et une densite de contraintes
`constraint_density`. Pour chaque instance, ABT et AWC sont executes jusqu'a quiescence.

**Ordres de grandeur attendus** (n_agents=5, domain_size=3, density=0.5) :

| Metrique | ABT | AWC | Lecture |
|----------|-----|-----|---------|
| Messages | 10-50 | similaire ou un peu moins | trafic d'`ok?` + `nogood` + `addlink` |
| Nogoods | 0-10 | 0-10 | depend du nombre de conflits rencontres |
| Taux de succes | 60-100% | 60-100% | depend de la satisfiabilite des instances |
| Temps | < 50 ms | < 50 ms | simulation FIFO en RAM |

**Comparaison ABT vs AWC** :

- Sur des instances peu contraintes, les deux convergent en quelques messages : les chiffres se
  ressemblent.
- Sur des instances denses, AWC peut etre plus rapide en messages car il **promeut dynamiquement**
  les agents qui accumulent les nogoods (leur priorite augmente, ce qui change l'ordre de
  propagation et evite des conflits ulterieurs).
- AWC paye ce gain par un cout : a chaque promotion, le systeme reordonnance toutes les priorites
  et rediffuse les `ok?` (`_on_awc_reorder`). Sur les petites instances, ce cout peut effacer le
  benefice.

**Si une instance n'est pas resolue** (`Resolu` = False) :

- Soit l'instance est **insatisfiable** (les contraintes aleatoires bloquent toute affectation)
- Soit `max_iterations` (ici 10 000) a ete atteint avant la quiescence

> **A retenir** : un benchmark DisCSP n'est pas un classement absolu, c'est une mesure de
> **comportement** sur une distribution d'instances. Pour comparer rigoureusement ABT et AWC, il
> faut faire varier `n_agents`, `density`, et tracer messages/nogoods en fonction de ces parametres.
'''


CELL_PATCHES = {
    "9393a18d": ("code", CELL_ABT_AGENT),
    "4055fe66": ("code", CELL_ABT_SYSTEM),
    "5fee8e73": ("code", CELL_AWC_AGENT),
    "69eff4b7": ("code", CELL_BENCHMARK),
    "27c153c7": ("markdown", CELL_INTERP_COLORATION),
    "98c58c2e": ("markdown", CELL_INTERP_VISU),
    "7d6810ce": ("markdown", CELL_INTERP_BENCH),
}


def main():
    nb = json.loads(NB_PATH.read_text(encoding='utf-8'))
    by_id = {c.get("id"): (i, c) for i, c in enumerate(nb["cells"])}
    missing = [k for k in CELL_PATCHES if k not in by_id]
    if missing:
        print(f"ERROR: cells not found: {missing}", file=sys.stderr)
        sys.exit(1)

    for cell_id, (cell_type, src) in CELL_PATCHES.items():
        idx, cell = by_id[cell_id]
        if cell["cell_type"] != cell_type:
            print(f"ERROR: cell {cell_id} expected type {cell_type}, got {cell['cell_type']}", file=sys.stderr)
            sys.exit(1)
        cell["source"] = to_list(src)
        # Reset outputs/execution_count for code cells (Papermill will refresh)
        if cell_type == "code":
            cell["outputs"] = []
            cell["execution_count"] = None
        print(f"Patched cell {idx} ({cell_id}, {cell_type}, {len(cell['source'])} lines)")

    NB_PATH.write_text(json.dumps(nb, indent=1, ensure_ascii=False) + "\n", encoding='utf-8')
    print(f"\nNotebook saved: {NB_PATH}")


if __name__ == "__main__":
    main()
