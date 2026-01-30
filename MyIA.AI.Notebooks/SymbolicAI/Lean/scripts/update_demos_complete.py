#!/usr/bin/env python3
"""
Complete update of Lean-9 demos with new problems and realistic simulation.
"""

import json
from pathlib import Path


def read_notebook(path: str):
    with open(path, 'r', encoding='utf-8', newline='') as f:
        return json.load(f)


def write_notebook(path: str, nb):
    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
        f.write('\n')


def get_cell_source(cell):
    return ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']


def set_cell_source(cell, source):
    lines = source.split('\n')
    cell['source'] = [line + '\n' for line in lines[:-1]] + ([lines[-1]] if lines[-1] else [])


# New DEMOS definition
NEW_DEMOS = '''DEMOS = [
    {
        "name": "DEMO_1_TRIVIAL",
        "theorem": "theorem demo_rfl (n : Nat) : n = n",
        "description": "Reflexivite - 1 lemme direct (Eq.refl)",
        "expected_iterations": "2-3",
        "complexity": "Triviale"
    },
    {
        "name": "DEMO_2_COMPOSITION",
        "theorem": "theorem add_zero_comm (n m : Nat) : n + m + 0 = m + n",
        "description": "Composition - 2 lemmes (add_zero + add_comm)",
        "expected_iterations": "5-7",
        "complexity": "Simple - necessite combiner 2 lemmes"
    },
    {
        "name": "DEMO_3_MULTI_REWRITE",
        "theorem": "theorem quad_comm (a b c d : Nat) : (a + b) + (c + d) = (d + c) + (b + a)",
        "description": "Reecritures multiples - 4 applications de add_comm + add_assoc",
        "expected_iterations": "10-15",
        "complexity": "Intermediaire - chaine de reecritures"
    },
    {
        "name": "DEMO_4_STRUCTURED",
        "theorem": "theorem distrib_both (a b c : Nat) : (a + b) * c + a * c = a * c + a * c + b * c",
        "description": "Preuve structuree - right_distrib + add_assoc + add_comm",
        "expected_iterations": "15-20",
        "complexity": "Avancee - decomposition + recombinaison"
    }
]'''


# New _simulate_response method (properly indented for class)
NEW_SIMULATE_METHOD = '''    def _simulate_response(self, message: str, state: ProofState) -> str:
        """
        Simulation realiste basee sur l'analyse du theoreme.
        La complexite vient du nombre de lemmes necessaires.
        """
        theorem = state.theorem_statement.lower()
        goal = state.theorem_goal or ""

        if self.name == "SearchAgent":
            return self._do_search(state, theorem, goal)
        elif self.name == "TacticAgent":
            return self._do_tactic(state, theorem, goal)
        elif self.name == "VerifierAgent":
            return self._do_verify(state, theorem, goal)
        elif self.name == "CriticAgent":
            return self._do_critic(state, theorem)
        elif self.name == "CoordinatorAgent":
            return self._do_coordinate(state, theorem)

        return f"[{self.name}] Action simulee."

    def _do_search(self, state: ProofState, theorem: str, goal: str) -> str:
        """Recherche de lemmes basee sur le theoreme."""
        search = self.plugins.get("search")
        state_mgr = self.plugins.get("state")

        if not search or not state_mgr:
            return "[SearchAgent] Plugins manquants."

        lemmas_found = []

        if "n = n" in theorem or goal.strip() == "n = n":
            state_mgr.add_discovered_lemma("Eq.refl", "a = a", "Logic", 1.0)
            lemmas_found.append("Eq.refl")

        if "+ 0" in theorem or "0 +" in theorem:
            state_mgr.add_discovered_lemma("Nat.add_zero", "n + 0 = n", "Nat", 0.9)
            lemmas_found.append("Nat.add_zero")

        if "+" in theorem and ("m + n" in theorem or "n + m" in theorem or "b + a" in theorem or "d + c" in theorem):
            state_mgr.add_discovered_lemma("Nat.add_comm", "n + m = m + n", "Nat", 0.85)
            lemmas_found.append("Nat.add_comm")

        if theorem.count("+") >= 2:
            state_mgr.add_discovered_lemma("Nat.add_assoc", "(n + m) + k = n + (m + k)", "Nat", 0.8)
            lemmas_found.append("Nat.add_assoc")

        if "*" in theorem and "+" in theorem:
            state_mgr.add_discovered_lemma("Nat.right_distrib", "(n + m) * k = n * k + m * k", "Nat", 0.9)
            lemmas_found.append("Nat.right_distrib")

        state_mgr.designate_next_agent("TacticAgent")
        return f"[SearchAgent] Lemmes: {', '.join(lemmas_found[:3])}. -> TacticAgent"

    def _do_tactic(self, state: ProofState, theorem: str, goal: str) -> str:
        """Generation de tactiques."""
        state_mgr = self.plugins.get("state")
        if not state_mgr:
            return "[TacticAgent] Plugin manquant."

        tactics_tried = len(state.tactics_history)

        # DEMO_1
        if "n = n" in theorem:
            state_mgr.log_tactic_attempt("rfl", goal, 1.0, "Reflexivite")
            state_mgr.designate_next_agent("VerifierAgent")
            return "[TacticAgent] Tactique: rfl. -> VerifierAgent"

        # DEMO_2
        if "n + m + 0 = m + n" in theorem:
            if tactics_tried == 0:
                state_mgr.log_tactic_attempt("simp [Nat.add_zero]", goal, 0.6, "Etape 1")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Etape 1: simp [Nat.add_zero]. -> VerifierAgent"
            else:
                state_mgr.log_tactic_attempt("simp [Nat.add_zero, Nat.add_comm]", goal, 0.95, "Complete")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique: simp [Nat.add_zero, Nat.add_comm]. -> VerifierAgent"

        # DEMO_3
        if "quad_comm" in theorem:
            if tactics_tried < 3:
                tactic = ["rw [Nat.add_comm c d]", "rw [Nat.add_comm a b]", "rw [Nat.add_comm]"][min(tactics_tried, 2)]
                state_mgr.log_tactic_attempt(tactic, goal, 0.5 + tactics_tried * 0.1, f"Etape {tactics_tried+1}")
                state_mgr.designate_next_agent("VerifierAgent")
                return f"[TacticAgent] Etape {tactics_tried+1}/4: {tactic}. -> VerifierAgent"
            else:
                state_mgr.log_tactic_attempt("simp only [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]", goal, 0.95, "AC norm")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique finale: AC normalization. -> VerifierAgent"

        # DEMO_4
        if "distrib_both" in theorem:
            tactics = ["rw [Nat.right_distrib]", "rw [Nat.add_assoc]", "rw [Nat.add_comm (a*c)]", "rw [<-Nat.add_assoc]", "ring"]
            if tactics_tried < len(tactics):
                t = tactics[tactics_tried]
                state_mgr.log_tactic_attempt(t, goal, 0.5 + tactics_tried * 0.1, f"Etape {tactics_tried+1}")
                state_mgr.designate_next_agent("VerifierAgent")
                return f"[TacticAgent] Etape {tactics_tried+1}/5: {t}. -> VerifierAgent"
            else:
                state_mgr.log_tactic_attempt("ring", goal, 0.95, "Solveur")
                state_mgr.designate_next_agent("VerifierAgent")
                return "[TacticAgent] Tactique finale: ring. -> VerifierAgent"

        state_mgr.log_tactic_attempt("simp", goal, 0.3, "Fallback")
        state_mgr.designate_next_agent("VerifierAgent")
        return "[TacticAgent] simp. -> VerifierAgent"

    def _do_verify(self, state: ProofState, theorem: str, goal: str) -> str:
        """Verification."""
        state_mgr = self.plugins.get("state")
        if not state_mgr or not state.tactics_history:
            return "[VerifierAgent] Rien a verifier."

        last = state.tactics_history[-1]
        n = len(state.tactics_history)

        # DEMO_1
        if "rfl" in last.tactic and "n = n" in theorem:
            state_mgr.add_verification_result(last.id, True, "OK", "", "", 50.0)
            state_mgr.set_proof_complete(last.tactic)
            return f"[VerifierAgent] SUCCES! {last.tactic}"

        # DEMO_2
        if "n + m + 0 = m + n" in theorem:
            if n == 1:
                state_mgr.add_verification_result(last.id, False, "n+m = m+n", "not closed", "", 80.0)
                state_mgr.designate_next_agent("CriticAgent")
                return "[VerifierAgent] Progres. But restant. -> CriticAgent"
            else:
                state_mgr.add_verification_result(last.id, True, "OK", "", "", 100.0)
                state_mgr.set_proof_complete(last.tactic)
                return f"[VerifierAgent] SUCCES apres {n} etapes!"

        # DEMO_3
        if "quad_comm" in theorem:
            if n < 4:
                state_mgr.add_verification_result(last.id, False, f"{n}/4", "continue", "", 100.0)
                state_mgr.designate_next_agent("CriticAgent")
                return f"[VerifierAgent] Etape {n}/4 OK. -> CriticAgent"
            else:
                state_mgr.add_verification_result(last.id, True, "OK", "", "", 150.0)
                state_mgr.set_proof_complete(last.tactic)
                return f"[VerifierAgent] SUCCES apres {n} reecritures!"

        # DEMO_4
        if "distrib_both" in theorem:
            if n < 5:
                state_mgr.add_verification_result(last.id, False, f"{n}/5", "continue", "", 120.0)
                state_mgr.designate_next_agent("CriticAgent")
                return f"[VerifierAgent] Etape {n}/5. -> CriticAgent"
            else:
                state_mgr.add_verification_result(last.id, True, "OK", "", "", 200.0)
                state_mgr.set_proof_complete(last.tactic)
                return f"[VerifierAgent] SUCCES apres {n} etapes!"

        state_mgr.add_verification_result(last.id, False, "", "error", "", 50.0)
        state_mgr.designate_next_agent("CriticAgent")
        return "[VerifierAgent] Echec. -> CriticAgent"

    def _do_critic(self, state: ProofState, theorem: str) -> str:
        """Analyse critique."""
        state_mgr = self.plugins.get("state")
        if not state_mgr:
            return "[CriticAgent] Plugin manquant."

        n = len(state.tactics_history)

        if "n + m + 0 = m + n" in theorem:
            state_mgr.designate_next_agent("TacticAgent")
            return "[CriticAgent] add_zero OK, besoin add_comm. -> TacticAgent"

        if "quad_comm" in theorem:
            if n < 3:
                state_mgr.designate_next_agent("TacticAgent")
                return f"[CriticAgent] Continuer reecritures ({n}/4). -> TacticAgent"
            else:
                state_mgr.designate_next_agent("CoordinatorAgent")
                return "[CriticAgent] Besoin strategie globale. -> CoordinatorAgent"

        if "distrib_both" in theorem:
            if n < 4:
                state_mgr.designate_next_agent("TacticAgent")
                return f"[CriticAgent] Continuer decomposition ({n}/5). -> TacticAgent"
            else:
                state_mgr.designate_next_agent("CoordinatorAgent")
                return "[CriticAgent] Finaliser. -> CoordinatorAgent"

        state_mgr.designate_next_agent("TacticAgent")
        return "[CriticAgent] Reessayer. -> TacticAgent"

    def _do_coordinate(self, state: ProofState, theorem: str) -> str:
        """Coordination."""
        state_mgr = self.plugins.get("state")
        if not state_mgr:
            return "[CoordinatorAgent] Plugin manquant."

        if "quad_comm" in theorem:
            state_mgr.set_proof_strategy("ac_normalization")
            state_mgr.designate_next_agent("TacticAgent")
            return "[CoordinatorAgent] Strategie: AC normalization. -> TacticAgent"

        if "distrib_both" in theorem:
            state_mgr.set_proof_strategy("ring_solver")
            state_mgr.designate_next_agent("TacticAgent")
            return "[CoordinatorAgent] Strategie: ring solver. -> TacticAgent"

        state_mgr.designate_next_agent("TacticAgent")
        return "[CoordinatorAgent] Default. -> TacticAgent"

'''


def main():
    script_dir = Path(__file__).parent
    notebook_dir = script_dir.parent
    lean9_path = notebook_dir / 'Lean-9-SK-Multi-Agents.ipynb'

    print("=" * 80)
    print("UPDATE LEAN-9 DEMOS WITH NEW PROBLEMS")
    print("=" * 80)

    nb = read_notebook(str(lean9_path))
    print(f"Read {len(nb['cells'])} cells")

    changes = 0

    # 1. Update DEMOS
    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'code':
            continue
        src = get_cell_source(cell)

        if 'DEMOS = [' in src and 'DEMO_1_TRIVIAL' in src:
            print(f"Found DEMOS in cell {i}")

            # Find DEMOS definition
            start = src.find('DEMOS = [')
            bracket_count = 0
            for j, c in enumerate(src[start:]):
                if c == '[':
                    bracket_count += 1
                elif c == ']':
                    bracket_count -= 1
                    if bracket_count == 0:
                        end = start + j + 1
                        break

            new_src = src[:start] + NEW_DEMOS + src[end:]
            set_cell_source(cell, new_src)
            print("  Updated DEMOS")
            changes += 1
            break

    # 2. Update SimpleAgent._simulate_response
    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'code':
            continue
        src = get_cell_source(cell)

        if 'class SimpleAgent:' in src and 'def _simulate_response' in src:
            print(f"Found SimpleAgent in cell {i}")

            # Find _simulate_response
            sim_start = src.find('    def _simulate_response')
            if sim_start == -1:
                print("  Could not find _simulate_response")
                continue

            # Find _call_llm
            call_llm = src.find('    def _call_llm', sim_start)
            if call_llm == -1:
                print("  Could not find _call_llm")
                continue

            # Replace
            new_src = src[:sim_start] + NEW_SIMULATE_METHOD + '\n' + src[call_llm:]
            set_cell_source(cell, new_src)
            print("  Updated _simulate_response")
            changes += 1
            break

    if changes == 2:
        write_notebook(str(lean9_path), nb)
        print(f"\nNotebook saved with {changes} updates")
        print("\nNew problems:")
        print("  DEMO_1: n = n (rfl, 2-3 iter)")
        print("  DEMO_2: n + m + 0 = m + n (add_zero + add_comm, 5-7 iter)")
        print("  DEMO_3: (a+b)+(c+d) = (d+c)+(b+a) (4 rewrites, 10-15 iter)")
        print("  DEMO_4: (a+b)*c + a*c = ... (5 steps, 15-20 iter)")
    else:
        print(f"\nOnly {changes}/2 updates made, not saving")


if __name__ == '__main__':
    main()
