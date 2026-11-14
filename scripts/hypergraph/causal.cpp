// Énumération bornée des histoires du système multiway de #23093.
#include <algorithm>
#include <iostream>
#include <map>
#include <set>
#include <vector>
#include "HypergraphMatcher.hpp"
#include "TokenEventGraph.hpp"

using namespace SetReplace;
using State = std::vector<AtomsVector>;
using States = std::set<State>;
struct Step { RuleID rule; TokenID input; std::vector<AtomsVector> outputs; };
struct Report { States states; size_t histories = 0, links = 0; std::set<Generation> heights; };

// Rejouer chaque histoire dans son propre graphe : copier TokenEventGraph
// partagerait son implémentation mutable entre branches.
void observe(const std::vector<Step>& history, const State& state, Report& report) {
    TokenEventGraph graph(1, TokenEventGraph::SeparationTrackingMethod::None);
    for (const auto& step : history)
        graph.addEvent(step.rule, {step.input}, static_cast<int>(step.outputs.size()));
    const auto& events = graph.events();
    std::map<TokenID, size_t> creator;
    size_t links = 0;
    for (size_t event = 0; event < events.size(); ++event) {
        for (auto token : events[event].inputTokens) {
            const auto parent = creator.at(token);
            if (parent != 0) ++links;  // La graine n'est pas un événement de réécriture.
            if (parent >= event) throw std::logic_error("causalité non orientée");
        }
        for (auto token : events[event].outputTokens) creator.emplace(token, event);
    }
    if (graph.eventsCount() != history.size()) throw std::logic_error("nombre d'événements");
    report.states.insert(state);
    ++report.histories;
    report.links += links;
    report.heights.insert(graph.largestGeneration());
}

void enumerate(const std::vector<AtomsVector>& tokens, const std::vector<TokenID>& active,
               std::vector<Step>& history, int depth, bool omit_rule, Report& report) {
    if (static_cast<int>(history.size()) == depth) {
        State state;
        for (auto id : active) state.push_back(tokens.at(id));
        std::sort(state.begin(), state.end());
        observe(history, state, report);
        return;
    }
    auto get = [&](const TokenID& id) -> const AtomsVector& { return tokens.at(id); };
    AtomsIndex index(get);
    index.addTokens(active);
    const std::vector<Rule> rules = {
        {{{-1, -2}}, {{-1, -2}, {-1, -1}}, EventSelectionFunction::All},
        {{{-1, -2}}, {{-1, -2}, {-2, -2}}, EventSelectionFunction::All}
    };
    auto separation = [](const TokenID&, const TokenID&) { return SeparationType::Unknown; };
    HypergraphMatcher matcher(rules, &index, get, separation, {},
                              HypergraphMatcher::EventDeduplication::None);
    matcher.addMatchesInvolvingTokens(active, [] { return false; });
    for (const auto& match : matcher.allMatches()) {
        if (omit_rule && match->rule == 1) continue;
        const auto input = match->inputTokens.at(0);
        const auto outputs = matcher.matchOutputAtomsVectors(match);
        auto next_tokens = tokens;
        auto next_active = active;
        next_active.erase(std::find(next_active.begin(), next_active.end(), input));
        for (const auto& edge : outputs) {
            next_active.push_back(static_cast<TokenID>(next_tokens.size()));
            next_tokens.push_back(edge);
        }
        history.push_back({match->rule, input, outputs});
        enumerate(next_tokens, next_active, history, depth, omit_rule, report);
        history.pop_back();
    }
}

States expected(int depth) {
    States states;
    for (int ones = 0; ones <= depth; ++ones) {
        State state{{1, 2}};
        for (int i = 0; i < ones; ++i) state.push_back({1, 1});
        for (int i = ones; i < depth; ++i) state.push_back({2, 2});
        std::sort(state.begin(), state.end());
        states.insert(state);
    }
    return states;
}
int main() {
    for (int depth = 1; depth <= 4; ++depth) {
        std::vector<Step> history;
        Report report, mutant;
        enumerate({{1, 2}}, {0}, history, depth, false, report);
        enumerate({{1, 2}}, {0}, history, depth, true, mutant);
        // Deux choix de règle sur chacune des n arêtes actives : 2^n n! histoires.
        size_t expected_histories = 1;
        for (int i = 1; i <= depth; ++i) expected_histories *= 2 * i;
        // Hauteurs vérifiées sur les petits arbres : chaîne et branchement
        // sont tous deux possibles dès trois événements.
        const std::vector<std::set<Generation>> heights = {{}, {1}, {2}, {2, 3}, {3, 4}};
        if (report.heights != heights.at(depth) ||
            report.states != expected(depth) || mutant.states == expected(depth) ||
            report.histories != expected_histories ||
            report.links != expected_histories * (depth - 1)) return 1;
        std::cout << "profondeur=" << depth << " états=" << report.states.size()
                  << " histoires=" << report.histories << " liens=" << report.links
                  << " hauteurs=";
        for (auto height : report.heights) std::cout << height << ",";
        std::cout << '\n';
    }
}
