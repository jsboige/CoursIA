// Mesure du grain B de #23093 avec le matcher officiel libSetReplace.
#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <set>
#include <string>
#include <vector>
#include "HypergraphMatcher.hpp"

using namespace SetReplace;
using State = std::vector<AtomsVector>;
using States = std::set<State>;

States successors(const State& state, bool inject_fault = false) {
    auto get = [&](const TokenID& i) -> const AtomsVector& { return state.at(i); };
    AtomsIndex index(get);
    std::vector<TokenID> ids(state.size());
    std::iota(ids.begin(), ids.end(), 0);
    index.addTokens(ids);
    const std::vector<Rule> rules = {
        {{{-1, -2}}, {{-1, -2}, {-1, -1}}, EventSelectionFunction::All},
        {{{-1, -2}}, {{-1, -2}, {-2, -2}}, EventSelectionFunction::All}
    };
    auto separation = [](const TokenID&, const TokenID&) { return SeparationType::Unknown; };
    HypergraphMatcher matcher(rules, &index, get, separation, {},
                              HypergraphMatcher::EventDeduplication::None);
    matcher.addMatchesInvolvingTokens(ids, [] { return false; });
    States result;
    for (const auto& match : matcher.allMatches()) {
        if (inject_fault && match->rule == 1) continue;
        State next = state;
        // Une seule arête en entrée pour chacune des règles du protocole.
        next.erase(next.begin() + match->inputTokens.at(0));
        for (const auto& edge : matcher.matchOutputAtomsVectors(match)) next.push_back(edge);
        std::sort(next.begin(), next.end());
        result.insert(next);
    }
    return result;
}

States expected_states(int step) {
    States expected;
    for (int ones = 0; ones <= step; ++ones) {
        State s{{1, 2}};
        for (int i = 0; i < ones; ++i) s.push_back({1, 1});
        for (int i = ones; i < step; ++i) s.push_back({2, 2});
        std::sort(s.begin(), s.end());
        expected.insert(s);
    }
    return expected;
}

int main(int argc, char** argv) {
    if (argc == 2 && std::string(argv[1]) == "--self-test") {
        const State seed{{1, 2}};
        if (successors(seed) != expected_states(1) ||
            successors(seed, true) == expected_states(1)) return 1;
        std::cout << "témoin positif et défaut injecté détecté\n";
        return 0;
    }
    if (argc != 2) { std::cerr << "usage: multiway profondeur\n"; return 2; }
    const int depth = std::atoi(argv[1]);
    if (depth < 1 || depth > 48) return 2;
    States states{{{1, 2}}};
    auto start = std::chrono::steady_clock::now();
    for (int step = 1; step <= depth; ++step) {
        States next;
        for (const auto& state : states) {
            const auto children = successors(state);
            next.insert(children.begin(), children.end());
            if (next.size() > 49) { std::cerr << "budget d’états dépassé\n"; return 1; }
        }
        states = std::move(next);
        // À chaque pas, une boucle 11 ou 22 est ajoutée. Le témoin vérifie
        // aussi le contenu, pas seulement le nombre d'états.
        if (states != expected_states(step)) { std::cerr << "témoin incorrect au pas " << step << '\n'; return 1; }
        if (std::chrono::steady_clock::now() - start > std::chrono::seconds(30)) {
            std::cerr << "budget de temps dépassé\n"; return 1;
        }
    }
    auto elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
    std::cout << "{\"depth\":" << depth << ",\"states\":" << states.size()
              << ",\"seconds\":" << elapsed << ",\"witness\":true}\n";
}
