#include <gtest/gtest.h>
#include <gmock/gmock.h>

#include <iostream>
#include <sstream>
#include <vector>
#include <string>

using std::istringstream;
using testing::Eq;

struct Automata {
    std::vector<std::string> states;
    std::vector<std::size_t> accepting_states;
    std::vector<std::vector<std::string>> transitions;

    bool operator ==(const Automata& other) const = default;
};

Automata ReadAutomata(std::istream& in) {
    std::size_t n;
    in >> n;
    Automata res;
    res.states.assign(n, {});
    res.transitions.assign(n, std::vector<std::string>(n));
    for (auto& el : res.states) {
        in >> el;
    }
    std::size_t accepting_states_count;
    in >> accepting_states_count;
    res.accepting_states.assign(accepting_states_count, {});
    for (auto& el : res.accepting_states) {
        in >> el;
    }
    for (auto& row : res.transitions) {
        for (auto& el : row) {
            in >> el;
        }
    }
    return res;
}

using ReachabilityMatrix = std::vector<std::vector<bool>>;

ReachabilityMatrix GetReachabilityMatrix(const Automata& a) {
    const auto n = a.states.size();
    ReachabilityMatrix res(n, ReachabilityMatrix::value_type(n));
    for (std::size_t i = 0; i < n; i++) {
        for (std::size_t j = 0; j < n; j++) {
            if (!a.transitions[i][j].empty()) {
                res[i][j] = true;
            }
        }
    }
    for (std::size_t k = 0; k < n; k++) {
        for (std::size_t i = 0; i < n; i++) {
            for (std::size_t j = 0; j < n; j++) {
                res[i][j] = res[i][j] || (res[i][k] && res[k][j]);
            }
        }
    }
    return res;
}

TEST(StringGeneratorTest, ReadsAutomata) {
  istringstream input{"2\n(bb)* b(bb)*\n1 0\n0 ab\nb 0\n"};

  auto got = ReadAutomata(input);

  ASSERT_THAT(got, Eq(Automata{{"(bb)*", "b(bb)*"},
                               {0},
                                    {
                                        {"0", "ab"},
                                        {"b", "0"},
                                    }}));
}

TEST(StringGeneratorTest, BuildsReachabilityMatrix) {
    Automata a{{"(bb)*", "b(bb)*"},
               {0},
               {
                   {"0", "ab"},
                   {"b", "0"},
               }};

    ReachabilityMatrix got = GetReachabilityMatrix(a);

    ASSERT_THAT(got, Eq(ReachabilityMatrix{{1, 1}, {1, 1}}));
}

