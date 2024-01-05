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
    for (auto& row : res.transitions) {
        for (auto& el : row) {
            in >> el;
        }
    }
    return res;
}

TEST(StringGeneratorTest, ReadsAutomata) {
  istringstream input{"2\n(bb)* b(bb)*\n0 ab\nb 0\n"};

  auto automata = ReadAutomata(input);

  ASSERT_THAT(automata, Eq(Automata{{"(bb)*", "b(bb)*"},
                                    {
                                        {"0", "ab"},
                                        {"b", "0"},
                                    }}));
}

TEST(StringGeneratorTest, BuildsReachabilityMatrix) {

}
