#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <iostream>
#include <random>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

using std::istringstream;
using testing::Contains;
using testing::Eq;

struct Transition {
  std::string symbols;
  std::size_t state;

  bool operator==(const Transition &other) const = default;
};

struct Automata {
  std::vector<std::string> states;
  std::unordered_set<std::size_t> accepting_states;
  std::vector<std::vector<Transition>> transitions;

  bool operator==(const Automata &other) const = default;
};

Automata ReadAutomata(std::istream &in) {
  std::size_t n;
  in >> n;
  Automata res;
  res.states.assign(n, {});
  for (auto &el : res.states) {
    in >> el;
  }
  std::size_t accepting_states_count;
  in >> accepting_states_count;
  for (std::size_t i = 0; i < accepting_states_count; i++) {
    std::size_t state;
    in >> state;
    res.accepting_states.insert(state);
  }
  res.transitions.assign(n, {});
  for (auto &row : res.transitions) {
    for (std::size_t i = 0; i < n; i++) {
      std::string transition;
      in >> transition;
      if (transition != "0") {
        row.push_back({transition, i});
      }
    }
  }
  return res;
}

using ReachabilityMatrix = std::vector<std::vector<std::size_t>>;

ReachabilityMatrix GetReachabilityMatrix(const Automata &a) {
  const auto n = a.states.size();
  std::vector<std::vector<bool>> dp(n, std::vector<bool>(n));
  for (std::size_t i = 0; i < n; i++) {
    for (auto &el : a.transitions[i]) {
      dp[i][el.state] = true;
    }
  }
  for (std::size_t k = 0; k < n; k++) {
    for (std::size_t i = 0; i < n; i++) {
      for (std::size_t j = 0; j < n; j++) {
        dp[i][j] = dp[i][j] || (dp[i][k] && dp[k][j]);
      }
    }
  }
  ReachabilityMatrix res(n);
  for (std::size_t i = 0; i < n; i++) {
    for (std::size_t j = 0; j < n; j++) {
      if (dp[i][j]) {
        res[i].push_back(j);
      }
    }
  }
  return res;
}

std::vector<std::size_t> GetRandomStateSequence(const ReachabilityMatrix &reachability,
                                                 const Automata &automata) {
  std::vector<std::size_t> res = {0};

  std::random_device rd;
  std::mt19937 generator(rd());

  auto min_states_count = std::uniform_int_distribution<std::int32_t>(0, 20)(generator);

  for (std::size_t i = 0; i < static_cast<std::size_t>(min_states_count); i++) {
    const auto& current_state_reachability = reachability[res.back()];
    auto next = std::uniform_int_distribution<std::int32_t>(0, current_state_reachability.size()-1)(generator);
    res.push_back(next);
  }
  if (!automata.accepting_states.contains(res.back())) {
    for (auto next : reachability[res.back()]) {
      // NOTE: choose random final state here?
      if (automata.accepting_states.contains(next)) {
        res.push_back(next);
      }
    }
  }
  if (!automata.accepting_states.contains(res.back())) {
    throw std::logic_error{"Can't build random state sequence"};
  }
  return res;
}

TEST(StringGeneratorTest, ReadsAutomata) {
  istringstream input{"2\n(bb)* b(bb)*\n1 0\n0 ab\nb 0\n"};

  auto got = ReadAutomata(input);

  ASSERT_THAT(got, Eq(Automata{{"(bb)*", "b(bb)*"},
                               {0},
                               {
                                   {{"ab", 1}},
                                   {{"b", 0}},
                               }}));
}

TEST(StringGeneratorTest, BuildsReachabilityMatrix) {
  Automata a{{"(bb)*", "b(bb)*"},
             {0},
             {
                 {{"ab", 1}},
                 {{"b", 0}},
             }};

  ReachabilityMatrix got = GetReachabilityMatrix(a);

  ASSERT_THAT(got, Eq(ReachabilityMatrix{{0, 1}, {0, 1}}));
}

TEST(StringGeneratorTest, BuildsRandomStateSequence) {
  Automata a{{"(bb)*", "b(bb)*"},
             {0},
             {
                 {{"ab", 1}},
                 {{"b", 0}},
             }};
  ReachabilityMatrix reachability = GetReachabilityMatrix(a);

  auto got = GetRandomStateSequence(reachability, a);

  EXPECT_THAT(got.front(), Eq(0));
  EXPECT_THAT(a.accepting_states, Contains(got.back()));
}

