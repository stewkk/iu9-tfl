#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include "string_generator.hpp"

using testing::Contains;
using testing::Eq;
using testing::Gt;
using testing::MatchesRegex;

TEST(StringGeneratorTest, ReadsAutomata) {
  std::istringstream input{"2\n(bb)* b(bb)*\n1 0\n0 ab\nb 0\n"};

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

  ASSERT_THAT(got, Eq(ReachabilityMatrix{{0, 1}, {0, 1}}));
}

TEST(StringGeneratorTest, BuildsRandomStateSequence) {
  Automata a{{"(bb)*", "b(bb)*"},
             {0},
             {
                 {"0", "ab"},
                 {"b", "0"},
             }};
  ReachabilityMatrix reachability = GetReachabilityMatrix(a);

  auto got = GetRandomStateSequence(reachability, a);

  EXPECT_THAT(got.front(), Eq(0));
  EXPECT_THAT(a.accepting_states, Contains(got.back()));
}

TEST(StringGeneratorTest, BuildsSegmentFromTwoStates) {
  Automata a{{"(bb)*", "b(bb)*"},
             {0},
             {
                 {"0", "ab"},
                 {"b", "0"},
             }};

  auto got = GetRandomSegment(0, 1, a);

  ASSERT_THAT(got, MatchesRegex(R"(a|b(b(a|b))*)"));
}

TEST(StringGeneratorTest, BuildsRandomStringFromStateSequence) {
  Automata a{{"(bb)*", "b(bb)*"},
             {0},
             {
                 {"0", "ab"},
                 {"b", "0"},
             }};
  auto states = GetRandomStateSequence(GetReachabilityMatrix(a), a);

  auto got = GetRandomString(a, states);

  ASSERT_THAT(got, MatchesRegex(R"(((a|b)b)*)"));
}

TEST(StringGeneratorTest, BuildsRandomStringsFromStateSequence) {
  Automata a{{"(bb)*", "b(bb)*"},
             {0},
             {
                 {"0", "ab"},
                 {"b", "0"},
             }};
  auto states = GetRandomStateSequence(GetReachabilityMatrix(a), a);

  auto got = GetRandomStrings(a, states);

  ASSERT_THAT(got.size(), Gt(0));
}
