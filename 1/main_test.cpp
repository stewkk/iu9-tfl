#include <gtest/gtest.h>
#include <gmock/gmock.h>

#include <optional>
#include <utility>

#include <fmt/format.h>
#include <range/v3/range/conversion.hpp>
#include <range/v3/view/enumerate.hpp>
#include <range/v3/view/join.hpp>
#include <range/v3/view/transform.hpp>
#include <range/v3/view/zip.hpp>

#include "parser.hpp"
#include "serializer.hpp"

using testing::Eq;
using namespace std::literals;

TEST(ParserTest, ParsesSimpleString) {
    Parser p;

    auto res = p.Parse("fg ->gf ");

    ASSERT_THAT(res, Eq(std::make_pair("fg"s, "gf"s)));
}

TEST(ParserTest, ThrowsOnBadInput) {
    Parser p;

    ASSERT_ANY_THROW(auto _ = p.Parse("fg - gf"));
}

TEST(ParserTest, NulloptOnEmptyString) {
    Parser p;

    auto res = p.Parse("   ");

    ASSERT_THAT(res, Eq(std::nullopt));
}

TEST(SerializerTest, SerializesSingleVariable) {
    Smt s;

    auto res = s.GetComponents("f");

    ASSERT_THAT(res, Eq(Smt::Components{"f1", "f2", "f3", "f4", "f5", "f6"}));
}

TEST(SerializerTest, SerializesSecondVariable) {
    Smt s;

    auto res = s.GetComponents("g"sv, Smt::Components{"f1", "f2", "f3", "f4", "f5", "f6"});

    ASSERT_THAT(res, Eq(Smt::Components{
            "(aadd (amul g1 f1) (amul g2 f3))",
            "(aadd (amul g1 f2) (amul g2 f4))",
            "(aadd (amul g3 f1) (amul g4 f3))",
            "(aadd (amul g3 f2) (amul g4 f4))",
            "(aadd (aadd (amul g1 f5) (amul g2 f6)) g5)",
            "(aadd (aadd (amul g3 f5) (amul g4 f6)) g6)",
            }));
}

TEST(SerializerTest, SerializesInequality) {
    Smt s;

    auto res = s.GetInequalitiesByComponents(Smt::Components{"f1", "f2", "f3", "f4", "f5", "f6"},
                           Smt::Components{"g1", "g2", "g3", "g4", "g5", "g6"});

    ASSERT_THAT(res, Eq("(assert (agt f1 g1))\n(assert (agt f2 g2))\n\
(assert (agt f3 g3))\n(assert (agt f4 g4))\n(assert (agt f5 g5))\n(assert (agt f6 g6))"));
}
