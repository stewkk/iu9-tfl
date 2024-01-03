#include <gtest/gtest.h>
#include <gmock/gmock.h>

#include <algorithm>
#include <array>
#include <optional>
#include <regex>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>

#include <fmt/format.h>
#include <range/v3/range/conversion.hpp>
#include <range/v3/view/enumerate.hpp>
#include <range/v3/view/join.hpp>
#include <range/v3/view/transform.hpp>
#include <range/v3/view/zip.hpp>

using testing::Eq;
using namespace std::literals;
using namespace ranges;

class Parser {
    public:
        std::optional<std::pair<std::string, std::string>> Parse(const std::string& s) {
          if (std::all_of(s.begin(), s.end(), isspace)) {
            return std::nullopt;
          }

          std::regex input_pattern(R"(\s*([a-zA-Z]+)\s*->\s*([a-zA-Z]+)\s*)",
                                   std::regex::ECMAScript);
          std::smatch match;

          if (!std::regex_match(s, match, input_pattern)) {
            throw std::invalid_argument("Invalid input format");
          }
          std::string l = match[1].str();
          std::string r = match[2].str();
          return std::make_pair(l, r);
        }
};

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

class Smt {
    public:
        using Components = std::array<std::string, 6>;

        Components Serialize(const std::string& composition) {
            if (composition.empty()) {
                throw std::invalid_argument{"Compostion should not be empty"};
            }
            auto func = composition.back();
            Components components;
            for (auto&& [i, component] : components | views::enumerate) {
                component = std::string{func} + std::to_string(i+1);
            }
            return Serialize(composition.substr(0, composition.size()-1), components);
        }

        Components Serialize(std::string_view composition, const Components& components) {
            if (composition.empty()) {
                return components;
            }
            Components res = components;
            std::string func{composition.back()};
            constexpr auto matrix_component_format = "(aadd (amul {}{} {}) (amul {}{} {}))";
            res[0] = fmt::format(matrix_component_format, func, "1", components[0], func, "2", components[2]);
            res[1] = fmt::format(matrix_component_format, func, "1", components[1], func, "2", components[3]);
            res[2] = fmt::format(matrix_component_format, func, "3", components[0], func, "4", components[2]);
            res[3] = fmt::format(matrix_component_format, func, "3", components[1], func, "4", components[3]);
            constexpr auto vector_component_format = "(aadd (aadd (amul {}{} {}) (amul {}{} {})) {}{})";
            res[4] = fmt::format(vector_component_format,
                                    func, "1",
                                    components[4],
                                    func, "2",
                                    components[5],
                                    func, "5"
                                 );
            res[5] = fmt::format(vector_component_format,
                                    func, "3",
                                    components[4],
                                    func, "4",
                                    components[5],
                                    func, "6"
                                 );
            return Serialize(composition.substr(0, composition.size()-1), res);
        }

        std::string Serialize(const Components& lhs, const Components& rhs) {
            return views::zip(lhs, rhs) | views::transform([](const auto& el) {
                return fmt::format("(assert (agt {} {}))", el.first, el.second);
            }) | views::join('\n') | to<std::string>();
        }
};

TEST(SerializerTest, SerializesSingleVariable) {
    Smt s;

    auto res = s.Serialize("f");

    ASSERT_THAT(res, Eq(Smt::Components{"f1", "f2", "f3", "f4", "f5", "f6"}));
}

TEST(SerializerTest, SerializesSecondVariable) {
    Smt s;

    auto res = s.Serialize("g"sv, Smt::Components{"f1", "f2", "f3", "f4", "f5", "f6"});

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

    auto res = s.Serialize(Smt::Components{"f1", "f2", "f3", "f4", "f5", "f6"},
                           Smt::Components{"g1", "g2", "g3", "g4", "g5", "g6"});

    ASSERT_THAT(res, Eq("(assert (agt f1 g1))\n(assert (agt f2 g2))\n\
(assert (agt f3 g3))\n(assert (agt f4 g4))\n(assert (agt f5 g5))\n(assert (agt f6 g6))"));
}
