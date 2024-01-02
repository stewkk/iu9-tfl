#include <gtest/gtest.h>
#include <gmock/gmock.h>

#include <string>
#include <string_view>
#include <utility>

#include <algorithm>
#include <optional>
#include <regex>
#include <stdexcept>
#include <array>

#include <fmt/format.h>
#include <range/v3/view/enumerate.hpp>


using testing::Eq;
using namespace std::literals;

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
        Components Serialize(char f) {
            Components res;
            for (auto&& [i, component] : res | ranges::views::enumerate) {
                component = std::string{f} + std::to_string(i+1);
            }
            return res;
        }
        Components Serialize(std::string_view rest, const Components& components) {
            Components res = components;
            char next = rest.back();
            res[0] = fmt::format("(aadd (amul {} {}) (amul {} {}))", std::string{next}+"1", components[0], std::string{next}+"2", components[2]);
            res[1] = fmt::format("(aadd (amul {} {}) (amul {} {}))", std::string{next}+"1", components[1], std::string{next}+"2", components[3]);
            res[2] = fmt::format("(aadd (amul {} {}) (amul {} {}))", std::string{next}+"3", components[0], std::string{next}+"4", components[2]);
            res[3] = fmt::format("(aadd (amul {} {}) (amul {} {}))", std::string{next}+"3", components[1], std::string{next}+"4", components[3]);
            res[4] = fmt::format("(aadd (aadd (amul {} {}) (amul {} {})) {})",
                                    std::string{next}+"1",
                                    components[4],
                                    std::string{next}+"2",
                                    components[5],
                                    std::string{next}+"5"
                                 );
            res[5] = fmt::format("(aadd (aadd (amul {} {}) (amul {} {})) {})",
                                    std::string{next}+"3",
                                    components[4],
                                    std::string{next}+"4",
                                    components[5],
                                    std::string{next}+"6"
                                 );
            return res;
        }
};

TEST(SerializerTest, SerializesSingleVariable) {
    Smt s;

    auto res = s.Serialize('f');

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
