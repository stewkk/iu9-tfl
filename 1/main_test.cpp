#include <gtest/gtest.h>
#include <gmock/gmock.h>

#include <string>
#include <string_view>
#include <utility>

#include <algorithm>
#include <optional>
#include <regex>
#include <stdexcept>

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
