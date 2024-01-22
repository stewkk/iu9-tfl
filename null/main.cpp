#include <iostream>
#include <unordered_map>
#include <utility>
#include <string>
#include <vector>
#include <regex>
#include <stdexcept>

#include <fmt/format.h>
#include <range/v3/range/conversion.hpp>
#include <range/v3/view/join.hpp>

using namespace ranges;

using Domino = std::pair<std::string, std::string>;

constexpr auto kVariable = "{}{}{}";
constexpr auto kVariableDefinitionFmt = "(declare-fun {} () Int)";
constexpr auto kVariableGeAssertFmt = "(assert (>= {} 0))";

std::unordered_map<char, std::int32_t> CountLetterOccurences(const std::string& str) {
    std::unordered_map<char, std::int32_t> res;
    for (auto el : str) {
        res[el]++;
    }
    return res;
}

std::vector<std::string> GetRules(const std::vector<Domino>& input) {

    std::vector<std::string> res;
    res.reserve(input.size()*4);

    // Объявление переменных и assert'ы >= 0
    for (std::size_t i = 0; i < input.size(); i++) {
        auto n = fmt::format(kVariable, "m", i, "");
        res.push_back(fmt::format(kVariableDefinitionFmt, n));
        res.push_back(fmt::format(kVariableGeAssertFmt, n));
        for (std::size_t j = 0; j < input.size(); j++) {
            auto m = fmt::format(kVariable, "n", i, j);
            res.push_back(fmt::format(kVariableDefinitionFmt, m));
            res.push_back(fmt::format(kVariableGeAssertFmt, m));
        }
    }

    // Сумма mi >= 1
    std::string sum_of_m = "0";
    for (std::size_t i = 0; i < input.size(); i++) {
        sum_of_m = fmt::format("(+ {} {})", sum_of_m, fmt::format("m{}", i));
    }
    res.push_back(fmt::format("(assert (>= {} 1))", sum_of_m));

    // Баланс букв по mi
    std::unordered_map<char, std::pair<std::string, std::string>> equations_by_letters;
    for (std::size_t i = 0; i < input.size(); i++) {
        auto& [lhs, rhs] = input[i];
        auto occurences_count_lhs = CountLetterOccurences(lhs);
        auto occurences_count_rhs = CountLetterOccurences(rhs);
        for (const auto& [letter, lhs] : occurences_count_lhs) {
            if (!equations_by_letters.contains(letter)) {
                equations_by_letters[letter] = {"0", "0"};
            }
            auto& [equations_lhs, equations_rhs] = equations_by_letters[letter];
            auto rhs_it = occurences_count_rhs.find(letter);
            if (rhs_it == occurences_count_rhs.end()) {
                equations_lhs = fmt::format("(+ {} {})", equations_lhs, fmt::format("(* {} m{})", lhs, i));
                continue;
            }
            auto rhs = rhs_it->second;
            if (lhs > rhs) {
                equations_lhs = fmt::format("(+ {} {})", equations_lhs, fmt::format("(* {} m{})", lhs-rhs, i));
            } else if (rhs > lhs) {
                equations_rhs = fmt::format("(+ {} {})", equations_rhs, fmt::format("(* {} m{})", rhs-lhs, i));
            }
        }
    }
    for (const auto& [letter, equation] : equations_by_letters) {
        res.push_back(fmt::format("(assert (= {} {}))", equation.first, equation.second));
    }

    for (std::size_t i = 0; i < input.size(); i++) {
        for (std::size_t j = 0; j < input.size(); j++) {
            res.push_back(fmt::format("(assert (and (>= n{}{} (- m{} 1)) (<= n{}{} m{})))", i, j, i, i, j, i));
            res.push_back(fmt::format("(assert (and (>= n{}{} (- m{} 1)) (<= n{}{} m{})))", j, i, i, j, i, i));
        }
    }

    return res;
}

std::int32_t main() {
    std::vector<Domino> input;
    input.reserve(100);
    std::string line;
    while (std::getline(std::cin, line)) {
        if (std::all_of(line.begin(), line.end(), isspace)) {
            continue;
        }
        std::regex input_pattern(R"(\s*\((.?.*),(.?.*)\)\s*)",
                                 std::regex::ECMAScript);
        std::smatch match;

        if (!std::regex_match(line, match, input_pattern)) {
            throw std::invalid_argument("Invalid input format");
        }
        std::string l = match[1].str();
        std::string r = match[2].str();
        input.push_back({l, r});
    }
    if (input.size() == 0) {
        throw std::invalid_argument("Empty input");
    }

    const auto rules = GetRules(input);

    std::cout << R"(
(set-logic QF_NIA)
)";

    std::cout << (rules | views::join('\n') | to<std::string>()) << '\n';

    std::cout << R"(
(check-sat)
(get-model)
)";

    return 0;
}
