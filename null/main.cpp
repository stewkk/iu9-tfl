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
constexpr auto kVariableLeAssertFmt = "(assert (<= {} 1))";

std::unordered_map<char, std::int32_t> CountLetterOccurences(const std::string& str) {
    std::unordered_map<char, std::int32_t> res;
    for (auto el : str) {
        res[el]++;
    }
    return res;
}

std::unordered_map<std::string, std::int32_t> CountPairOccurences(const std::string& str) {
    std::unordered_map<std::string, std::int32_t> res;
    for (std::size_t i = 0; i < str.size()-1; i++) {
        res[str.substr(i, 2)]++;
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
        for (std::size_t j = 0; j <= input.size(); j++) {
            auto m = fmt::format(kVariable, "n", i, j);
            res.push_back(fmt::format(kVariableDefinitionFmt, m));
            res.push_back(fmt::format(kVariableGeAssertFmt, m));
            if (j == input.size()) {
                res.push_back(fmt::format(kVariableLeAssertFmt, m));
            }
        }
    }

    // Сумма mi >= 1
    std::string sum_of_m = "0";
    for (std::size_t i = 0; i < input.size(); i++) {
        sum_of_m = fmt::format("(+ {} {})", sum_of_m, fmt::format("m{}", i));
    }
    res.push_back(fmt::format("(assert (>= {} 1))", sum_of_m));

    std::string sum_of_n0 = "0";
    for (std::size_t i = 0; i < input.size(); i++) {
        sum_of_n0 = fmt::format("(+ {} {})", sum_of_n0, fmt::format("n{}{}", i, input.size()));
    }
    res.push_back(fmt::format("(assert (= {} 1))", sum_of_n0));

    // Баланс букв по mi
    std::unordered_map<char, std::pair<std::string, std::string>> equations_by_letters;
    for (std::size_t i = 0; i < input.size(); i++) {
        auto& [lhs, rhs] = input[i];
        auto occurences_count_lhs = CountLetterOccurences(lhs);
        auto occurences_count_rhs = CountLetterOccurences(rhs);
        auto occurences_count_both = CountLetterOccurences(lhs+rhs);
        for (const auto& [letter, _] : occurences_count_both) {
            if (!equations_by_letters.contains(letter)) {
                equations_by_letters[letter] = {"0", "0"};
            }
            auto& [equations_lhs, equations_rhs] = equations_by_letters[letter];
            auto lhs_it = occurences_count_lhs.find(letter);
            auto rhs_it = occurences_count_rhs.find(letter);
            if (rhs_it == occurences_count_rhs.end()) {
                equations_lhs = fmt::format("(+ {} {})", equations_lhs, fmt::format("(* {} m{})", lhs_it->second, i));
                continue;
            }
            if (lhs_it == occurences_count_lhs.end()) {
                equations_rhs = fmt::format("(+ {} {})", equations_rhs, fmt::format("(* {} m{})", rhs_it->second, i));
                continue;
            }
            auto lhs = lhs_it->second;
            auto rhs = rhs_it->second;
            if (lhs == rhs) {
                continue;
            }
            equations_lhs = fmt::format("(+ {} {})", equations_lhs, fmt::format("(* {} m{})", lhs, i));
            equations_rhs = fmt::format("(+ {} {})", equations_rhs, fmt::format("(* {} m{})", rhs, i));
        }
    }
    for (const auto& [letter, equation] : equations_by_letters) {
        res.push_back(fmt::format("(assert (= {} {}))", equation.first, equation.second));
    }

    // Связь n с m
    for (std::size_t i = 0; i < input.size(); i++) {
        std::string sum = "0";
        for (std::size_t j = 0; j <= input.size(); j++) {
            sum = fmt::format("(+ n{}{} {})", i, j, sum);
        }
        res.push_back(fmt::format("(assert (= {} m{}))", sum, i));
    }
    for (std::size_t i = 0; i < input.size(); i++) {
        std::string sum = "0";
        for (std::size_t j = 0; j < input.size(); j++) {
            sum = fmt::format("(+ n{}{} {})", j, i, sum);
        }
        res.push_back(fmt::format("(assert (or (= {} m{}) (= {} (- m{} 1))))", sum, i, sum, i));
    }

    // Баланс пар букв
    std::unordered_map<std::string, std::pair<std::string, std::string>> equations_by_pairs;
    for (std::size_t i = 0; i < input.size(); i++) {
        for (std::size_t j = 0; j <= input.size(); j++) {
            auto lhs = input[i].first;
            if (j != input.size()) {
                lhs += input[j].first.front();
            }
            auto rhs = input[i].second;
            if (j != input.size()) {
                rhs += input[j].second.front();
            }
            auto lhs_pairs = CountPairOccurences(lhs);
            auto rhs_pairs = CountPairOccurences(rhs);
            auto both_pairs = CountPairOccurences(lhs+rhs);
            for (const auto& [pair, _] : both_pairs) {
              if (!equations_by_pairs.contains(pair)) {
                equations_by_pairs[pair] = {"0", "0"};
              }
              auto& [equations_lhs, equations_rhs] = equations_by_pairs[pair];
              auto lhs_it = lhs_pairs.find(pair);
              auto rhs_it = rhs_pairs.find(pair);
              if (rhs_it == rhs_pairs.end() && lhs_it == lhs_pairs.end()) {
                  continue;
              }
              if (rhs_it == rhs_pairs.end()) {
                equations_lhs = fmt::format("(+ {} {})", equations_lhs,
                                            fmt::format("(* {} n{}{})", lhs_it->second, i, j));
                continue;
              }
              if (lhs_it == lhs_pairs.end()) {
                equations_rhs = fmt::format("(+ {} {})", equations_rhs,
                                            fmt::format("(* {} n{}{})", rhs_it->second, i, j));
                continue;
              }
              auto lhs = lhs_it->second;
              auto rhs = rhs_it->second;
              if (lhs == rhs) {
                continue;
              }
              equations_lhs
                  = fmt::format("(+ {} {})", equations_lhs, fmt::format("(* {} n{}{})", lhs, i, j));
              equations_rhs
                  = fmt::format("(+ {} {})", equations_rhs, fmt::format("(* {} n{}{})", rhs, i, j));
            }
        }
    }
    for (const auto& [_, equation] : equations_by_pairs) {
        res.push_back(fmt::format("(assert (= {} {}))", equation.first, equation.second));
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
        std::regex input_pattern(R"(\s*\(\s*(.?.*)\s*,\s*(.?.*)\s*\)\s*)",
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
