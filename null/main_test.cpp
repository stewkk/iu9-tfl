#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <fmt/format.h>

using testing::Eq;

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
    /*
    ** TODO
    ** 1. [X] Объявить переменные m и n
    ** 2. [X] Наложить ограничения на m и n (>= 0)
    ** 3. Уравнения на баланс правил по буквам
    ** 4. Уравнения на равенство количества правил и их количества в связях
    ** 5. Уравнения для крайних пар?
        */

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

    // Связь mi с ni отдельно для группы с префиксами, группы с суффиксами, префикс и суффиксами, средними элементами
    for (std::size_t i = 0; i < input.size(); i++) {
        for (std::size_t j = 0; j < input.size(); j++) {
            res.push_back(fmt::format("(assert (and (>= n{}{} (- m{} 1)) (<= n{}{} m{})))", i, j, i, i, j, i));
            res.push_back(fmt::format("(assert (and (>= n{}{} (- m{} 1)) (<= n{}{} m{})))", j, i, i, j, i, i));
        }
    }

    return res;
}

static const std::vector<Domino> MOCK_INPUT = {
        {"ab", "a"},
        {"aa", "b"},
        {"bb", "a"},
    };

TEST(SmtTest, DefinesVariables) {
    auto res = GetRules(MOCK_INPUT);

    EXPECT_THAT(res[0], Eq("(declare-fun m0 () Int)"));
    EXPECT_THAT(res[1], Eq("(assert (>= m0 0))"));
    EXPECT_THAT(res[2], Eq("(declare-fun n00 () Int)"));
    EXPECT_THAT(res[3], Eq("(assert (>= n00 0))"));
}
