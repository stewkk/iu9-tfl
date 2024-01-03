#pragma once

#include <array>
#include <string>
#include <string_view>
#include <unordered_set>

#include <fmt/format.h>
#include <range/v3/range/conversion.hpp>
#include <range/v3/view/concat.hpp>
#include <range/v3/view/enumerate.hpp>
#include <range/v3/view/filter.hpp>
#include <range/v3/view/iota.hpp>
#include <range/v3/view/join.hpp>
#include <range/v3/view/single.hpp>
#include <range/v3/view/transform.hpp>
#include <range/v3/view/zip.hpp>

using namespace ranges;

class Smt {
    public:
        using Components = std::array<std::string, 6>;

        Components GetComponents(const std::string& composition) {
            if (composition.empty()) {
                throw std::invalid_argument{"Compostion should not be empty"};
            }
            auto func = composition.back();
            Components components;
            for (auto&& [i, component] : components | views::enumerate) {
                component = std::string{func} + std::to_string(i+1);
            }
            return GetComponents(composition.substr(0, composition.size()-1), components);
        }

        Components GetComponents(std::string_view composition, const Components& components) {
            if (composition.empty()) {
                return components;
            }
            Components res = components;
            std::string func{composition.back()};
            constexpr auto kMatrixComponentFormat = "(aadd (amul {}{} {}) (amul {}{} {}))";
            res[0] = fmt::format(kMatrixComponentFormat, func, "1", components[0], func, "2", components[2]);
            res[1] = fmt::format(kMatrixComponentFormat, func, "1", components[1], func, "2", components[3]);
            res[2] = fmt::format(kMatrixComponentFormat, func, "3", components[0], func, "4", components[2]);
            res[3] = fmt::format(kMatrixComponentFormat, func, "3", components[1], func, "4", components[3]);
            constexpr auto kVectorComponentFormat = "(aadd (aadd (amul {}{} {}) (amul {}{} {})) {}{})";
            res[4] = fmt::format(kVectorComponentFormat,
                                    func, "1",
                                    components[4],
                                    func, "2",
                                    components[5],
                                    func, "5"
                                 );
            res[5] = fmt::format(kVectorComponentFormat,
                                    func, "3",
                                    components[4],
                                    func, "4",
                                    components[5],
                                    func, "6"
                                 );
            return GetComponents(composition.substr(0, composition.size()-1), res);
        }

        std::string GetInequalities(const std::string& lhs, const std::string& rhs) {
            return GetInequalitiesByComponents(GetComponents(lhs), GetComponents(rhs));
        }

        std::string GetInequalitiesByComponents(const Components& lhs, const Components& rhs) {
            return views::zip(lhs, rhs) | views::transform([](const auto& el) {
                return fmt::format("(assert (agt {} {}))", el.first, el.second);
            }) | views::join('\n') | to<std::string>();
        }

        std::string GetVariables(const std::string& composition) {
            auto get_statements = [](char func) {
                constexpr auto kVariableDefinitionFmt = "(declare-fun {}{} () Int)";
                constexpr auto kVariableGeAssertFmt = "(assert (>= {}{} -1))";
                constexpr auto kVariableGtAssertFmt = "(assert (> {}1 -1))";
                constexpr auto kVectorElementAssertFmt = "(assert (or (>= {}5 0) (and (= {}5 0) (= {}6 0))))";
                const auto definitions = views::ints(1, 7) | views::transform([func, &kVariableDefinitionFmt](auto i) {
                    return fmt::format(kVariableDefinitionFmt, func, i);
                });
                const auto ge_asserts = views::ints(1, 6) | views::transform([func, &kVariableGeAssertFmt](auto i) {
                    return fmt::format(kVariableGeAssertFmt, func, i);
                });

                return views::concat(
                    definitions,
                    ge_asserts,
                    views::single(fmt::format(kVariableGtAssertFmt, func)),
                    views::single(fmt::format(kVectorElementAssertFmt, func, func, func))
                ) | views::join('\n') | to<std::string>();
            };

            std::vector<std::string> statements;
            statements.reserve(composition.size());
            for (auto func : composition) {
                if (defined_funcs_.contains(func)) {
                    continue;
                }
                defined_funcs_.insert(func);
                statements.push_back(get_statements(func));
            }
            return statements | views::join('\n') | to<std::string>();
        }

    private:
        std::unordered_set<char> defined_funcs_;
};
