#pragma once

#include <array>
#include <string>
#include <string_view>

#include <fmt/format.h>
#include <range/v3/range/conversion.hpp>
#include <range/v3/view/enumerate.hpp>
#include <range/v3/view/join.hpp>
#include <range/v3/view/transform.hpp>
#include <range/v3/view/zip.hpp>

using namespace ranges;

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

        std::string Serialize(const std::string& lhs, const std::string& rhs) {
            return Serialize(Serialize(lhs), Serialize(rhs));
        }

        std::string Serialize(const Components& lhs, const Components& rhs) {
            return views::zip(lhs, rhs) | views::transform([](const auto& el) {
                return fmt::format("(assert (agt {} {}))", el.first, el.second);
            }) | views::join('\n') | to<std::string>();
        }
};
