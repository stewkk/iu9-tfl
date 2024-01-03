#include <iostream>
#include <sstream>

#include "parser.hpp"
#include "serializer.hpp"

// TODO: stress tests

std::int32_t main(std::int32_t argc, char* argv[]) {
    std::ostringstream out;
    // Define functions
    out << "(set-logic QF_NIA)\n";
    out << "(declare-fun aadd ((a Int) (b Int) Int ()))\n";
    out << "(declare-fun amul ((a Int) (b Int) Int ()))\n";
    out << "(declare-fun agt ((a Int) (b Int) Int ()))\n";

    Parser p;
    std::string line;
    Smt s;
    while (std::getline(std::cin, line)) {
        auto rule = p.Parse(line);
        if (!rule.has_value()) {
            continue;
        }
        auto& [lhs, rhs] = rule.value();

        s.Serialize(lhs);

        // Define variablies

        // Asserts on variables

        // Asserts on inequalities
    }

    // Check-sat

    std::cout << out.str();
    return 0;
}
