#include <iostream>
#include <sstream>

#include "parser.hpp"
#include "serializer.hpp"

std::int32_t main() {
    std::ostringstream out;
    out << "(set-logic QF_NIA)\n";
    out << "(define-fun aadd ((a Int) (b Int)) Int (ite (> a b) a b))\n";
    out << "(define-fun amul ((a Int) (b Int)) Int (ite (or (= a -1) (= b -1)) -1 (+ a b)))\n";
    out << "(define-fun agt ((a Int) (b Int)) Bool (or (> a b) (and (= a -1) (= b -1))))\n";

    Parser p;
    std::string line;
    Smt s;
    while (std::getline(std::cin, line)) {
        auto rule = p.Parse(line);
        if (!rule.has_value()) {
            continue;
        }
        auto& [lhs, rhs] = rule.value();
        out << s.GetVariables(lhs) << '\n';
        out << s.GetVariables(rhs) << '\n';
        out << s.GetInequalities(lhs, rhs) << '\n';
    }

    out << "(check-sat)\n(get-model)\n(exit)\n";
    std::cout << out.str();
    return 0;
}
