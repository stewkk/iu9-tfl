#include <iostream>

#include "string_generator.hpp"

std::int32_t main() {
    auto automata = ReadAutomata(std::cin);
    for (const auto& el : GetRandomStrings(automata, GetRandomStateSequence(GetReachabilityMatrix(automata), automata))) {
        std::cout << el << '\n';
    }
    return 0;
}
