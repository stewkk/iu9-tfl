#include <cstdint>
#include <iostream>
#include <regex>

#include "string_generator.hpp"

bool Match(const std::string& str, const Automata& automata, std::size_t state, std::size_t index) {
    if (index == str.size()) {
        return automata.accepting_states.contains(state);
    }
    bool res = false;
    for (std::size_t next = 0; next < automata.states.size(); next++) {
        if (automata.transitions[state][next] == "0") {
            continue;
        }
        for (auto el : automata.transitions[state][next]) {
            if (el == str[index]) {
                res = res || Match(str, automata, next, index+1);
            }
        }
    }
    return res;
}

std::int32_t main() {
    auto automata = ReadAutomata(std::cin);
    std::string regex;
    std::cin >> regex;
    std::string str;
    while (std::cin >> str) {
      bool is_matched_by_automata = Match(str, automata, 0ul, 0ul);
      std::regex pattern(regex, std::regex::ECMAScript);
      std::smatch match;
      bool is_matched_by_regex = std::regex_match(str, match, pattern);

      if (is_matched_by_automata != is_matched_by_regex) {
          std::cout << "FAIL: " << automata.states.front() << ' ' << regex << ' ' << is_matched_by_automata << ' ' << is_matched_by_regex << ' ' << str << '\n';
      } else {
          std::cout << "Pass: " << automata.states.front() << ' ' << regex << ' ' << str << '\n';
      }
    }
    return 0;
}
