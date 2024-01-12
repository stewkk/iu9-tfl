#pragma once

#include <string>
#include <unordered_set>
#include <vector>

struct Automata {
  std::vector<std::string> states;
  std::unordered_set<std::size_t> accepting_states;
  std::vector<std::vector<std::string>> transitions;

  bool operator==(const Automata &other) const = default;
};

Automata ReadAutomata(std::istream &in);

using ReachabilityMatrix = std::vector<std::vector<std::size_t>>;

ReachabilityMatrix GetReachabilityMatrix(const Automata &a);

std::vector<std::size_t> GetRandomStateSequence(const ReachabilityMatrix &reachability,
                                                       const Automata &automata);

std::string GetRandomSegment(std::size_t start, std::size_t end, const Automata &a);

std::vector<std::string> GetRandomSegments(const Automata &a,
                                                  const std::vector<std::size_t> &states);

std::string GetRandomString(const Automata &a, const std::vector<std::size_t> &states);

char ChooseRandomSymbolFromString(std::string s);

std::string ReplaceSymbol(std::string s);

std::string AddSymbol(std::string s);

std::string ReverseString(std::string s);

std::string SwapSymbols(std::string s);

std::string SwapFragments(std::string s);

std::string SymbolRepetition(std::string s);

std::string FragmentRepetition(std::string s);

std::string ErasingSymbol(std::string s);

std::string ErasingFragment(std::string s);

std::string ApplyRandomMutation(std::string s);

std::vector<std::string> GetRandomStrings(const Automata &a,
                                                 const std::vector<std::size_t> &states);
