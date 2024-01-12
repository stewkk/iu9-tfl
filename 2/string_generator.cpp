#include "string_generator.hpp"

#include <algorithm>
#include <iostream>
#include <queue>
#include <random>
#include <sstream>

static std::random_device rd;
static std::mt19937 generator(rd());


Automata ReadAutomata(std::istream &in) {
  std::size_t n;
  in >> n;
  Automata res;
  res.states.assign(n, {});
  for (auto &el : res.states) {
    in >> el;
  }
  std::size_t accepting_states_count;
  in >> accepting_states_count;
  for (std::size_t i = 0; i < accepting_states_count; i++) {
    std::size_t state;
    in >> state;
    res.accepting_states.insert(state);
  }
  res.transitions.assign(n, std::vector<std::string>(n));
  for (auto &row : res.transitions) {
    for (auto &el : row) {
      in >> el;
    }
  }
  return res;
}

ReachabilityMatrix GetReachabilityMatrix(const Automata &a) {
  const auto n = a.states.size();
  std::vector<std::vector<bool>> dp(n, std::vector<bool>(n));
  for (std::size_t i = 0; i < n; i++) {
    for (std::size_t j = 0; j < n; j++) {
      if (a.transitions[i][j] != "0") {
        dp[i][j] = true;
      }
    }
  }
  for (std::size_t k = 0; k < n; k++) {
    for (std::size_t i = 0; i < n; i++) {
      for (std::size_t j = 0; j < n; j++) {
        dp[i][j] = dp[i][j] || (dp[i][k] && dp[k][j]);
      }
    }
  }
  ReachabilityMatrix res(n);
  for (std::size_t i = 0; i < n; i++) {
    for (std::size_t j = 0; j < n; j++) {
      if (dp[i][j]) {
        res[i].push_back(j);
      }
    }
  }
  return res;
}

std::vector<std::size_t> GetRandomStateSequence(const ReachabilityMatrix &reachability,
                                                       const Automata &automata) {
  std::vector<std::size_t> res = {0};

  auto min_states_count = std::uniform_int_distribution<std::int32_t>(5, 30)(generator);

  for (std::size_t i = 0; i < static_cast<std::size_t>(min_states_count); i++) {
    const auto &current_state_reachability = reachability[res.back()];
    if (current_state_reachability.size() == 0) {
      break;
    }
    auto next = std::uniform_int_distribution<std::int32_t>(
        0, current_state_reachability.size() - 1)(generator);
    res.push_back(current_state_reachability[next]);
  }
  if (!automata.accepting_states.contains(res.back())) {
    for (auto next : reachability[res.back()]) {
      // TODO: choose random final state here?
      if (automata.accepting_states.contains(next)) {
        res.push_back(next);
      }
    }
  }
  if (!automata.accepting_states.contains(res.back())) {
    throw std::logic_error{"Can't build random state sequence"};
  }
  return res;
}

std::string GetRandomSegment(std::size_t start, std::size_t end, const Automata &a) {
  std::queue<std::size_t> q;
  std::vector<std::int32_t> used(a.states.size(), -1);
  q.push(static_cast<int32_t>(start));
  used[start] = -2;
  while (!q.empty()) {
    auto cur = q.front();
    q.pop();
    // TODO: кажется, восстанавливать ответ надо более умным способом
    if (cur == end) {
      std::ostringstream out;
      auto prev = used[cur];
      while (prev != -2) {
        auto transition = a.transitions[prev][cur];
        auto symbol = transition[std::uniform_int_distribution<std::int32_t>(
            0, transition.size() - 1)(generator)];
        out << symbol;
        cur = prev;
        prev = used[cur];
      }
      auto tmp = out.str();
      std::reverse(tmp.begin(), tmp.end());
      return tmp;
    }
    for (std::size_t next = 0; next < a.states.size(); next++) {
      if (a.transitions[cur][next] != "0" && used[next] == -1) {
        used[next] = cur;
        q.push(next);
      }
    }
  }
  throw std::logic_error{"GetRandomSegment failed"};
}

std::vector<std::string> GetRandomSegments(const Automata &a,
                                                  const std::vector<std::size_t> &states) {
  std::vector<std::string> segments;
  for (std::size_t i = 0; i < states.size() - 1; i++) {
    auto [l, r] = std::pair{states[i], states[i + 1]};
    segments.push_back(GetRandomSegment(l, r, a));
  }
  return segments;
}

std::string GetRandomString(const Automata &a, const std::vector<std::size_t> &states) {
  std::ostringstream res;
  for (const auto &el : GetRandomSegments(a, states)) {
    res << el;
  }
  return res.str();
}

char ChooseRandomSymbolFromString(std::string s) {
  std::sort(s.begin(), s.end());
  auto last = std::unique(s.begin(), s.end());
  auto to_replace = std::uniform_int_distribution<std::int32_t>(
      0, static_cast<std::int32_t>(last - s.begin()) - 1)(generator);
  return s[to_replace];
}

std::string ReplaceSymbol(std::string s) {
  auto where = std::uniform_int_distribution<std::int32_t>(
      0, static_cast<std::int32_t>(s.size()) - 1)(generator);
  s[where] = ChooseRandomSymbolFromString(s);
  return s;
}

std::string AddSymbol(std::string s) {
  auto where = std::uniform_int_distribution<std::int32_t>(
      0, static_cast<std::int32_t>(s.size()) - 1)(generator);
  s.insert(where, std::string{ChooseRandomSymbolFromString(s)});
  return s;
}

std::string ReverseString(std::string s) {
  std::reverse(s.begin(), s.end());
  return s;
}

std::string SwapSymbols(std::string s) {
  auto l = std::uniform_int_distribution<std::int32_t>(
      0, static_cast<std::int32_t>(s.size()) - 1)(generator);
  auto r = std::uniform_int_distribution<std::int32_t>(
      0, static_cast<std::int32_t>(s.size()) - 1)(generator);
  std::swap(s[l], s[r]);
  return s;
}

std::string SwapFragments(std::string s) {
  auto m = std::uniform_int_distribution<std::int32_t>(
      0, static_cast<std::int32_t>(s.size()) - 1)(generator);
  std::ostringstream out;
  out << s.substr(0, m) << s.substr(m, s.size() - m);
  return out.str();
}

std::string SymbolRepetition(std::string s) {
  auto where = std::uniform_int_distribution<std::int32_t>(
      0, static_cast<std::int32_t>(s.size()) - 1)(generator);
  s.insert(where + 1, std::string{s[where]});
  return s;
}

std::string FragmentRepetition(std::string s) {
  auto from = std::uniform_int_distribution<std::int32_t>(
      0, static_cast<std::int32_t>(s.size()) - 1)(generator);
  auto count = std::uniform_int_distribution<std::int32_t>(
      1, static_cast<std::int32_t>(s.size() - from))(generator);
  return s.insert(from, s.substr(from, count));
}

std::string ErasingSymbol(std::string s) {
  auto where = std::uniform_int_distribution<std::int32_t>(
      0, static_cast<std::int32_t>(s.size()) - 1)(generator);
  return s.erase(where, 1);
}

std::string ErasingFragment(std::string s) {
  auto from = std::uniform_int_distribution<std::int32_t>(
      0, static_cast<std::int32_t>(s.size()) - 1)(generator);
  auto count = std::uniform_int_distribution<std::int32_t>(
      1, static_cast<std::int32_t>(s.size() - from))(generator);
  return s.erase(from, count);
}

std::string ApplyRandomMutation(std::string s) {
  const std::vector mutations
      = {ReplaceSymbol,    AddSymbol,          ReverseString, SwapSymbols,    SwapFragments,
         SymbolRepetition, FragmentRepetition, ErasingSymbol, ErasingFragment};
  auto i = std::uniform_int_distribution<std::int32_t>(0, mutations.size() - 1)(generator);
  return (mutations[i])(s);
}

std::vector<std::string> GetRandomStrings(const Automata &a,
                                                 const std::vector<std::size_t> &states) {
  const std::size_t strings_count = 10;

  std::vector<std::string> res;
  auto segments = GetRandomSegments(a, states);
  {
    std::ostringstream out;
    for (const auto &el : segments) {
      out << el;
    }
    res.push_back(out.str());
  }
  for (std::size_t i = 1; i < strings_count; i++) {
    std::ostringstream out;
    for (const auto &segment : segments) {
      if (segment.empty()) {
        continue;
      }
      if (std::uniform_int_distribution<std::int32_t>(0, 4)(generator) == 0) {
        out << ApplyRandomMutation(segment);
      } else {
        out << segment;
      }
    }
    res.push_back(out.str());
  }
  return res;
}

