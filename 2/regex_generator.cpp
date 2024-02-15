#include <sys/time.h>

#include <cassert>
#include <iostream>
#include <random>
#include <sstream>
#include <string>

#define _GLIBCXX_REGEX_STATE_LIMIT 500000

class RegexGenerator {
public:
  RegexGenerator(std::int32_t alphabet_power, std::int32_t star_height, std::int32_t max_letters);
  std::string GenerateString();

private:
  std::int32_t alphabet_power_;
  std::int32_t star_height_;
  std::int32_t max_letters_;

  void Regex(std::ostringstream& stream, std::int32_t letters_left, std::int32_t star_height);
  void Binary(std::ostringstream& stream);
  void Unary(std::ostringstream& stream);
  void Symbol(std::ostringstream& stream);
};

std::int32_t Random(std::vector<double> probs) {
  std::random_device rd;
  static std::mt19937 generator(rd());
  std::uniform_int_distribution<std::int32_t> distribution(0, 10000);
  const double rnd = distribution(generator) / 10000.0;
  double lhs = 0;
  for (std::int32_t v = 0; v < probs.size(); ++v) {
    const auto& prob = probs[v];
    if (rnd >= lhs && rnd <= lhs + prob) {
      return v;
    }
    lhs += prob;
  }
  throw std::logic_error{"Random error"};
}

void RegexGenerator::Regex(std::ostringstream& stream, std::int32_t letters_left, std::int32_t star_height) {
  assert(letters_left > 0);
  if (letters_left == 1) {
    Symbol(stream);
    if (const auto rnd_value = Random({0.2, 0.8});
        star_height + 1 <= star_height_ && rnd_value == 0) {
      Unary(stream);
    }
    return;
  }
  auto rnd_value = Random({0.4, 0.1, 0.05, 0.4, 0.05});
  if (letters_left > 2) {
    rnd_value = Random({0.75, 0.1, 0.05, 0.05, 0.05});
  }
  switch (rnd_value) {
    case 0:
      Regex(stream, letters_left - 1, star_height);
      Binary(stream);
      Regex(stream, 1, star_height);
      break;
    case 1:
      stream << '(';
      Regex(stream, letters_left, star_height);
      stream << ')';
      break;
    case 2:
      if (star_height + 1 <= star_height_) {
        stream << '(';
        Regex(stream, letters_left, star_height+1);
        stream << ')';
        Unary(stream);
      } else {
        Symbol(stream);
      }
      break;
    case 3:
      Symbol(stream);
      break;
    case 4:
      stream << "ε";
      break;
  }
}

void RegexGenerator::Binary(std::ostringstream& stream) {
  const auto rnd_value = Random({0.4, 0.2, 0.4});
  switch (rnd_value) {
    case 0:
      stream << '|';
      break;
    case 1:
      stream << '#';
      break;
    case 2:
      break;
  }
}

void RegexGenerator::Unary(std::ostringstream& stream) {
  stream << '*'; }

void RegexGenerator::Symbol(std::ostringstream& stream) {
  const double p = 1.0 / alphabet_power_;
  std::vector<double> probs;
  for (std::int32_t i = 0; i < alphabet_power_; i++) {
    probs.push_back(p);
  }
  stream << (std::vector{'a', 'b', 'c', 'd', 'e'})[Random(probs)];
}

std::string RegexGenerator::GenerateString() {
  std::ostringstream res;
  Regex(res, max_letters_, 0);
  return res.str();
}

RegexGenerator::RegexGenerator(std::int32_t alphabet_power, std::int32_t star_height,
                               std::int32_t max_letters)
    : alphabet_power_(alphabet_power), star_height_(star_height), max_letters_(max_letters) {}

std::int32_t main(int argc, char** argv) {
  if (argc != 4) {
    return 1;
  }
  RegexGenerator generator(std::stoi(argv[1]), std::stoi(argv[2]), std::stoi(argv[3]));
  std::cout << generator.GenerateString() << std::endl;
  return 0;
}
