#include <sys/time.h>

#include <cassert>
#include <iostream>
#include <random>
#include <sstream>
#include <string>

class RegexGenerator {
public:
  RegexGenerator(std::int32_t alphabet_power, std::int32_t star_height, std::int32_t max_letters);
  std::string GenerateString();

private:
  std::int32_t alphabet_power_;
  std::int32_t star_height_;
  std::int32_t max_letters_;

  std::int32_t current_star_height_;

  void Regex(std::ostringstream& stream, std::int32_t letters_left);
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

void RegexGenerator::Regex(std::ostringstream& stream, std::int32_t letters_left) {
  assert(letters_left > 0);
  if (letters_left == 1) {
    Symbol(stream);
    if (const auto rnd_value = Random({0.5, 0.5});
        current_star_height_ + 1 <= star_height_ && rnd_value == 0) {
      current_star_height_++;
      Unary(stream);
    }
    return;
  }
  const auto rnd_value = Random({0.35, 0.1, 0.45, 0.1});
  switch (rnd_value) {
    case 0:
      Regex(stream, letters_left - 1);
      Binary(stream);
      Regex(stream, 1);
      break;
    case 1:
      stream << '(';
      Regex(stream, letters_left);
      stream << ')';
      break;
    case 2:
      if (current_star_height_ + 1 <= star_height_) {
        current_star_height_++;
        Regex(stream, letters_left);
        Unary(stream);
      } else {
        Symbol(stream);
      }
      break;
    case 3:
      Symbol(stream);
      break;
  }
}

void RegexGenerator::Binary(std::ostringstream& stream) {
  const auto rnd_value = Random({0.5, 0.5});
  switch (rnd_value) {
    case 0:
      stream << '|';
      break;
    case 1:
      stream << '#';
      break;
  }
}

void RegexGenerator::Unary(std::ostringstream& stream) { stream << '*'; }

void RegexGenerator::Symbol(std::ostringstream& stream) {
  const double p = 1.0 / alphabet_power_;
  std::vector<double> probs;
  for (std::int32_t i = 0; i < alphabet_power_; i++) {
    probs.push_back(p);
  }
  stream << (std::vector{'a', 'b', 'c', 'd', 'e'})[Random(probs)];
}

std::string RegexGenerator::GenerateString() {
  current_star_height_ = 0;
  std::ostringstream res;
  Regex(res, max_letters_);
  return res.str();
}

RegexGenerator::RegexGenerator(std::int32_t alphabet_power, std::int32_t star_height,
                               std::int32_t max_letters)
    : alphabet_power_(alphabet_power), star_height_(star_height), max_letters_(max_letters) {}

std::int32_t main(int argc, char** argv) {
  if (argc != 4) {
    std::cerr << "regex_generator [alphabet_power] [star_height] [max_letters]" << std::endl;
    return 1;
  }
  RegexGenerator generator(std::stoi(argv[1]), std::stoi(argv[2]), std::stoi(argv[3]));
  std::cout << generator.GenerateString() << std::endl;
  return 0;
}
