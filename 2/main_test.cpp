#include <gmock/gmock.h>

class RegexGenerator {
  public:
    RegexGenerator() {}

    std::string GetString() {return "";}
};

TEST(GeneratorTest, GeneratesString) {
  RegexGenerator g;

  auto regex = g.GetString();

  ASSERT_THAT(regex, testing::Eq(""));
}

