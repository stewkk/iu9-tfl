#include <gtest/gtest.h>
#include <gmock/gmock.h>

using testing::Eq;

TEST(GeneratorTest, GeneratesString) {
  ASSERT_THAT(2*2, Eq(4));
}
