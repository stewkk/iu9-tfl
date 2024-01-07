cc_binary(
  name = "regex_generator",
  srcs = ["regex_generator.cpp"],
)

cc_binary(
  name = "string_generator",
  srcs = ["string_generator.cpp"],
  deps = [":string_generator_lib"],
)

cc_library(
  name = "string_generator_lib",
  hdrs = ["string_generator.hpp",],
  srcs = ["string_generator.cpp"],
)

cc_test(
  name = "string_generator_test",
  size = "small",
  srcs = ["string_generator_test.cpp"],
  deps = ["@com_google_googletest//:gtest_main", "@com_github_ericniebler_range-v3//:range-v3", "@fmt", ":string_generator_lib"],
)
