cc_binary(
  name = "regex_generator",
  srcs = ["regex_generator.cpp"],
)

cc_test(
  name = "string_generator_test",
  size = "small",
  srcs = ["string_generator_test.cpp"],
  deps = ["@com_google_googletest//:gtest_main", "@com_github_ericniebler_range-v3//:range-v3", "@fmt",],
)
