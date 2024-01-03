cc_test(
  name = "main_test",
  size = "small",
  srcs = ["main_test.cpp"],
  deps = [":lab1-lib"],
)

cc_library(
  name = "lab1-lib",
  hdrs = ["serializer.hpp", "parser.hpp"],
  deps = ["@com_google_googletest//:gtest_main", "@com_github_ericniebler_range-v3//:range-v3", "@fmt",],
)

cc_binary(
    name = "lab1",
    srcs = ["main.cpp"],
    deps = [
        ":lab1-lib",
    ],
)
