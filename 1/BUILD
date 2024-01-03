cc_test(
  name = "main_test",
  size = "small",
  srcs = ["main_test.cpp"],
  deps = ["@com_google_googletest//:gtest_main", "@com_github_ericniebler_range-v3//:range-v3", "@fmt", ":main-lib"],
)

cc_library(
  name = "main-lib",
  hdrs = ["serializer.hpp", "parser.hpp"],
  linkstatic = True,
  visibility = ["//visibility:public"],
)
