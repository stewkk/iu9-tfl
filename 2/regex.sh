#!/usr/bin/env sh

bazel build //:regex_generator //:string_generator //:fuzz > /dev/null 2>&1

while true
do
    regex=$(bazel-bin/regex_generator 3 2 3)
    echo "regex is $regex"
done
