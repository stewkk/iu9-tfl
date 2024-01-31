#!/usr/bin/env sh

set -e
set -o pipefail

bazel build //:regex_generator //:string_generator //:fuzz > /dev/null 2>&1

while true
do

    regex=$(bazel-bin/regex_generator 3 2 10)
    echo ""
    echo "regex is $regex"
    adderalbaby=$(python3 adderalbaby/manual.py <<EOF
abc
$regex
EOF
               )
    automata=$(echo "$adderalbaby" | head --lines -1 -)
    canonical_regex=$(echo "$adderalbaby" | tail --lines 1 -)
    for (( i = 1; i <= 5; i++ ))
    do
        strings=$(bazel-bin/string_generator <<EOF
$automata
EOF
               )
        bazel-bin/fuzz <<EOF
$automata
$canonical_regex
$strings
EOF
    done

done
