bazel run //:lab1 <<< "ff -> f" | tee /dev/tty | z3 -smt2 -in
