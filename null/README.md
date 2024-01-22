Запуск:

``` sh
bash run.sh
```

``` sh
bazel run //:lab1 <<< "(a, aa)" | tee /dev/tty | z3 -smt2 -in
```

Сборка:

``` sh
bazel build //:lab1 # -> bazel-bin/lab1
```

