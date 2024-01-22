#!/usr/bin/env sh

set -e

cat test | bazel run --ui_event_filters=-info,-stdout,-stderr --noshow_progress --logging=0 //:lab1 | z3 -smt2 -in
