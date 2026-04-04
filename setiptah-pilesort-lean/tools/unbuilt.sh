#!/usr/bin/env bash
find . -name "*.lean" -not -path "./.lake/*" \
  | sed 's|^\./||;s|/|.|g;s|\.lean$||' \
  | sort > .all.txt

lake clean && lake build 2>&1 | tee /dev/stderr | grep "Built" | awk '{print $NF}' | sort > .built.txt

comm -23 .all.txt .built.txt

rm .all.txt .built.txt
