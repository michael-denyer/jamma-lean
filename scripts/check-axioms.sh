#!/usr/bin/env bash
# Fail unless every `#print axioms` line in Audit.lean reports only Lean's
# standard axioms. A `sorry` shows up as `sorryAx`; a new `axiom` shows up by
# name. Also fail if any `#print axioms` produced no report (a typo'd name
# errors instead of printing).
set -euo pipefail

out=$(lake env lean Audit.lean 2>&1) || { echo "$out"; exit 1; }

expected=$(grep -c '^#print axioms' Audit.lean)
reported=$(grep -c 'depends on axioms\|does not depend on any axioms' <<<"$out" || true)
if [ "$reported" -ne "$expected" ]; then
  echo "$out"
  echo "::error::Audit.lean has $expected '#print axioms' lines but $reported reports"
  exit 1
fi

bad=$(grep 'depends on axioms' <<<"$out" \
  | grep -vE 'depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$' || true)
if [ -n "$bad" ]; then
  echo "$bad"
  echo "::error::theorems depend on non-standard axioms (sorryAx means an unfinished proof)"
  exit 1
fi

echo "$reported theorems audited; all use only propext, Classical.choice, Quot.sound"
