#!/usr/bin/env bash
# Exercise the shipped verified-only CLI, including failure and worker teardown.
# Uses committed inputs and their existing upstream expected verdicts; no export
# step or network is required. Timeouts are failures, never accept/decline.
set -euo pipefail
cd "$(dirname "$0")/../.."
ulimit -c 0

BIN=${C1_BIN:-.lake/build/bin/pskernel-c1}
LIMIT=${C1_TEST_TIMEOUT:-120}
LOGDIR=_tmp/c1/verdicts
mkdir -p "$LOGDIR"
test -x "$BIN" || { echo "missing executable: $BIN" >&2; exit 1; }

fail=0
count=0

check() { # expected-exit label args...
  local expected=$1 label=$2 got=0
  shift 2
  count=$((count + 1))
  timeout --signal=TERM --kill-after=5s "$LIMIT" "$BIN" "$@" \
    >"$LOGDIR/$label.stdout" 2>"$LOGDIR/$label.stderr" || got=$?
  if [ "$got" != "$expected" ]; then
    echo "FAIL $label: expected $expected, got $got"
    cat "$LOGDIR/$label.stdout" "$LOGDIR/$label.stderr"
    fail=1
  elif [ "$got" != 0 ] && grep -q '^pskernel-c1: accepted ' "$LOGDIR/$label.stdout"; then
    echo "FAIL $label: unsuccessful run printed an acceptance"
    fail=1
  else
    echo "PASS $label: exit $got"
  fi
}

fixture() { # filename jobs
  local name=$1 jobs=$2 expected
  expected=$(awk -v name="$name" '$1 ~ /^[0123]$/ && $2 == name { print $1 }' tests/e2e-expected.txt)
  if [[ ! "$expected" =~ ^[0123]$ ]]; then
    echo "fixture needs one pinned upstream expectation: $name" >&2
    exit 1
  fi
  check "$expected" "${name%.ndjson}-j$jobs" "--jobs=$jobs" "tests/e2e/$name"
  if [ "$expected" = 0 ] && ! grep -q '^pskernel-c1: accepted ' "$LOGDIR/${name%.ndjson}-j$jobs.stdout"; then
    echo "FAIL ${name%.ndjson}-j$jobs: accepted input has no acceptance line"
    fail=1
  fi
}

# The accepted cases exercise definitions, indexed inductives, arithmetic pins,
# and the parallel install. The negative cases distinguish invalid input,
# deliberately unsupported assumptions/features, and parser failure.
for jobs in 1 2; do
  for name in opaque_decl indexed_vec nat_ops_edge pinstall_ok \
    tolerated_axiom_unused let_bad_type nat_add_wrong trust_native_use \
    custom_axiom_declined tolerated_axiom_use ind_unsafe nat_ops_nonstandard \
    malformed_midstream pinstall_reject_mid pinstall_dup; do
    fixture "$name.ndjson" "$jobs"
  done
  check 1 "first-failure-j$jobs" "--jobs=$jobs" tests/annot/annot_split_bad2.ndjson
  if ! grep -q 'badFirst' "$LOGDIR/first-failure-j$jobs.stderr"; then
    echo "FAIL first-failure-j$jobs: did not identify the first failing record"
    fail=1
  fi
  check 3 "directory-j$jobs" "--jobs=$jobs" tests/e2e
  check 3 "missing-file-j$jobs" "--jobs=$jobs" "$LOGDIR/absent.ndjson"
done

GOOD=tests/e2e/opaque_decl.ndjson
check 0 explicit-verified --verified --jobs=1 "$GOOD"
check 0 default-worker-count "$GOOD"
check 0 help --help
check 0 version --version
check 3 missing-input
check 3 two-inputs "$GOOD" "$GOOD"
check 3 unknown-option --not-a-c1-option "$GOOD"
check 3 trusted-mode --trusted "$GOOD"
check 3 zero-workers --jobs=0 "$GOOD"
check 3 malformed-workers --jobs=x "$GOOD"
check 3 missing-workers --jobs "$GOOD"

echo "C1 CLI: $count cases; failures=$fail (logs: $LOGDIR)"
exit "$fail"
