#!/usr/bin/env bash
# Compare the same verified checker with statistics disabled and enabled.
# No build or export step: CI supplies the binaries and committed fixtures.
# Timing values are deliberately not test assertions.
set -euo pipefail
cd "$(dirname "$0")/.."
ulimit -c 0

BIN=${C1_BIN:-.lake/build/bin/pskernel-c1}
BASELINE=${C1_BASELINE_BIN:-.lake/build/bin/con-leche}
LIMIT=${C1_TEST_TIMEOUT:-120}
LOGDIR=_tmp/c1/stats
mkdir -p "$LOGDIR"
for executable in "$BIN" "$BASELINE"; do
  test -x "$executable" || { echo "missing executable: $executable" >&2; exit 1; }
done

# ParInstall explicitly snapshots ONLY finished workers, without waiting.
# On rejection every worker can still be running and the commit thread may
# have installed no records itself. Then the correct report has zero counted
# records and an empty top list, with the omitted workers disclosed. Requiring
# a numeric top entry in that case made this test depend on thread scheduling.
install_stats_present() {
  local log=$1
  grep -q '^con-leche: stats: install.* wall, .* busy ' "$log" || return 1
  if grep -q '^con-leche: stats: install.* 0 records, busy ' "$log"; then
    grep -q '^con-leche: stats: install pool ([1-9][0-9]* still running, not counted):' "$log" &&
      grep -q '^con-leche: stats: slowest installs: $' "$log"
  else
    grep -q '^con-leche: stats: slowest installs: [0-9]' "$log"
  fi
}

# Deterministic tests of both legitimate report shapes and missing data.
contract_log="$LOGDIR/contract.stderr"
printf '%s\n' \
  'con-leche: stats: install pool (2 still running, not counted): 0.001s wall, 2 workers + the commit thread, 0 records, busy 0.000s (-)' \
  'con-leche: stats: slowest installs: ' > "$contract_log"
install_stats_present "$contract_log" || { echo 'FAIL zero-sample contract'; exit 1; }
sed 's/0 records/1 records/' "$contract_log" > "$LOGDIR/nonempty-missing.stderr"
if install_stats_present "$LOGDIR/nonempty-missing.stderr"; then
  echo 'FAIL nonempty report must retain its top sample'; exit 1
fi
sed 's/ (2 still running, not counted)//' "$contract_log" > "$LOGDIR/undisclosed.stderr"
if install_stats_present "$LOGDIR/undisclosed.stderr"; then
  echo 'FAIL empty report must disclose omitted workers'; exit 1
fi
printf '%s\n' \
  'con-leche: stats: install: 0.001s wall, 1 worker, 1 records, busy 0.001s (100.0%)' \
  'con-leche: stats: slowest installs: 0.001s example' > "$contract_log"
install_stats_present "$contract_log" || { echo 'FAIL nonempty-sample contract'; exit 1; }

fail=0
count=0

pair() { # expected-exit reached-phase label fixture jobs
  local expected=$1 phase=$2 label=$3 fixture=$4 jobs=$5
  local tag="$label-j$jobs" off=0 on=0
  count=$((count + 1))
  timeout --signal=TERM --kill-after=5s "$LIMIT" "$BIN" "--jobs=$jobs" "$fixture" \
    >"$LOGDIR/$tag-off.stdout" 2>"$LOGDIR/$tag-off.stderr" || off=$?
  timeout --signal=TERM --kill-after=5s "$LIMIT" "$BIN" "--jobs=$jobs" --stats "$fixture" \
    >"$LOGDIR/$tag-on.stdout" 2>"$LOGDIR/$tag-on.stderr" || on=$?
  if [ "$off" != "$expected" ] || [ "$on" != "$expected" ]; then
    echo "FAIL $tag: expected $expected, default=$off, --stats=$on"
    cat "$LOGDIR/$tag-off.stderr" "$LOGDIR/$tag-on.stderr"
    fail=1
  fi
  if grep -q '^con-leche: stats: ' "$LOGDIR/$tag-off.stderr"; then
    echo "FAIL $tag: default C1 run printed statistics"
    fail=1
  fi
  if ! install_stats_present "$LOGDIR/$tag-on.stderr"; then
    echo "FAIL $tag: --stats omitted or contradicted install statistics"
    cat "$LOGDIR/$tag-on.stderr"
    fail=1
  fi
  if [ "$phase" = both ]; then
    if ! grep -q '^con-leche: stats: phases: parse .*, install .*, check [0-9]' "$LOGDIR/$tag-on.stderr" ||
       ! grep -q '^con-leche: stats: check.* wall, .* busy ' "$LOGDIR/$tag-on.stderr" ||
       ! grep -q '^con-leche: stats: slowest checks: [0-9]' "$LOGDIR/$tag-on.stderr"; then
      echo "FAIL $tag: --stats omitted check statistics"
      fail=1
    fi
  elif ! grep -q '^con-leche: stats: phases: .*check not reached$' "$LOGDIR/$tag-on.stderr"; then
    echo "FAIL $tag: install failure did not report check not reached"
    fail=1
  fi
  sed '/^con-leche: stats: /d' "$LOGDIR/$tag-on.stderr" >"$LOGDIR/$tag-on.verdict"
  if ! diff -u "$LOGDIR/$tag-off.stdout" "$LOGDIR/$tag-on.stdout" ||
     ! diff -u "$LOGDIR/$tag-off.stderr" "$LOGDIR/$tag-on.verdict"; then
    echo "FAIL $tag: statistics changed the verdict output"
    fail=1
  fi
}

for jobs in 1 2; do
  pair 0 both accept tests/annot/annot_split_good.ndjson "$jobs"
  pair 1 both check-reject tests/annot/annot_split_bad.ndjson "$jobs"
  pair 1 install install-reject tests/e2e/corner_andpin_def_bad.ndjson "$jobs"
  pair 2 install decline tests/e2e/custom_axiom_declined.ndjson "$jobs"
done

# The existing con-leche entry point does not opt out: its default remains on.
baseline_exit=0
timeout --signal=TERM --kill-after=5s "$LIMIT" "$BASELINE" --verified --jobs=1 \
  tests/annot/annot_split_good.ndjson >"$LOGDIR/upstream.stdout" 2>"$LOGDIR/upstream.stderr" || baseline_exit=$?
if [ "$baseline_exit" != 0 ] ||
   ! grep -q '^con-leche: stats: phases: ' "$LOGDIR/upstream.stderr"; then
  echo "FAIL upstream default: expected acceptance and statistics, got exit $baseline_exit"
  fail=1
fi

echo "C1 statistics: $count paired cases, four report-contract cases and upstream default; failures=$fail (logs: $LOGDIR)"
exit "$fail"
