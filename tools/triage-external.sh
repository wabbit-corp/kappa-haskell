#!/usr/bin/env bash
# Triage database for the external fixture corpus.
#
# Usage: tools/triage-external.sh [RAW_LOG] [CSV_OUT] [SUMMARY_OUT]
#
# Consumes the per-fixture raw log written by tools/run-external-fixtures.sh
# (one PASS/FAIL/UNSUPPORTED/HARNESS-ERROR line per fixture directory) and
# produces:
#   - CSV_OUT (default /tmp/triage.csv): one line per fixture with
#     fixture-dir, category-prefix, outcome, first-error-code,
#     first-error-message
#   - SUMMARY_OUT (default /tmp/triage-summary.txt): per category-prefix,
#     counts by outcome and the most frequent first-error-codes.
#
# category-prefix is the first dot segment of the fixture directory name
# (e.g. queries.qtt.appendix_t.x -> queries), or the first underscore
# token for undotted names (e.g. app_reject_too_many_arguments -> app).
# first-error-code is the first diagnostic code mentioned in the result
# detail (assertion failures quote the codes they saw/expected).
set -u

RAW_LOG="${1:-/tmp/external-raw.log}"
CSV="${2:-/tmp/triage.csv}"
SUMMARY="${3:-/tmp/triage-summary.txt}"

if [ ! -s "$RAW_LOG" ]; then
  echo "raw log $RAW_LOG not found or empty; run tools/run-external-fixtures.sh first" >&2
  exit 2
fi

awk '
function csvq(s) { gsub(/"/, "\"\"", s); return "\"" s "\"" }
BEGIN { print "fixture-dir,category-prefix,outcome,first-error-code,first-error-message" }
/^(PASS|FAIL|UNSUPPORTED|HARNESS-ERROR) \// {
  outcome = $1
  path = $2
  # everything after "OUTCOME path " is the parenthesized detail
  detail = $0
  sub(/^[A-Z-]+ [^ ]+ ?/, "", detail)
  sub(/^\(/, "", detail); sub(/\)$/, "", detail)
  # fixture-dir: basename of the path
  n = split(path, segs, "/")
  name = segs[n]
  # category-prefix: first dot segment, else first underscore token
  cat = name
  if (index(name, ".") > 0) { split(name, ds, "."); cat = ds[1] }
  else { split(name, us, "_"); cat = us[1] }
  # first diagnostic code mentioned in the detail
  code = ""
  if (match(detail, /[EW]_[A-Z0-9_]+/)) code = substr(detail, RSTART, RLENGTH)
  msg = detail
  if (length(msg) > 240) msg = substr(msg, 1, 237) "..."
  o = outcome
  if (o == "PASS") o = "pass"
  else if (o == "FAIL") o = "fail"
  else if (o == "UNSUPPORTED") o = "unsupported"
  else o = "harnessError"
  print name "," cat "," o "," code "," csvq(msg)
}
' "$RAW_LOG" >"$CSV"

awk -F',' '
NR == 1 { next }
{
  # re-join quoted message is unnecessary: we only need fields 2..4
  cat = $2; outcome = $3; code = $4
  cats[cat] = 1
  total[cat]++
  count[cat SUBSEP outcome]++
  if (code != "" && outcome != "pass") {
    codes[cat SUBSEP code]++
    codekeys[cat] = codekeys[cat] code "\n"
  }
}
END {
  printf "%-24s %6s %6s %6s %6s %6s  %s\n", "category", "total", "pass", "fail", "unsup", "herr", "top-error-codes"
  ncat = 0
  for (c in cats) order[++ncat] = c
  # insertion sort by total desc, then name
  for (i = 2; i <= ncat; i++) {
    v = order[i]; j = i - 1
    while (j >= 1 && (total[order[j]] < total[v] || (total[order[j]] == total[v] && order[j] > v))) {
      order[j + 1] = order[j]; j--
    }
    order[j + 1] = v
  }
  gp = gf = gu = gh = gt = 0
  for (i = 1; i <= ncat; i++) {
    c = order[i]
    p = count[c SUBSEP "pass"] + 0
    f = count[c SUBSEP "fail"] + 0
    u = count[c SUBSEP "unsupported"] + 0
    h = count[c SUBSEP "harnessError"] + 0
    gp += p; gf += f; gu += u; gh += h; gt += total[c]
    # top three codes for this category
    delete top; delete topn
    for (k in codes) {
      split(k, kk, SUBSEP)
      if (kk[1] != c) continue
      for (t = 1; t <= 3; t++) {
        if (codes[k] > topn[t] || (codes[k] == topn[t] && kk[2] < top[t])) {
          for (s = 3; s > t; s--) { top[s] = top[s-1]; topn[s] = topn[s-1] }
          top[t] = kk[2]; topn[t] = codes[k]
          break
        }
      }
    }
    tops = ""
    for (t = 1; t <= 3; t++)
      if (topn[t] > 0) tops = tops (tops == "" ? "" : ", ") top[t] ":" topn[t]
    printf "%-24s %6d %6d %6d %6d %6d  %s\n", c, total[c], p, f, u, h, tops
  }
  printf "%-24s %6d %6d %6d %6d %6d\n", "TOTAL", gt, gp, gf, gu, gh
}
' "$CSV" >"$SUMMARY"

echo "triage csv: $CSV ($(wc -l <"$CSV") lines)" >&2
echo "summary:    $SUMMARY" >&2
