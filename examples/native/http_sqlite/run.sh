#!/usr/bin/env bash
# Build and exercise the native HTTP + sqlite3 demo end to end:
#   compile server.kp -> native ELF, start it, send 3 HTTP requests, and
#   verify each response reflects a sqlite write+read (the hit counter),
#   then confirm the database persisted the final count.
#
# Bounded (timeouts throughout) and self-cleaning.  Requires a C driver
# (set $KAPPA_CC, e.g. to "zig cc") and -lsqlite3 available.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
PORT="${PORT:-8088}"
DB="/tmp/kappa_http_demo.db"
EXE="/tmp/kserver"
LOG="/tmp/kserver.log"

cd "$ROOT"
rm -f "$DB" "$LOG" "$EXE"

echo "== building the demo via its build manifest -> native executable =="
timeout 240 cabal run -v0 kappa -- build --update --manifest examples/native/http_sqlite -o "$EXE"
file "$EXE" | sed 's/^/  /'

echo "== starting server =="
"$EXE" >"$LOG" 2>&1 &
SRV=$!
trap 'kill "$SRV" 2>/dev/null || true' EXIT
for _ in $(seq 1 50); do grep -q listening "$LOG" 2>/dev/null && break; sleep 0.1; done
cat "$LOG" | sed 's/^/  /'

echo "== sending 3 HTTP requests =="
ok=1
for n in 1 2 3; do
  if command -v curl >/dev/null 2>&1; then
    body="$(curl -s --max-time 5 "http://127.0.0.1:${PORT}/")"
  else
    exec 3<>"/dev/tcp/127.0.0.1/${PORT}"
    printf 'GET / HTTP/1.1\r\nHost: localhost\r\n\r\n' >&3
    body="$(cat <&3 | tail -1)"
    exec 3<&-
  fi
  echo "  request $n -> $body"
  [ "$body" = "hits=$n" ] || { echo "  MISMATCH: expected hits=$n"; ok=0; }
  sleep 0.2
done

wait "$SRV" 2>/dev/null || true
trap - EXIT
echo "== server exited =="
cat "$LOG" | sed 's/^/  /'

echo "== sqlite database state =="
if command -v sqlite3 >/dev/null 2>&1; then
  final="$(sqlite3 "$DB" 'SELECT hits FROM counter;')"
  echo "  counter.hits = $final"
  [ "$final" = "3" ] || { echo "  MISMATCH: expected 3"; ok=0; }
else
  echo "  (sqlite3 CLI unavailable; db file present: $([ -f "$DB" ] && echo yes || echo no))"
fi

if [ "$ok" = 1 ]; then echo "DEMO OK"; else echo "DEMO FAILED"; exit 1; fi
