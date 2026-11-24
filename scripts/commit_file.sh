#!/bin/sh
# Commit exactly one path with one message, then push. It retries when another process holds the git index lock.
# Usage: scripts/commit_file.sh <path> "<message>"
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
done=0
for i in 1 2 3 4 5 6 7 8 9 10; do
  if git add -- "$1" 2>/dev/null && git commit -q -m "$2" -- "$1" 2>/dev/null; then
    done=1; break
  fi
  if git diff --quiet HEAD -- "$1" 2>/dev/null && git ls-files --error-unmatch "$1" >/dev/null 2>&1; then
    exit 0
  fi
  sleep 2
done
if [ "$done" != 1 ]; then echo "commit failed for $1" >&2; exit 1; fi
for i in 1 2 3; do
  git push -q origin main 2>/dev/null && exit 0
  sleep 3
done
echo "push failed for now, the next commit will push it" >&2
exit 0
