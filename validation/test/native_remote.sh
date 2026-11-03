#!/usr/bin/env bash
# Run from the user's network-enabled terminal. No sudo or KVM is used.
set -euo pipefail
VERIFY_ROOT=$(cd "$(dirname "$0")/.." && pwd)
NATIVE_BUNDLE=${1:?usage: bash test/native_remote.sh bundle.tar.gz user@host}
NATIVE_HOST=${2:?usage: bash test/native_remote.sh bundle.tar.gz user@host}
NATIVE_NAME=$(basename "$NATIVE_BUNDLE" .tar.gz)
case "$NATIVE_NAME" in
  ''|*[!a-zA-Z0-9_-]*) echo 'Bundle name must contain only letters, digits, underscores and hyphens.' >&2; exit 2 ;;
esac
NATIVE_RESULT="$VERIFY_ROOT/test/out/$NATIVE_NAME-returned"
if [ ! -f "$NATIVE_BUNDLE" ]; then echo "Missing bundle: $NATIVE_BUNDLE" >&2; exit 2; fi
if [ -e "$NATIVE_RESULT" ]; then echo "Result directory already exists: $NATIVE_RESULT" >&2; exit 2; fi
NATIVE_REMOTE=$(ssh "$NATIVE_HOST" 'mktemp -d /tmp/verify-native.XXXXXXXX')
if [[ ! "$NATIVE_REMOTE" =~ ^/tmp/verify-native\.[a-zA-Z0-9]+$ ]]; then
  echo 'SSH did not return a valid temporary directory.' >&2; exit 1
fi
scp "$NATIVE_BUNDLE" "$NATIVE_HOST:$NATIVE_REMOTE/input.tar.gz"
NATIVE_STATUS=0
ssh "$NATIVE_HOST" "tar -xzf '$NATIVE_REMOTE/input.tar.gz' -C '$NATIVE_REMOTE' && python3 '$NATIVE_REMOTE/$NATIVE_NAME/native.py' run '$NATIVE_REMOTE/$NATIVE_NAME'" || NATIVE_STATUS=$?
# Retrieve diagnostics even when compilation/ptrace/execution fails.
scp -r "$NATIVE_HOST:$NATIVE_REMOTE/$NATIVE_NAME" "$NATIVE_RESULT"
echo "Returned results: $NATIVE_RESULT"
echo "Remote artifacts retained at $NATIVE_HOST:$NATIVE_REMOTE"
exit "$NATIVE_STATUS"
