#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
root=$(pwd -P)
python3 comparator/check.py

if [[ $# -gt 1 || ( $# -eq 1 && $1 != --preflight ) ]]; then
  echo 'Usage: bash comparator/run.sh [--preflight]' >&2
  exit 2
fi
if [[ $(id -u) -eq 0 ]]; then
  echo 'Comparator must run as an unprivileged user.' >&2
  exit 1
fi

export COMPARATOR_LANDRUN=${COMPARATOR_LANDRUN:-$root/.lake/comparator-tools/bin/landrun}
export COMPARATOR_NANODA=${COMPARATOR_NANODA:-$root/.lake/comparator-tools/bin/nanoda_bin}
export COMPARATOR_LEAN4EXPORT=${COMPARATOR_LEAN4EXPORT:-$root/.lake/packages/lean4export/.lake/build/bin/lean4export}
comparator=$root/.lake/packages/Comparator/.lake/build/bin/comparator
for binary in "$COMPARATOR_LANDRUN" "$COMPARATOR_NANODA" "$COMPARATOR_LEAN4EXPORT" "$comparator"; do
  if [[ $binary != /* || ! -x $binary ]]; then
    echo "Missing executable at absolute path: $binary (see comparator/README.md)" >&2
    exit 1
  fi
done

unit=(systemd-run --user --wait --pipe --collect
  --property=RestrictAddressFamilies=~AF_UNIX --working-directory="$root"
  -E PATH -E HOME -E COMPARATOR_LANDRUN -E COMPARATOR_NANODA -E COMPARATOR_LEAN4EXPORT)
if [[ ${1:-} == --preflight ]]; then
  "${unit[@]}" "$COMPARATOR_LANDRUN" --best-effort --ro / --rw /dev -ldd -add-exec -- /usr/bin/true
  echo 'Sandbox preflight passed; no Solution or endpoint proof was checked.'
else
  exec "${unit[@]}" lake env "$comparator" comparator/comparator.json
fi
