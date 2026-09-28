#!/usr/bin/env bash
# Reference projects are blueprint-only; validate only the primary Lean package.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
selected=false
if [[ ${1:-} == --all ]]; then
  selected=true
elif (( $# == 1 || $# == 2 )); then
  if (( $# == 2 )); then
    mapfile -t changed_files < <(git diff --name-only "$1" "$2" --)
  else
    mapfile -t changed_files < <(
      { git diff --name-only "$1" --; git ls-files --others --exclude-standard; } | sort -u
    )
  fi
  for path in "${changed_files[@]}"; do
    case "$path" in
      PoincareConjecture/references/*|PoincareConjecture/contracts/*) continue ;;
      PoincareConjecture/*.lean|PoincareConjecture/lakefile.toml|PoincareConjecture/lake-manifest.json|PoincareConjecture/lean-toolchain)
        selected=true ;;
    esac
  done
else
  echo 'Usage: scripts/validate-lean-changes.sh --all | <base-ref> [<head-ref>]' >&2
  exit 2
fi
if [[ $selected == false ]]; then
  echo 'No Lean package changes require validation.'
  exit 0
fi
echo 'Building PoincareConjecture (PoincareConjecture)'
(cd PoincareConjecture && lake exe cache get && make check)
python3 scripts/lean_stats.py PoincareConjecture \
  --exclude references --exclude contracts --exclude Comparator/Challenge.lean \
  --output .verification/statistics --check
