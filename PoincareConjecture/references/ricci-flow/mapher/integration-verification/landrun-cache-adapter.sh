#!/bin/sh
# Forward build-cache settings through Landrun's clean environment.
export LAKE_CACHE_DIR=/home/axel/.horizon/development-tmp/poincare-draft-pr/PoincareConjecture/.lake/comparator-artifact-cache
export LAKE_ARTIFACT_CACHE=true
export LAKE_RESTORE_ARTIFACTS=true
exec /home/axel/.horizon/development-tmp/poincare-draft-pr/PoincareConjecture/.lake/comparator-tools/bin/landrun --env LAKE_CACHE_DIR --env LAKE_ARTIFACT_CACHE --env LAKE_RESTORE_ARTIFACTS "$@"
