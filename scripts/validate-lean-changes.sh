#!/usr/bin/env bash
# Build changed Lean packages and every local package that depends on them.
set -euo pipefail

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

declare -a project_order=(
  Shared
  DoCarmo
  MorganTian
  LeeRiemannian
  Topping
  PoincareConjecture
  CaoZhu
  CheegerGromovTaylor
  ChowEtAl
  ChowKnopf
  Evans
  GilbargTrudinger
  HanLinLectureNotes
  Hatcher
  KleinerLott
  LeeSmooth
  Petersen
  Thurston
)

declare -A project_path=(
  [PoincareConjecture]="PoincareConjecture"
  [Shared]="shared"
  [CaoZhu]="formalized-sources/CaoZhu"
  [CheegerGromovTaylor]="formalized-sources/CheegerGromovTaylor"
  [ChowEtAl]="formalized-sources/ChowEtAl"
  [ChowKnopf]="formalized-sources/ChowKnopf"
  [DoCarmo]="formalized-sources/DoCarmo"
  [Evans]="formalized-sources/Evans"
  [GilbargTrudinger]="formalized-sources/GilbargTrudinger"
  [HanLinLectureNotes]="formalized-sources/HanLinLectureNotes"
  [Hatcher]="formalized-sources/Hatcher"
  [KleinerLott]="formalized-sources/KleinerLott"
  [LeeRiemannian]="formalized-sources/LeeRiemannian"
  [LeeSmooth]="formalized-sources/LeeSmooth"
  [MorganTian]="formalized-sources/MorganTian"
  [Petersen]="formalized-sources/Petersen"
  [Thurston]="formalized-sources/Thurston"
  [Topping]="formalized-sources/Topping"
)

declare -A sorry_baseline=(
  [PoincareConjecture]=0
  [Shared]=0
  [CaoZhu]=0
  [CheegerGromovTaylor]=0
  [ChowEtAl]=0
  [ChowKnopf]=0
  [DoCarmo]=0
  [Evans]=0
  [GilbargTrudinger]=0
  [HanLinLectureNotes]=0
  [Hatcher]=0
  [KleinerLott]=0
  [LeeRiemannian]=0
  [LeeSmooth]=280
  [MorganTian]=0
  [Petersen]=0
  [Thurston]=0
  [Topping]=0
)

declare -A selected=()

select_project() {
  local project=$1
  selected["$project"]=1

  case "$project" in
    Shared)
      select_project DoCarmo
      ;;
    DoCarmo)
      for dependent in CaoZhu CheegerGromovTaylor ChowEtAl ChowKnopf \
        GilbargTrudinger HanLinLectureNotes MorganTian
      do
        selected["$dependent"]=1
      done
      select_project MorganTian
      ;;
    MorganTian)
      selected[LeeRiemannian]=1
      selected[Topping]=1
      ;;
  esac
}

select_all() {
  local project
  for project in "${project_order[@]}"; do
    selected["$project"]=1
  done
}

usage() {
  cat <<'EOF'
Usage:
  scripts/validate-lean-changes.sh --all
  scripts/validate-lean-changes.sh <base-ref> [<head-ref>]

With one ref, validates tracked and untracked working-tree changes since that
ref. With two refs, validates the committed changes between them.
EOF
}

if [[ ${1:-} == "--all" ]]; then
  select_all
elif (( $# == 1 || $# == 2 )); then
  base_ref=$1
  if (( $# == 2 )); then
    mapfile -t changed_files < <(
      git diff --name-only --diff-filter=ACDMRTUXB "$base_ref" "$2" --
    )
  else
    mapfile -t changed_files < <(
      {
        git diff --name-only --diff-filter=ACDMRTUXB "$base_ref" --
        git ls-files --others --exclude-standard
      } | sort -u
    )
  fi

  for path in "${changed_files[@]}"; do
    case "$path" in
      PoincareConjecture/*)
        select_project PoincareConjecture
        ;;
      shared/*)
        select_project Shared
        ;;
      formalized-sources/*/*)
        project=${path#formalized-sources/}
        project=${project%%/*}
        if [[ -n ${project_path[$project]:-} ]]; then
          select_project "$project"
        elif [[ "$path" == *.lean || "$path" == */lakefile.* ||
            "$path" == */lake-manifest.json || "$path" == */lean-toolchain ]]; then
          select_all
        fi
        ;;
      *.lean|lakefile.*|lake-manifest.json|lean-toolchain)
        select_all
        ;;
    esac
  done
else
  usage >&2
  exit 2
fi

if (( ${#selected[@]} == 0 )); then
  echo "No Lean package changes require validation."
  exit 0
fi

mapfile -t scratch_files < <(
  find PoincareConjecture shared formalized-sources -type f \
    -iname '*scratch*.lean' -not -path '*/.lake/*' -print | sort
)
if (( ${#scratch_files[@]} != 0 )); then
  printf 'error: scratch Lean modules must not be published:\n' >&2
  printf '  %s\n' "${scratch_files[@]}" >&2
  exit 1
fi

count_matches() {
  local root=$1
  local pattern=$2
  local matches
  matches=$(rg -n -g '*.lean' -g '!.lake/**' "$pattern" "$root" 2>/dev/null || true)
  if [[ -z "$matches" ]]; then
    echo 0
  else
    printf '%s\n' "$matches" | wc -l | tr -d ' '
  fi
}

for project in "${project_order[@]}"; do
  [[ -n ${selected[$project]:-} ]] || continue
  root=${project_path[$project]}
  baseline=${sorry_baseline[$project]}

  printf '\n==> Building %s (%s)\n' "$project" "$root"
  (
    cd "$root"
    lake exe cache get
    lake build
  )

  sorry_count=$(count_matches "$root" \
    '^[[:space:]]*sorry[[:space:]]*$|by sorry|:= sorry')
  if (( sorry_count > baseline )); then
    printf 'error: %s sorry count increased (%s > %s)\n' \
      "$root" "$sorry_count" "$baseline" >&2
    exit 1
  fi

  axiom_count=$(count_matches "$root" \
    "^axiom[[:space:]]+[a-zA-Z_][a-zA-Z0-9_']*[[:space:]]*$")
  if (( axiom_count != 0 )); then
    printf 'error: %s contains %s standalone axiom declaration(s)\n' \
      "$root" "$axiom_count" >&2
    exit 1
  fi

  printf '%s: build passed; sorry=%s/%s; axiom=0\n' \
    "$project" "$sorry_count" "$baseline"
done
