#!/usr/bin/env bash
# Compile the consolidated runtime suite, then check expected compile failures.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if (($# == 0)); then
  set -- "$repo_root/test"
fi

declare -A selected_tests=()
failed=0
for test_path in "$@"; do
  if [[ ! -e "$test_path" ]]; then
    printf 'Test path does not exist: %s\n' "$test_path" >&2
    failed=1
    continue
  fi
  test_path="$(realpath -- "$test_path")"
  while IFS= read -r -d '' test_file; do
    if [[ "$test_file" == "$repo_root/test/compile_fail/"*.mojo ||
          "$test_file" == */test_*.mojo ]]; then
      selected_tests["$test_file"]=1
    fi
  done < <(find "$test_path" -type f -name '*.mojo' -not -path '*/.pixi/*' -print0)
done

if ((${#selected_tests[@]} == 0)); then
  printf 'No test files found in: %s\n' "$*" >&2
  exit 1
fi
mapfile -d '' -t test_files < <(printf '%s\0' "${!selected_tests[@]}" | sort -z)

mojo_cmd=(mojo)
if ! command -v mojo >/dev/null 2>&1; then
  mojo_cmd=(pixi run -e dev mojo)
fi

runner="$repo_root/test/run_tests.mojo"
runner_source="$(tr -d '[:space:]' < "$runner")"
flags=(-D MOREGEX_TEST_FILTERED=1)
runtime_count=0
missing=false
for test_file in "${test_files[@]}"; do
  if [[ "$test_file" == "$repo_root/test/compile_fail/"*.mojo ]]; then
    continue
  fi
  runtime_count=$((runtime_count + 1))
  relative="${test_file#"$repo_root/"}"
  module="${relative%.mojo}"
  module="${module//\//.}"
  alias="$(basename "$test_file" .mojo)"
  if [[ "$runner_source" != *"import${module}as${alias}"* ||
        "$runner_source" != *"module_selected[\"$alias\"]()"* ||
        "$runner_source" != *"tests.run(\"$relative\",$alias.run_tests[True]"* ]]; then
    printf 'Test missing from test/run_tests.mojo: %s\n' "$relative" >&2
    missing=true
  fi
  flags+=(-D "MOREGEX_TEST_$alias=1")
done

if "$missing"; then
  failed=1
elif ((runtime_count > 0)); then
  if ! "${mojo_cmd[@]}" run -Werror -I "$repo_root" "${flags[@]}" "$runner"; then
    failed=1
  fi
fi

compile_fail_output="$(mktemp)"
compile_fail_build="$(mktemp -d)"
trap 'rm -f "$compile_fail_output"; rm -rf "$compile_fail_build"' EXIT
compile_fail_count=0
for test_file in "${test_files[@]}"; do
  if [[ "$test_file" != "$repo_root/test/compile_fail/"*.mojo ]]; then
    continue
  fi
  compile_fail_count=$((compile_fail_count + 1))
  printf '\nChecking expected compile failure: %s\n' "${test_file#"$repo_root/"}"
  output="$compile_fail_build/$(basename "$test_file" .mojo)"
  if "${mojo_cmd[@]}" build -Werror -I "$repo_root" "$test_file" \
    -o "$output" >"$compile_fail_output" 2>&1; then
    printf 'FAIL: %s unexpectedly compiled\n' "$test_file" >&2
    failed=1
  elif ! grep -q "invalid regex" "$compile_fail_output"; then
    printf 'FAIL: %s produced the wrong diagnostic\n' "$test_file" >&2
    cat "$compile_fail_output" >&2
    failed=1
  fi
done

printf '\nChecked %d runtime modules and %d expected compile failures.\n' \
  "$runtime_count" "$compile_fail_count"
exit "$failed"
