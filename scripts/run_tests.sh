#!/usr/bin/env bash
# Run each Mojo test file independently and report all failures.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
test_dir="${1:-$repo_root/test}"
failure_file="$(mktemp)"
compile_fail_output="$(mktemp)"
compile_fail_build="$(mktemp -d)"
trap 'rm -f "$failure_file" "$compile_fail_output"; rm -rf "$compile_fail_build"' EXIT

test_count=0
failure_count=0

mojo_cmd=(mojo)
if ! command -v mojo >/dev/null 2>&1; then
  mojo_cmd=(pixi run mojo)
fi

while IFS= read -r test_file; do
  test_count=$((test_count + 1))
  printf '\n[%d] %s\n' "$test_count" "${test_file#"$repo_root/"}"
  if ! "${mojo_cmd[@]}" run -Werror -I "$repo_root" "$test_file"; then
    failure_count=$((failure_count + 1))
    printf '%s\n' "$test_file" >>"$failure_file"
  fi
done < <(
  find "$test_dir" -name 'test_*.mojo' -type f -not -path '*/.pixi/*' | sort
)

if [[ "$test_dir" == "$repo_root/test" ]]; then
  while IFS= read -r test_file; do
    test_count=$((test_count + 1))
    printf '\n[%d] %s (expected compile failure)\n' \
      "$test_count" "${test_file#"$repo_root/"}"
    output="$compile_fail_build/$(basename "$test_file" .mojo)"
    if "${mojo_cmd[@]}" build -Werror -I "$repo_root" "$test_file" \
      -o "$output" >"$compile_fail_output" 2>&1; then
      failure_count=$((failure_count + 1))
      printf '%s (unexpectedly compiled)\n' "$test_file" >>"$failure_file"
    elif ! grep -q "invalid regex" "$compile_fail_output"; then
      failure_count=$((failure_count + 1))
      printf '%s (wrong diagnostic)\n' "$test_file" >>"$failure_file"
      cat "$compile_fail_output" >&2
    fi
  done < <(
    find "$repo_root/test/compile_fail" -name '*.mojo' -type f | sort
  )
fi

if ((test_count == 0)); then
  printf 'No test files found in: %s\n' "$test_dir" >&2
  exit 1
fi

if ((failure_count > 0)); then
  printf '\n%d/%d test files failed:\n' "$failure_count" "$test_count" >&2
  sed "s#^$repo_root/##" "$failure_file" >&2
  exit 1
fi

printf '\nAll %d test files passed.\n' "$test_count"
