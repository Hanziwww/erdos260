#!/usr/bin/env bash

set -euo pipefail

# These revisions use Nanoda's whitespace-based export format 2.0.0. Upstream
# lean4export now emits JSON 3.1.0, which Nanoda's current parser cannot read.
readonly LEAN4EXPORT_REV="f3cf6458a309d643dc586a80f9ab5a93c2304db9"
readonly NANODA_REV="e5438ac0a85a036b6dfe093aa457bc3448498014"
readonly ROOT="$(pwd)"
readonly WORK="$(mktemp -d "${RUNNER_TEMP:-/tmp}/erdos260-nanoda.XXXXXX")"

cleanup() {
  rm -rf -- "${WORK}"
}
trap cleanup EXIT

fetch_revision() {
  local repository="$1"
  local revision="$2"
  local destination="$3"
  git init --quiet "${destination}"
  git -C "${destination}" remote add origin "${repository}"
  git -C "${destination}" fetch --quiet --depth 1 origin "${revision}"
  git -C "${destination}" checkout --quiet --detach FETCH_HEAD
}

echo "::group::Build the pinned Nanoda-compatible Lean exporter"
fetch_revision \
  https://github.com/ammkrn/lean4export.git \
  "${LEAN4EXPORT_REV}" \
  "${WORK}/lean4export"
git -C "${WORK}/lean4export" apply --check \
  "${ROOT}/.github/patches/lean4export-v4.32.patch"
git -C "${WORK}/lean4export" apply \
  "${ROOT}/.github/patches/lean4export-v4.32.patch"
cp "${ROOT}/lean-toolchain" "${WORK}/lean4export/lean-toolchain"
grep -Fq 'def semver := "2.0.0"' "${WORK}/lean4export/Main.lean"
lake build --dir "${WORK}/lean4export"
echo "::endgroup::"

echo "::group::Build the pinned Nanoda checker"
fetch_revision \
  https://github.com/ammkrn/nanoda_lib.git \
  "${NANODA_REV}" \
  "${WORK}/nanoda"
cargo build --release --locked --manifest-path "${WORK}/nanoda/Cargo.toml"
echo "::endgroup::"

cat > "${WORK}/nanoda.json" <<'EOF'
{
  "use_stdin": true,
  "permitted_axioms": [
    "propext",
    "Classical.choice",
    "Quot.sound",
    "Lean.trustCompiler"
  ],
  "unpermitted_axiom_hard_error": true,
  "nat_extension": true,
  "string_extension": true,
  "print_success_message": true
}
EOF

mapfile -t declarations < <(
  lake env lean --run "${ROOT}/.github/scripts/ListErdos260Declarations.lean" |
    LC_ALL=C sort -u
)

# Nanoda expands kernel literal nodes back into ordinary Lean expressions.
# These constants are therefore semantic dependencies of `#ELN`/`#ELS` rows,
# even though Lean's `Expr.getUsedConstants` cannot see them inside a literal.
readonly -a LITERAL_EXTENSION_ROOTS=(
  Nat
  Nat.zero
  Nat.succ
  List
  List.nil
  List.cons
  String
  String.mk
  Char
  Char.ofNat
)

if (( ${#declarations[@]} < 39 )); then
  echo "Expected at least the 39 paper-labelled declarations; found ${#declarations[@]}." >&2
  exit 1
fi
printf -v declaration_text '%s\n' "${declarations[@]}"
grep -Fxq 'Erdos260.thm_main_density' <<< "${declaration_text}"
grep -Fxq 'Erdos260.erdos_260' <<< "${declaration_text}"
printf 'Nanoda will check %d project declarations and their dependency closure.\n' \
  "${#declarations[@]}"
printf 'The export also includes %d kernel-literal support roots required by Nanoda.\n' \
  "${#LITERAL_EXTENSION_ROOTS[@]}"

echo "::group::Check every project declaration with Nanoda"
lake env "${WORK}/lean4export/.lake/build/bin/lean4export" \
  Erdos260 -- "${LITERAL_EXTENSION_ROOTS[@]}" "${declarations[@]}" |
  "${WORK}/nanoda/target/release/nanoda_bin" "${WORK}/nanoda.json"
echo "::endgroup::"
