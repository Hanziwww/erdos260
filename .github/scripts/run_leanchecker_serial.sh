#!/usr/bin/env bash

set -euo pipefail

# `leanchecker` treats a target as a module-name prefix and checks all matching
# modules concurrently. Invoking it once for `Erdos260` therefore retains many
# copies of the imported Mathlib environment. Give every source module its own
# process so memory is released before the next replay starts.
while IFS= read -r source; do
  module="${source%.lean}"
  module="${module//\//.}"
  echo "::group::leanchecker ${module}"
  lake env leanchecker --verbose "${module}"
  echo "::endgroup::"
done < <(find Erdos260 -type f -name '*.lean' -print | LC_ALL=C sort)
