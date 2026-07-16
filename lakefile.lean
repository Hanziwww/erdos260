import Lake

open Lake DSL

/-!
The package name intentionally matches the aggregate module `Erdos260`.
Besides making the public entry point unambiguous, this lets external checkers
that infer a root module from a Lean lakefile export the complete environment.
-/
package Erdos260 where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require "leanprover-community" / mathlib @ git "v4.32.0"

@[default_target]
lean_lib Erdos260 where
  globs := #[`Erdos260, `Erdos260.+]
