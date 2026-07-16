# Contributing

Contributions that improve correctness, readability, portability, or the
paper-to-Lean audit trail are welcome.

## Before opening a pull request

1. Install the toolchain selected by `lean-toolchain`.
2. Restore Mathlib's binary cache with `lake exe cache get`.
3. Make the smallest change that addresses the issue.
4. Run the complete verification commands:

   ```console
   lake build --wfail
   lake env lean Erdos260/SkeletonAudit.lean
   ```

## Proof and interface policy

- Do not introduce `sorry`, `admit`, new mathematical `axiom` declarations, or
  `opaque` stand-ins.
- Preserve the exact type of `Erdos260.erdos_260`. Changes to an intermediate
  public interface should explain why the new statement remains faithful to
  the accompanying paper.
- Keep imports acyclic and respect the dependency order documented in the
  README.
- New helper lemmas should be proved in the same pull request and placed in the
  lowest module that has the required dependencies.
- Definitions must retain mathematical semantics. In particular, do not turn
  an analytic or combinatorial object into an arbitrary witness merely to make
  a downstream theorem easier to prove.
- Use `ℝ≥0∞` for nonnegative mass until finiteness has been proved; real-valued
  conversion must carry an explicit finiteness certificate.
- Do not silently weaken a theorem to bypass a proof obstruction. Document a
  missing hypothesis or fidelity repair in `blueprint.md`.

## Documentation and audits

If a paper-labelled declaration changes, update its row in `blueprint.md` and
the corresponding `#check` in `Erdos260/SkeletonAudit.lean`. Add a focused
regression example when repairing an edge case.

A pull request should state:

- what mathematical or engineering issue it addresses;
- which declarations and paper labels are affected;
- whether any public type changed and why;
- the result of the full build and audit commands.

CI repeats the full build, declaration audit, source-placeholder scan, and
endpoint axiom audit on every pull request.
