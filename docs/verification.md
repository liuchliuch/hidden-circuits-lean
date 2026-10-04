# Verification

The toolchain and every dependency revision are fixed by `lean-toolchain` and
`lake-manifest.json`. Run `lake exe cache get` to prepare the pinned dependencies.
No other checkout, project object directory, or machine-specific path is needed.
Python 3.9 or later is sufficient for the check script.

## Production build and axiom audit

```sh
python3 scripts/check.py --jobs 2
```

This builds every production Lean module in dependency order, verifies that
all are reachable from `Proofs`, checks that the production sources contain no
proof holes or unchecked native proofs, and performs an ownership-based audit.
The audit includes private declarations and generated helpers, rejects
production-owned axioms, requires every audited constant to belong to the
checked kernel environment, and traverses type and proof dependencies with
`Lean.Util.CollectAxioms`. The whitelist is exactly `propext`, `Classical.choice`,
and `Quot.sound`. Sources are hashed before and after the run.

The public root and proof module are compiled together by `lake build`.
The audit's declaration inventory, logs, and source digest are written under
`.lake/check/`, which is ignored by Git. Use `--jobs 1` to reduce peak memory.
`--plan` checks the source inventory and statement coverage without compiling;
it is not a proof-verification result.

## Statement comparison and kernel replay

`Statements.lean` and `Proofs.lean` declare the same public theorem names with
explicit matching types. The former contains the challenge placeholders; the
latter connects those statements to the proved library results.
`comparator.json` lists every public theorem and the permitted axioms.

```sh
scripts/comparator.sh --local
```

This downloads the official Comparator at commit
`e6831abb2f76b7ce6f2fb28e6410a0df878e6e4b` and uses its committed dependency
lockfile, including `lean4export` commit
`048394e1afeeb52b0fa27bcf3f1ade2ff0f0ab6d`. It checks the toolchain and tracked
checkout before building the tools. The tools and exports are build-time
artifacts, not repository dependencies or release contents.

Comparator compares theorem types and their referenced definitions, checks the
proofs' transitive axioms, and replays the solution export in Lean's kernel.
This release uses the Lean kernel; it does not claim an independent Nanoda run.
The local command deliberately provides no operating-system sandbox and is
intended for this reviewed source tree.

For sandboxed checking on Linux, install
[landrun](https://github.com/Zouuup/landrun) and provide a functioning user
`systemd` session, then run:

```sh
scripts/comparator.sh
```

The script applies the address-family restriction recommended by current
upstream Comparator guidance. It stops if the required sandbox tools are absent;
it never silently falls back to local mode.

## What is trusted

The challenge and the definitions it imports must be reviewed and trusted.
Both public modules import the audited mathematical library. They are separately
compiled modules, not two independent reconstructions of all foundational
definitions. A change to the challenge or a referenced definition requires a
new semantic review against the paper. Comparator checks agreement with that
challenge; it cannot establish the intended meaning of an informal theorem.

See the [Lean proof-validation reference](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
for the distinction between compilation, axiom inspection, statement comparison,
and independent kernel implementations. The release record reports only checks
actually completed on the distributed sources.
