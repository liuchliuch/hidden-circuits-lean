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

For sandboxed checking on Linux, install Go and provide a functioning user
`systemd` session, then run:

```sh
scripts/comparator.sh
```

The script builds pinned [Landrun](https://github.com/Zouuup/landrun) revision
`811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`. Preflight tests require an
unprivileged user, Landlock ABI 6 or later, and effective filesystem, TCP and
AF_UNIX restrictions. A systemd address-family guard complements Landrun.
Sandbox mode never falls back to local mode. Tools are built outside the
repository's writable build directory and checked against their pinned revisions.

Both commands also test three invalid solutions: a changed conclusion, an
added premise and an extra axiom. Each must fail with the expected Comparator
diagnostic. Reports and logs are written under `.lake/ci/comparison/`.

## Continuous integration

The [workflow](https://github.com/liuchliuch/hidden-circuits-lean/actions/workflows/ci.yml)
uses two Ubuntu 24.04 jobs, each with a 350-minute budget. The first starts with
no project build products, builds every production module with two workers,
and audits all production declarations. The second verifies the source commit
and SHA-256 hashes of that run's build artifact before running the official
Linux sandboxed Comparator on all 40 public statements and all three rejection
controls. Reusing the checked build avoids compiling the library twice.

The workflow retains source fingerprints, declaration inventories, command
results and Comparator logs as artifacts. Dependency revisions, public
statements and the axiom whitelist are unchanged. The original local release
record is historical; current CI results establish whether a published commit
passed the Linux checks.

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
