# Hidden Circuits and Exact Counting in Ordered Graphs

Lean formalization of [Chenghua Liu and Boning Meng, arXiv:2609.18132v1](https://arxiv.org/abs/2609.18132v1).

The development proves perfect-matching counting completeness for monotone,
unit interval, and chordal permutation graphs; the global encoding projection
and circuit reductions; the strict inclusion of quasi-chain graphs in
distance-hereditary graphs; and the distance-hereditary counting algorithm.
It also includes machine-based approximation and exact sampling results.

Start with [Statements.lean](Statements.lean) to review the public claims and
[Proofs.lean](Proofs.lean) for their proofs. The [paper correspondence](docs/paper.md)
maps all 32 numbered items and explains the input, complexity, and probability models.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
```

Lean **4.29.0-rc6** and mathlib commit
**f156f7abd91ac67adb22bf999e5a71ba22e22e41** are pinned. Keep the committed
`lake-manifest.json`; do not run `lake update` when reproducing this version.

## Verify

```sh
python3 scripts/check.py --jobs 2
scripts/comparator.sh --local
```

The first command checks every production module, import coverage, and all
production declarations' transitive axioms. The second uses the official
[Comparator](https://github.com/leanprover/comparator) to compare the separate
statement and proof modules, enforce the axiom whitelist, and replay exported
proofs in the Lean kernel. `--local` runs without a sandbox; see
[verification details](docs/verification.md) for the Linux sandbox command.

`Statements.lean` contains intentional challenge placeholders and is excluded
from the production build and axiom audit. Production proofs permit only
`propext`, `Classical.choice`, and `Quot.sound`.

The repository contains source, pinned configuration, documentation, and checks.
Build products and dependency caches stay under `.lake/`. GitHub Actions runs
the same checks. See [the release verification record](docs/validation.json).

Licensed under [Apache-2.0](LICENSE).
