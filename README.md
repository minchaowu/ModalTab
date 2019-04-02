# Verified decision procedures for modal logics

The proofs compile after commit [1780d89](https://github.com/minchaowu/ModalTab/commit/1780d89c4ba14dda9e36ac88b2f1713c90120a0d). For neater proof scripts and enhancement of efficiency, please follow the recent commits.

How to compile:

+ Install [Lean](https://github.com/leanprover/lean/releases/tag/v3.4.2) using [elan](https://github.com/leanprover-community/mathlib/blob/master/docs/elan.md).

+ Run `leanpkg build` in the root of this repository. Several lines of tests will be printed, but there should be no errors reported by Lean.

For each implementation, `is_sat` is the function to run. For K, it is in `jump.lean`. For KT and S4, they are in `vanilla.lean`. Alternatively, `tableau` in the same file can be used to inspect the model returned.
