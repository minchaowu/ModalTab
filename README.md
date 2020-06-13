# Verified decision procedures for modal logics

The proofs compile after commit [5173c54](https://github.com/minchaowu/ModalTab/commit/5173c548ac9710d7ec9b259e82c76a1208cf4a41). For neater proof scripts and enhancement of efficiency, please follow the recent commits.

How to compile:

+ Install [Lean](https://github.com/leanprover-community/lean) using [elan](https://github.com/Kha/elan) or following the [build instructions](https://github.com/leanprover-community/lean/blob/master/doc/make/index.md).

+ Run `leanpkg build` in the root of this repository. Several lines of tests will be printed, but there should be no errors reported by Lean.

For each implementation, `is_sat` is the function to run. For K, it is in `jump.lean`. For KT and S4, they are in `vanilla.lean`. Alternatively, `tableau` in the same file can be used to inspect the model returned.
