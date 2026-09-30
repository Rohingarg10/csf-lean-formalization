# Verification results

Every claim about builds, `sorry` and axioms in this repository was checked independently of the tool that
produced the formalization. All checks used Lean v4.28.0 and Mathlib `v4.28.0` (the manifest in both
projects), on 28–29 Sep 2026.

## Summary

| Check | Aristotle | OpenGauss run 1 | OpenGauss run 2 |
|---|---|---|---|
| `lake build` of the project | ✅ succeeds, no warnings about `sorry` | — (archived, not a Lake target) | ✅ succeeds (8026 jobs), exactly 2 `sorry` warnings (`CSF.lean` lines 507, 517) |
| `#print axioms` on the main results | ✅ 11 of 11 standard only | ✅ 10 of 10 standard only | ✅ 48 of 51 theorems standard only; 3 depend on `sorryAx` |
| Single-file compile (this folder) | ✅ 0 errors, 37 s | ✅ 0 errors, 18 s | ✅ 0 errors, 2 `sorry` warnings, 10 s |
| AXLE `check` (Axiom Lean Engine) | ✅ passed | ✅ passed | ✅ compiles; exactly the 3 expected incomplete declarations |
| AXLE `disprove` on the 2 `sorry` lemmas | n/a | n/a | not run (first attempt invalid, not repeated; see below) |
| Hand check of the 2 `sorry` statements on a circle | n/a | n/a | ✅ both statements correct for a circle |

"Standard" means only `propext`, `Classical.choice` and `Quot.sound`.

The three OpenGauss run 2 declarations that depend on `sorryAx` are `Flow.signedArea_eq_enclosedArea`
(Green's theorem) and `Flow.total_curvature_eq_two_pi` (Umlaufsatz), which are the two `sorry`s, and
`Flow.enclosedArea_evolution` (Lemma 6(ii)), which is proved from them. In particular
`embeddedness_preserved` (Theorem 3.0.1) is sorry-free. The tool's own report
(`opengauss/RequestProject/CSF.coverage.md`) says the same.

## Files here

| File | What it is |
|---|---|
| `Aristotle_single.lean` | Aristotle's nine files concatenated in import order into one file, for single-file checkers. Only change: `import RequestProject.*` lines removed and each original file wrapped in its own `section` (header comment explains). No declaration edited. Ends with `Main.lean`'s 11 `#print axioms` lines. |
| `run1_PDE_check.lean` | OpenGauss run 1's `PDE.lean`, unchanged, with `#print axioms` lines appended for all 10 declarations. |
| `OpenGauss_run2_CSF.lean` | OpenGauss run 2's `CSF.lean`, unchanged. |
| `*.log` | Output of compiling each of the three files locally. |
| `axiom_report_run2.lean` | Lean script that lists the axioms of every theorem in run 2's module; its output is `opengauss/run2-axioms.txt`. |
| `AXLE_results.md` | AXLE outputs, verbatim, and the circle check. |

## How each check was run

**Project builds.** `lake exe cache get && lake build` in each project folder. For Aristotle,
`lake env lean RequestProject/Main.lean` prints the 11 axiom lines. For run 2,
`lake env lean ../verification/axiom_report_run2.lean` from `opengauss/` tags every theorem `ok` or `SORRY`.

**Single-file compiles.** `lake env lean <file>` for each of the three `.lean` files here, run from the
OpenGauss project (same toolchain and Mathlib). Logs are the `.log` files.

**AXLE.** The Axiom Lean Engine, Axiom Math's hosted Lean checker, at [axle.axiommath.ai](https://axle.axiommath.ai), environment
`lean-4.28.0` with Mathlib, one file per check. It confirmed the local results for all three files.

**`disprove`.** AXLE's `disprove` tries to prove the negation of a statement (automation plus Plausible
counterexample search). A first attempt pasted only the two lemma statements without the definitions they
use, so AXLE read them as `sorry = 2π` and `sorry = sorry`; that result is meaningless and is recorded as
invalid. I did not repeat it: even with the whole file as input, "failed to prove negation" would be weak
evidence, since these tools cannot construct a curve-shortening flow to test against. The circle check below
serves the same purpose.

**Circle check.** For a circle of radius `r` with the inward normal, in either orientation, the file's
definitions give total curvature `∫₀^{2π} κ v du = (1/r)·r·2π = 2π` and signed area
`−½∫₀^{2π} v⟨γ, n⟩ du = −½·2π·r·(−r) = πr²`, matching both lemma statements. So neither is false in the
obvious way (for example, a sign or orientation error).
