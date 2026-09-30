# Curve shortening flow: coverage and handoff

Source: `MTL603_PDE_project-9-13.pdf`, Chapter 3, printed pages 8–12.
Output: `RequestProject/CSF.lean`. Verification date: 2026-09-28.

## Source coverage

| Source claim | Main declaration(s) in namespace `CSF` | Status |
| --- | --- | --- |
| Lemma 1 | `hasDerivAt_arclength`, `arclength_chain_rule` | Checked |
| Lemma 2 | `Flow.velocity_evolution` | Checked |
| Lemma 3 | `Flow.arclength_commutator` | Checked |
| Lemma 4 | `Flow.tangent_evolution`, `Flow.normal_evolution` | Checked |
| Lemma 5 | `Flow.curvature_evolution` | Checked |
| Lemma 6(i) | `Flow.length_evolution` | Checked |
| Lemma 6(ii) | `Flow.enclosedArea_evolution` | Two geometric dependencies unfinished |
| Consequences after Lemma 6 | `Flow.length_antitoneOn`, `area_affine`, `area_strictAntiOn`, `lifetime_le_of_nonnegative_area`, `extinction_time_of_zero_area` | Checked with explicit hypotheses |
| Theorem 3.0.1 | `embeddedness_preserved` | Checked |

## Modeling and scope

- `Flow` records actual spatial/time derivatives, a planar orthonormal Frenet frame,
  positive speed, and mixed-partial symmetry. Evolution conclusions are proved, not fields.
- Closed curves are periodic real lifts with period `2π`. Embeddedness is injectivity on
  the half-open fundamental interval. `ClassicalClosedFlow` includes continuity and
  immersion at initial time without assuming a backward extension of the flow.
- Integral differentiation uses explicit joint continuity assumptions.
- Enclosed area is Lebesgue measure of the bounded complementary components, not a
  definition by the signed support integral. The inward-normal condition fixes the sign.
- The analytic signed-area evolution and boundary cancellation are independently checked.
- Scalar area/lifetime consequences explicitly assume the area derivative law. Equality
  of extinction time additionally assumes zero endpoint area. Existence until geometric
  point extinction, which the excerpt attributes to an earlier result, is not proved here.
- Theorem 3.0.1 retains the source's one-sided curvature upper bound. Its proof establishes
  the stronger conclusion without using that bound: uniform local injectivity, the
  two-point spatial minimum inequality, and a compact minimum principle suffice.

## Remaining proof obligations

1. `Flow.signedArea_eq_enclosedArea`: Green's theorem for the regular Jordan boundary,
   including the required topology, measure, and boundary regularity facts.
2. `Flow.total_curvature_eq_two_pi`: the turning-tangent theorem for regular embedded
   closed planar curves with inward normal.

Local mathlib searches did not locate the needed Jordan/turning theorems. Available
divergence-theorem results concern rectangular boxes and do not directly discharge the
first obligation. Simple automation did not solve either goal. Do not replace geometric
area by signed area or add these conclusions as flow assumptions to hide the gaps.
Suggested next workflow: `/lean4:formalize` targeting these two declarations.

## Verification

- `lake env lean RequestProject/CSF.lean`: succeeds with exactly two `sorry` warnings.
- `lake build`: succeeds (8027 jobs), with the same two warnings.
- Full `#print axioms` audit of all 51 theorem declarations: exactly the two unfinished
  lemmas and `Flow.enclosedArea_evolution` depend on `sorryAx`. The other 48 use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- In particular, `embeddedness_preserved` has no `sorryAx` dependency.
- `git diff --check`: passes. No custom axioms were introduced.

This is a partially completed formalization, not a fully checked rendition of every claim.
All nine source claim groups were attempted. The workflow stops with an empty attempt
queue, not with all proof obligations solved. Tracker totals: 12 cycles, one stuck cycle,
four deep invocations. Automatic commit was unavailable because Git author identity is
unset; no identity configuration was changed and no commit was created.
