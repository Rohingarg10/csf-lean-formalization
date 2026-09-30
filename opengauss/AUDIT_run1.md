# Audit: OpenGauss run 1 vs. the original notes (Chapter 3)

Audit of `RequestProject/PDE.lean` (tag `run1`) against Chapter 3 of `MTL603_PDE_project-9-13.pdf`, in
the same format as the Aristotle audit (`AUDIT_NOTES.md` in the Aristotle project).

## Summary

Run 1 formalizes the **local calculus core** of Lemmas 1–5 and 6(i) and nothing beyond Lemma 6(i). The
file is clean (no `sorry`, no axioms, docstring on every declaration), and the agent's own status file is
candid about the gaps. But most "lemmas" are stated in a *local, conditional* form: the geometric facts
that make them CSF lemmas (Serret–Frenet, the flow equation, commuting partials, the tangent-angle
identities) are supplied as **hypotheses** rather than derived. There is no definition of a moving curve,
tangent, normal, curvature, or of CSF itself.

## Definitions

- `speed γ u = ‖γ'(u)‖` and `arcLength γ u = ∫₀ᵘ speed` — match the notes. These are for a single curve
  `γ : ℝ → E` in a general real inner-product space, not for a moving curve `γ(u,t)` in the plane.
- **Missing:** unit tangent, normal, curvature, closed/periodic curves, embeddedness, enclosed area, and
  the flow equation `∂γ/∂t = κn` (equation 2.1). Compare Aristotle, which defines all of these
  (`Defs.lean`) and states every lemma for an actual `IsCSF` flow.

## Lemma by lemma

| Notes | Lean | Verdict |
|---|---|---|
| Lemma 1 | `hasDerivAt_arcLength`, `arclength_chain_rule` | **Faithful.** Genuine statements about an arbitrary curve; continuity of speed and `v ≠ 0` made explicit. |
| Lemma 2 (`∂v/∂t = −κ²v`) | `speed_evolution_local` | **Conditional core.** Spatial Serret–Frenet (`hN`) and the CSF mixed-partial identity (`hflow`) are hypotheses; `T` is an arbitrary unit vector with `w t = v•T`. Proves the inner-product computation, not the lemma for a flow. |
| Lemma 3 (commutator) | `arclength_commutator_local` | **Conditional core.** Product-rule computation for `v⁻¹ q`, taking Lemma 2's conclusion as a hypothesis; the identification of `qₜ` with a mixed partial is only in the docstring. |
| Lemma 4 (`∂T/∂t`, `∂n/∂t`) | `tangent_evolution_local`, `normal_evolution_local` | **Conditional core.** The key expansion `∂t∂uγ = κᵤn − vκ²T` is hypothesis `hq`; the normal identity is linearity of an abstract rotation `J` applied to the tangent identity. |
| Lemma 5 (`∂κ/∂t = κ_ss + κ³`) | `curvature_evolution_of_angle` | **Algebra only.** Given the commutator and the angle identities `D_sθ = κ`, `D_tθ = D_sκ` as hypotheses about abstract operators, the conclusion follows by rewriting and `ring`. It follows the notes' tangent-angle route (Aristotle used Lemmas 3–4 instead), but the angle's existence and both identities are assumed. |
| Lemma 6(i) (`dL/dt = −∫κ²ds`) | `length_evolution_of_speed` | **Faithful, with real analytic content.** Differentiation under the integral via dominated convergence, with domination as an explicit hypothesis and Lemma 2's law as `hevol`. |
| Lemma 6(ii), monotonicity, `T₀ = A₀/2π`, Theorem 3.0.1 | — | **Not formalized.** |

## Where and why it stopped

Stopped on Lemma 6(ii) after 3 stuck cycles, having searched Mathlib for (1) Green's/divergence theorem on
a Jordan domain (only boxes available), (2) Hopf's Umlaufsatz / turning number (absent), (3) a
homotopy/curve-integral route (insufficient). This is the **same gap** Aristotle met. The strategies differ:

- **Aristotle** kept the full statements and isolated the missing facts as three explicit, named hypotheses
  (`htotal`, `harea`, `hlim`), which let it finish the chapter including Theorem 3.0.1.
- **OpenGauss run 1** declined to assume the Lemma 6(ii) conclusions and stopped — but in Lemmas 2–5 it
  did assume the geometric inputs locally. Its "no assumed conclusions" stance is therefore partial: it
  avoids assuming *global* facts but makes each local lemma conditional on the facts that make it a CSF
  statement.

## Noteworthy

- Honest self-reporting: `PDE-status.md` states plainly that the build succeeding is not evidence of full
  coverage and lists every remaining obligation.
- The agent noted that equation (2.1) and the earlier argument Theorem 3.0.1 relies on are outside the
  supplied excerpt (pp. 9–13) — true, and it applies equally to Aristotle's input.
- Settings caveat: run 1 ran at roughly default settings (120-min budget, 0 deep passes), because the flags
  were sent as a follow-up message and not all were picked up. See `OPENGAUSS_RUNS.md`.

## Still to do

- ~~Rerun `#print axioms` ourselves~~ Done 28 Sep: `axle/run1_PDE_check.lean` compiles with no errors, and all 10
  declarations depend only on `propext`, `Classical.choice`, `Quot.sound` (log: `axle/run1_PDE_check.log`).
- Your own read of the statements against the notes: this audit is a first pass.
