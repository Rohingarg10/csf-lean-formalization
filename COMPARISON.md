# Aristotle and OpenGauss on one chapter of CSF: write-up and results

## Summary

I gave two AI formalization systems — Harmonic's **Aristotle** and Math Inc's **OpenGauss** — the same
chapter of my curve-shortening-flow notes and the same instruction, then audited each output against the
notes and checked every build and axiom claim independently.

- **Both formalized the whole chapter**, including Theorem 3.0.1 (embeddedness is preserved), which my notes
  state without proof. Both proofs of it are complete and sorry-free.
- **Both hit the same wall**: Lemma 6(ii) needs Green's theorem for a Jordan domain and Hopf's Umlaufsatz,
  neither of which is in Mathlib. **They handled it differently.** Aristotle made the missing facts explicit
  hypotheses of its theorems; OpenGauss stated them as lemmas and left their proofs as `sorry`, while
  defining area as the true enclosed area rather than as an integral.
- **They independently reached the same mathematical conclusions** in several places where they departed
  from my notes — most notably that Theorem 3.0.1 does not need its curvature bound on `[0, T₀)`.
- OpenGauss needed a second, longer-budget run to get there; its first run stopped after the local
  calculus of Lemmas 1–6(i).

This is **one data point, not a benchmark**: one chapter, one Aristotle run, two OpenGauss runs, settings
not tuned for either tool. It does not declare a winner.

## Setup

| | Aristotle | OpenGauss run 1 | OpenGauss run 2 |
|---|---|---|---|
| Form | Hosted service; PDF uploaded | Local orchestrator (`gauss /autoformalize`) driving Codex CLI, in WSL2 | same |
| Model | Harmonic's own (not user-selectable) | GPT-6-Astra, reasoning effort **low**¹ | same |
| Instruction | "Fully formalize the contents of the attached. For each formal declaration, add a docstring that clearly and explicitly references the corresponding informal declaration in the original source file." | same, naming the PDF file rather than "the attached" | same |
| Lean / Mathlib | v4.28.0 / `v4.28.0` | identical `lake-manifest.json` | identical |
| Workflow settings | — | close to defaults²: 3 stuck cycles, deep mode on stuck, 120-min budget | 8 stuck cycles, deep mode always, 360-min budget, checked rigor |
| Human input | none | workflow flags re-sent once at startup | one usage-limit reset + one `continue` message |
| Time / compute | not recorded | 10.5 min; 130K tokens | 63 min of workflow time; 352K tokens |

¹ OpenGauss runs Codex from its own managed configuration, so a higher effort set in my own Codex
configuration did not apply. ² Run 1's flags were sent as a follow-up message and were only partly picked
up. Full details: [`opengauss/OPENGAUSS_RUNS.md`](opengauss/OPENGAUSS_RUNS.md).

## Results

| Result in the notes | Aristotle | OpenGauss run 1 | OpenGauss run 2 |
|---|---|---|---|
| Definitions: moving curve, `T`, `n`, `κ`, CSF | Defined from `γ`; `IsCSF` = smooth, regular, `∂γ/∂t = κn` | speed and arclength only | `Flow` structure bundling `γ, T, n, v, κ` with `∂γ/∂t = κn`, a Frenet frame and mixed-partial symmetry as fields |
| Serret–Frenet equations | **derived** | hypotheses | spatial `∂T/∂u = vκn` is a field (it defines `κ`); `∂n/∂u` derived |
| Lemma 1, arclength | ✅ | ✅ | ✅ |
| Lemma 2, `∂v/∂t = −κ²v` | ✅ | conditional core only | ✅ |
| Lemma 3, commutator | ✅ | conditional core only | ✅ |
| Lemma 4, `∂T/∂t`, `∂n/∂t` | ✅ | conditional core only | ✅ |
| Lemma 5, `∂κ/∂t = κ_ss + κ³` | ✅ via Lemmas 3–4 | algebra only (tangent-angle route, angle identities assumed) | ✅ by differentiating the Frenet equation |
| Lemma 6(i), `dL/dt = −∫κ² ds` | ✅ | ✅ | ✅, plus length is non-increasing |
| Lemma 6(ii), `dA/dt = −2π` | ✅ given `htotal` (Umlaufsatz) | — | ✅ from two `sorry` lemmas (Green, Umlaufsatz) |
| Remark: `T₀ ≤ A₀/2π`, `T₀ = A₀/2π` | ✅ given `harea`; `=` also given `hlim` | — | ✅ as scalar lemmas; `≤` needs `A ≥ 0` (proved for the true area), `=` needs `A(T) = 0` |
| Theorem 3.0.1, embeddedness preserved | ✅ (~400 lines) | — | ✅ (~500 lines) |
| Size | 1,688 lines in 9 files; 83 theorems | 154 lines; 8 theorems | 1,128 lines in 1 file; 51 theorems |
| `sorry` | 0 | 0 | 2 |
| Axioms | standard only, all results | standard only | standard only for 48 of 51 theorems; 3 depend on `sorryAx` |
| Docstrings citing the notes | every declaration | every declaration | every declaration |

"Conditional core" means the lemma is stated with the geometric facts that make it a CSF statement (the
Frenet equations, the flow equation, commuting partials) as hypotheses about arbitrary vectors and
functions, so what is proved is the algebra at its centre. Audits: [`aristotle/AUDIT_NOTES.md`](aristotle/AUDIT_NOTES.md),
[`opengauss/AUDIT_run1.md`](opengauss/AUDIT_run1.md), [`opengauss/AUDIT_run2.md`](opengauss/AUDIT_run2.md).

## The main difference: the same gap, handled two ways

Lemma 6(ii) in my notes uses two facts without proof: that the area enclosed by the curve equals the
Green's-formula integral `½∫(γ₁γ₂′ − γ₂γ₁′) du`, and Hopf's Umlaufsatz, `∫κ ds = 2π`, for a simple closed
curve with inward normal. Neither is in Mathlib, and neither tool proved them.

**Aristotle** kept the chapter's statements and turned the missing facts into explicit, named hypotheses:
`htotal` (Umlaufsatz), `harea` (enclosed area ≥ 0) and `hlim` (area → 0 at the maximal time). It *defined*
the enclosed area to be the Green's-formula integral, so whether that integral is the true area is never
asked. Every theorem is sorry-free and states exactly what it assumes.

**OpenGauss (run 2)** defined the enclosed area as the Lebesgue measure of the bounded region the curve
encloses — the true area — and stated the two missing facts as lemmas:
`signedArea_eq_enclosedArea` (Green) and `total_curvature_eq_two_pi` (Umlaufsatz), with `sorry` proofs.
Lemma 6(ii) is proved from them. Because its area is a measure, `area ≥ 0` is a one-line proof, so the
counterpart of Aristotle's `harea` disappears. The end-of-flow condition remains an explicit hypothesis, as
with Aristotle's `hlim`.

**OpenGauss (run 1)**, on a short budget, declined to assume these facts and stopped before them.

The logical content is nearly the same; the packaging is not. Aristotle's results are complete proofs of
conditional statements, and `#print axioms` shows only the standard axioms. OpenGauss's Lemma 6(ii) is an
unconditional statement whose proof depends on two named, unproved lemmas, and `#print axioms` shows
`sorryAx` for exactly those three declarations. Both are honest about the gap; they differ in where the
reader finds it — in the theorem statement, or in the axiom report.

## The trade-off at the foundations

The difference runs the other way at the bottom layer. Aristotle starts from a bare smooth map `γ(u, t)`
and **derives** the unit tangent, normal, curvature, the Serret–Frenet equations and the symmetry of mixed
partials from smoothness. OpenGauss's `Flow` structure takes the tangent, normal and curvature as separate
data and requires the Frenet relation `∂T/∂u = vκn` and mixed-partial symmetry as fields; nothing in the
file shows that a smooth regular `γ` gives rise to a `Flow`. So Aristotle is more self-contained at the
foundations, and OpenGauss is more faithful about what "area" means.

## Where they independently agreed

The two tools share no code and were run independently, yet made the same choices at four points where
both departed from my notes:

1. **Theorem 3.0.1 does not need the curvature bound `κ ≤ c` on `[0, T₀)`.** Both proofs keep the hypothesis only
   to match my statement and never use it (Aristotle binds it as `have _ := hκ`; OpenGauss names it `_hbound`).
   Why this happens, and what it says about my statement, is the subject of the next section.
2. **The same proof of Theorem 3.0.1**, which my notes do not give: local injectivity from compactness, the
   minimum over parameter pairs of the distance between two points of the curve, and a minimum principle
   showing it cannot reach zero in finite time.
3. **Lemma 5 without the tangent angle.** My notes prove `∂κ/∂t = κ_ss + κ³` through the angle `θ(s, t)` of the
   tangent. Both final formalizations avoid choosing a global angle and work with the moving frame directly.
   (Run 1, which only proved the algebra, did follow the angle route.)
4. **A weaker hypothesis at `t = 0`.** Both require the flow equation only for `t > 0`, with continuity and
   regularity at `t = 0`, instead of my notes' blanket smoothness — a strictly stronger theorem.

Both also split the notes' remark after Lemma 6 into `T₀ ≤ A₀/2π` and `T₀ = A₀/2π`, the second needing the
area to vanish at `T₀`, which the notes take from an earlier existence result not in the excerpt.

## A closer look at Theorem 3.0.1

In my notes, Theorem 3.0.1 reads:

> Let `γ : S¹ × [0, T₀) → ℝ²` be a family of closed curves satisfying equation (2.1). If the initial curve `γ₀`
> is embedded and if there exists `c ∈ ℝ` such that `κ(u, t) ≤ c` for all `(u, t) ∈ S¹ × [0, T₀)`, then `γ_t` is an
> embedded curve for each `t ∈ [0, T₀)`.

I stated it without proof, as "a concrete form of a result we had shown earlier". Both tools proved it, and
neither used the bound. This is not an accident of the formalization.

Fix `t₁ < T₀`. On the compact interval `[0, t₁]` the flow is smooth, so `κ` and `T` are bounded and uniformly
continuous there. That is all the proof needs. Pairs of points that are far apart on the curve cannot meet,
since the minimum distance between them cannot decrease (the two-point maximum principle). Pairs that are
close on the curve stay apart by local injectivity, which follows from the uniform control of `T` on `[0, t₁]`.
Every `t < T₀` lies in such an interval, so a bound uniform on all of `[0, T₀)` is never used.

A uniform bound does matter, but for statements at `T₀`, not before it. To conclude that the limit curve
`γ_{T₀}` is embedded, the control near the diagonal has to be uniform up to `T₀`; otherwise arcs can pinch or
form a cusp in the limit. And if `|κ|` stays bounded on `[0, T)`, the flow extends smoothly past `T` —
equivalently, the curvature blows up at the maximal time. Neither formalization says anything at `T₀`.

So I think Theorem 3.0.1, as I wrote it, mixes two statements. It attaches a hypothesis that belongs to the
behaviour at `T₀` (or to continuing the flow past it) to a conclusion about all `t < T₀`. Two things point this
way. First, the bound is one-sided, `κ ≤ c`, while both uses above need `|κ| ≤ c`. Second, the same slip
appears in my remark after Lemma 6, where "the flow cannot exist beyond `T = A₀/2π`" and "the maximal `T` is
`T = A₀/2π`" are run together. Both tools split that remark into an inequality and an equality, and the
equality needs the area to vanish at `T₀`.

The statement both tools actually prove is the cleaner one:

> Let `γ` be a smooth solution of curve-shortening flow on `S¹ × (0, T₀)`, continuous and regular up to
> `t = 0`. If `γ₀` is embedded, then `γ_t` is embedded for every `t ∈ [0, T₀)`.

None of this is new mathematics. Preservation of embeddedness under curve-shortening flow is a standard
consequence of the maximum principle, and a quantitative form is Huisken's distance comparison
principle [3]. What the two formalizations add is two independent, kernel-checked proofs that
never touch the bound.

The "earlier result" behind my remark after Lemma 6 — that the flow exists until the curve shrinks to a
point — is the Gage–Hamilton–Grayson theorem [1, 2]. Both tools recognised that it lies well beyond the
chapter and took it as an explicit hypothesis (`hlim` for Aristotle, `A(T) = 0` for OpenGauss) rather than
pretending to prove it.

## Observations on the process

- **Aristotle** was a single submission with no configuration; after a local refresh of the Mathlib
  build cache on my machine, the returned project built cleanly.
- **OpenGauss** is a local toolkit rather than a service, so the setup is part of the experience: a broken
  hosted-template download (worked around with the repository's own template), running only under WSL2
  on Windows, workflow flags that are only honoured on the command line, a managed Codex configuration
  that silently overrode my reasoning-effort setting, and automatic commits that failed because the agent's
  shell uses its own home directory. None of these affected the mathematics, but each cost time.
- **Budget mattered a lot for OpenGauss.** With near-default settings it stopped after about ten minutes,
  three stuck cycles and no deep-mode passes. With a larger stuck budget and deep mode always on, it
  attempted all nine claims, used deep mode four times, and proved Theorem 3.0.1.
- **OpenGauss's self-reports were accurate.** Its coverage files state plainly what is and is not proved,
  and warn that a successful build is not evidence of full coverage. Every claim in them held up under
  independent checking.

## Verification

Every build and axiom claim in this document was checked outside the tools that produced it — by local
builds, an independent per-theorem axiom report, single-file compiles, and AXLE, Axiom Math's Lean checker. Details
and reproduction steps: [`verification/RESULTS.md`](verification/RESULTS.md).

## Caveats

- One chapter, one Aristotle run and two OpenGauss runs. Nothing here generalizes to the tools overall.
- OpenGauss ran at **low** reasoning effort on a Codex Plus plan and hit a usage limit during run 2; a
  higher-effort run might do better. Aristotle's run time and compute were not available to me.
- Runs 1 and 2 differ in both budget and how their settings were passed, so run 1 is not a controlled
  "low budget" condition.
- The source excerpt (pp. 9–13) refers to an equation and an earlier result outside it. Both tools had the
  same excerpt.
- The audits are my reading of the statements against my own notes, drafted with AI assistance.

## How to describe each result

- **Aristotle:** "Formally verified in Lean 4, *modulo three explicit hypotheses*" (`htotal`, `harea`, `hlim`).
- **OpenGauss run 2:** "Formalized in Lean 4 with two explicitly unproved lemmas (Green's theorem for Jordan
  domains; Hopf's Umlaufsatz), on which only the area evolution law depends; everything else, including
  Theorem 3.0.1, is fully proved."
- **OpenGauss run 1:** "Partial: the local calculus of Lemmas 1–6(i)."

## References

1. M. Gage and R. S. Hamilton, *The heat equation shrinking convex plane curves*, J. Differential Geom. **23**
   (1986), no. 1, 69–96.
2. M. A. Grayson, *The heat equation shrinks embedded plane curves to round points*, J. Differential Geom. **26**
   (1987), no. 2, 285–314.
3. G. Huisken, *A distance comparison principle for evolving curves*, Asian J. Math. **2** (1998), no. 1, 127–133.
