# Curve-shortening flow in Lean 4: two AI formalizations of one small chapter

I basically wanted to test some of the autoformalisation agents available, and the most tractable way to do that was to test them on some of my old notes from a PDE course. This repository contains two independent Lean 4 formalizations of a part of my notes on curve-shortening flow (CSF) produced by two AI formalization systems, together with my audit of each against the notes, a comparison, and independent verification of every claim made here.

| | Tool | Result |
|---|---|---|
| [`aristotle/`](aristotle/) | [Aristotle](https://aristotle.harmonic.fun) (Harmonic) | **Formally verified in Lean 4, *modulo three explicit hypotheses*.** |
| [`opengauss/`](opengauss/) | [OpenGauss](https://github.com/math-inc/OpenGauss) (Math Inc), Codex backend | **Formalized in Lean 4 with two explicitly unproved lemmas (Green's theorem for Jordan domains; Hopf's Umlaufsatz), on which only the area evolution law depends; everything else, including Theorem 3.0.1, is fully proved.** |

The source is [`notes/MTL603_PDE_project-9-13.pdf`](notes/MTL603_PDE_project-9-13.pdf) (pp. 8–12). Both tools
received the same PDF and the same instruction:

> Fully formalize the contents of the attached. For each formal declaration, add a docstring that clearly
> and explicitly references the corresponding informal declaration in the original source file.

**Read next:** [`COMPARISON.md`](COMPARISON.md) (write-up and results) ·
[`verification/RESULTS.md`](verification/RESULTS.md) (how every claim was checked).

## What the chapter contains

For a smooth family of closed plane curves `γ(u, t)` moving by curve-shortening flow `∂γ/∂t = κn`:

- **Lemmas 1–5** — evolution of arclength, speed (`∂v/∂t = −κ²v`), the commutator `[∂t, ∂s] = κ²∂s`,
  the tangent and normal, and curvature (`∂κ/∂t = κ_ss + κ³`).
- **Lemma 6** — length and enclosed area evolve by `dL/dt = −∫κ² ds` and `dA/dt = −2π`.
- **Remark** — hence the flow exists for time at most `A₀/2π`, with equality if the curve shrinks away.
- **Theorem 3.0.1** — an embedded curve stays embedded under the flow (stated without proof in the notes).

## Results at a glance

| Result in the notes | Aristotle | OpenGauss |
|---|---|---|
| Lemmas 1–5 | ✅ proved | ✅ proved |
| Lemma 6(i), length | ✅ proved | ✅ proved |
| Lemma 6(ii), area `dA/dt = −2π` | ✅ proved, assuming Umlaufsatz (`htotal`) | ✅ proved *from* two `sorry` lemmas (Green, Umlaufsatz) |
| Extinction time `T₀ = A₀/2π` | ✅ `≤` assuming `htotal` and `area ≥ 0` (`harea`); `=` also assuming area → 0 (`hlim`) | ✅ as scalar lemmas: `≤` given `A ≥ 0` (proved for the true area), `=` given `A(T) = 0`; applied to the flow they rest on Lemma 6(ii) |
| Theorem 3.0.1, embeddedness | ✅ proved | ✅ proved |
| `sorry` | none | 2 |
| Axioms | standard only (all results) | standard only, except the 3 results that depend on the 2 `sorry` lemmas |

Two facts the notes use without proof — Hopf's Umlaufsatz (`∫κ ds = 2π` for a simple closed curve) and
Green's theorem for the region a Jordan curve bounds — are not in Mathlib. The tools handled this gap
differently; [`COMPARISON.md`](COMPARISON.md) explains how, and why it matters.

A first, short OpenGauss run (settings close to the defaults) is archived in
[`opengauss/run1/`](opengauss/run1/); it covers only the local calculus of Lemmas 1–6(i).

## Repository layout

```
├── README.md                this file
├── COMPARISON.md            write-up: setup, results, differences, agreements, caveats
├── notes/                   the source PDF
├── aristotle/               Lake project — Aristotle's formalization (9 files, unchanged)
│   ├── RequestProject/      Defs, Calculus, Frenet, Evolution, LengthArea, MaximalTime,
│   │                        MaxPrinciple, Embedded, Main (Main holds the #print axioms checks)
│   ├── AUDIT_NOTES.md       my audit against the notes
│   ├── ARISTOTLE_SUMMARY.md Aristotle's own summary of the run
│   └── README.md            Aristotle's citation note
├── opengauss/               Lake project — OpenGauss run 2 (unchanged)
│   ├── RequestProject/      CSF.lean (formalization), CSF.coverage.md (the agent's own coverage report)
│   ├── run1/                archived output of the first run (not built by Lake)
│   ├── OPENGAUSS_RUNS.md    full log of both runs: settings, timings, tokens, interventions
│   ├── AUDIT_run1.md, AUDIT_run2.md   my audits against the notes
│   ├── run2-axioms.txt      axioms of every theorem in CSF.lean
│   └── logs/                Gauss startup context for each run
└── verification/            single-file versions, local and AXLE check results
```

All Lean files and tool outputs are exactly as the tools produced them. The audit and log files were
written while the work was in progress, so a few of their file references point to the original working
folders: `axle/…` there is `verification/…` here, and `run1-output/` is `opengauss/run1/`.

## Building and checking

Each of `aristotle/` and `opengauss/` is a standalone Lake project on **Lean v4.28.0** and **Mathlib
`v4.28.0`**; their `lake-manifest.json` files are byte-identical. Building either one is enough to check it
(each downloads the prebuilt Mathlib cache, several GB).

```bash
# Aristotle — expect no errors and no sorry
cd aristotle
lake exe cache get && lake build
lake env lean RequestProject/Main.lean      # 11 × "depends on axioms: [propext, Classical.choice, Quot.sound]"

# OpenGauss run 2 — expect exactly two "declaration uses `sorry`" warnings (CSF.lean lines 507, 517)
cd ../opengauss
lake exe cache get && lake build
lake env lean ../verification/axiom_report_run2.lean   # tags every theorem ok / SORRY

# OpenGauss run 1 (archived) — compiled from the opengauss project, needs only Mathlib
lake env lean ../verification/run1_PDE_check.lean
```

All three formalizations were also checked independently with [AXLE](https://axle.axiommath.ai), the Axiom
Lean Engine from [Axiom Math](https://axiommath.ai), using the single-file versions in
[`verification/`](verification/). AXLE confirmed the local results: Aristotle and run 1 are clean, and run 2
compiles with exactly the three declarations that depend on its two `sorry` lemmas. See
[`verification/RESULTS.md`](verification/RESULTS.md).

## How the work was done

- **Aristotle**: the PDF and instruction were submitted to Harmonic's hosted service (run
  `33cfe4c0-21b4-4419-b3ba-d700c3d3f1b4`); the returned project was built and checked locally.
- **OpenGauss**: run locally in WSL2 via `gauss /autoformalize`, which drives the Codex CLI (model
  GPT-6-Astra, reasoning effort *low*) through the `lean4-skills` autoformalize workflow. Two runs from the
  same empty starting point; every setting, timing, token count and human intervention is in
  [`opengauss/OPENGAUSS_RUNS.md`](opengauss/OPENGAUSS_RUNS.md).
- **Verification**: local builds and per-theorem axiom checks, plus an independent check of all three
  formalizations with Axiom Math's AXLE checker.
- **Audits and comparison**: my reading of each formal statement against the notes. I drafted these with the
  help of Claude (Anthropic), then reviewed them myself. The mathematical judgements here are all mine.

This is one chapter and one data point, not a benchmark of the tools. See the caveats in
[`COMPARISON.md`](COMPARISON.md).

## Related work

After both formalizations were finished I came across
[`qinz1yang/differential-geometry`](https://github.com/qinz1yang/differential-geometry), a large Lean 4 library
whose latest release (v0.1.3) is dated 27 September 2026. I was not aware of it while doing this work. It
contains a curve-shortening flow development, but in a different setting: loops in a Riemannian
three-manifold whose metric evolves by Ricci flow, as part of a finite-extinction argument. It has Riemannian
analogues of Lemmas 2–5 and a least-disk-area law with the same `−2π`. As far as I can see it has no planar
version of Theorem 3.0.1, no planar Umlaufsatz and no Green's theorem for Jordan domains, so it does not close
the gaps discussed here. It is on Lean and Mathlib `v4.33.1`, and neither formalization here uses it or depends
on it. I have not built or checked it; I mention it for completeness.

## Credits

- Formalizations: [Aristotle](https://aristotle.harmonic.fun) (Harmonic), and
  [OpenGauss](https://github.com/math-inc/OpenGauss) (Math Inc) with OpenAI's Codex.
- Independent checking: [AXLE](https://axle.axiommath.ai), the Axiom Lean Engine (Axiom Math).
