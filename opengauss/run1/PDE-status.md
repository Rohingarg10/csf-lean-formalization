# PDE formalization status

Source: `MTL603_PDE_project-9-13.pdf`, Chapter 3, printed pages 8–12.
Output: `RequestProject/PDE.lean`.

**Partial formalization, not completion of the PDF.** The Lean file contains two
definitions and eight proved theorems. Every declaration has a source-referencing
docstring. There are no `sorry`s or custom axioms, but this does not mean the source
is fully covered: several results are only conditional analytic components.

## Source coverage

| Source | Checked declarations | Remaining work |
|---|---|---|
| Lemma 1, p. 8 | `speed`, `arcLength`, `hasDerivAt_arcLength`, `arclength_chain_rule` | None for the stated continuous-speed, regular-point formulation. |
| Lemma 2, pp. 8–9 | `speed_evolution_local` | Construct tangent, normal and curvature from a smooth planar flow; derive Frenet and mixed-partial hypotheses from that construction and CSF. |
| Lemma 3, p. 9 | `arclength_commutator_local` | Instantiate with actual spatial/time derivatives and prove their commutation from smoothness. |
| Lemma 4, p. 10 | `tangent_evolution_local`, `normal_evolution_local` | Supply geometric frame, its quarter-turn map, and the local hypotheses from a flow. |
| Lemma 5, pp. 10–11 | `curvature_evolution_of_angle` | Construct a local tangent angle and prove its two differential identities; instantiate the operators. The checked result is only the final operator-algebra step. |
| Lemma 6(i), p. 11 | `length_evolution_of_speed` | Instantiate speed/curvature and obtain domination from a smooth compact family. |
| Lemma 6(ii), pp. 11–12 | Not formalized | Enclosed-area definition, Green's formula, area variation, and total signed curvature `2π`. |
| Length and area decrease, p. 12 | Not formalized | Deduce monotonicity from the geometric evolution laws. |
| Maximal time `A₀/(2π)`, p. 12 | Not formalized | Integrate area law; formalize the continuation/shrinking-to-a-point result invoked by the source. Area nonnegativity alone only gives an upper bound. |
| Theorem 3.0.1, p. 12 | Not formalized | Formalize the periodic smooth CSF and prove preservation of embeddedness. Equation (2.1) and the earlier argument referenced by the theorem are outside the supplied excerpt. |

## Blocker review

The run stopped on Lemma 6(ii), rather than replacing its geometric content with
an assumed conclusion. Three unsuccessful passes examined:

1. Green/divergence library results: the located divergence theorem is for boxes,
   not the arbitrary region enclosed by an embedded curve.
2. Total curvature / turning number / Hopf Umlaufsatz: local and semantic searches
   did not locate an applicable theorem in the installed mathlib.
3. Alternative curve-integral/homotopy route: the located Poincare results concern
   closed forms and supplied homotopies. They do not by themselves establish the
   enclosed-region area formula or the degree of the tangent of a simple curve.

These are missing developments in this formalization, not claims that the
mathematical statements are false or that no library solution can exist.
The next substantive task is a geometric regular-periodic-curve API together
with the planar turning theorem and a suitable area formula. The earlier local
results also need their geometric links before being counted as full CSF lemmas.

## Verification and reproducibility

The managed shell changes `HOME`; the installed toolchain is available with:

```bash
ELAN_HOME=/home/rohin/.elan lake env lean RequestProject/PDE.lean
ELAN_HOME=/home/rohin/.elan lake build
```

- Lean/LSP diagnostics: no errors or warnings in the final Lean file.
- Project build: succeeded, 3111 jobs.
- Axiom scan: all 10 declarations use only standard axioms.
- Sorries: 0 before, 0 after; omitted obligations are listed above.
- No existing Lean declarations were changed.
- Git commit failed because author identity is not configured. No identity was invented.

## Autoformalize session summary

- Session: `lean4-session-58DIvR`.
- Stop reason: `max-stuck` on Lemma 6(ii).
- Claims attempted: 6 of 9 queue entries (Lemmas 1–6; then monotonicity,
  extinction time, and Theorem 3.0.1). Attempted does not mean fully formalized.
- Cycles: 9 total; 3 consecutive stuck cycles; 0 deep invocations.
- Elapsed at stop: 521 seconds (tracker display: 8m/120m).
- Generated file: 1, no statement redrafts.

Continue with guided formalization of the missing geometry, preserving the
existing theorem contracts. Do not treat this file's successful build as evidence
that the complete source has been formalized.
