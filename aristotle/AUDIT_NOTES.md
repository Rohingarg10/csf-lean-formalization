# Audit Notes: Aristotle Formalization vs. Original Notes (Chapter 3)

Audit of `RequestProject/` against Chapter 3 ("Properties of Curve Shortening Flow",
pp. 8-12) of `MTL603_PDE_project-9-13.pdf`. Axiom check passed cleanly first (see
`RequestProject/Main.lean`): all eleven results depend only on `propext`,
`Classical.choice`, `Quot.sound` — no `sorryAx`, no hidden gaps.

## Definitions match the notes

In `RequestProject/Defs.lean`:

- `curvature` (`Defs.lean:48-51`) = `⟨∂T/∂s, n⟩` with `n = I·T` — matches the signed
  curvature convention from the Lemma 5 proof exactly.
- `IsCSF` (`Defs.lean:56-60`) encodes `∂γ/∂t = κn` (equation 2.1) correctly, and adds
  smoothness and regularity as explicit standing hypotheses (reasonable — the notes'
  proofs implicitly assume both).
- `enclosedArea` (`Defs.lean:73-80`) is exactly the Green's-formula integral
  `½∫(γ₁∂γ₂/∂u − γ₂∂γ₁/∂u)du` from the Lemma 6(ii) proof.
- `IsEmbeddedAt` (`Defs.lean:82-85`) is injectivity on `[0, 2π)` — matches "simple
  closed curve."

## Lemmas 1-4 and 6(i): faithful translations

`RequestProject/Evolution.lean` follows the notes' proofs essentially line-by-line,
including the Serret-Frenet equations. One notable improvement: rather than taking
Serret-Frenet as given (as the notes do, presumably citing Chapter 2), Aristotle
*derives* `∂T/∂s = κn` and `∂n/∂s = −κT` from the definitions of `curvature`/
`normal`/`tangent` alone (`Frenet.lean:138-153`), so the whole chapter is
self-contained. Lemma 6(i) (`dL/dt = −∫κ²ds`) matches exactly.

## Confirmed issues from the first pass

- **Three explicit hypotheses**, as flagged initially:
  - `htotal` (Hopf's Umlaufsatz, `∫κds = 2π`) — `LengthArea.lean:231`
  - `harea` (enclosed area ≥ 0) — `MaximalTime.lean:77`
  - `hlim` (area → 0 as `t → T₀`) — `MaximalTime.lean:100`

  None of these are proved. Hopf's Umlaufsatz isn't in Mathlib and isn't proved in
  the notes either — the notes' Lemma 6(ii) proof just asserts `∫κds=2π` "since
  each `γ_t` is a closed curve," which *is* Umlaufsatz, uncited.

- **`enclosedArea`'s equality with the true enclosed area is unproved.** It is only
  the Green's-formula definition; connecting it to the actual Jordan-domain area
  would need the Jordan curve theorem, not attempted.

- **The notes' Lemma 6(ii) proof (p.11) is correct up to a typo.** On a first pass I
  flagged it as garbled, because a variable `φ` appears with no antecedent. It is a
  typo for `γ`. With `γ` in place of `φ`, the two middle terms of
  `−½∫(κv − (γ·n)κ²v + κv + (γ·n)vκ²) du` cancel, and the computation gives
  `dA/dt = −∫κv du`: a valid, if compressed, integration by parts. Aristotle reaches
  the same formula by a more direct route: a pointwise identity writing the time
  derivative of the area integrand as a `u`-derivative plus `−2κv`
  (`LengthArea.lean:108-114`), whose integral over a period vanishes because the
  curve is closed.

- **Lemma 5 is proved via Lemmas 3-4, not the tangent-angle argument.** Confirmed:
  `Evolution.lean:186-224` computes `∂κ/∂t` via the commutator identity (Lemma 3)
  and `∂n/∂t` (Lemma 4), never introducing the angle `θ(s,t)` the notes use.

- **Theorem 3.0.1's curvature bound `κ ≤ c` is genuinely unused.** Confirmed at
  `Embedded.lean:387` (`have _ := hκ` — the hypothesis is bound but never invoked
  in the proof body). The formal statement is strictly stronger than the notes:
  it only needs `γ` and `∂γ/∂u` continuous at `t=0`, plus smoothness for `t>0`,
  rather than the notes' blanket smoothness assumption on all of `S¹×[0,T₀)`.

## Significant addition not in the notes

The notes state Theorem 3.0.1 **without proof** ("a concrete form of a result we
had shown earlier"). Aristotle supplies an original, complete proof
(`Embedded.lean`, `MaxPrinciple.lean`, ~400 lines) via the standard two-point
maximum-principle argument (Gage-Hamilton/Grayson-style): local injectivity from
a compactness argument, a chord-distance infimum over parameter pairs, and a
maximum principle showing the minimal chord length cannot decrease to zero in
finite time. Since the notes never give this proof, it can't be checked line-
by-line against them — only for internal mathematical correctness, which it has
(this is a legitimate, well-known proof strategy for embeddedness preservation
under CSF).

A smaller logical sharpening worth citing: the notes' remark deriving `T = A₀/2π`
after Lemma 6 conflates "cannot exist beyond" and "is equal to" in one paragraph.
Aristotle correctly splits this into `maximal_time_le` (unconditional given
`htotal`, `harea`) and `maximal_time_eq` (additionally needs `hlim`) — a faithful
sharpening of an informal step, not an error.
