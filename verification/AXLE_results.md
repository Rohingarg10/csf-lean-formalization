# AXLE results (Axiom Lean Engine, https://axle.axiommath.ai), 28 Sep 2026

Environment: Lean 4.28.0 + Mathlib. Files as in this folder.

| File | AXLE result |
|---|---|
| `Aristotle_single.lean` | Passed: compiles, no `sorry`, standard axioms only. |
| `run1_PDE_check.lean` | Passed: compiles, no `sorry`, standard axioms only. |
| `OpenGauss_run2_CSF.lean` | Compiles. Exactly three incomplete declarations, matching `run2-axioms.txt`; everything else passes. |

## `OpenGauss_run2_CSF.lean`, AXLE output (verbatim, as reported)

```
lean_messages:
warning-:507:8-507:34: warning: declaration uses `sorry`
warning-:517:8-517:33: warning: declaration uses `sorry`
tool_messages:
warning Declaration 'CSF.Flow.total_curvature_eq_two_pi' is incomplete (uses 'sorry' or has errors)
warning Declaration 'CSF.Flow.signedArea_eq_enclosedArea' is incomplete (uses 'sorry' or has errors)
warning Declaration 'CSF.Flow.enclosedArea_evolution' is incomplete (uses 'sorry' or has errors)
info-:510:2: info: unsolved goals at sorry:
J : Set ℝ
F : CSF.Flow CSF.Plane J
t : ℝ
ht : t ∈ J
hc : F.ClosedAt t
he : F.EmbeddedAt t
hn : F.InwardAt t
⊢ F.signedArea 0 (2 * Real.pi) t = F.enclosedArea t
info-:520:2: info: unsolved goals at sorry:
J : Set ℝ
F : CSF.Flow CSF.Plane J
t : ℝ
ht : t ∈ J
hc : F.ClosedAt t
he : F.EmbeddedAt t
hn : F.InwardAt t
⊢ F.arcIntegral F.curvature 0 (2 * Real.pi) t = 2 * Real.pi
failed_declarations:
CSF.Flow.total_curvature_eq_two_pi
CSF.Flow.signedArea_eq_enclosedArea
CSF.Flow.enclosedArea_evolution
```

`enclosedArea_evolution` is listed because its proof uses the two `sorry` lemmas, not because of a gap of
its own.

## `disprove` on the two `sorry` lemmas

**First attempt (29 Sep) — invalid.** Only the theorem statements were pasted, without the rest of the file, so
`F.ClosedAt`, `F.arcIntegral`, `F.signedArea`, etc. were unknown identifiers and were elaborated as `sorry`
(negated goals `… sorry = 2 * Real.pi` and `… sorry = sorry`). "Failed to prove negation" on those says
nothing about the real lemmas. To redo: `content` = the whole `OpenGauss_run2_CSF.lean`, `names` =
`CSF.Flow.total_curvature_eq_two_pi` / `CSF.Flow.signedArea_eq_enclosedArea`.

**Not repeated.** `disprove` uses automation (`grind`) and Plausible counterexample search, which cannot
construct a `Flow`, so even a valid rerun would give only weak evidence. The hand check below is used instead.

**Hand check on a circle** (radius r, inward normal, either orientation), using the file's definitions
`arcIntegral f = ∫ f·v du`, `support = v⟨γ, n⟩`, `signedArea = −½∫ support`:
- total curvature: κ = 1/r, v = r ⇒ ∫₀^{2π} κ v du = 2π ✓
- signed area: ⟨γ, n⟩ = −r, v = r ⇒ −½ ∫₀^{2π} (−r²) du = πr² = enclosed area ✓

Both statements have the right orientation and normalisation; neither is false in the obvious way.
