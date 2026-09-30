# OpenGauss run log

Record of every OpenGauss attempt on Chapter 3 of `MTL603_PDE_project-9-13.pdf`. Every run is
reported, including partial ones; none are dropped.

## Common setup (all runs)

| | |
|---|---|
| Orchestrator | OpenGauss (`math-inc/OpenGauss`), `/autoformalize` → lean4-skills `autoformalize` workflow |
| Backend | Codex CLI v0.158.0, ChatGPT-subscription login |
| Model | GPT-6-Astra, **reasoning effort: low** (per Codex `/status` in run 2; Gauss runs Codex from its own managed config at `~/.gauss/autoformalize/codex/managed/codex-home/`, so the user's `~/.codex/config.toml` setting did not apply). Run 1 is assumed to have used the same managed config. Codex account: Plus. |
| Environment | WSL2 Ubuntu on Windows, project at `~/csf-opengauss` |
| Lean / Mathlib | Lean v4.28.0; Mathlib `v4.28.0`. `lake-manifest.json` is byte-identical to the Aristotle project's (checked with `cmp`). |
| Starting state | Empty `RequestProject/`, plus the PDF, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` (baseline commit). No Aristotle output present. |
| Instruction | Aristotle's instruction verbatim, except the PDF is named by file rather than attached: "Fully formalize the contents of MTL603_PDE_project-9-13.pdf. For each formal declaration, add a docstring that clearly and explicitly references the corresponding informal declaration in the original source file." |

## Run 1 — 28 Sep 2026 (git tag `run1`)

**How it was started.** `/autoformalize` in Gauss with the plain-English instruction only. Gauss forwarded
this to the workflow as `/lean4:autoformalize <instruction>` (see `run1-logs/20260928-153718-autoformalize.md`).
The workflow reported that `--source`, `--claim-select` and `--out` were missing and did nothing. The flags
were then sent as a follow-up chat message inside the running Codex session:
```
--source=MTL603_PDE_project-9-13.pdf --claim-select=regex:".*" --out=RequestProject/CSF.lean
--rigor=checked --draft-mode=attempt --max-total-runtime=360m
```

**Flags were only partly applied.** The workflow's own session summary shows a runtime budget of
**120 min (the default), not 360**, and the output went to `PDE.lean`, not the requested `CSF.lean`. So at
least `--max-total-runtime` and `--out` were not picked up from the follow-up message; whether `--rigor` and
`--draft-mode` were is not recorded. Run 1 should be read as "approximately default settings". (Run 2 passes
the flags directly on the `/autoformalize` line to avoid this.)

**Timeline and budget.** Started ~15:37. Workflow elapsed at stop: 521 s (tracker 8m/120m); Codex reported
10 min 31 s of agent work. 9 cycles in total, 3 consecutive stuck, **0 deep invocations** (default
`--deep=stuck` did not trigger a deep pass before the stuck limit).

**Resource use:** Codex tokens — total 130,169 (input 115,902 + 3,107,968 cached; output 14,267, of which
reasoning 3,145). Context 116K / 258K at end. Codex 5-hour limit 61% remaining afterwards; weekly 94%.
Codex session `01a0e8aa-d58a-7060-b626-fee28889e826`; workflow session `lean4-session-58DIvR`;
Gauss session `20260928_153605_424d8b`.

**Output.** `RequestProject/PDE.lean` (2 definitions, 8 theorems, a docstring on every one citing lemma and
page) and `RequestProject/PDE-status.md` (the agent's own coverage table and blocker review). Independently
checked: no `sorry`, `admit` or `axiom` in the file. Agent reports `lake build` OK (3111 jobs) and only standard
axioms on all 10 declarations — `#print axioms` still to be rerun by us.

**Claim queue:** 9 entries (Lemmas 1–6, length/area monotonicity, extinction time, Theorem 3.0.1); 6 attempted.
Stopped on Lemma 6(ii) (`max-stuck`) after searching Mathlib for a Green's theorem on Jordan domains, the
Hopf Umlaufsatz, and a homotopy/curve-integral route — none available. See `AUDIT_run1.md` for what the
proved statements actually cover.

**Other deviations:** the workflow's auto-commit failed (git identity unset). No separate baseline commit
existed, so tag `run1` is the repository's root commit and contains the setup files and run 1's output together.

## Run 2 — 28 Sep 2026 (git tag `run2`) — completed (`queue-empty`), 2 `sorry` remaining

**Start.** Branch `run2` from `run1` with run 1's output removed in commit `6e7ec9b`, and `.lake/build` cleared
(Mathlib packages kept). Same model, instruction and Gauss/Codex setup. Flags passed directly on the
`/autoformalize` line:
`--source=MTL603_PDE_project-9-13.pdf --claim-select=regex:".*" --out=RequestProject/CSF.lean --rigor=checked
--draft-mode=attempt --max-total-runtime=360m --max-stuck-cycles=8 --deep=always`.
The workflow echoed all of these back as resolved ("No ignored flags or startup validation errors").

**Interruption.** Stopped mid-run when the Codex 5-hour usage limit reached 0% (reset at 20:38; weekly limit 84% left; context 152K / 258K used). Codex session `01a0e8cc-2bd5-72b0-9293-96ae4d36bb8e`. Resumed by using one Codex usage-limit reset (instead of waiting for 20:38), then a single `continue` message in the same session — the only intervention in run 2. No
workflow commits had been made at that point. The working file was copied, without touching the repo, to
`run2-snapshot-at-limit/RequestProject/CSF.lean`. We did not switch to a smaller model, to keep the run
single-model. Plan: resume the same session after the limit resets with a single `continue` message, and log
it here as the only intervention.

**State at the limit (snapshot, 626 lines, 3 `sorry`).** Last agent message: length evolution, length
monotonicity, the signed-area integral calculation and the scalar extinction-time calculation (conditional
on zero area at the endpoint) were checked; two geometric steps for enclosed area were still open.
- A `Flow` structure for a regular planar CSF: position, tangent, normal, speed and curvature as fields, with
  `∂γ/∂t = κn` and the spatial Frenet equation `∂T/∂u = vκn` as fields (the latter *defines* the curvature),
  plus explicit mixed-partial symmetry fields.
- Lemmas 1–6(i) proved for that structure (no longer only local algebraic cores as in run 1), including
  `curvature_evolution`, `length_evolution`, `length_antitoneOn`.
- Lemma 6(ii): `signedArea_evolution` (integration by parts) proved; `enclosedArea` defined as the true
  Lebesgue area of the bounded complementary component. The two links are stated as theorems and left
  as `sorry`: `signedArea_eq_enclosedArea` (Green's theorem on a Jordan region) and
  `total_curvature_eq_two_pi` (Hopf's Umlaufsatz). `enclosedArea_evolution` (`dA/dt = −2π`) is proved *from*
  these two.
- After Lemma 6: `area_affine`, `area_strictAntiOn`, `lifetime_le_of_nonnegative_area`,
  `extinction_time_of_zero_area` proved (the last conditional on `A(T) = 0`, like Aristotle's `hlim`).
  `enclosedArea_nonneg` is proved outright, since the area is a measure.
- Theorem 3.0.1: `ClassicalClosedFlow` structure (continuity at `t = 0`, CSF for `t > 0`) and
  `embeddedness_preserved` stated; the `t = 0` case is proved, the `t > 0` case is `sorry`.

**Final result (after resuming).** Workflow stop reason: `queue-empty` (all 9 claims attempted). Agent's summary:
Lemmas 1–5, Lemma 6(i) and Theorem 3.0.1 proved; 2 `sorry` remain, both geometric inputs to Lemma 6(ii)
(Green's theorem on the Jordan region, and total turning = 2π). Sorries 0 → 2. Agent reports `lake build`
passes and that the embeddedness theorem is sorry-free (independent check: `run2-axioms.txt`).
Output: `RequestProject/CSF.lean`, `RequestProject/CSF.coverage.md`. The workflow's auto-commit failed again
(the managed shell uses its own `HOME`, so the global git identity was not visible); committed manually as tag `run2`.

**Run 2 metrics.**

| | |
|---|---|
| Claims attempted | 9 / 9 |
| Cycles / stuck / deep invocations | 12 / 1 / 4 |
| Workflow elapsed | 63 min (across the quota pause) |
| Codex work after resume | 26 min 9 s, ending 17:20 |
| Gauss session wall-clock | 1 h 21 min (includes the pause) |
| Codex tokens | total 352,210 (input 282,696 + 10,272,256 cached; output 69,514, of which reasoning 27,383) |
| Interventions | one Codex usage-limit reset + one `continue` message |
