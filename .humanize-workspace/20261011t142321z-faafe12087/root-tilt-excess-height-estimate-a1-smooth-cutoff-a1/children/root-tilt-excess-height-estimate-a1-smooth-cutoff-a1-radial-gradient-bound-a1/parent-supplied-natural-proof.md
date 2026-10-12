# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_height_estimate-a1.smooth_cutoff-a1`
- Child DAG node: `root.tilt_excess_height_estimate-a1.smooth_cutoff-a1.radial_gradient_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 7 of the parent's supplied proof ("ζ is (3/ρ)-Lipschitz ... hence ‖fderiv ℝ ζ x‖ <= 3/ρ"), with the constant 3 replaced by a general K ∈ ℝ≥0.

1. Lipschitz estimate. Let y, z ∈ R^m.
  - The Lipschitz property of φ and ρ > 0 give
    |ζ(y) − ζ(z)| <= K·|‖y − ξ‖/ρ − ‖z − ξ‖/ρ| = (K/ρ)·|‖y − ξ‖ − ‖z − ξ‖|.
  - The reverse triangle inequality (abs_norm_sub_norm_le) gives |‖y − ξ‖ − ‖z − ξ‖| <= ‖(y − ξ) − (z − ξ)‖ = ‖y − z‖.
  - Hence |ζ(y) − ζ(z)| <= (K/ρ)·‖y − z‖ = (K/ρ)·dist(y, z).

2. So ζ is Lipschitz on all of R^m with the nonnegative constant K/ρ.
  - In Lean: LipschitzWith (K / ρ.toNNReal) ζ, via LipschitzWith.of_dist_le_mul and step 1.
  - The real value of the ℝ≥0 constant K / ρ.toNNReal is (K : ℝ)/ρ. This follows from NNReal.coe_div together with Real.coe_toNNReal (ρ.toNNReal coerces back to ρ because ρ >= 0).

3. If a function on a normed space is C-Lipschitz everywhere, its Fréchet derivative has operator norm at most C at every point (norm_fderiv_le_of_lipschitz). At points where it is not differentiable, fderiv is 0 and the bound is trivial. Applying this with C = K / ρ.toNNReal at x, and rewriting C as (K : ℝ)/ρ by step 2, gives ‖fderiv ℝ ζ x‖ <= K/ρ. ∎

## Key steps

1. |ζ(y) − ζ(z)| <= (K/ρ)|‖y − ξ‖ − ‖z − ξ‖| <= (K/ρ)‖y − z‖ (Lipschitz φ, ρ > 0, abs_norm_sub_norm_le)
2. ζ is LipschitzWith (K / ρ.toNNReal), whose real value is K/ρ (LipschitzWith.of_dist_le_mul, NNReal.coe_div, Real.coe_toNNReal)
3. norm_fderiv_le_of_lipschitz gives ‖fderiv ℝ ζ x‖ <= K/ρ at every x

## Reference use

### local-project

Queries:
- `rg -n '^(theorem|lemma|protected theorem|nonrec theorem|def|noncomputable def)' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `rg -n 'theorem contDiff_infty_iff_deriv|theorem contDiff_top_iff_deriv|theorem contDiffAt_norm\b|theorem norm_fderiv_le_of_lipschitz\b|theorem norm_fderiv_le_of_lipschitzOn|theorem lipschitzWith_of_nnnorm_deriv_le|theorem integral_hasDerivAt_right\b|theorem integral_hasStrictDerivAt\b|theorem integral_mono_interval|theorem integral_add_adjacent_intervals\b|theorem contDiff_iff_contDiffAt\b|theorem lipschitzWith_one_norm|theorem LipschitzWith.norm|theorem ContDiffAt.congr_of_eventuallyEq|theorem contDiffAt_const\b' -g '*.lean' <snapshot>/mathlib/Mathlib`
- `rg -n 'lipschitzWith_of_nnnorm_deriv_le|lipschitzWith_of_nnnorm_fderiv_le|theorem integral_hasStrictDerivAt\b|integral_hasDerivAt\b|theorem _root_.Continuous.integral_hasStrictDerivAt|deriv_integral_right' -g '*.lean' <snapshot>/mathlib/Mathlib`
- `rg -n -g '*.lean' 'exists_smooth_step_profile_lipschitz_three|contDiff_radial_profile_of_eq_one_le_half|norm_fderiv_radial_profile_le_of_lipschitzWith' <snapshot>/project <snapshot>/mathlib/Mathlib`
- `grep -c 'exists_smooth_step_profile_lipschitz_three\|contDiff_radial_profile_of_eq_one_le_half\|norm_fderiv_radial_profile_le_of_lipschitzWith' dag.json; python3 -I scan of dag.json nodes[*].lean_name`
- `rg -n -g '*.lean' 'exists_smooth_step_profile_lipschitz_three|contDiff_radial_profile_of_eq_one_le_half|norm_fderiv_radial_profile_le_of_lipschitzWith|smoothTransition|norm_fderiv_le_of_lipschitz|cutoff' lake-packages-25730c7c/simongmt/Poincare`
- `rg -n -g '*.lean' 'def scaledRadialCutoff|def monotonicityCutoff|theorem monotonicityCutoff|theorem scaledRadialCutoff|LipschitzWith' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04`
- `diff GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean; diff GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean`
- `sed -n 190,290p book/chapter-05.txt (proof of Simon 5.2.1: choice of the cutoff)`
- `lean GMT/Ch05/Submission.lean -o /tmp/smooth-cutoff-decomp/build/GMT/Ch05/Submission.olean; lean Scope.lean (3 frozen child types in replayed comparator scope); lean Assembly.lean (frozen parent type from the 3 child types as hypotheses); lean Profile.lean Radial.lean Radial2.lean (trial child proofs); lean AllChildren.lean (Submission.* children + parent + exact Submission.X checks + #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1-smooth-cutoff-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1-smooth-cutoff-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/smooth-cutoff-decomp/check/Scope.lean`
- `/tmp/smooth-cutoff-decomp/check/Assembly.lean`
- `/tmp/smooth-cutoff-decomp/check/AllChildren.lean`

Pinned versions: the snapshot manifest pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The snapshot project/GMT/Ch05/Contract.lean is byte-identical to the workspace Contract.lean, which is identical to Submission.lean.

No match for the proposed names: none of the three occurs in the snapshot project, the snapshot Mathlib, the SimonGMT sources, or any dag.json lean_name.

No reusable cutoff exists. SimonGMT Chapter04/FirstVariation.lean has only two cutoffs, neither with a Lipschitz or derivative bound, so neither gives the 3/ρ estimate:
- the squared-radius scaledRadialCutoff ξ φ ρ x = φ(‖x−ξ‖²/ρ²);
- monotonicityCutoff ε t = 1 − smoothTransition((t−1)/ε).
Also smoothTransition has S'(1/2) = 2 (checked numerically), so the direct profile 1 − S(2t−1) has slope 4 > 3. That is why the integral construction is needed.

The pinned Mathlib supplies every tool the child proofs cite:
- Real.smoothTransition.{one_of_one_le, zero_of_nonpos, le_one, nonneg, contDiff} (SmoothTransition.lean:161–205);
- contDiff_infty_iff_deriv (ContDiff/Deriv.lean:103);
- Continuous.integral_hasStrictDerivAt and intervalIntegral.integral_hasDerivAt_right (FundThmCalculus.lean:656, 725);
- intervalIntegral.integral_mono_interval and integral_add_adjacent_intervals (IntervalIntegral/Basic.lean:1405, 1095);
- lipschitzWith_of_nnnorm_deriv_le (MeanValue.lean:743);
- contDiff_iff_contDiffAt and ContDiffAt.congr_of_eventuallyEq (ContDiff/Defs.lean:1103, 966);
- contDiffAt_const (ContDiff/Basic.lean:111);
- contDiffAt_norm (InnerProductSpace/Calculus.lean:154);
- norm_fderiv_le_of_lipschitz (FDeriv/Basic.lean:947).

Book source: chapter-05.txt (proof of 2.1) only says to choose ζ ≡ 1 in B_{ρ/2}(0), ζ ≡ 0 outside B_ρ(0), with |∇ζ| ≤ 3/ρ, and gives no construction. So the child proofs are extracted from the parent's supplied construction.

Lean checks:
- All 3 frozen child types elaborate in the replayed comparator scope.
- The frozen parent type is proved sorry-free from them.
- Trial proofs of all children, the assembled parent, and the exact Submission.X checks pass with axioms [propext, Classical.choice, Quot.sound]. An independent reviewer reproduced this with its own Lean files (ACCEPT).
