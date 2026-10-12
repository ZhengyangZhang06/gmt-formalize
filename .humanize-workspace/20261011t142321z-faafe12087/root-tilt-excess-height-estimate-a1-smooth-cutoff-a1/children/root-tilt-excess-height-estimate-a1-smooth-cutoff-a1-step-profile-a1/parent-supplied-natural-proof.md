# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_height_estimate-a1.smooth_cutoff-a1`
- Child DAG node: `root.tilt_excess_height_estimate-a1.smooth_cutoff-a1.step_profile-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1–4 of the parent's supplied proof, which build the profile φ of the cutoff ζ(x) = φ(‖x − ξ‖/ρ). The Lipschitz estimate is from its step 3. In Lean, ContDiff ℝ (⊤ : ℕ∞) means C^infinity, and LipschitzWith 3 φ (3 : ℝ≥0) means |φ(s) − φ(t)| <= 3|s − t|.

Let S := Real.smoothTransition. Mathlib (Analysis/SpecialFunctions/SmoothTransition.lean) gives:
- S is C^infinity (Real.smoothTransition.contDiff);
- 0 <= S <= 1 (Real.smoothTransition.nonneg, Real.smoothTransition.le_one);
- S(s) = 0 for s <= 0 (Real.smoothTransition.zero_of_nonpos);
- S(s) = 1 for s >= 1 (Real.smoothTransition.one_of_one_le).

1. The bump g. Define g(t) := S(12(t − 1/2)) · S(12(1 − t)) for t ∈ R.
  (a) g is C^infinity. The maps t ↦ 12(t − 1/2) and t ↦ 12(1 − t) are affine, hence C^infinity. Composing them with S and multiplying keeps C^infinity. In particular g is continuous, so it is interval-integrable on every interval.
  (b) 0 <= g(t) <= 1 for every t, as a product of two numbers in [0, 1].
  (c) If t <= 1/2, then 12(t − 1/2) <= 0, so the first factor is 0 and g(t) = 0. If t >= 1, then 12(1 − t) <= 0, so the second factor is 0 and g(t) = 0.
  (d) If 7/12 <= t <= 11/12, then 12(t − 1/2) >= 12·(1/12) = 1 and 12(1 − t) >= 12·(1/12) = 1. Both factors equal 1, so g(t) = 1.

2. The normalizing constant. Let c := ∫_{1/2}^{1} g(s) ds.
  - By 1(d), ∫_{7/12}^{11/12} g = ∫_{7/12}^{11/12} 1 ds = 11/12 − 7/12 = 1/3 (intervalIntegral.integral_congr with the constant 1 on [7/12, 11/12]).
  - We have 1/2 <= 7/12 <= 11/12 <= 1, g >= 0 by 1(b), and g is integrable on [1/2, 1]. So the integral over the subinterval is at most the integral over the whole interval (intervalIntegral.integral_mono_interval): 1/3 <= c.
  - Hence c > 0 and c^{-1} <= 3.

3. The profile and its derivative. Define φ(t) := 1 − c^{-1} ∫_{1/2}^{t} g(s) ds (oriented interval integral).
  (a) g is continuous, so by the fundamental theorem of calculus (Continuous.integral_hasStrictDerivAt, or intervalIntegral.integral_hasDerivAt_right) u ↦ ∫_{1/2}^{u} g has derivative g(t) at every t. So φ is differentiable at every t with φ'(t) = −c^{-1} g(t). That is, φ is differentiable on R and deriv φ = −c^{-1}·g.
  (b) φ is C^infinity. By contDiff_infty_iff_deriv, ContDiff ℝ ∞ φ holds iff φ is differentiable and deriv φ is C^infinity. The first holds by (a). The second holds by (a) and 1(a), since a constant multiple of g is C^infinity.
  (c) φ is 3-Lipschitz. For every t, |φ'(t)| = c^{-1} g(t) <= c^{-1} · 1 <= 3, by 1(b) and step 2. A differentiable function R → R whose derivative has absolute value at most 3 everywhere is 3-Lipschitz, by the mean value inequality (lipschitzWith_of_nnnorm_deriv_le).

4. Values of φ.
  (a) Case t <= 1/2. Every s between t and 1/2 has s <= 1/2, so g(s) = 0 by 1(c). Hence ∫_{1/2}^{t} g = 0 (intervalIntegral.integral_congr with the zero function) and φ(t) = 1 − c^{-1}·0 = 1.
  (b) Case t >= 1. By additivity over adjacent intervals (intervalIntegral.integral_add_adjacent_intervals; g is integrable on both pieces), ∫_{1/2}^{t} g = ∫_{1/2}^{1} g + ∫_{1}^{t} g. The second integral is 0, since g(s) = 0 for every s ∈ [1, t] by 1(c). So ∫_{1/2}^{t} g = c and φ(t) = 1 − c^{-1}c = 0 (as c ≠ 0).
  (c) Case 1/2 < t < 1.
    - g >= 0 and 1/2 <= t give ∫_{1/2}^{t} g >= 0 (intervalIntegral.integral_nonneg).
    - g >= 0 and [1/2, t] ⊆ [1/2, 1] give ∫_{1/2}^{t} g <= ∫_{1/2}^{1} g = c (intervalIntegral.integral_mono_interval).
    - Multiplying by c^{-1} > 0 gives 0 <= c^{-1} ∫_{1/2}^{t} g <= c^{-1}c = 1, so 0 <= φ(t) <= 1.
  Every real t falls in one of these three cases. In cases (a) and (b), φ(t) ∈ {1, 0} ⊆ [0, 1]. Hence 0 <= φ(t) <= 1 for all t.

5. Conclusion. φ satisfies every required property:
  - C^infinity, by 3(b);
  - values in [0, 1], by 4;
  - equal to 1 for t <= 1/2, by 4(a);
  - equal to 0 for t >= 1, by 4(b);
  - 3-Lipschitz, by 3(c). ∎

(Remark: in fact c = 5/12 by the symmetry S(s) + S(1 − s) = 1, but only c >= 1/3 is used.)

## Key steps

1. With S = Real.smoothTransition, g(t) = S(12(t − 1/2))·S(12(1 − t)) is C^∞, 0 <= g <= 1, g = 0 for t <= 1/2 and for t >= 1, and g = 1 on [7/12, 11/12]
2. c = ∫_{1/2}^{1} g >= ∫_{7/12}^{11/12} 1 = 1/3 (intervalIntegral.integral_mono_interval), so c > 0 and c^{-1} <= 3
3. φ(t) = 1 − c^{-1}∫_{1/2}^{t} g has deriv φ = −c^{-1} g by FTC (Continuous.integral_hasStrictDerivAt), so φ is C^∞ by contDiff_infty_iff_deriv
4. |φ'| = c^{-1} g <= c^{-1} <= 3, so φ is 3-Lipschitz (lipschitzWith_of_nnnorm_deriv_le)
5. φ = 1 for t <= 1/2 (g vanishes on [t, 1/2]); φ = 0 for t >= 1 (adjacent intervals, g vanishes on [1, t]); 0 <= φ <= 1 for 1/2 < t < 1 since 0 <= ∫_{1/2}^{t} g <= c

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
