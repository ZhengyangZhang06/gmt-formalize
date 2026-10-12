# Parent-supplied natural-language proof

- Parent DAG node: `root.affine_approximation-a1.lp_monotonicity-a1`
- Child DAG node: `root.affine_approximation-a1.lp_monotonicity-a1.curvature_holder-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the Hoelder step of Simon, Ch. 4, 4.2-4.3. The parent proof uses it in Step 3 (with psi = phi_epsilon(r/rho)) and in Step 5b (with psi = the indicator of B_t(y)).
Notation:
 - B := B_t(y), the closed ball.
 - ||H||_t := (integral_B |H|^p dmu)^(1/p), a finite real number by hypothesis.
 - q := p/(p - 1) > 1, so 1/p + 1/q = 1 and 1/q = 1 - 1/p.

1. Supports, measurability, integrability.
 - psi vanishes outside B, hence so does f(x) := psi(x)(x - y).H(x). Therefore integral f dmu = integral_B f dmu and integral psi dmu = integral_B psi dmu.
 - psi is integrable: it is a.e. strongly measurable, 0 <= psi <= 1_B, and mu(B) < infinity. In particular integral psi dmu >= 0.
 - On B, f is a.e. strongly measurable for mu restricted to B. Indeed, psi is a.e. strongly measurable, x -> x - y is continuous, and H is a.e. strongly measurable on B because it is integrable there.
 - On B, |f| <= t |H|, which is integrable. So f is integrable.

2. Pointwise bound. For x in B, Cauchy-Schwarz and |x - y| <= t give
 |psi(x)(x - y).H(x)| <= psi(x) |x - y| |H(x)| <= t psi(x) |H(x)|.
 Hence |integral f dmu| <= t integral_B psi |H| dmu.

3. Hoelder. On the measure space (B, mu restricted to B), |H| and psi are nonnegative and a.e. strongly measurable. Moreover |H| is in L^p, since integral_B |H|^p dmu < infinity, and psi is in L^q, being bounded on a set of finite measure. Hoelder's inequality with the conjugate exponents p and q gives
 integral_B psi |H| dmu <= ||H||_t (integral_B psi^q dmu)^(1/q).

4. Removing the power of psi. Since 0 <= psi <= 1 and q >= 1, psi^q <= psi pointwise. So integral_B psi^q dmu <= integral_B psi dmu = integral psi dmu. As s -> s^(1/q) is nondecreasing on [0, infinity) and 1/q = 1 - 1/p,
 (integral_B psi^q dmu)^(1/q) <= (integral psi dmu)^(1 - 1/p).

5. Conclusion. Steps 2-4 give
 |integral psi(x)(x - y).H(x) dmu| <= t ||H||_t (integral psi dmu)^(1 - 1/p),
 which is the claim. Both sides are real numbers and t >= 0.

## Key steps

1. psi and the pairing psi(x)(x-y).H(x) vanish off B_t(y). Both are integrable, since mu(B_t(y)) < infinity and H is in L^1(B_t(y)).
2. On B_t(y), |psi (x-y).H| <= t psi |H|.
3. Hoelder on B_t(y) with exponents p and q = p/(p-1): integral psi|H| <= ||H||_t (integral psi^q)^(1/q).
4. psi^q <= psi because 0 <= psi <= 1. So (integral psi^q)^(1/q) <= (integral psi)^(1-1/p).

## Reference use

### local-project

Queries:
- `timeout 300 rg -n "aal_radial|radial_first_variation|curvature_pairing|integrating_factor|monotonicity_of_radial" <snapshot>/project`
- `timeout 300 rg -n "^theorem integral_mul_le_Lp_mul_Lq_of_nonneg|^theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le|^theorem tendsto_integral_filter_of_dominated_convergence|^theorem integral_hasDerivAt_right|^theorem integral_integral_swap|^theorem integral_eq_sub_of_hasDerivAt\b|^lemma starProjection_orthogonal'|^theorem norm_starProjection_apply_le|^theorem contDiffAt_norm|^theorem intervalIntegrable_rpow'|^theorem integral_rpow" <snapshot>/mathlib/Mathlib`
- `timeout 300 rg -n "theorem trace_smulRight|protected theorem contDiff|protected theorem monotone|theorem zero_of_nonpos|theorem one_of_one_le" <snapshot>/mathlib/Mathlib/LinearAlgebra/Trace.lean <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `timeout 300 rg -n "theorem setIntegral_nonneg_of_ae_restrict|theorem lintegral_mono_set|theorem measure_mono" <snapshot>/mathlib/Mathlib`
- `timeout 300 rg -n "theorem LocallyIntegrableOn.integrableOn_compact_subset|theorem isBoundedBilinearMap_apply|protected theorem prodMk" <snapshot>/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean <snapshot>/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `grep -n "^theorem\|^def\|^structure\|^private theorem" .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/{FirstVariation,LpMeanCurvature,LpCancellation,MeanCurvature,LpAnnular}.lean`
- `python3 -I: verifier/lean_contract.py validate_lean_statement on the four child types; string comparison of the assembled aal_lp_monotonicity and aal_tangent_structure types against the handoff files`
- `lake env lean /tmp/claude-1000/lpm-check/Check.lean (contract lines 1-459 + sorried aal_tangent_structure and four children + sorry-free assembly of Submission.aal_lp_monotonicity + example instantiating children 2 and 3 inside child 4's context)`
- `lake env lean /tmp/claude-1000/lpm-check/CheckAx.lean (#print axioms GMT.Ch05.Submission.aal_lp_monotonicity with children as axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpAnnular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpCancellation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/claude-1000/lpm-check/Check.lean`
- `/tmp/claude-1000/lpm-check/CheckAx.lean`

Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d.

No existing declarations: the snapshot project has no match for the proposed child names or their topics.

Mathlib tools located for the children (paths under mathlib/Mathlib):
- Child 2: integral_mul_le_Lp_mul_Lq_of_nonneg (MeasureTheory/Integral/Bochner/Basic.lean:1230), Hölder.
- Child 3: hasDerivAt_integral_of_dominated_loc_of_deriv_le (Analysis/Calculus/ParametricIntegral.lean:286); integral_hasDerivAt_right (IntervalIntegral/FundThmCalculus.lean:725) and integral_eq_sub_of_hasDerivAt (:1148) for the FTC; integral_integral_swap (MeasureTheory/Integral/Prod.lean:478) for Fubini; intervalIntegrable_rpow' (SpecialFunctions/Integrability/Basic.lean:47).
- Child 4: tendsto_integral_filter_of_dominated_convergence (MeasureTheory/Integral/DominatedConvergence.lean:67); integral_rpow (SpecialFunctions/Integrals/Basic.lean:146); smoothTransition contDiff/monotone/zero_of_nonpos/one_of_one_le (Analysis/SpecialFunctions/SmoothTransition.lean:161-222).
- Child 1: contDiffAt_norm (Analysis/InnerProductSpace/Calculus.lean:154); LinearMap.trace_smulRight (LinearAlgebra/Trace.lean:272).
- Parent assembly: starProjection_orthogonal' (InnerProductSpace/Projection/Basic.lean:223); norm_starProjection_apply_le (:411); LocallyIntegrableOn.integrableOn_compact_subset (MeasureTheory/Function/LocallyIntegrable.lean:122); isBoundedBilinearMap_apply (Normed/Operator/BoundedLinearMaps.lean:391); AEStronglyMeasurable.prodMk (AEStronglyMeasurable.lean:256); setIntegral_nonneg_of_ae_restrict (Bochner/Set.lean:809).

Pinned SimonGMT Chapter04 (outside the snapshot):
- Directly usable, stated for any finite-dimensional E and Submodule P: trace_starProjection, trace_radialEndomorphism and inner_starProjection_eq_norm_sq (FirstVariation.lean:122-157) for child 1; monotonicityCutoff = 1 - smoothTransition((t-1)/eps) and its lemmas (FirstVariation.lean:825-870) for child 4.
- Patterns to adapt from SimonGMT's own varifold structure to an abstract finite measure: hasDerivAt_integral_scaledRadialCutoff_mul (FirstVariation.lean:680) and cancelledCutoffMass_squeeze (LpCancellation.lean:400).
- Not used: exists_lpAnnularCorrection (LpAnnular.lean:358). It is the same result for the strengthened Chapter04.RectifiableVarifold, and the supplied proof deliberately avoids that bridge. The printed Simon Ch. 4, 3.2-3.6 and 4.1-4.8 (book/chapter-04.txt) matches Steps 0-6.

Lean checks:
- Check.lean compiles. All four child types elaborate in the contract scope and pass validate_lean_statement.
- The sorry-free assembly of the exact frozen aal_lp_monotonicity type typechecks from children 1 and 4 plus aal_tangent_structure.
- The example shows child 4 can instantiate children 2 and 3.
- CheckAx.lean: #print axioms lists only propext, Classical.choice, Quot.sound and the three used declarations.
