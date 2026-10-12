# Parent-supplied natural-language proof

- Parent DAG node: `root.weighted_monotonicity-a1`
- Child DAG node: `root.weighted_monotonicity-a1.kernel_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. E := Ambient n ℓ = EuclideanSpace ℝ (Fin (n+ℓ)) = ℝ^{n+ℓ} with its Borel σ-algebra; B_s(ξ) := closedBall ξ s is the CLOSED ball; r = r(x) := |x − ξ|; λ is Lebesgue measure on ℝ and ∫_{(a,b]} means the integral over Ioc a b; φ' := deriv φ. This is Step 5 of the parent proof (the corrected prefactors of Simon 3.5: on the support of the τ-derivative, s^{-n} ≤ τ^{-n} ≤ (1+ε)ⁿ s^{-n}).
1. (Properties of φ'.) φ' is continuous. φ' ≤ 0 everywhere, because φ is differentiable and nonincreasing (Antitone.deriv_nonpos). φ'(t) = 0 for t < 1 and for t > 1 + ε, because φ is constant (1, resp. 0) on the open sets (−∞, 1) and (1 + ε, ∞). Hence φ'(t) ≠ 0 implies 1 ≤ t ≤ 1 + ε.
2. (The function g.) For τ > 0 let g(τ) := φ(s/τ). Since d/dτ(s/τ) = −s/τ², the chain rule gives that g is differentiable at every τ > 0 with g'(τ) = −(s/τ²)φ'(s/τ); g' is continuous on [σ, ρ] ⊂ (0, ∞), and g'(τ) ≥ 0 because s/τ² ≥ 0 and φ'(s/τ) ≤ 0.
3. (Fundamental theorem of calculus.) ∫_{(σ,ρ]} g'(τ)dτ = ∫_σ^ρ g'(τ)dτ = g(ρ) − g(σ) = φ(s/ρ) − φ(s/σ) (intervalIntegral.integral_of_le, intervalIntegral.integral_eq_sub_of_hasDerivAt; g' is continuous, hence interval integrable, on [σ, ρ]).
4. (Pointwise bounds.) For τ ∈ (σ, ρ]: g'(τ)/sⁿ ≤ g'(τ)/τⁿ ≤ (1 + ε)ⁿ·(g'(τ)/sⁿ). If g'(τ) = 0 all three terms vanish. Otherwise φ'(s/τ) ≠ 0, so by 1, 1 ≤ s/τ ≤ 1 + ε, i.e. τ ≤ s ≤ (1 + ε)τ (τ > 0). Then τⁿ ≤ sⁿ gives 1/sⁿ ≤ 1/τⁿ, and sⁿ ≤ (1 + ε)ⁿτⁿ gives 1/τⁿ ≤ (1 + ε)ⁿ/sⁿ; multiplying by g'(τ) ≥ 0 gives the two inequalities.
5. (Integration.) The three functions τ ↦ g'(τ)/sⁿ, g'(τ)/τⁿ, (1 + ε)ⁿg'(τ)/sⁿ are continuous on [σ, ρ], hence integrable on (σ, ρ]; by 4 and monotonicity of the integral (setIntegral_mono_on), (1/sⁿ)∫_{(σ,ρ]}g' ≤ ∫_{(σ,ρ]}g'(τ)/τⁿdτ ≤ ((1 + ε)ⁿ/sⁿ)∫_{(σ,ρ]}g'. The middle integral is k(s), since g'(τ)/τⁿ = −(s/τ²)φ'(s/τ)/τⁿ, and by 3 the outer ones equal (φ(s/ρ) − φ(s/σ))/sⁿ and (1 + ε)ⁿ(φ(s/ρ) − φ(s/σ))/sⁿ. This is the claim.

## Key steps

1. φ' continuous, φ' ≤ 0, and φ'(t) ≠ 0 only for 1 ≤ t ≤ 1 + ε
2. g(τ) = φ(s/τ) has g'(τ) = −(s/τ²)φ'(s/τ) ≥ 0 on (0, ∞)
3. FTC: ∫_{(σ,ρ]} g' = φ(s/ρ) − φ(s/σ)
4. Where g' ≠ 0: τ ≤ s ≤ (1+ε)τ, so s^{-n} ≤ τ^{-n} ≤ (1+ε)ⁿ s^{-n}
5. Integrate the pointwise squeeze over (σ, ρ]

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `rg -n 'def weight|def tangentialGradient|def normalRadialSq|def IsTestField|def HasMeanCurvatureIn' <snapshot>/project/GMT/Ch04/Contract.lean`
- `rg -n 'theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le|theorem integral_integral_swap|theorem continuousOn_of_dominated|theorem tendsto_integral_filter_of_dominated_convergence|theorem _root_.aestronglyMeasurable_of_tendsto_ae|theorem _root_.IsCompact.exists_cthickening_subset_open|theorem cthickening_closedBall|theorem LocallyIntegrableOn.integrableOn_compact_subset|theorem integral_eq_sub_of_hasDerivAt|theorem MeasureTheory.AEStronglyMeasurable.comp_snd|theorem norm_starProjection_apply_le|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem _root_.Continuous.comp_aestronglyMeasurable₂|theorem isBoundedBilinearMap_apply|theorem contDiffAt_norm|theorem ContDiffOn.continuousOn_fderiv_of_isOpen|theorem fderiv_of_notMem_tsupport' <snapshot>/mathlib/Mathlib`
- `rg -n "starProjection_orthogonal'|Antitone.deriv_nonpos|StronglyMeasurable.integral_prod_right" <snapshot>/mathlib/Mathlib`
- `rg -n 'zero_of_nonpos|one_of_one_le|protected theorem monotone' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `grep -n -E '^(theorem|lemma|def|private theorem)' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/{FirstVariation,WeightedFirstVariation,WeightedCutoff,WeightedRadiusIntegration,WeightedBallIntegration,MeanCurvature,LogarithmicError}.lean`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/wm-a1-decomp/olean/GMT/Ch04/Submission.olean`
- `python3 -I /tmp/wm-a1-decomp/scripts/gen.py (verifier/gmt-compare.py contract_scope + child_modules; verifier/lean_contract.validate_lean_statement)`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/wm-a1-decomp/olean lean /tmp/wm-a1-decomp/gen/Challenge_*.lean`
- `LEAN_PATH=... lean /tmp/wm-a1-decomp/probe/Parse.lean (set_option pp.notation false)`
- `LEAN_PATH=... lean /tmp/wm-a1-decomp/probe/Assembly.lean (sorry'd children + radial_first_variation, parent glue)`
- `LEAN_PATH=... lean /tmp/wm-a1-decomp/val/Full.lean (sorry-free proofs of all six children, glue, exact-Submission targets, #print axioms)`
- `lake env lean /tmp/wm-a1-decomp/probe/SimonAx.lean (#print axioms of SimonGMT monotonicityCutoff lemmas, contDiff_smul_of_tsupport_subset, exists_larger_closedBall_subset)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/WeightedFirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/WeightedCutoff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/LogarithmicError.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-weighted-monotonicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/tmp/wm-a1-decomp/val/Full.lean`
- `/tmp/wm-a1-decomp/probe/Assembly.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (sha256 6e58e5dd…0f4770b, project commit ff75f52a, mathlib 25730c7c). The definitions used here (weight, tangentialGradient = p_x(gradient h), normalRadialSq, IsTestField, HasMeanCurvatureIn with its L¹_loc conjunct) are at project/GMT/Ch04/Contract.lean lines 103–166. Every analytic tool the children need is in the snapshot Mathlib: hasDerivAt_integral_of_dominated_loc_of_deriv_le (Calculus/ParametricIntegral.lean:286); integral_integral_swap and AEStronglyMeasurable.comp_snd (Integral/Prod.lean:478, 135); StronglyMeasurable.integral_prod_right (Integral/Prod.lean:67); continuousOn_of_dominated (Integral/Bochner/Basic.lean:467); tendsto_integral_filter_of_dominated_convergence (Integral/DominatedConvergence.lean:67); integral_eq_sub_of_hasDerivAt (FundThmCalculus.lean:1148); setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:486); LocallyIntegrableOn.integrableOn_compact_subset (LocallyIntegrable.lean:122); aestronglyMeasurable_of_tendsto_ae and Continuous.comp_aestronglyMeasurable₂ (AEStronglyMeasurable.lean:696, 263); IsCompact.exists_cthickening_subset_open (Thickening.lean:426) with cthickening_closedBall (Ball/Pointwise.lean:318); starProjection_orthogonal' and norm_starProjection_apply_le (Projection/Basic.lean:223, 411); isBoundedBilinearMap_apply; contDiffAt_norm; ContDiffOn.continuousOn_fderiv_of_isOpen; fderiv_of_notMem_tsupport; Antitone.deriv_nonpos; and Real.smoothTransition with zero_of_nonpos, one_of_one_le and monotone. SimonGMT's Chapter04 monotonicity chain (FirstVariation.lean cutoff_squeeze, stationaryMonotonicity_real, hasDerivAt_integral_mul_of_compact; WeightedCutoff.lean; LogarithmicError.lean) is stated for SimonGMT's own Chapter04.RectifiableVarifold structure, not for the contract's quotient type, so it cannot be applied to V. Its V-independent helpers (monotonicityCutoff lemmas, contDiff_smul_of_tsupport_subset, exists_larger_closedBall_subset) depend only on propext, Classical.choice and Quot.sound, and they match the constructions used here. All six child types elaborate in the comparator's contract scope, and all six have complete sorry-free Lean proofs with only standard axioms. The selected frozen theorem compiles from them plus a sorry'd radial_first_variation at its frozen dag.json type, and exact-Submission NodeSolution targets compile for every child and for the selected node.
