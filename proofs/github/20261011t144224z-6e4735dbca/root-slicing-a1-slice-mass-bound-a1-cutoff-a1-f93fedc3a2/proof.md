# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_mass_bound-a1`
- Child DAG node: `root.slicing-a1.slice_mass_bound-a1.cutoff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 3(v) (the cut-off functions of Simon Ch. 6, 4.11, whose slope bound (1+ε)/(b−a) is printed there), with the construction indicated in the parent: mollify, with a radius smaller than κ, the piecewise linear function equal to 1 on (−∞, t−h+κ], to 0 on [t−κ, ∞) and linear in between.

Setting. t, h, ε ∈ ℝ with h > 0 and ε > 0. χ′ denotes deriv χ.

1. (Parameters.) Put κ := εh/(2(1+ε)). Since 0 < ε/(1+ε) < 1 we have 0 < κ < h/2, and h − 2κ = h − εh/(1+ε) = h/(1+ε) > 0, so 1/(h − 2κ) = (1+ε)/h. Put r := κ/2, so 0 < r < κ.

2. (Piecewise linear profile.) Define λ : ℝ → ℝ by λ(s) := min(1, max(0, (t − κ − s)/(h − 2κ))). Then λ is continuous and 0 ≤ λ ≤ 1. If s ≤ t − h + κ then (t − κ − s)/(h − 2κ) ≥ (h − 2κ)/(h − 2κ) = 1, so λ(s) = 1; if s ≥ t − κ then (t − κ − s)/(h − 2κ) ≤ 0, so λ(s) = 0. λ is the composition of the affine map s ↦ (t − κ − s)/(h − 2κ), which is Lipschitz with constant 1/(h − 2κ) = (1+ε)/h, with the 1-Lipschitz clamp u ↦ min(1, max(0, u)); hence |λ(s) − λ(s′)| ≤ ((1+ε)/h)|s − s′| for all s, s′.

3. (Mollifier.) Let ρ : ℝ → ℝ be a C^∞ function with ρ ≥ 0, ρ(y) = 0 for |y| ≥ r, and ∫ρ(y) dy = 1 (for instance ρ := (∫φ)⁻¹·φ for a `ContDiffBump` φ centred at 0 with outer radius r, which is C^∞, ≥ 0, has ∫φ > 0 and vanishes for |y| ≥ r; `ContDiffBump.normed` gives the same function but needs `import Mathlib.Analysis.Calculus.BumpFunction.Normed`). Define χ(s) := ∫ ρ(y) λ(s − y) dy, i.e. χ = ρ ⋆ λ.

4. (Smoothness.) ρ is C^∞ with compact support and λ is continuous, hence locally integrable; therefore χ = ρ ⋆ λ is C^∞ (`HasCompactSupport.contDiff_convolution_left`).

5. (Range.) Since ρ ≥ 0, ∫ρ = 1 and 0 ≤ λ ≤ 1, we get 0 = ∫ρ·0 ≤ χ(s) ≤ ∫ρ·1 = 1 for every s.

6. (Plateaus on open neighbourhoods.) Let O₁ := (−∞, t − h + κ − r) and O₂ := (t − κ + r, ∞). If s ∈ O₁ and ρ(y) ≠ 0, then |y| < r, so s − y < t − h + κ and λ(s − y) = 1 by step 2; hence χ(s) = ∫ρ(y)·1 dy = 1. If s ∈ O₂ and ρ(y) ≠ 0, then s − y > t − κ, so λ(s − y) = 0 and χ(s) = 0. Thus χ ≡ 1 on O₁ and χ ≡ 0 on O₂. Because κ − r = r > 0, O₁ ⊇ (−∞, t − h] and O₂ ⊇ [t, ∞); in particular χ(s) = 1 for s ≤ t − h and χ(s) = 0 for s ≥ t.

7. (Slope bound.) For all s, s′: |χ(s) − χ(s′)| = |∫ρ(y)(λ(s − y) − λ(s′ − y)) dy| ≤ ∫ρ(y)·((1+ε)/h)|s − s′| dy = ((1+ε)/h)|s − s′|, using step 2 and ∫ρ = 1. So χ is Lipschitz with constant (1+ε)/h. χ is differentiable at every s (step 4), and the derivative of a function that is Lipschitz with constant K has absolute value at most K (`norm_deriv_le_of_lipschitz`, applied with the constant C := Real.toNNReal((1+ε)/h), whose coercion to ℝ is (1+ε)/h because (1+ε)/h > 0): |χ′(s)| = lim_{u→0} |χ(s+u) − χ(s)|/|u| ≤ (1+ε)/h for every s.

8. (Vanishing derivative off (t − h, t).) Let s ∉ (t − h, t). Then s ≤ t − h or s ≥ t, so s ∈ O₁ or s ∈ O₂ by step 6. χ is constant on that open set, which is a neighbourhood of s, hence χ′(s) = 0.

9. (Conclusion.) Steps 4–8 show that χ is C^∞, 0 ≤ χ ≤ 1, χ(s) = 1 for s ≤ t − h, χ(s) = 0 for s ≥ t, |χ′(s)| ≤ (1+ε)/h for all s, and χ′(s) = 0 for all s ∉ (t − h, t). ∎

## Key steps

1. κ := εh/(2(1+ε)) gives 1/(h−2κ) = (1+ε)/h; the clamped affine profile λ equals 1 on (−∞, t−h+κ], 0 on [t−κ, ∞) and is Lipschitz with constant (1+ε)/h.
2. χ := ρ ⋆ λ for a normalized C^∞ bump ρ ≥ 0 supported in (−κ/2, κ/2): χ is C^∞ and 0 ≤ χ ≤ 1.
3. χ ≡ 1 on the open set (−∞, t−h+κ/2) ⊇ (−∞, t−h] and χ ≡ 0 on (t−κ/2, ∞) ⊇ [t, ∞).
4. Convolution with a probability density preserves the Lipschitz constant, so |χ′| ≤ (1+ε)/h; χ′ = 0 off (t−h, t) since χ is locally constant there.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean workspaces/gmt-ch06/GMT/Ch06/Submission.lean (identical); cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (identical)`
- `rg -n 'slicing_mb_' local-references/197bdd4b88278494/project (no match)`
- `rg -n 'theorem norm_deriv_le_of_lipschitz|theorem LipschitzOnWith.extend_real|theorem LipschitzWith.ae_differentiableAt|theorem Monotone.ae_differentiableAt|theorem MonotoneOn.intervalIntegrable_deriv|theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc|theorem liminf_const_mul_of_ne_top|theorem hasDerivAt_integral_of_dominated_loc_of_lip|HasCompactSupport.contDiff_convolution_left|theorem alternatizeUncurryFin_apply|theorem tendsto_measure_biInter_gt|theorem Orthonormal.exists_orthonormalBasis_extension_of_card_eq|theorem fderiv_fun_smul|theorem ofReal_integral_eq_lintegral_ofReal|theorem tendsto_integral_filter_of_dominated_convergence' local-references/197bdd4b88278494/mathlib/Mathlib/{Analysis,Order,MeasureTheory,Topology,LinearAlgebra}`
- `grep -n 'covectorEuclideanNorm|def massAdmissibleOn|def GeometricCurrentOn.massOn|abbrev Covector|abbrev DifferentialForm|def IsTestForm|abbrev exteriorDerivative|abbrev TestFormOn|structure GeometricCurrentOn|boundary_apply|tsupport_exteriorDerivative_subset|abbrev NVector' simongmt/Poincare/SimonGMT/Chapter06/{Mass,Forms,Currents,FormsDuality}.lean`
- `python3 scan of dag.json (200 nodes): lean_name uniqueness of the seven proposed names; search of titles/statements/lean_statements for alternatizeUncurryFin, smulRight, liminf, Monotone, cut-off, mollif, wedge, Dini, McShane, Rademacher (no identical type)`
- `python3 read of nodes/root-slicing-a1-slice-mass-bound-a1/{parent-child-handoff.json, decomposition-v3.json, decomposition-audit-v1..v4.json, decomposition-review-receipt-v1..v4.json}`
- `python3 read of .humanize/swarm-configs/*.json for github_selected_issue 676: 97b6c024c2834d99b1a86982198ed548.json max_nodes=1000 max_depth=6 (older 9bd566bbce374e36839dbfed5b2a4b01.json max_nodes=200)`
- `contract_scope/child_modules in verifier/gmt-compare.py (replayed child scope)`
- `lake env printenv LEAN_PATH; lean -o /tmp/smb_split_v5_bWB45t/out/GMT/Ch06/Submission.olean GMT/Ch06/Submission.lean`
- `lean /tmp/smb_split_v5_bWB45t/check/Stmts.lean (7 child types + parent in the comparator child scope: 0 errors)`
- `lean /tmp/smb_split_v5_bWB45t/check/Instances.lean (wedge degree m+1, operator norms by rfl, C^∞ index)`
- `lean /tmp/smb_split_v5_bWB45t/check/Assembly.lean (#print axioms HumanizeNodeComparator.assembly: [propext, Classical.choice, Quot.sound])`
- `lean /tmp/smb_split_v5_bWB45t/check/Plumbing.lean (dependency instantiations type-check)`
- `lean /tmp/smb_split_v5_bWB45t/check/Names.lean (#check of every lemma cited in the child proofs)`
- `sed -n '1340,1415p' book/chapter-06.txt (Simon Ch. 6, 4.6–4.11)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/decomposition-audit-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/swarm-configs/97b6c024c2834d99b1a86982198ed548.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/smb_split_v5_bWB45t/check/Stmts.lean`
- `/tmp/smb_split_v5_bWB45t/check/Instances.lean`
- `/tmp/smb_split_v5_bWB45t/check/Assembly.lean`
- `/tmp/smb_split_v5_bWB45t/check/Plumbing.lean`
- `/tmp/smb_split_v5_bWB45t/check/Names.lean`

The pinned snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract, and it is byte-identical to the workspace Submission, so child types may use only contract, SimonGMT and Mathlib names. SimonGMT supplies GeometricCurrentOn with boundary ∂T(ω) = T(dω), massOn via covectorEuclideanNorm, TestFormOn, exteriorDerivative (Mathlib's extDeriv, i.e. alternatizeUncurryFin ∘ fderiv) and tsupport_exteriorDerivative_subset. Mathlib supplies McShane extension (LipschitzOnWith.extend_real), Rademacher's theorem (LipschitzWith.ae_differentiableAt), convolution smoothness, differentiation under the integral, Lebesgue's theorem for monotone functions with the integral bound for their derivative, liminf algebra in ℝ≥0∞, dominated convergence along countably generated filters and continuity from above. Every cited name exists at the pinned revision. Neither library contains the sharp cut-off, the wedge coefficient-norm bound, the smooth approximation with an a.e. gradient bound, the slice estimates or the Dini-derivative majorant; these become the seven children. In a scratch compile of the frozen Submission, all seven child types and the parent type elaborate in the comparator's child scope. The exact parent follows from slicing_mass_representation, slicing_representation_unique, slicing_mb_pointwise and slicing_mb_density_majorant with axioms [propext, Classical.choice, Quot.sound], and the dependency instantiations type-check. No proposed name occurs in the snapshot project or among the 200 DAG nodes. The active issue-676 configuration allows 1000 nodes at depth ≤ 6. The printed Simon text (4.9–4.11) matches the supplied proof.
