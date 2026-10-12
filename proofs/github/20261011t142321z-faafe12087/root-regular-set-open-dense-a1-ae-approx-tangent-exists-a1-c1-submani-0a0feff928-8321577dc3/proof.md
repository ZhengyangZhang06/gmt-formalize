# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_submanifold_tangent-a1`
- Child DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_submanifold_tangent-a1.chart_lower_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source (provenance only): step 2 of the parent proof (the lower bound (a)); the proof below is self-contained.
Notation: B_ρ(p) is the closed ball and B̆_ρ(p) the open ball; L := Dφ(v₀) = fderiv ℝ φ v₀.
1. Antilipschitz bound for L. L is a linear map on the finite-dimensional space ℝᵐ with trivial kernel (it is injective; LinearMap.ker_eq_bot). By LinearMap.exists_antilipschitzWith there is K > 0 such that L is K-antilipschitz; AntilipschitzWith.le_mul_dist applied to u and 0 gives ‖u‖ ≤ K‖Lu‖ for every u ∈ ℝᵐ. Put c := 1/(2K) > 0. Then 2c‖u‖ = ‖u‖/K ≤ ‖Lu‖ for every u.
2. Choice of δ. Since V is open and φ is C¹ on V, v ↦ Dφ(v) is continuous on V (ContDiffOn.continuousOn_fderiv_of_isOpen, 1 ≤ 1), hence continuous at v₀ ∈ V. Choose δ₁ > 0 with ‖Dφ(v) − L‖ < c whenever dist(v, v₀) < δ₁ (Metric.continuousAt_iff) and δ₂ > 0 with B̆_{δ₂}(v₀) ⊆ V (Metric.isOpen_iff). Put δ := min(δ₁, δ₂)/2 > 0. Then δ < δ₁ and δ < δ₂, so B_δ(v₀) ⊆ B̆_{δ₂}(v₀) ⊆ V (closedBall_subset_ball). This is the first assertion.
3. Differentiability on B_δ(v₀). φ is differentiable on V (ContDiffOn.differentiableOn, since the order 1 is nonzero). Every v ∈ B_δ(v₀) lies in the open set V, so φ is differentiable at v and has Fréchet derivative Dφ(v) there (DifferentiableOn.differentiableAt, DifferentiableAt.hasFDerivAt). Let g(v) := φ(v) − L(v − v₀). The map v ↦ L(v − v₀) has derivative L at every point (chain rule for the continuous linear map L after v ↦ v − v₀), so g has derivative Dφ(v) − L at every v ∈ B_δ(v₀) (HasFDerivAt.sub). For such v, dist(v, v₀) ≤ δ < δ₁, hence ‖fderiv ℝ g v‖ = ‖Dφ(v) − L‖ ≤ c.
4. Mean value inequality. Let w ∈ ℝᵐ with ‖w‖ ≤ δ. Then v₀ ∈ B_δ(v₀) and v₀ + w ∈ B_δ(v₀). The closed ball B_δ(v₀) is convex, so Convex.norm_image_sub_le_of_norm_fderiv_le, applied to g on B_δ(v₀) with the bound c of step 3, gives ‖g(v₀ + w) − g(v₀)‖ ≤ c‖(v₀ + w) − v₀‖ = c‖w‖. Since g(v₀ + w) − g(v₀) = φ(v₀ + w) − Lw − φ(v₀), this reads ‖φ(v₀ + w) − Lw − φ(v₀)‖ ≤ c‖w‖.
5. Conclusion. Since Lw = (φ(v₀ + w) − φ(v₀)) − (φ(v₀ + w) − Lw − φ(v₀)), the triangle inequality and steps 1 and 4 give 2c‖w‖ ≤ ‖Lw‖ ≤ ‖φ(v₀ + w) − φ(v₀)‖ + ‖φ(v₀ + w) − Lw − φ(v₀)‖ ≤ ‖φ(v₀ + w) − φ(v₀)‖ + c‖w‖. Hence c‖w‖ ≤ ‖φ(v₀ + w) − φ(v₀)‖ for every w with ‖w‖ ≤ δ.

## Key steps

1. L := Dφ(v₀) is injective on the finite-dimensional ℝᵐ, so ‖u‖ ≤ K‖Lu‖ for some K > 0; put c := 1/(2K)
2. continuity of Dφ at v₀ and openness of V give δ > 0 with B_δ(v₀) ⊆ V and ‖Dφ(v) − L‖ ≤ c on B_δ(v₀)
3. mean value inequality for g(v) = φ(v) − L(v − v₀) on the convex ball B_δ(v₀): ‖φ(v₀+w) − φ(v₀) − Lw‖ ≤ c‖w‖
4. triangle inequality with ‖Lw‖ ≥ 2c‖w‖ gives c‖w‖ ≤ ‖φ(v₀+w) − φ(v₀)‖

## Reference use

### local-project

Queries:
- `rg -n 'def IsC1Submanifold' <snapshot>/project/GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Submission.lean`
- `rg -n 'WeightedArea|AreaLipschitz|NormDet' <snapshot>/project/GMT/Ch05/`
- `cmp <snapshot>/project/GMT/Ch05/{Contract,Submission}.lean against workspace GMT/Ch05/{Contract,Submission}.lean`
- `grep -n 'def blowUpMap|def HasApproximateTangentSpaceAt' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n 'theorem integral_area_formula_of_injective_derivative|theorem continuous_normDet|theorem areaJacobianAt_eq_normDet' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/`
- `rg -n 'def normDet' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `rg -n 'theorem tendsto_integral_filter_of_dominated_convergence' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `rg -n 'theorem HasFDerivAt.lim' <snapshot>/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `rg -n 'theorem norm_image_sub_le_of_norm_fderiv_le' <snapshot>/mathlib/Mathlib/Analysis/Calculus/`
- `rg -n 'theorem LinearMap.exists_antilipschitzWith' <snapshot>/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `rg -n 'euclideanHausdorffMeasure_eq_volume' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem ContDiffOn.continuousOn_fderiv_of_isOpen' <snapshot>/mathlib/Mathlib/Analysis/Calculus/`
- `rg -l 'c1tan' <snapshot>/project ; rg -l -t lean 'c1tan' <snapshot>/mathlib/Mathlib`
- `grep -c c1tan dag.json ; git grep -l -E 'c1tan' <all 385 distinct ref tips> -- '*.lean'`
- `dag.json scan of lean_name/lean_statement matching approxTangent|blowUp|C1Sub|chart|HasApproximateTangentSpaceAt`
- `Lean probe after import GMT.Ch05.Submission: #check ContinuousLinearMap.normDet, Poincare.SimonGMT.Chapter02.areaJacobianAt, .integral_area_formula_of_injective_derivative, .continuous_normDet`
- `lake env lean Chal_0..4.lean, Leaf_{A,B,C,D,E}.lean, Assembly.lean, FullAssembly.lean, Sol_0..5.lean, DefHash_{Contract,Submission}.lean`
- `leaf_verification.check_source_delta(base, base + child block, name) for each child; git show 9f4dca65:GMT/Ch05/Submission.lean | grep ^import`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-c1-submani-3373b6823b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/parent_verification.py`
- `/runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/runtime.py`
- `/tmp/c1tan-dmcvwp/Chal_0.lean`
- `/tmp/c1tan-dmcvwp/Leaf_D.lean`
- `/tmp/c1tan-dmcvwp/FullAssembly.lean`
- `/tmp/c1tan-cand-0MAW2m/GMT/Ch05/Submission.lean`
- `/tmp/c1tan-cand-0MAW2m/Sol_5.lean`
- `/tmp/c1tan-cand-0MAW2m/DefHash_Submission.lean`

PINS. Project ea5607598f3133b40a13241f2e51517a8c6423cd (equal to workspace HEAD and to this node's proof base 4426c5c3 for Submission.lean), Mathlib 25730c7c759d108ef87ab70af2342a196760f79d, simongmt 2b3663083f3fe399b6296fb8eaee52169170e197. The snapshot Contract.lean and Submission.lean are byte-identical to the workspace copies.

FROZEN DEFINITIONS. IsC1Submanifold (Contract.lean:74) has: open V and W; ContDiffOn ℝ 1 φ V; InjOn φ V; φ '' V = W ∩ S; properness; injective fderiv on V. blowUpMap x r y = r⁻¹ • (y − x). HasApproximateTangentSpaceAt is finrank = n together with the 𝓝[>] 0 limit for every C_c test function. The child statements use these definitions exactly.

IMPORT CLOSURE. The area formula (simongmt Chapter02/WeightedArea.lean:151), continuous_normDet (AreaApproximation.lean:28), areaJacobianAt (Area.lean:35) and Mathlib's normDet (InnerProductSpace/NormDet.lean:69) all exist, but none is in the import closure of GMT.Ch05.Submission: no match for 'WeightedArea|AreaLipschitz|NormDet' in snapshot GMT/Ch05, and the Lean #check calls fail. The leaf gate forbids imports, so these tools are confined to the parent glue. An accepted parent (9f4dca65) already adds Chapter02 imports.

AVAILABLE TO LEAVES. Every Mathlib tool the children use is available after import GMT.Ch05.Submission: tendsto_integral_filter_of_dominated_convergence, HasFDerivAt.lim, norm_image_sub_le_of_norm_fderiv_le, LinearMap.exists_antilipschitzWith, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, ContDiffOn.continuousOn_fderiv_of_isOpen.

REUSE. Accepted DAG theorems aetp_c1_piece_approxTangent, tae_c1_chart_image_approxTangent and rsod_blowUp_setIntegral_eq have types different from every proposed child, so none is reused.

NAMES. The prefix rsod_c1tan_ has no match in dag.json, other node files, the snapshot project, snapshot Mathlib, GMT, simongmt, or any .lean file at the 385 distinct git ref tips.

LEAN RESULTS.
- All 5 child challenges elaborate.
- All 5 child proofs compile as single-theorem leaves; each passes check_source_delta and uses only propext, Classical.choice and Quot.sound.
- The parent assembly compiles with no sorry.
- The candidate Submission builds, and all 6 comparator-form solutions typecheck.
- The 80 frozen definition hashes are identical between Contract and the candidate.
