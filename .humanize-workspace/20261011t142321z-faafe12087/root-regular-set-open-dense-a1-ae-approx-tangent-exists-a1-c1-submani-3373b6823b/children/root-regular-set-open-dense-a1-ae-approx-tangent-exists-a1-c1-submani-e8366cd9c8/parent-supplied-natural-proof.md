# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_submanifold_tangent-a1`
- Child DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_submanifold_tangent-a1.approx_tangent_local-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source (provenance only): step 4 of the parent proof, first half: since f vanishes off B := B_R(0), ∫_{η_{x,r}(S)} f = ∫_{η_{x,r}(S) ∩ B} f, and for rR < ε the sets η_{x,r}(S) ∩ B and η_{x,r}(W ∩ S) ∩ B coincide. Here it is stated for any two sets that agree near x.
Notation: η_{x,r}(y) := blowUpMap x r y = r⁻¹(y − x); B_ρ(p) closed ball, B̆_ρ(p) open ball; all integrals are with respect to Hᵐ = μHE[m] on ℝ^N.
1. Dimension. finrank P = m is the first component of the hypothesis for T.
2. Support radius. Fix f ∈ C_c(ℝ^N, ℝ). tsupport f is compact, hence bounded, so tsupport f ⊆ B_{R₀}(0) for some R₀. Put R := max(R₀, 1) > 0 and B := B_R(0). Then f(y) = 0 for y ∉ B.
3. Cutting off. For every set A ⊆ ℝ^N, ∫_A f = ∫_{A ∩ B} f. Indeed f = 1_B·f pointwise by step 2, and setIntegral_indicator gives ∫_A 1_B f = ∫_{A ∩ B} f; it only needs B measurable (B is closed). No measurability of A is needed.
4. The cut-off blow-ups agree. Let 0 < r < ε/R, so rR < ε. First, if A ∩ B̆_ε(x) ⊆ A′, then η_{x,r}(A) ∩ B ⊆ η_{x,r}(A′) ∩ B. Indeed, let y = r⁻¹(z − x) with z ∈ A and ‖y‖ ≤ R. Since r > 0, ‖y‖ = r⁻¹‖z − x‖, so ‖z − x‖ ≤ rR < ε. Thus z ∈ A ∩ B̆_ε(x) ⊆ A′ and y ∈ η_{x,r}(A′). Apply this with (A, A′) = (T, S), using T ∩ B̆_ε(x) = S ∩ B̆_ε(x) ⊆ S, and with (A, A′) = (S, T), using S ∩ B̆_ε(x) = T ∩ B̆_ε(x) ⊆ T. Hence η_{x,r}(T) ∩ B = η_{x,r}(S) ∩ B.
5. Conclusion. For 0 < r < ε/R, steps 3 and 4 give ∫_{η_{x,r}(S)} f = ∫_{η_{x,r}(S) ∩ B} f = ∫_{η_{x,r}(T) ∩ B} f = ∫_{η_{x,r}(T)} f. The interval (0, ε/R) belongs to 𝓝[>] 0 (Ioo_mem_nhdsGT), so the two functions of r agree eventually as r → 0⁺. By hypothesis, ∫_{η_{x,r}(T)} f → ∫_P f as r → 0⁺; hence ∫_{η_{x,r}(S)} f → ∫_P f as well (Tendsto.congr'). Since f was arbitrary and finrank P = m, HasApproximateTangentSpaceAt m S x P holds.

## Key steps

1. finrank P = m is inherited from T
2. f vanishes off B = B_R(0), so ∫_A f = ∫_{A ∩ B} f for every A (setIntegral_indicator)
3. for 0 < r < ε/R, η_{x,r}(S) ∩ B = η_{x,r}(T) ∩ B because S and T agree on B̆_ε(x)
4. the blow-up integrals of S and T agree eventually as r → 0⁺, so the limit transfers

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
