# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_tangent_cone_planar-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_tangent_cone_planar-a1.plane_ball_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the convention 'H²(Q ∩ B_ρ(y)) = ω_2ρ² for y ∈ Q' of the parent proof of `idtp_cone_tangent_cone_planar` (used in its step 10), proved here for every n. Notation: ℝ^P := Euclid P, Q := span(range τ).
1. (The parametrization.) Define ψ : Euclid n → ℝ^P by ψ(a) := Σ_i a_i τ_i. ψ is linear, and by orthonormality ‖ψ(a)‖² = Σ_{i,k} a_ia_k⟪τ_i, τ_k⟫ = Σ_i a_i² = ‖a‖², so ‖ψ(a)‖ = ‖a‖; hence ‖ψ(a) − ψ(b)‖ = ‖ψ(a − b)‖ = ‖a − b‖, i.e. ψ is an isometry.
2. (Range.) range ψ = Q: each ψ(a) is a linear combination of the τ_i, and conversely every z ∈ span(range τ) can be written z = Σ_i c_iτ_i (Submodule.mem_span_range_iff_exists_fun), i.e. z = ψ(c).
3. (The disc is the image of a ball.) Let y ∈ Q and ρ > 0; by step 2, y = ψ(b) for some b. Then ψ '' B_ρ(b) = B_ρ(y) ∩ Q: if ‖a − b‖ < ρ then ψ(a) ∈ Q and ‖ψ(a) − y‖ = ‖a − b‖ < ρ; conversely, if z ∈ B_ρ(y) ∩ Q then z = ψ(a) for some a and ‖a − b‖ = ‖ψ(a) − ψ(b)‖ = ‖z − y‖ < ρ.
4. (Measure.) Isometries preserve μHE[n] of images (Mathlib Isometry.euclideanHausdorffMeasure_image), so μHE[n](B_ρ(y) ∩ Q) = μHE[n](ψ '' B_ρ(b)) = μHE[n](B_ρ(b)), the latter computed in Euclid n. On Euclid n, μHE[n] = volume (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume), and volume is an additive Haar measure, so by Measure.addHaar_ball_of_pos, volume(B_ρ(b)) = ofReal(ρ^{finrank ℝ (Euclid n)})·volume(B_1(0)) = ofReal(ρ^n)·unitBallVolume n (finrank_euclideanSpace_fin; unitBallVolume n = volume(ball (0 : Euclid n) 1) by definition). Commuting the factors gives μHE[n](B_ρ(y) ∩ Q) = unitBallVolume n·ofReal(ρ^n). ∎

## Key steps

1. ψ(a) = Σ a_iτ_i is a linear isometry Euclid n → ℝ^P with range span(range τ).
2. For y = ψ(b) ∈ Q, ψ maps B_ρ(b) onto B_ρ(y) ∩ Q.
3. Isometries preserve μHE[n], μHE[n] = volume on Euclid n, and volume(B_ρ(b)) = ofReal(ρ^n)·unitBallVolume n (addHaar_ball_of_pos).

## Reference use

### local-project

Queries:
- `cat nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c77e317e89/{parent-child-handoff.json,parent-supplied-natural-proof.md,parent-supplied-plan.md}`
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; git show 1d91497:GMT/Ch07/Submission.lean | diff - GMT/Ch07/Contract.lean`
- `python3 scans of dag.json: lean_name/status/lean_statement of density_and_tangent_cones, dimred_minimizing_monotonicity, dimred_invariant_cone_splitting, dimred_one_dim_minimizing_cone, dimred_im_mass_measure, idtp_planar_cycle_eq_const_mul, dtc_blowUp_{algebra,imrep,massOn_image,testForm_corr}, moving_blowups, dtc_blowUp_compactness; accepted statements containing IsConeCurrent|MassMeasuresConverge|ConvergesWeakly|HasMassDensity; grep 'unitBallVolume', 'support = ∅', 'P < n' over all node statements`
- `python3 read of nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-v3.json and decomposition-scope-v3.json (sibling children and the parent's dependency closure)`
- `grep -n 'def \|structure \|abbrev ' simongmt/Poincare/SimonGMT/Chapter06/{Mass,CurrentLocalEquality,Currents,Forms}.lean (support, zeroRegion, VanishesOn, massOn, massAdmissibleOn, boundary, boundary_apply, exteriorDerivativeTestOn, GeometricCurrentOn.ext)`
- `grep -rn 'μHE\[|euclideanHausdorffMeasure_image|euclideanHausdorffMeasure_eq_volume|ext_of_integral_eq_on_compactlySupported|Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure|addHaar_ball_of_pos|map_linearDependent|isometryOfOrthonormal|ext_of_forall_integral_eq' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `sed -n 300,312p; 405,420p; 495,512p; 552,570p book/chapter-07.txt; grep -n 'A.4\|invarian' book/chapter-07.txt book/chapter-A.txt; sed -n 52,135p book/chapter-A.txt`
- `grep -c idtp_cttp_ dag.json; grep -rl idtp_cttp_ nodes decomposition-reopenings; grep -rl idtp_cttp_ .swarm-worktrees/*/gmt-ch07/GMT (all: no match)`
- `lake env lean /tmp/cttp_dec/check/{Stmts,Assembly,T1Proto,T3Proto,T4Proto,T5Proto}.lean; lake env lean /tmp/cttp_dec/verify/EndToEnd.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c77e317e89/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c77e317e89/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c77e317e89/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-scope-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-A.txt`
- `/tmp/cttp_dec/check/Stmts.lean`
- `/tmp/cttp_dec/check/Assembly.lean`
- `/tmp/cttp_dec/check/T1Proto.lean`
- `/tmp/cttp_dec/check/T3Proto.lean`
- `/tmp/cttp_dec/check/T4Proto.lean`
- `/tmp/cttp_dec/check/T5Proto.lean`
- `/tmp/cttp_dec/verify/EndToEnd.lean`

Pins match the manifest: workspace HEAD b4d606d, Mathlib 25730c7c, SimonGMT 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, and the proof base 1d91497 equals the contract.

Relevant findings:
- Accepted with exact types: dtc_blowUp_algebra, dtc_blowUp_imrep, dimred_im_mass_measure, dimred_cs_mi_hasMassDensity_unique, cone_current_imrep_measure_smul_image (cone scaling) and adr_rescaled_translate_tendstoUniformly.
- Speculative-ready or rlcr siblings in the dependency closure: density_and_tangent_cones, dimred_minimizing_monotonicity, dimred_invariant_cone_splitting and dimred_one_dim_minimizing_cone.
- codim1_subspace_ball_euclideanHausdorff states the plane-disc measure, but it is not accepted and belongs to another branch, so it is not reused. The disc measure becomes child plane_ball_measure under a unique name.
- Mathlib supplies: Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_ball_of_pos, MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported (Riesz uniqueness for regular measures), the instance Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure, AlternatingMap.map_linearDependent and LinearMap.isometryOfOrthonormal.
- Book: Theorem 3.1 is chapter-07.txt lines 302–309, Lemma 3.5 is 410–418, formula (10) is 556–568, and the ℝx-translation-invariance step of tangent objects of cones is in the proof of A.4, chapter-A.txt lines 125–131.
- No idtp_cttp_* name exists anywhere.

Lean: all five child statements elaborate. The sorry-stub assembly proves the exact frozen parent type with axioms propext, Classical.choice, Quot.sound and sorryAx from stubs only. Lean proofs of all five children (child 2 from the reviewer) elaborate with only the cited DAG results stubbed at their DAG types.
