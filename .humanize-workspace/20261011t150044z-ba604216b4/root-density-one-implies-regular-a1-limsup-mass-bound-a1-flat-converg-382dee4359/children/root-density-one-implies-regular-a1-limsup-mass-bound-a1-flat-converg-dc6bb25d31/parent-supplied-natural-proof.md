# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1.isometric_pushforward-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1.isometric_pushforward-a1.orientation_transport-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent-supplied proof (unit orientations are transported). This is the Jacobian-one case of Simon Ch. 6, 3.4–3.5 and 3.7 (book/chapter-06.txt lines 785–835): for an isometric L, L_#(τ₁ ∧ ⋯ ∧ τ_d) = Lτ₁ ∧ ⋯ ∧ Lτ_d is again a unit simple d-vector.
1. L preserves norms and inner products. L is linear, so L0 = 0, and the isometry property gives |Lx| = |x| for all x (Isometry.norm_map_of_map_zero). Therefore L is a linear isometry ℝ^P →ₗᵢ ℝ^Q, and ⟨Lx, Ly⟩ = ⟨x, y⟩ for all x, y by polarization (LinearIsometry.inner_map_map).
2. Unpack the hypothesis. IsUnitOrientationOf ξ S gives τ : Fin d → ℝ^P with τ orthonormal and span(range τ) = S. Moreover either (+) ξ(α) = α(τ) for every d-covector α of ℝ^P, or (−) ξ(α) = −α(τ) for every such α.
3. The new frame. Let τ' := L∘τ = (Lτ₀, …, Lτ_{d−1}). By step 1, ⟨Lτ_i, Lτ_j⟩ = ⟨τ_i, τ_j⟩ = δ_ij, so τ' is orthonormal (Orthonormal.comp_linearIsometry).
4. The new span. range τ' = L(range τ) (Set.range_comp). The span of the image of a set under a linear map is the image of its span (Submodule.span_image). Hence span(range τ') = (span(range τ)).map L = S.map L.
5. The sign identity. Let β be a d-covector of ℝ^Q. By definition of composition of continuous linear maps (ContinuousLinearMap.comp_apply) and of L^* (ContinuousAlternatingMap.compContinuousLinearMapCLM_apply), ((∧L)ξ)(β) = ξ(L^*β) with L^*β = β.compContinuousLinearMap L. Also (L^*β)(v) = β(L∘v) for every v : Fin d → ℝ^P (ContinuousAlternatingMap.compContinuousLinearMap_apply), so (L^*β)(τ) = β(τ').
 In case (+), the hypothesis with α = L^*β gives ((∧L)ξ)(β) = (L^*β)(τ) = β(τ') for every β.
 In case (−) it gives ((∧L)ξ)(β) = −(L^*β)(τ) = −β(τ') for every β.
6. Conclusion. By steps 3–5, τ' is orthonormal, spans S.map L, and satisfies the same sign alternative for (∧L)ξ. This is IsUnitOrientationOf ((∧L)ξ) (S.map L). The argument is uniform in d; for d = 0, τ and τ' are empty and both spans are {0}. ∎

## Key steps

1. L preserves norms and hence inner products: it is a linear isometry.
2. τ' = L∘τ is orthonormal and span(range τ') = span(L(range τ)) = S.map L.
3. ((∧L)ξ)(β) = ξ(β∘L) = ±(β∘L)(τ) = ±β(τ'), with the same sign as for ξ.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean <workspace>/GMT/Ch07/Submission.lean (identical)`
- `rg -n "dtop_ip_|isometry_change_of_variables|approxTangent_isometry|unitOrientation_isometry|image_imrep" <snapshot>/project .lake/packages/simongmt --glob '*.lean' (no match)`
- `rg -n -i "isometr" and rg -n "affinePushforward" <snapshot>/project/GMT --glob '*.lean' (only Ch05 rotated-plane docstrings and the Ch07 contract's blowUp)`
- `read SimonGMT Chapter03/Rectifiable.lean (CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt), Chapter06/AffineCurrentPushforward.lean (affinePullbackForm, affinePullbackTestOn, affinePushforward_apply rfl), Chapter06/Mass.lean (massOn, mass = massOn U), Chapter06/Forms.lean and Currents.lean`
- `rg Isometry.map_euclideanHausdorffMeasure / Isometry.euclideanHausdorffMeasure_image in <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (lines 131, 141)`
- `rg MeasurableEmbedding.restrict_map, ae_map_iff, restrict_restrict_of_subset, integral_map, lintegral_map, aestronglyMeasurable_map_iff, IsClosedEmbedding.measurableEmbedding, Isometry.isClosedEmbedding, Isometry.lipschitzWith, IsClosedEmbedding.isProperMap, HasCompactSupport.comp_isClosedEmbedding, Orthonormal.comp_linearIsometry, adjoint_inner_left, span_image, equivMapOfInjective, Continuous.clm_comp, withDensity_apply, setIntegral_congr_fun, image_inter_preimage in <snapshot>/mathlib/Mathlib`
- `python3 -I scans of the run's dag.json (1552 nodes): HasApproximateTangentSpaceAt / IsUnitOrientationOf / Isometry / affinePushforward statements and the types of dtc_blowUp_imrep, dtc_hausdorff_dilation, dtc_approxTangent_dilation, dpfir_bilipschitz_image_imrep_exists, dpf_approxTangent_bilipschitz_image_ae, dpf_unitOrientation_map_gramNormalized, codim1_rdo_gc_unitOrientation_isometry, dor_imrep_massOn_eq_measure_and_support; collision check of the four new lean_names`
- `git show 047b3402ecebcae7b968f8ca435cbbb0b9ed036f:GMT/Ch07/Submission.lean (lines 455-740, accepted dtc_blowUp_imrep template)`
- `sed -n 395,440p and 765,880p book/chapter-06.txt (Simon 6.2.23-2.24, 6.3.3-3.9)`
- `python3 -I gen.py: gmt-compare.py child_modules (contract scope) + lean_contract.validate_lean_statement on the four types; lake env lean /tmp/isopf-decomp/challenges/Challenge_*.lean and /tmp/isopf-decomp/lean/{Stmts,Assembly,Full,SolutionCheck,Names}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Maps/Proper/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Span/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/Submodule/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-382dee4359/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-b4c8dbc0a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/isopf-decomp/lean/Full.lean`
- `/tmp/isopf-decomp/lean/SolutionCheck.lean`

Snapshot: project b4d606db and Mathlib 25730c7c. Its Ch07 Contract.lean is byte-identical to the workspace Submission.lean.

No-match results:
- No snapshot or SimonGMT declaration transports Hausdorff measure, approximate tangent spaces, unit orientations or IMReps along a linear isometric embedding ℝ^P → ℝ^Q.
- Accepted DAG lemmas only treat self-maps of ℝ^P (dilations, bi-Lipschitz/C¹ diffeomorphisms) or plane parametrisations, so none can be reused for P ≠ Q.
- None of the four new names occurs in dag.json, the snapshot or SimonGMT.

The children use only snapshot Mathlib:
- Isometry.map_euclideanHausdorffMeasure, Isometry.euclideanHausdorffMeasure_image, Isometry.isClosedEmbedding;
- the MeasurableEmbedding API (restrict_map, integral_map, lintegral_map, ae_map_iff, aestronglyMeasurable_map_iff);
- HasCompactSupport.comp_isClosedEmbedding, Orthonormal.comp_linearIsometry, Submodule.span_image, ContinuousLinearMap.adjoint.

From SimonGMT they use affinePullbackForm, affinePullbackTestOn and affinePushforward_apply.

The accepted dtc_blowUp_imrep is the structural template.

Lean results:
- All four child types compile as the exact comparator challenges.
- Full proofs of all four children check with only propext, Classical.choice and Quot.sound.
- The exact selected type follows in 7 lines from image_imrep and the accepted dor_imrep_massOn_eq_measure_and_support.
