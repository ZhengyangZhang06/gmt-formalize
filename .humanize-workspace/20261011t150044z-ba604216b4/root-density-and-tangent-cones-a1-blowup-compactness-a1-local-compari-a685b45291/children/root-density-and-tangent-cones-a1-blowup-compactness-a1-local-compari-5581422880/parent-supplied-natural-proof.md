# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.carrier_facts-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1(b)–(c) and 3(a) of the parent proof (Simon Ch. 6, 2.11 and Remark 3.2(3), chapter-06.txt lines 297–301 and 763–766). The frozen type is byte-identical to that of dimred_mbl_pf_imrep_carrier_mass_support in another branch.
Notation: Hⁿ := μHE[n]. For a representation R = (M, θ, ξ) (IMRep univ n), μ_R := R.measure = θ·Hⁿ⌞M, so μ_R(B) = ∫⁻_{M∩B} θ dHⁿ for Borel B. For a current Y ∈ 𝒟_n(ℝ^P), spt Y = ℝ^P ∖ Z(Y), where the zero region Z(Y) is the union of all open W with closure(W) compact (and ⊆ ℝ^P) such that Y(ω) = 0 for every ω ∈ 𝒟ⁿ(ℝ^P) with tsupport ω ⊆ W (SimonGMT GeometricCurrentOn.support and zeroRegion). M_W(Y) = Y.massOn W is the supremum of ofReal(Y(ω)) over the admissible ω (ω ∈ 𝒟ⁿ(ℝ^P), tsupport ω ⊆ W, covectorEuclideanNorm(ω(z)) ≤ 1 for all z), and M(Y) = Y.mass = Y.massOn ℝ^P.
1. Closedness. For every Y₁ ∈ 𝒟_n(ℝ^P), Z(Y₁) is open, as a union of open sets (isOpen_zeroRegion); hence spt Y₁ = ℝ^P ∖ Z(Y₁) is closed. This is the first claim of part (2).
2. The mass vanishes off the support. Let Y be represented by R = (M, θ, ξ), K := spt Y and W := ℝ^P ∖ K, which is open by step 1. If ω is admissible for M_W(Y), then tsupport ω ⊆ W is disjoint from K = spt Y, so Y(ω) = 0 by the sibling vanish_off_support (U = ℝ^P, S = Y). Thus every element of the set whose supremum is M_W(Y) equals ofReal(0) = 0, and M_W(Y) = 0.
3. The carrier is null off the support. The sibling mass_eq_measure (U = ℝ^P open, W open, W ⊆ ℝ^P, R represents Y) gives μ_R(W) = M_W(Y) = 0, i.e. ∫⁻_{M∩W} θ dHⁿ = 0 (W is Borel). Since θ is ℕ-valued and θ(x) > 0 for x ∈ M (R.mult_pos), θ ≥ 1 on M, so Hⁿ(M ∩ W) = ∫⁻_{M∩W} 1 dHⁿ ≤ ∫⁻_{M∩W} θ dHⁿ = 0. As M ∖ spt Y = M ∩ W, Hⁿ(M ∖ spt Y) = 0.
4. Total mass. By definition M(Y) = M_{ℝ^P}(Y), and by mass_eq_measure with W = ℝ^P, M(Y) = μ_R(ℝ^P).
5. Finiteness for compact support. Suppose K = spt Y is compact. K is closed, hence Borel, so μ_R(ℝ^P) = μ_R(K) + μ_R(W) = μ_R(K) by step 3, and μ_R(K) = ∫⁻_{M∩K} θ dHⁿ < ∞ by R.locallyIntegrable_mult applied to the compact set K ⊆ ℝ^P. Hence μ_R(ℝ^P) ≠ ∞. Steps 3–5 prove part (1).
6. Support of a difference. Let Y₁, Y₂ ∈ 𝒟_n(ℝ^P) and x ∈ ℝ^P with x ∉ spt Y₁ ∪ spt Y₂. Then x ∈ Z(Y₁) ∩ Z(Y₂): there are open sets W₁, W₂ containing x, with compact closures, such that Y_i(ω) = 0 whenever tsupport ω ⊆ W_i (i = 1, 2). W := W₁ ∩ W₂ is open and contains x, and closure(W) ⊆ closure(W₁) is compact (a closed subset of a compact set) and contained in ℝ^P. If tsupport ω ⊆ W, then tsupport ω ⊆ W₁ and tsupport ω ⊆ W₂, so (Y₁ − Y₂)(ω) = Y₁(ω) − Y₂(ω) = 0 − 0 = 0 (the difference of currents in the contract's Sub instance is evaluated pointwise). Hence W is one of the sets forming Z(Y₁ − Y₂), x ∈ Z(Y₁ − Y₂) and x ∉ spt(Y₁ − Y₂). So spt(Y₁ − Y₂) ⊆ spt Y₁ ∪ spt Y₂, the second claim of part (2). ∎

## Key steps

1. Supports are complements of open zero regions, hence closed.
2. Y kills every admissible form supported in the open set ℝ^P ∖ spt Y (vanish_off_support), so M_{ℝ^P∖spt Y}(Y) = 0; by mass_eq_measure, ∫_{M∖spt Y} θ dHⁿ = 0 and, as θ ≥ 1 on M, Hⁿ(M ∖ spt Y) = 0.
3. mass_eq_measure with W = ℝ^P gives M(Y) = μ_R(ℝ^P); for compact spt Y, μ_R(ℝ^P) = μ_R(spt Y) = ∫_{M∩spt Y} θ dHⁿ < ∞.
4. A common relatively compact neighbourhood on which Y₁ and Y₂ vanish lies in the zero region of Y₁ − Y₂, so spt(Y₁ − Y₂) ⊆ spt Y₁ ∪ spt Y₂.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; read GMT/Ch07/Contract.lean, GMT/Ch07/README.md, PROBLEM.md and this node's parent-child-handoff.json, parent-supplied-plan.md, parent-supplied-natural-proof.md (proof identical to the handoff)`
- `grep '^theorem|^def|^structure|^abbrev|^instance' simongmt Poincare/SimonGMT/Chapter06/{Forms,Currents,Mass,CurrentLocalEquality,AffineCurrentPushforward}.lean and Chapter03/{Rectifiable,Differential}.lean`
- `grep '^theorem' simongmt Poincare/SimonGMT/Chapter02/{AreaLipschitz,AreaNoninjective,AreaCritical,AreaDomain,Area}.lean (weighted_area_formula_lipschitz_injOn, area_image_criticalSet_eq_zero, linear_area_formula)`
- `python3 -I scans of dag.json (995 nodes): lean_name/statement matching push|area|pullback|compContinuousLinearMap|mollif|fderiv|ContDiffOn; status and candidate_commit of dpf_pushforward_formula_current_exists, dpf_pushforward_formula_boundaryVanishes, dpf_smooth_approx_compact_perturbation, dpf_rectifiable_bilipschitz_pieces, covectorEuclideanNorm_gram_bounds, ptd_ae_approxTangent_iff_of_subset, ptd_piece_image_approxTangent_ae; parallel nodes dimred_mbl_pf_* and dor_lmb_pc_* (all decomposing); byte-identity comparisons; collision check of dtc_bc_lc_pf_* (none)`
- `git show <candidate_commit>:GMT/Ch07/Submission.lean | grep 'theorem Submission.<name>' for the six reused declarations (types identical); git log --all --oneline -S'dtc_bc_lc_pf_' (no match)`
- `read nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1/decomposition-v1.json, nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-comparison-a1/decomposition-v1.json, and the parent-child-handoff.json of the reused nodes (audited proofs)`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint|_overlay_accepted_children' /runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `grep Mathlib at the pin: exists_contDiff_support_eq_eq_one_iff, IsCompact.exists_cthickening_subset_open, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, MeasurableSet.image_of_continuousOn_injOn, LipschitzWith.ae_differentiableAt, ContDiffOn.continuousOn_fderiv_of_isOpen, norm_compContinuousLinearMap_le, ae_tendsto_average_norm_sub, ae_tendsto_measure_inter_div, norm_integral_le_of_norm_le, LipschitzOnWith.hausdorffMeasure_image_le, Filter.EventuallyEq.fderiv_eq, ContDiffBump.convolution_tendsto_right_of_continuous, Isometry.hausdorffMeasure_image, euclideanHausdorffMeasure_smul₀, LinearMap.euclideanHausdorffMeasure_image`
- `sed -n book/chapter-06.txt lines 395-540 and 760-870 (2.23-2.29, 3.1-3.10); book/chapter-03.txt lines 330-412 (2.1-2.6)`
- `lake env lean /tmp/pfdecomp/check/Types2.lean (12 child types in the scope from gmt-compare.py contract_scope); lake env lean /tmp/pfdecomp/check/Assembly2.lean with #print axioms; verifier lean_contract.validate_lean_statement on all 12 strings; topological sort of depends_on`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/PROBLEM.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-a685b45291/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-a685b45291/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/tmp/pfdecomp/check/Types2.lean`
- `/tmp/pfdecomp/check/Assembly2.lean`

The pinned SimonGMT library has currents, boundary, mass with the Euclidean coefficient norm, support and zero region, countable rectifiability, approximate tangent spaces and the Lipschitz area formula on ℝⁿ. It has only the affine push-forward, and no push-forward of integer multiplicity currents by C¹ maps. Comparator-accepted DAG declarations already prove, for compactly supported C¹ perturbations of the identity, that the push-forward formula defines a current and maps cycles to cycles (dpf_pushforward_formula_current_exists, dpf_pushforward_formula_boundaryVanishes). They are reused together with the node's four inherited dependencies (dtc_mass_eq_measure, dtc_vanish_off_support, cmc_imRep_locality_restrict_sub, rsd_cmr_support_subset_of_vanish), all with types identical to their accepted candidate commits. Five new types are byte-identical to the unaccepted dimred_mbl_pf_*/dor_lmb_pc_* nodes and get new unique names dtc_bc_lc_pf_*; c1_perturbation is new. All 12 types elaborate in the comparator scope, and a Lean assembly proves the exact frozen parent type from them using only propext, Classical.choice and Quot.sound.
