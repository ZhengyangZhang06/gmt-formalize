# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1`
- Child DAG node: `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.restriction_open_im-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: (6d) and (7a) of the parent proof (“the same argument with the open set A_γ shows that R_k = τ(M′_k ∩ A_γ, θ′_k, ξ′_k) is i.m.”), stated for an arbitrary open set A.

1. Data. Since X is integer multiplicity there are M, θ, ξ such that (M, θ, ξ) is a rectifiable triple in U of dimension k (IsRectifiableTriple U k M θ ξ), θ(x) ∈ ℕ for every x ∈ M, and X(ω) = tauAction(M, θ, ξ)(ω) = ∫_M θ ξ(ω) dHᵏ for every ω ∈ D^k(U).

2. Formula for R. By the comparator-accepted declaration Submission.polyhedral_approx_restriction_tau (U open), every restriction R of X to a set A satisfies R(ω) = tauAction(M ∩ A, θ, ξ)(ω) for all ω ∈ D^k(U). (Not needed; an alternative route: (Hᵏ⌞M, θξ) is a measure representation of X, with integrability from Submission.ltg_tau_integrable; R is given by some representation (μ₁, v₁) of X; Submission.slicing_representation_unique with W := U shows that both representations have the same integral over the measurable set A, and ∫_A θξ(ω) d(Hᵏ⌞M) = tauAction(M ∩ A, θ, ξ)(ω).)

3. (M ∩ A, θ, ξ) is a rectifiable triple in U. A is open, hence measurable.
 - subset: M ∩ A ⊆ M ⊆ U.
 - null-measurability: M is Hᵏ-null-measurable and A is measurable, so M ∩ A is Hᵏ-null-measurable.
 - countable k-rectifiability: M ∩ A ⊆ M (CountablyRectifiable.mono).
 - positivity: θ > 0 on M ∩ A ⊆ M.
 - local integrability: for compact K ⊆ U, θ is Hᵏ-integrable on M ∩ K, hence on the subset (M ∩ A) ∩ K (IntegrableOn.mono_set).
 - measurability of ξ: ξ is AE-strongly measurable for Hᵏ⌞M, hence for Hᵏ⌞(M ∩ A) ≤ Hᵏ⌞M (Measure.restrict_mono).
 - orientation: the orients property of (M, θ, ξ) holds Hᵏ⌞M-a.e., hence Hᵏ⌞(M ∩ A)-a.e. (ae_restrict_of_ae_restrict_of_subset), and Hᵏ⌞(M ∩ A)-a.e. x lies in M ∩ A (ae_restrict_mem₀). Fix such an x, together with an orthonormal τ : Fin k → ℝ^P such that HasWeightedApproximateTangentSpaceAt k M θ x (span τ) and ξ(x) = ±simpleNVector τ. The symmetric difference of M and M ∩ A is M ∖ A, which does not meet A, so Hᵏ(symmDiff M (M ∩ A) ∩ A) = Hᵏ(∅) = 0. A is open and contains x, and θ′ := θ agrees with θ everywhere. Hence the comparator-accepted declaration Submission.br_weightedTangent_congr (with V := A, M′ := M ∩ A, θ′ := θ, L := span τ) gives HasWeightedApproximateTangentSpaceAt k (M ∩ A) θ x (span τ). With the same τ and the same sign of ξ(x), the orients property of (M ∩ A, θ, ξ) holds at x.

4. Integrality. θ(x) ∈ ℕ for every x ∈ M ∩ A, since M ∩ A ⊆ M.

5. Conclusion. By steps 2–4, (M ∩ A, θ, ξ) witnesses IsIntegerMultiplicity R. ∎

## Key steps

1. Write X = τ(M, θ, ξ) with integer θ.
2. Submission.polyhedral_approx_restriction_tau gives R = τ(M ∩ A, θ, ξ) on D^k(U).
3. (M ∩ A, θ, ξ) inherits subset, null-measurability, rectifiability, positivity, local integrability and measurability.
4. Orientation: (M ∖ A) ∩ A = ∅ and A is open, so Submission.br_weightedTangent_congr transfers the weighted tangent planes of (M, θ) to (M ∩ A, θ).
5. θ is integer-valued on M ∩ A, so R is integer multiplicity.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean workspace GMT/Ch06/Submission.lean (identical)`
- `python3 scan of dag.json: lean_name/status of all nodes (458 at last check); no ind_pi_* names; frozen types and statuses of iwl_restriction_theory, br_restrictDomain_isIntegerMultiplicity, br_weightedTangent_congr, polyhedral_approx_restriction_tau, slicing_representation_unique, ltg_tau_integrable, iwl_restriction_weak_limit, iwl_smooth_pushforward, iwl_top_dim_integrality, ind_const_multiple_integer, iwl_im_closure`
- `keyword scan of all 192 accepted dag.json statements for restrictDomain|IsMeasureRepresentation|simpleNVector|span|IsRestriction|support|volume|∃ X : GeometricCurrentOn`
- `grep -n 'def |theorem ' simongmt Poincare/SimonGMT/Chapter06/{Currents,CurrentLocalEquality,Mass,Forms,FormsDuality}.lean and Chapter03/Rectifiable.lean (CountablyRectifiable.mono)`
- `rg in snapshot mathlib: Isometry.map_euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, MeasurableEmbedding.integral_map, IsClosedEmbedding.measurableEmbedding, Isometry isClosedEmbedding, IsClosedEmbedding.isCompact_preimage, exists_contDiff_zero_iff_one_iff_of_isClosed, IsCompact.exists_cthickening_subset_open, closure_thickening_subset_cthickening, cthickening_subset_thickening', IsCompact.cthickening, lintegral_liminf_le, frequently_lt_of_liminf_lt, liminf_le_of_frequently_le', extraction_of_frequently_atTop, ae_lt_top, ae_neBot, Set.Countable.measure_zero, norm_fderiv_le_of_lipschitz, LipschitzWith.of_le_add, norm_add_sq_eq_norm_sq_add_norm_sq_real, Orthonormal.inner_sum, orthonormal_iff_ite, EuclideanSpace.real_norm_sq_eq, Continuous.integrable_of_hasCompactSupport, norm_setIntegral_le_of_norm_le_const, setIntegral_eq_integral_of_ae_compl_eq_zero, setIntegral_eq_zero_of_forall_eq_zero, setIntegral_eq_integral_of_forall_compl_eq_zero, Submodule.closed_of_finiteDimensional, Submodule.mem_span_range_iff_exists_fun, norm_iteratedFDeriv_zero, ae_restrict_of_ae_restrict_of_subset, ae_restrict_mem₀, HasCompactSupport.smul_right, tsupport_smul_subset_left, Measurable.liminf, image_eq_zero_of_notMem_tsupport`
- `sed -n 2300,2500p book/chapter-06.txt (printed Proof of 8.2, displays (8)-(10))`
- `verifier gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') + lean_contract.validate_lean_statement on the 7 child statements`
- `lake env lean /tmp/pi-decomp-scratch/{Stmts,AsmParent,AsmL,AsmP,LeafG,LeafSPAN,LeafMC,LeafROI,LeafSEL}.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Filter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/pi-decomp-scratch/Stmts.lean`
- `/tmp/pi-decomp-scratch/AsmParent.lean`
- `/tmp/pi-decomp-scratch/AsmL.lean`
- `/tmp/pi-decomp-scratch/AsmP.lean`
- `/tmp/pi-decomp-scratch/LeafG.lean`
- `/tmp/pi-decomp-scratch/LeafSPAN.lean`
- `/tmp/pi-decomp-scratch/LeafMC.lean`
- `/tmp/pi-decomp-scratch/LeafROI.lean`
- `/tmp/pi-decomp-scratch/LeafSEL.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 Contract and a byte-identical Submission.

Library support for the child proofs:
- SimonGMT supplies GeometricCurrentOn with restrictDomain, testFormOnInclusion, zeroRegion, support and isOpen_zeroRegion; massOn with massOn_mono and le_massOn; NVector with simpleNVector_apply and covectorPullback; and CountablyRectifiable.mono.
- Mathlib supplies all lemmas cited in the child proofs:
  - Isometry.map_euclideanHausdorffMeasure and EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:141,187);
  - exists_contDiff_zero_iff_one_iff_of_isClosed (Geometry/Manifold/PartitionOfUnity.lean:809);
  - IsCompact.exists_cthickening_subset_open, cthickening_subset_thickening', closure_thickening_subset_cthickening and IsCompact.cthickening (Topology/MetricSpace/Thickening.lean);
  - lintegral_liminf_le, ae_lt_top, extraction_of_frequently_atTop and LipschitzWith.of_le_add (Topology/MetricSpace/Lipschitz.lean:87);
  - Isometry.isClosedEmbedding (declared as `theorem isClosedEmbedding` at Topology/MetricSpace/Isometry.lean:209).
- Three `theorem <name>` searches found no match, because the lemmas are generated or namespaced: frequently_lt_of_liminf_lt (generated by to_dual at Order/LiminfLimsup.lean:645), image_eq_zero_of_notMem_tsupport (to_additive-generated) and Isometry.isClosedEmbedding (above). All three elaborate in the checks.

DAG findings:
- No dag.json node has an ind_pi_* name.
- No accepted declaration has the type of any proposed child.
- The closest node is iwl_im_closure, whose conjunct 2 is stronger than restriction_open_im (any measurable A instead of open A). It is unaccepted (waiting-children).
- The child proofs reuse these accepted declarations with byte-identical types: iwl_restriction_theory, br_restrictDomain_isIntegerMultiplicity, br_weightedTangent_congr and polyhedral_approx_restriction_tau. The prose also mentions slicing_representation_unique and ltg_tau_integrable, which are accepted, as an alternative route.
- RWL, SPF and TOP are byte-identical to the frozen types of iwl_restriction_weak_limit, iwl_smooth_pushforward and iwl_top_dim_integrality. The sibling ind_const_multiple_integer type is byte-identical to dag.json.

Lean checks in the exact contract scope prove:
- the parent from the children and the sibling;
- localized_cycles from its five siblings and accepted lemmas;
- projected_limit from frame_geometry and span_integral;
- every leaf (outright, or from accepted-declaration types).

All checks print only [propext, Classical.choice, Quot.sound].

The printed Proof of 8.2 (book chapter-06 lines 2400–2500) matches the supplied Steps 5–8: display (8)/(9) is localized_cycles and display (10) plus the final convergence is projected_limit.
