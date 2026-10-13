# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1.set_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Supplied proof of the parent node, facts 1(i), 1(iv) and step 4 (countable decomposition and ε → 0), with c_ε replaced by an arbitrary factor t > 1 as provided by the sibling local_comparison.

Notation. ι* is the adjoint of ι, H^m = μHE[m] and L^m = volume. All integrals are lower integrals of ENNReal.ofReal∘J with respect to L^m.

1. (G is injective, and continuous on D.) First, ι*ι = id: ⟨v, ι*ιw⟩ = ⟨ιv, ιw⟩ = ⟨v, w⟩ for all v (LinearIsometry.inner_map_map, ext_inner_left). Second, ι*ι' = 0: ⟨v, ι*ι'u⟩ = ⟨ιv, ι'u⟩ = 0. Hence ι*(G(w)) = w for all w ∈ ℝ^m, and G is injective. G is continuous on D because ι and ι' are continuous and g is continuous on D (it is C¹ there).

2. (Two-sided bound for a fixed t > 1.) Fix t > 1. We show H^m(G(A)) ≤ t·∫_A J and ∫_A J ≤ t·H^m(G(A)). If A = ∅, all quantities are 0. Assume A ≠ ∅.
 (a) For each w₀ ∈ D, the sibling local_comparison (with this t) gives r(w₀) > 0 with B_{r(w₀)}(w₀) ⊆ D and both inequalities for every measurable B ⊆ B_{r(w₀)}(w₀).
 (b) ℝ^m is second countable, and each B_{r(w₀)}(w₀) is a neighbourhood of w₀. Hence there is a countable T ⊆ D with D ⊆ ⋃_{w₀∈T} B_{r(w₀)}(w₀) (TopologicalSpace.countable_cover_nhdsWithin). T ≠ ∅, since A ≠ ∅ and A ⊆ D. Enumerate T = {e_0, e_1, e_2, …}, repetitions allowed (Set.Countable.exists_eq_range), and put B_j := B_{r(e_j)}(e_j).
 (c) Let A_j := A ∩ (B_j ∖ ⋃_{i<j} B_i), i.e. A ∩ disjointed B j. The A_j are measurable (MeasurableSet.disjointed) and pairwise disjoint (disjoint_disjointed), and A_j ⊆ B_j (disjointed_subset). Also ⋃_j A_j = A ∩ ⋃_j B_j = A (iUnion_disjointed), since A ⊆ D ⊆ ⋃_j B_j.
 (d) G(A) = ⋃_j G(A_j). The sets G(A_j) are pairwise disjoint because G is injective (step 1). They are Borel by the Lusin–Souslin theorem: A_j is Borel, and G is continuous on A_j ⊆ D and injective (MeasurableSet.image_of_continuousOn_injOn; ℝ^m is Polish). By countable additivity of H^m (measure_iUnion) and of B ↦ ∫_B J (lintegral_iUnion, for disjoint measurable sets and any integrand):
 H^m(G(A)) = Σ_j H^m(G(A_j)) and ∫_A J = Σ_j ∫_{A_j} J.
 (e) By (a) with B = A_j ⊆ B_j: H^m(G(A_j)) ≤ t∫_{A_j} J and ∫_{A_j} J ≤ t·H^m(G(A_j)). Summing over j (ENNReal.tsum_le_tsum, ENNReal.tsum_mul_left) gives H^m(G(A)) ≤ t∫_A J and ∫_A J ≤ t·H^m(G(A)).

3. (Letting t ↓ 1.) Let x, y ∈ [0, ∞] with x ≤ ofReal(t)·y for every real t > 1. As t → 1 from above, ofReal(t)·y → ofReal(1)·y = y: multiplication by a fixed y is continuous at a limit factor ≠ 0 (ENNReal.Tendsto.mul_const, ENNReal.continuous_ofReal). Hence x ≤ y (ge_of_tendsto along 𝓝[>] 1). Apply this to both inequalities of step 2, which hold for every t > 1: H^m(G(A)) ≤ ∫_A J and ∫_A J ≤ H^m(G(A)). So H^m(G(A)) = ∫_A J (le_antisymm). ∎

## Key steps

1. ι*G = id (ι*ι = id, ι*ι' = 0), so G is injective; G is continuous on D.
2. For fixed t > 1, local_comparison gives balls around each point of D. Second countability gives a countable subcover, which is disjointified to a measurable partition A = ⊔ A_j with each A_j inside one ball.
3. G(A) = ⊔ G(A_j) with Borel pieces (Lusin–Souslin, injectivity). Summing the local inequalities gives H^m(G A) ≤ t∫_A J and ∫_A J ≤ t H^m(G A).
4. Letting t ↓ 1 in [0, ∞] gives equality.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; cat lakefile.toml lean-toolchain`
- `rg -n 'euclideanHausdorffMeasure|μHE' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'det_adjoint|adjoint.*det|det.*adjoint' and rg -n 'theorem toMatrix_adjoint|toEuclideanLin_conjTranspose|toMatrixOrthonormal_adjoint' in local-references/123e8435b4a2469b/mathlib/Mathlib; sed -n 1,80p, 260,300p, 385,450p Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `lake env lean /tmp/ga-dec/Check2.lean (#check LinearMap.normDet, LinearMap.hausdorffMeasure_image, ContinuousLinearMap.normDet_sq after import GMT.Ch07.Submission)`
- `python3 import-closure walk of .lake/packages/simongmt from Chapter03.Rectifiable, Chapter06.Mass, Chapter06.CurrentLocalEquality, Chapter06.AffineCurrentPushforward; grep -n '^theorem\|^lemma\|^def' on Chapter01/Basic, Chapter01/Hausdorff, Chapter01/MetricCriterion, Chapter02/Lipschitz, Chapter04/Basic; sed -n 186,260p Chapter02/Lipschitz.lean`
- `python3 scans of dag.json: regex 'area|Lipschitz|Jacobian|adjoint|graph' over titles, statements and lean_statements; lean_statements containing adjoint+μHE, Real.sqrt+volume/μHE, LinearMap.det, InjOn+'ofReal (J', 'linear' titles with μHE/volume; lean_name prefix codim1_zsl; membership of the five new names; byte comparison of the selected lean_statement with dag.json and the handoff`
- `grep -n 'def check_source_delta' -A40 /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py; git show 434bc6d3dbb2f6ea9b32f146b1997dfa769d1cd5 -- GMT/Ch07/Submission.lean`
- `rg -n 'theorem map_comap_subtype_coe|countable_cover_nhdsWithin|theorem restrict_withDensity|MeasurableSet.subtype_image' local-references/123e8435b4a2469b/mathlib/Mathlib; grep -n 'theorem integral_image_eq_integral_abs_det_fderiv_smul' -A40 and 'theorem restrict_map_withDensity_abs_det_fderiv_eq_addHaar' -A40 Mathlib/MeasureTheory/Function/Jacobian.lean`
- `lake env lean /tmp/ga-dec/Check0.lean, Check1.lean, Check3.lean (#check of about 80 Mathlib/SimonGMT names, including Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_image_continuousLinearMap, MeasurableSet.image_of_continuousOn_injOn, MeasurableEmbedding.integral_map, measurable_fderiv, Convex.norm_image_sub_le_of_norm_fderiv_le, LinearIsometry.adjoint_comp_self)`
- `lake env lean /tmp/ga-dec/Types1.lean, C1.lean, Cbilip.lean, C2.lean, C3.lean, C4.lean, Full.lean with #print axioms`
- `sed -n 268,300p and 735,790p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-df95e3f55f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-df95e3f55f/parent-supplied-plan.md`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/ga-dec/Types1.lean`
- `/tmp/ga-dec/C1.lean`
- `/tmp/ga-dec/Cbilip.lean`
- `/tmp/ga-dec/C2.lean`
- `/tmp/ga-dec/C3.lean`
- `/tmp/ga-dec/C4.lean`
- `/tmp/ga-dec/Full.lean`

Pins and contract. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to the workspace. GMT/Ch07/Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Not importable. Mathlib's linear Hausdorff area formula LinearMap.hausdorffMeasure_image / normDet (Analysis/InnerProductSpace/NormDet.lean) exists in the snapshot but is NOT in the import closure of GMT.Ch07.Submission (#check reports unknown constants). SimonGMT Chapter02.AreaFormula is also outside the closure. Hence linear_area re-proves Simon 3.1 with the same isometry-onto-range argument.

Available in the closure:
- Mathlib Volume/Measure.lean (μHE[d], Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, euclideanHausdorffMeasure_def).
- SimonGMT Chapter02/Lipschitz.lean:216, euclideanHausdorffMeasure_image_le_of_lipschitzOn (the μHE form of Simon 1.8(i)), reached via Chapter03.Rectifiable.
- Every other Mathlib lemma cited in the children, e.g. Measure.addHaar_image_continuousLinearMap, MeasurableSet.image_of_continuousOn_injOn, MeasurableEmbedding.integral_map, map_comap_subtype_coe (Restrict.lean:934), restrict_withDensity (WithDensity.lean:215), TopologicalSpace.countable_cover_nhdsWithin (Bases.lean:964), LinearMap.toMatrix_adjoint (Adjoint.lean:1029), measurable_fderiv, Convex.norm_image_sub_le_of_norm_fderiv_le, LinearIsometry.adjoint_comp_self. Recent renames: ContDiffOn.differentiableOn takes 1 ≠ 0; the lambda form uses fderiv_fun_sub; Set.restrict/ContinuousOn.restrict are deprecated in favour of domRestrict.

DAG. No accepted node has the type of any proposed child. Related accepted nodes have other types: dimred_rpd_bilipschitz_image_measure (bi-Lipschitz relative to the identity), dorag_tes_lipschitz_graph_area_bounds (inequalities only), dgoj_unitOrientation_of_injective (needs an extra MultiVector conjunct). The area-formula nodes dpf_raf_piece_area_formula_gram, codim1_lur_rectifiable_area_formula and idtp_carrier_area_formula are unaccepted and have different types. The five new names codim1_zsl_ga_* have no match in dag.json.

Leaf rule. check_source_delta allows only the single selected theorem per leaf (no helper declarations, imports or set_option). This motivates the split; none of the scratch proofs uses a forbidden token.

Lean checks.
- The children's types and the parent assembly elaborate.
- Full.lean proves the whole chain, and #print axioms gives only propext, Classical.choice and Quot.sound.

Book. chapter-02.txt lines 743–776 give 3.1 with its proof and state 3.2–3.3 'by an approximation argument based on the linear case 3.1'. Lines 270–296 give Theorem 1.8(i), valid for non-measurable A.
