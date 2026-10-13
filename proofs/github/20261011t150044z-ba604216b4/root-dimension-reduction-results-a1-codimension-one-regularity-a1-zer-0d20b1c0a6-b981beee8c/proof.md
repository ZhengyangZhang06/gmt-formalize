# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1.integral_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Supplied proof of the parent node, steps 5 (push-forward form H^m⌞G(A) = G_#(J·L^m⌞A)) and 6 (Bochner integrals via a measurable embedding), stated abstractly. The argument is the one Mathlib uses for integral_image_eq_integral_abs_det_fderiv_smul (MeasureTheory/Function/Jacobian.lean).

Notation. L^m = volume on ℝ^m. ρ := L^m with density ofReal∘J (volume.withDensity). A carries the subspace topology and σ-algebra, and ν := comap of ρ under the inclusion A → ℝ^m.

1. (Measurable embedding.) Let φ : A → ℝ^P, φ(x) := G(x). φ is continuous because G is continuous on A (ContinuousOn.domRestrict), hence measurable; it is injective because G is injective on A. Let s ⊆ A be measurable in the subtype. Its image in ℝ^m is measurable (MeasurableSet.subtype_image, A measurable), and G is continuous and injective on it. By the Lusin–Souslin theorem (MeasurableSet.image_of_continuousOn_injOn; ℝ^m is Polish), φ(s) = G(s) is Borel. Hence φ is a measurable embedding.

2. (Identification of μ⌞G(A).) Claim: μ⌞G(A) = φ_#ν. Let Y ⊆ ℝ^P be measurable. Then (μ⌞G(A))(Y) = μ(Y ∩ G(A)) (Measure.restrict_apply). Put A_Y := A ∩ G^{−1}(Y). It is the image in ℝ^m of the measurable set φ^{−1}(Y) of the subtype, hence a measurable subset of A, and Y ∩ G(A) = φ(φ^{−1}(Y)) = G(A_Y). By hypothesis, μ(G(A_Y)) = ∫_{A_Y} J dL^m = ρ(A_Y). On the other side, (φ_#ν)(Y) = ν(φ^{−1}(Y)) = ρ(A_Y), by Measure.map_apply, by MeasurableEmbedding.comap_apply for the inclusion of the measurable set A (MeasurableEmbedding.subtype_coe), and by withDensity_apply. The two measures agree on measurable sets, so they are equal (Measure.ext).

3. (Change of variables along φ and the inclusion.) Since φ is a measurable embedding, ∫ f d(φ_#ν) = ∫_A f(φ(x)) dν(x) for every f, measurable or not (MeasurableEmbedding.integral_map). The inclusion A → ℝ^m is also a measurable embedding, and pushing ν forward by it gives ρ⌞A (map_comap_subtype_coe). Hence ∫_A f(φ(x)) dν(x) = ∫ f(G(w)) d(ρ⌞A)(w). Moreover ρ⌞A = (L^m⌞A) with density ofReal∘J (restrict_withDensity).

4. (Removing the density.) Since ofReal(J(w)) = ↑(J(w)⁺) with J⁺ := Real.toNNReal∘J measurable, integral_withDensity_eq_integral_smul gives ∫ F d((L^m⌞A) with density ofReal∘J) = ∫_A J(w)⁺·F(w) dw for every F : ℝ^m → ℝ. Take F := f∘G. Since J ≥ 0 on A, J(w)⁺ = J(w) for w ∈ A, so the integrand equals J(w)·f(G(w)) on the measurable set A (setIntegral_congr_fun).

5. (Conclusion.) Combining steps 2–4:
 ∫_{G(A)} f dμ = ∫ f d(μ⌞G(A)) = ∫ f d(φ_#ν) = ∫_A J(w)·f(G(w)) dw.
Every step is an identity of Bochner integrals valid for arbitrary f. In particular, if one side is not integrable, both sides are 0. ∎

## Key steps

1. φ := G restricted to the subtype A is continuous and injective, and it maps measurable sets to Borel sets (Lusin–Souslin), so it is a measurable embedding.
2. For measurable Y, Y ∩ G(A) = G(A ∩ G⁻¹Y) with A ∩ G⁻¹Y measurable. The hypothesis gives μ⌞G(A) = φ_#(ρ restricted to A), where ρ = L^m with density ofReal∘J.
3. MeasurableEmbedding.integral_map (for any f), map_comap_subtype_coe and restrict_withDensity turn ∫_{G(A)} f dμ into ∫ f∘G d((L^m⌞A) with density J).
4. integral_withDensity_eq_integral_smul and J ≥ 0 on A give ∫_A J·(f∘G) dL^m.

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
