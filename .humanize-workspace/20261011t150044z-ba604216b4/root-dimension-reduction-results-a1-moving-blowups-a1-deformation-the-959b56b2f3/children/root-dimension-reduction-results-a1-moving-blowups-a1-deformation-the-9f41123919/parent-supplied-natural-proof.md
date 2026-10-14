# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1.cylinder_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 2 (tangent planes of M at piece points: for a.e. u ∈ A_i, M has approximate tangent space V_i(u) = DG_i(u)(ℝⁿ) at G_i(u)) and the orientation part of step 6 (for a.e. z ∈ Â_i, M̃ has approximate tangent space ℝe₀ ⊕ J(V_i(tail z)) at Ĝ_i(z); the Fubini null set; the exceptional set consists of Lipschitz images of Lebesgue-null sets and ι((0,1) × Z)), with uniqueness of approximate tangent spaces (HasApproximateTangentSpaceAt.unique). The parent's combination "ptd_piece_image_approxTangent_ae + (IMC)(a) + (NT)" is exactly the statement of the accepted sibling dpf_approxTangent_ae_bilipschitz_piece, which is used for it. Siblings used: dimred_mbl_dt_lp_imc_suspension, dimred_mbl_dt_lp_imc_product_null, dimred_mbl_dt_lp_imc_cylinder_measure, dpf_rectifiable_bilipschitz_pieces, dpf_approxTangent_ae_bilipschitz_piece.

Notation. Φ_d(t, u) := WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) ∈ ℝ^{d+1}, Ψ := Φ_N; Φ_d is injective and continuous, hence a measurable embedding (Continuous.measurableEmbedding). M̃ := Ψ((0, 1) × M); e₀, J, Q̃ as in the statement; Hᵈ := μHE[d]; on ℝᵈ, Hᵈ = vol (EuclideanSpace.euclideanHausdorffMeasure_eq_volume). V(K, u) := range DK(u) (D = fderiv). For z ∈ ℝ^{n+1}: z₀ := (WithLp.ofLp z) 0 and tail z := WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)).

1. Finiteness of M̃. M̃ is Borel (image of the Borel set (0, 1) × M under the measurable embedding Ψ). Evaluating the sibling identity Ψ_*((vol⌞(0, 1)) ⊗ (Hⁿ⌞M)) = H^{n+1}⌞M̃ (dimred_mbl_dt_lp_imc_cylinder_measure) on ℝ^{N+1} gives H^{n+1}(M̃) = vol((0, 1))·Hⁿ(M) = Hⁿ(M) < ∞ (Measure.map_apply, Measure.prod_prod, Real.volume_Ioo). In particular H^{n+1}(M̃ ∩ C) < ∞ and Hⁿ(M ∩ C) < ∞ for every compact C.

2. Pieces. The sibling dpf_rectifiable_bilipschitz_pieces (P := N) applied to M gives, for i ∈ ℕ, L_i-Lipschitz F_i : ℝⁿ → ℝ^N, Borel B_i ⊆ ℝⁿ and m_i > 0 with m_i|a − a'| ≤ |F_i(a) − F_i(a')| on B_i, F_i differentiable with injective derivative at every point of B_i, F_i(B_i) ⊆ M, and Hⁿ(Z₀) = 0 for Z₀ := M ∖ ⋃_i F_i(B_i).

3. Tangent planes of M at piece points. For each i, the sibling dpf_approxTangent_ae_bilipschitz_piece with P := N, degree n, U := ℝ^N (open), Y := M (Borel, Hⁿ(M ∩ C) < ∞ by step 1), F := F_i, B := B_i, m := m_i gives a vol-null set Z_i ⊆ ℝⁿ such that HasApproximateTangentSpaceAt n M (F_i u) (V(F_i, u)) for every u ∈ B_i ∖ Z_i (choose Z_i as a null set containing the exceptional points, via ae_restrict_iff' and ae_iff).

4. Product pieces. For each i put Ĝ_i(z) := Φ_N(z₀, F_i(tail z)), so Ĝ_i(Φ_n(t, u)) = Ψ(t, F_i u) (Fin.cons_zero, Fin.tail_cons), and Â_i := Φ_n((0, 1) × B_i), a Borel subset of ℝ^{n+1}. By the sibling dimred_mbl_dt_lp_imc_suspension (G := F_i, Gh := Ĝ_i): (a) Ĝ_i is max(1, L_i)-Lipschitz; (b) min(1, m_i)|z − z'| ≤ |Ĝ_i z − Ĝ_i z'| for z, z' ∈ Â_i (write z = Φ_n(t, u), z' = Φ_n(t', u') with u, u' ∈ B_i), and min(1, m_i) > 0; (c) at every z = Φ_n(t, u) ∈ Â_i, Ĝ_i is differentiable with injective derivative and V(Ĝ_i, z) = Q̃(V(F_i, u)). Moreover Ĝ_i(Â_i) = Ψ((0, 1) × F_i(B_i)) ⊆ M̃.

5. Tangent planes of M̃ at product-piece points. For each i, the sibling dpf_approxTangent_ae_bilipschitz_piece with P := N + 1, degree n + 1, U := ℝ^{N+1}, Y := M̃ (Borel, locally finite by step 1), F := Ĝ_i, B := Â_i, m := min(1, m_i) (hypotheses by step 4) gives a vol-null set W_i ⊆ ℝ^{n+1} with HasApproximateTangentSpaceAt (n+1) M̃ (Ĝ_i z) (V(Ĝ_i, z)) for every z ∈ Â_i ∖ W_i.

6. Fubini null sets. W'_i := Φ_n(ℝ × Z_i) is vol-null in ℝ^{n+1}: the sibling dimred_mbl_dt_lp_imc_product_null with N := n and Z := Z_i (Hⁿ(Z_i) = vol(Z_i) = 0 on ℝⁿ) gives H^{n+1}(W'_i) = 0, and H^{n+1} = vol on ℝ^{n+1}.

7. Exceptional set. E := ⋃_i Ĝ_i(W_i ∪ W'_i) ∪ Ψ(ℝ × Z₀). Each Ĝ_i(W_i ∪ W'_i) is H^{n+1}-null: Ĝ_i is Lipschitz, so μH[n+1](Ĝ_i(S)) ≤ Lip(Ĝ_i)^{n+1}μH[n+1](S) (LipschitzWith.hausdorffMeasure_image_le), μHE[n+1] = c·μH[n+1] with c ≠ 0, and H^{n+1}(W_i ∪ W'_i) = vol(W_i ∪ W'_i) = 0. Ψ(ℝ × Z₀) is H^{n+1}-null by the sibling product_null (Hⁿ(Z₀) = 0). Hence H^{n+1}(E) = 0 by countable subadditivity.

8. Good points. Let y ∈ M̃ ∖ E, t ∈ ℝ, x ∈ ℝ^N with y = Ψ(t, x), and Q a subspace with HasApproximateTangentSpaceAt n M x Q. Since y ∈ M̃ = Ψ((0, 1) × M) and Ψ is injective, t ∈ (0, 1) and x ∈ M. Since y ∉ Ψ(ℝ × Z₀), x ∉ Z₀, so x = F_i(u) for some i and u ∈ B_i. Put z := Φ_n(t, u) ∈ Â_i; then Ĝ_i(z) = Ψ(t, F_i u) = y. Since y ∉ Ĝ_i(W_i ∪ W'_i), z ∉ W_i and z ∉ W'_i; the latter gives u ∉ Z_i (otherwise z = Φ_n(t, u) ∈ W'_i). By step 3, M has approximate tangent space V(F_i, u) at x = F_i(u), so Q = V(F_i, u) by uniqueness (HasApproximateTangentSpaceAt.unique). By steps 5 and 4(c), M̃ has approximate tangent space V(Ĝ_i, z) = Q̃(V(F_i, u)) = Q̃(Q) at y.

9. Conclusion. The asserted property holds at every y ∈ M̃ ∖ E and H^{n+1}(E) = 0, so it holds for H^{n+1}⌞M̃-a.e. y (ae_restrict_iff' with M̃ Borel, measure_mono_null). ∎

Formalization note (optional aid; the proof above is self-contained): a complete Lean proof of exactly this statement from the five sibling statements (about 165 lines; axioms propext, Classical.choice, Quot.sound) was compiled during decomposition, file /tmp/imcyl/verified/WireTangent.lean on the decomposition host (if available there) (sibling statements as hypotheses hSU, hPN, hCM, hPC, hPT).

## Key steps

1. H^{n+1}(M̃) = Hⁿ(M) < ∞ from the cylinder measure identity.
2. Pieces F_i(B_i) of M; for a.e. u ∈ B_i, M has approximate tangent space range DF_i(u) at F_i(u) (accepted piece-tangent lemma).
3. Product pieces Ĝ_i on Φ_n((0,1) × B_i) are bi-Lipschitz with injective derivative and range Q̃(range DF_i(u)); for a.e. z, M̃ has approximate tangent space range DĜ_i(z) at Ĝ_i(z).
4. Exceptional set ⋃_i Ĝ_i(W_i ∪ Φ_n(ℝ × Z_i)) ∪ Ψ(ℝ × Z₀) is null (Lipschitz images, product-null lemma).
5. At a good y = Ψ(t, F_i u), uniqueness forces Q = range DF_i(u), so M̃ has approximate tangent space Q̃(Q) at y.

## Reference use

### local-project

Queries:
- `cat SNAPSHOT/manifest.json (project_commit b4d606db, mathlib_commit 25730c7c); git -C SNAPSHOT/mathlib rev-parse HEAD (25730c7c); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean workspace GMT/Ch07/Submission.lean (identical)`
- `rg -n -i 'cylinder|\[\[0, ?1\]\]|product.?null|hausdorffMeasure.*prod|prod.*hausdorffMeasure' SNAPSHOT/project/GMT -g '*.lean' (no match)`
- `rg -n 'theorem hausdorffMeasure_le_liminf_tsum|theorem hausdorffMeasure_apply|theorem hausdorffMeasure_prod_real|theorem normDet_sq_eq_det_gram|theorem volume_preserving_piFinSuccAbove|theorem det_succ_row_zero|theorem hausdorffMeasure_image_le|theorem one_le_hausdorffMeasure_zero_of_nonempty|theorem integral_prod' SNAPSHOT/mathlib/Mathlib (all found; the only Hausdorff product result is hausdorffMeasure_prod_real on ℝ × ℝ)`
- `grep -rn SNAPSHOT/mathlib/Mathlib for Continuous.measurableEmbedding, curryLeftLI, compContinuousLinearMapCLM, lintegral_map, prod_sum_right, map_sum, restrict_iUnion, restrict_congr_set, exists_pos_sum_of_countable, volume_preserving_toLp, setLIntegral_comp_emb, of_dist_le_mul, measurable_fderiv, HasFDerivAt.prodMk, orthonormal_iff_ite, range_cons, map_span, inner_single_left, norm_single, euclideanHausdorffMeasure_def, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero, prod_prod, ae_restrict_iff', lintegral_prod, integral_Ioc_eq_integral_Ioo, image_of_continuousOn_injOn (all found)`
- `grep of SimonGMT (lake-packages-25730c7c/simongmt): weighted_area_formula_lipschitz_injOn, injective_area_formula_lipschitzOn, areaJacobianAt / areaJacobianAt_eq_normDet, measurable_areaJacobianAt, HasApproximateTangentSpaceAt and .unique, CountablyRectifiable, blowUpMap; Chapter06/Product.lean (only the point product {p} × T)`
- `python3 scans of RUN/dag.json (2102 nodes) for accepted lean_statements mentioning HasApproximateTangentSpaceAt, Fin.cons, Measure.map, IMRep (found dpf_rectifiable_bilipschitz_pieces, dpf_approxTangent_ae_bilipschitz_piece, regcomp_approx_tangent_locality, ptd_ae_approxTangent_iff_of_subset, cbr_ci_imc_isIntegerMultiplicity_of_rectifiable, dpf_pfc_imrep_pairing_integrable_abs_le, dpf_raf_piece_area_formula_gram); twin node cmcdt_lpi_cylinder_im (decomposing, different hypotheses); lean_name scan and grep of RUN/nodes for the 8 new names (no hits)`
- `grep/sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose with max_depth 6, _existing_lean_name_problem, _accepted_checkpoint: both reused nodes accepted with candidate commits a2ba78fc and a2168047, _reference_use_problem); verifier gmt-compare.py contract_scope/child_modules (replayed challenge scope); both validate_lean_statement implementations on all 10 types`
- `lake env lean /tmp/imcyl/lean/Types.lean (11 types, only sorry warnings); lake env lean on Assembly.lean, WireImrep.lean, WireTangent.lean, WireMeasure.lean, WireRect.lean, LeafSuspension.lean, LeafOrientation.lean, LeafProductNull.lean, LeafPieceMeasure.lean and Combined.lean (#print axioms: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-959b56b2f3/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-a2fdfc1c6f/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-680a7024c9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-bilipschi-4344c8c0d8/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/imcyl/lean/Types.lean`
- `/tmp/imcyl/verified/Assembly.lean`
- `/tmp/imcyl/verified/WireImrep.lean`
- `/tmp/imcyl/verified/WireTangent.lean`
- `/tmp/imcyl/verified/WireMeasure.lean`
- `/tmp/imcyl/verified/WireRect.lean`
- `/tmp/imcyl/verified/LeafSuspension.lean`
- `/tmp/imcyl/verified/LeafOrientation.lean`
- `/tmp/imcyl/verified/LeafProductNull.lean`
- `/tmp/imcyl/verified/LeafPieceMeasure.lean`
- `/tmp/imcyl/verified/Combined.lean`

The pins match: project b4d606db, Mathlib 25730c7c, and the workspace Submission is identical to the snapshot Ch07 contract. Neither the snapshot project, Mathlib nor SimonGMT contains a product-null lemma, a product formula for Hausdorff measure on cylinders over rectifiable sets, tangent planes of cylinders, or integrality of [[0,1]] × X. Mathlib's only Hausdorff product result is hausdorffMeasure_prod_real on ℝ × ℝ, and SimonGMT's Product.lean covers only {p} × T. So eight children are new obligations under fresh names dimred_mbl_dt_lp_imc_*. Two needed steps already exist as accepted DAG declarations with exactly the required types and are reused verbatim: dpf_rectifiable_bilipschitz_pieces (B1) and dpf_approxTangent_ae_bilipschitz_piece. Every cited Mathlib/SimonGMT name exists in the pinned sources, for example weighted_area_formula_lipschitz_injOn, normDet_sq_eq_det_gram, hausdorffMeasure_apply / hausdorffMeasure_le_liminf_tsum, volume_preserving_piFinSuccAbove and curryLeftLI. All ten child types elaborate in the comparator's challenge scope and pass both validators. Lean proofs establish every child (leaves outright, the others from their declared siblings) and the selected type, using only propext, Classical.choice and Quot.sound.
