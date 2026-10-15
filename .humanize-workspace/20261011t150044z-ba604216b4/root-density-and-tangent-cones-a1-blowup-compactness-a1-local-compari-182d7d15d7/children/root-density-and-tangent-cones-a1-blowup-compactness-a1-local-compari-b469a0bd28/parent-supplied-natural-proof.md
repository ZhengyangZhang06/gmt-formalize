# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1.piece_pushforward-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5–9 of the parent proof (Simon 3.6–3.7) for one piece G(A) of M; the image orientation is transported from ξ instead of being written with a measurable sign, and the critical case is the parent's step 7 ("the integrand vanishes there"). Siblings used: piece_tangent (accepted dpf_approxTangent_ae_bilipschitz_piece), gram_area (accepted codim1_lura_gram_area_formula), change_of_variables, orient_algebra.
Notation: H := φ∘G; for a ∈ A, H is differentiable at a with DH(a) = Dφ(G(a))∘DG(a) (chain rule; φ is differentiable everywhere); J_G, J_H are the Gram Jacobians (J_F(a) = (det[⟨DF(a)e_k, DF(a)e_l⟩])^{1/2}); ‖Dφ(x)‖ ≤ Λ for all x (norm_fderiv_le_of_lipschitz); (★) denotes the hypothesis on ξ∘G.
1. Preliminaries.
 (a) G is injective on A (κ > 0). change_of_variables (II) for (F, B) := (G, A) gives: G(A) is Borel, every Hⁿ⌞G(A)-a.e. property holds at G(a) for a.e. a ∈ A, and ∫_{G(A)} h dHⁿ = ∫_A J_G(a)h(G(a)) da for every h a.e. strongly measurable for Hⁿ⌞G(A).
 (b) For a strongly measurable β put h_β(x) := θ(x)·ξ(x)(β(φ(x))∘Dφ(x)). h_β is a.e. strongly measurable for Hⁿ⌞G(A): θ is measurable (R.measurable_mult); ξ is a.e. strongly measurable for Hⁿ⌞M (R.aestronglyMeasurable_orient), hence for Hⁿ⌞G(A) (G(A) ⊆ M); x ↦ β(φ(x)) is strongly measurable (φ continuous); x ↦ compContinuousLinearMapCLM(Dφ(x)) is strongly measurable (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp_stronglyMeasurable (measurable_fderiv ℝ φ).stronglyMeasurable), so x ↦ β(φ(x))∘Dφ(x) = compContinuousLinearMapCLM(Dφ(x))(β(φ(x))) is strongly measurable ((continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable); and (ζ, α) ↦ ζ(α) is continuous. By (a): LHS(β) := ∫_{G(A)} h_β dHⁿ = ∫_A J_G(a)·θ(G(a))·ξ(G(a))(β(H(a))∘Dφ(G(a))) da.
 (c) J_G(a) > 0 for a ∈ A, by orient_algebra (c) applied to the injective DG(a).
 (d) Let ξ̃ be strongly measurable with ξ̃ = ξ Hⁿ⌞M-a.e. (AEStronglyMeasurable.mk); then ξ̃ = ξ Hⁿ⌞G(A)-a.e. (G(A) ⊆ M), so by (a) ξ̃(G(a)) = ξ(G(a)) for a.e. a ∈ A.
 (e) By (★) and the chain rule, for a.e. a ∈ A there is σ_a ∈ {1, −1} with, for every covector α, J_G(a)·ξ(G(a))(α∘Dφ(G(a))) = σ_a·(α∘Dφ(G(a)))(DG(a)e) = σ_a·α(DH(a)e_1, …, DH(a)e_n).
2. Critical case (D(φ∘G)(a) not injective for every a ∈ A). Take N := ∅, g := 0, η := 0. Then N is Borel, N ⊆ φ(G(A)), N is countably n-rectifiable (Hⁿ(∅) = 0), g is measurable, η is strongly measurable, the a.e. statement over Hⁿ⌞∅ = 0 is trivial, and ∫⁻_∅ |g| = 0 ≤ Λⁿ∫⁻_{G(A)} θ. For the identity: by orient_algebra (d) applied to DH(a), α(DH(a)e) = 0 for every α and a ∈ A, so by (e) the integrand in 1(b) vanishes for a.e. a ∈ A and LHS(β) = 0 = ∫_∅ g·η(β) dHⁿ.
3. Regular case (κ' > 0 with κ'|a − a'| ≤ |H(a) − H(a')| on A, DH(a) injective for a ∈ A).
 (a) H is (ΛL)-Lipschitz, injective on A, and differentiable with injective derivative on A. Put N := H(A) ⊆ φ(G(A)). change_of_variables (II) for (F, B) := (H, A) gives: N is Borel, ψ := invFunOn H A is measurable, and ∫_N h dHⁿ = ∫_A J_H(a)h(H(a)) da for every h a.e. strongly measurable for Hⁿ⌞N. Moreover ψ(H(a)) = a for a ∈ A, and ψ(y) ∈ A, H(ψ(y)) = y for y ∈ N. N ⊆ range H with H Lipschitz, so N is countably n-rectifiable (definition with M₀ := ∅ and the constant sequence H, or Poincare.SimonGMT.Chapter03.countablyRectifiable_range and CountablyRectifiable.mono).
 (b) Definitions. g(y) := θ(G(ψ(y))) (as an integer) for y ∈ N and g(y) := 0 for y ∉ N. η(y) := (J_G(ψ(y))/J_H(ψ(y)))·(ξ̃(G(ψ(y)))∘C(y)), where C(y) := compContinuousLinearMapCLM(Dφ(G(ψ(y)))), i.e. η(y)(α) = (J_G(ψ y)/J_H(ψ y))·ξ̃(G(ψ y))(α∘Dφ(G(ψ y))). g is measurable (θ measurable, G continuous, ψ measurable, N Borel). η is strongly measurable: J_G, J_H are Borel (gram_area (i)), so c(y) := J_G(ψ y)/J_H(ψ y) is measurable; ξ̃∘G∘ψ is strongly measurable (StronglyMeasurable.comp_measurable); y ↦ C(y) is strongly measurable (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp_stronglyMeasurable applied to (measurable_fderiv ℝ φ).stronglyMeasurable, composed with the measurable G∘ψ); and y ↦ c(y)•(ξ̃(G(ψ y))).comp(C(y)) is strongly measurable by hc.stronglyMeasurable.smul ((continuous_fst.clm_comp continuous_snd).comp_stronglyMeasurable (hξ.prodMk hC)). For y ∈ N, G(ψ(y)) ∈ G(A) ⊆ M, so θ(G(ψ y)) > 0 (R.mult_pos) and g(y) ≠ 0.
 (c) Jacobian comparison (parent (A3)): for a ∈ A, DH(a) = Dφ(G(a))∘DG(a) is injective, so change_of_variables (I) with (A, L) := (DG(a), Dφ(G(a))) gives J_H(a) ≤ ‖Dφ(G(a))‖ⁿ·J_G(a) ≤ Λⁿ·J_G(a).
 (d) Mass bound. By gram_area for (H, A) with g := |g|, the identities g(H(a)) = θ(G(a)) (a ∈ A), step (c), and gram_area for (G, A) with g := θ: ∫⁻_N |g| dHⁿ = ∫⁻_A ofReal(J_H(a))·θ(G(a)) da ≤ Λⁿ·∫⁻_A ofReal(J_G(a))·θ(G(a)) da = Λⁿ·∫⁻_{G(A)} θ dHⁿ. In particular Hⁿ(N) ≤ ∫⁻_N |g| < ∞ (|g| ≥ 1 on N).
 (e) Orientation. piece_tangent with (U := ℝ^P, Y := N, F := H, B := A, L := ΛL, m := κ') (N Borel, Hⁿ(N ∩ C) ≤ Hⁿ(N) < ∞, H(A) = N) gives: for a.e. a ∈ A, HasApproximateTangentSpaceAt n N (H(a)) (range DH(a)). Let A₀ ⊆ A be a Borel Lⁿ-null set outside which this, 1(d) and 1(e) hold. gram_area on A₀ gives Hⁿ(H(A₀)) = ∫⁻_{A₀} ofReal(J_H) = 0. Let y ∈ N ∖ H(A₀) and a := ψ(y) ∈ A ∖ A₀, so H(a) = y. By 1(d), 1(e): η(y)(α) = J_H(a)⁻¹·J_G(a)·ξ(G(a))(α∘Dφ(G(a))) = σ_a·J_H(a)⁻¹·α(DH(a)e) for every α. By orient_algebra (c) for the injective DH(a), J_H(a)⁻¹·DH(a)_#e is a unit orientation of range DH(a); its negative is one as well (IsUnitOrientationOf allows either sign with the same orthonormal frame). So η(y) is a unit orientation of range DH(a), which is an approximate tangent space of N at y. This holds for Hⁿ-a.e. y ∈ N.
 (f) Identity. Let β be strongly measurable; y ↦ g(y)·η(y)(β(y)) is a.e. strongly measurable for Hⁿ⌞N. By 3(a), ∫_N g·η(β) dHⁿ = ∫_A J_H(a)·g(H(a))·η(H(a))(β(H(a))) da = ∫_A J_H(a)·θ(G(a))·(J_G(a)/J_H(a))·ξ̃(G(a))(β(H(a))∘Dφ(G(a))) da. As J_H(a) > 0 on A (orient_algebra (c) for the injective DH(a)) and ξ̃(G(a)) = ξ(G(a)) for a.e. a ∈ A (1(d)), the integrand equals J_G(a)·θ(G(a))·ξ(G(a))(β(H(a))∘Dφ(G(a))) for a.e. a ∈ A, so ∫_N g·η(β) dHⁿ = LHS(β) by 1(b).
4. Steps 2 and 3 give N, g, η with all the stated properties in both cases. ∎

## Key steps

1. change_of_variables for G on A rewrites ∫_{G(A)} θ ξ(β(φ)∘Dφ) as ∫_A J_G·θ∘G·ξ∘G(β(H)∘Dφ∘G); with (★) and the chain rule the integrand is θ(G a)·σ_a·β(H a)(DH(a)e).
2. Critical case: DH(a)e is linearly dependent, the integrand vanishes, take N = ∅.
3. Regular case: N := H(A) is Borel with measurable inverse ψ; g := θ∘G∘ψ and η := (J_G/J_H)∘ψ·(ξ̃∘G∘ψ)∘Dφ(G∘ψ) are measurable.
4. change_of_variables (I) gives J_H ≤ Λⁿ J_G, hence ∫_N |g| ≤ Λⁿ∫_{G(A)} θ by gram_area.
5. piece_tangent for H on A and (★) show η(y) = ±J_H⁻¹DH_#e orients range DH, an approximate tangent space of N, Hⁿ-a.e.
6. change_of_variables for H on A turns ∫_N g η(β) into the same integral over A.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606d, mathlib 25730c7c); read GMT/Ch07/Contract.lean, GMT/Ch07/README.md and this node's parent-child-handoff.json (proof identical to the selected one)`
- `python3 -I scans of dag.json (1538 nodes): lean_name / lean_statement matching IsIntegerMultiplicity, bilipschitz, area, Real.sqrt (Matrix.det, normDet, approxTangent, imrep, int_density, pieces; status and candidate_commit of dpf_rectifiable_bilipschitz_pieces, dpf_approxTangent_ae_bilipschitz_piece, ptd_piece_image_approxTangent_ae, ptd_piece_image_measurable_ae_pullback, codim1_lura_gram_area_formula, codim1_lurpt_piece_area_jacobian, codim1_zsl_ga_linear_area, cmcdt_ims_imrep_of_int_density, dpfir_integral_eq_of_area_lintegral, dpf_unitOrientation_map_gramNormalized, dgoj_covector_eq_det_mul_of_mem_span, rsd_isIntegerMultiplicity_int_combination, regcomp_ims_imrep_of_signed_pieces, dpf_raf_piece_area_formula_gram; sibling nodes dimred_mbl_pf_* and dor_lmb_pc_* (decomposing, no decomposition files)`
- `read nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-a685b45291/decomposition-v1.json (the parent's 12-child split) and the parent-child-handoff.json / parent-supplied-natural-proof.md of the four reused nodes`
- `git show <candidate_commit>:GMT/Ch07/Submission.lean | grep 'theorem Submission.<name>' for a2ba78f, a216804, d5ba41d, c48b246 (types identical); git show b18a413 (accepted dpf_imrep_bilipschitz_image_rep: continuous_compContinuousLinearMapCLM, clm_apply measurability pattern); git log --all --oneline -S'<each new name>' (no match)`
- `grep -n in /runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean: max_depth, _existing_lean_name_problem, _accepted_checkpoint, _overlay_accepted_children, leaf_verification.check_source_delta`
- `rg in .lake/packages/simongmt/Poincare/SimonGMT: weighted_area_formula_lipschitz_injOn, areaJacobianAt, area_image_criticalSet_eq_zero, linear_area_formula (Chapter02, not imported by GMT.Ch07.Submission), CountablyRectifiable.mono, countablyRectifiable_range, countablyRectifiable_iUnion, HasApproximateTangentSpaceAt.unique (Chapter03/Rectifiable.lean), Covector, TestFormOn, covectorEuclideanNorm (Chapter06)`
- `grep in Mathlib at the pin: normDet (NormDet.lean, not imported), euclideanHausdorffMeasure_image_eq_normDet_mul_volume, hausdorffMeasure_image_le, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, MeasurableSet.image_of_continuousOn_injOn, LinearMap.exists_antilipschitzWith, continuous_clm_apply, Measurable.find, integral_tsum, integral_iUnion, lintegral_iUnion, Measurable.nnreal_tsum, ContinuousAlternatingMap.apply, exists_contDiff_support_eq_eq_one_iff, singularValues (no opNorm bound), Hadamard (none)`
- `lake env lean /tmp/pfint_decomp/check/{Check1..Check6,Types,Assembly}.lean (imports, instances, lemma names, child types, assembly with #print axioms)`
- `python3 -I /tmp/pfint_decomp/scripts/{scope.py,validate.py}: contract_scope replay and lean_contract.validate_lean_statement on all 12 strings`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-182d7d15d7/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-a685b45291/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-bilipschi-4344c8c0d8/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-680a7024c9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-im-74efcb8c6f/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-db95546c3f/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/leaf_verification.py`
- `/tmp/pfint_decomp/check/Types.lean`
- `/tmp/pfint_decomp/check/Assembly.lean`

The pinned project has no push-forward of integer multiplicity currents by C¹ maps. It has four comparator-accepted declarations that are exactly steps 2, 3+(TL), the area formula and step 11 of the supplied proof: dpf_rectifiable_bilipschitz_pieces, dpf_approxTangent_ae_bilipschitz_piece, codim1_lura_gram_area_formula and cmcdt_ims_imrep_of_int_density. They are reused with byte-identical types. LinearMap.normDet and the SimonGMT Chapter02 area files are not in the import closure of GMT.Ch07.Submission, so the new statements use the Gram-determinant Jacobian, as the accepted area formula does. The eight new statements have globally unique names, elaborate in the comparator scope and pass validate_lean_statement. A sorry-free Lean assembly derives the exact frozen parent type from the 12 child types using only propext, Classical.choice and Quot.sound.
