# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Steps 1, 2 and 3 (definition of g and 3(a)); Simon Ch. 3, Lemma 1.2, Remark 1.3, Remark 1.5(2) and Definition 2.1; Ch. 2, Theorems 1.2, 1.5 and §4. Notation: H^{n+1} = μHE[n+1] (= L^{n+1} on ℝ^{n+1}); for a chart ψ and y in its domain, Q(y) := Dψ(y)(ℝ^{n+1}).

1. Submanifold cover. By the sibling c1_cover (Lean dor_lmbsf_rectifiable_c1_cover, m = n+1): M ⊆ N₀ ∪ ⋃_l N_l with H^{n+1}(N₀) = 0 and each N_l satisfying IsEmbeddedSubmanifold 1 (n+1) N_l.

2. Countably many charts. Fix l. For each z ∈ N_l the definition gives an open V ⊆ ℝ^{n+1}, an open W ∋ z and ψ, C¹ on V, injective on V, with Dψ injective on V and ψ(V) = W ∩ N_l. N_l is Lindelöf (a subspace of the second countable ℝ^P), so countably many of these W cover N_l. Replace each V by V' := V ∩ ψ⁻¹(U), open because ψ is continuous on the open set V (ContinuousOn.isOpen_inter_preimage). Then ψ(V') ⊆ U and W ∩ N_l ∩ U ⊆ ψ(V'). Collecting over l we obtain countably many charts (V^s, ψ^s), s ∈ ℕ, satisfying (a), with M ∖ N₀ ⊆ ⋃_s ψ^s(V^s) (because M ⊆ U).

3. Balls and C¹ approximation. Fix s, write V = V^s, ψ = ψ^s. Let 𝔅_s be the countable family of closed balls B̄ = B̄_r(c) with c ∈ ℚ^{n+1}, r ∈ ℚ, r > 0 and B̄_{2r}(c) ⊆ V; it covers V. For B̄ ∈ 𝔅_s put B̄' := B̄_{2r}(c). Dψ is continuous on V, hence bounded by some Λ on the compact convex B̄', so ψ is Λ-Lipschitz on B̄' (mean value inequality) and u := f∘ψ is LΛ-Lipschitz on B̄'. Let ũ : ℝ^{n+1} → ℝ be a Lipschitz extension of u|_{B̄} (Ch. 2, Theorem 1.2; McShane). By the sibling c1_approx (Lean dor_lmbsf_lipschitz_c1_approx) with ε = 1/k, for every k ≥ 1 there is a C¹ function G_k with L^{n+1}({ũ ≠ G_k}) < 1/k. The set B̄ ∖ ⋃_k {u = G_k} is contained in ⋂_k {ũ ≠ G_k}, so it is L^{n+1}-null, and its image under ψ (Lipschitz on B̄) is H^{n+1}-null (SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn).

4. Indexing. Enumerate the countably many triples (s, B̄, k) as j ∈ ℕ (if there are only finitely many, pad with V_j = C_j = Y_j := ∅, ψ_j := 0, F_j := 0; all claims are then vacuous for these j). Put V_j := V^s, ψ_j := ψ^s, C_j := B̄ ∩ {u = G_k} (a closed subset of B̄, hence compact, and C_j ⊆ V_j), C'_j := B̄' (compact, C_j ⊆ B̄ ⊆ int C'_j, C'_j ⊆ V_j), F_j := G_k, E_j := ψ_j(C_j) (compact). By steps 1–3, every x ∈ M ∖ N₀ is ψ^s(v) with v in some B̄ ∈ 𝔅_s, and either v ∈ C_j for some j or v lies in the null set of step 3. Hence H^{n+1}(M ∖ ⋃_j E_j) = 0.

5. Disjoint pieces (Remark 1.3). M_j := (M ∩ E_j) ∖ ⋃_{i<j} E_i are Borel, pairwise disjoint, and ⋃_j M_j = M ∩ ⋃_j E_j. Put Y_j := C_j ∩ ψ_j⁻¹(M_j). It is Borel, because ψ_j restricted to the closed set C_j is continuous, and ψ_j(Y_j) = M_j because M_j ⊆ E_j = ψ_j(C_j). For y ∈ Y_j ⊆ {u = G_k}: f(ψ_j(y)) = u(y) = G_k(y) = F_j(y).

6. Null deletions. Steps 7 and 8 delete H^{n+1}-null subsets of the M_j. If a property holds for H^{n+1}-a.e. x ∈ M_j, its exceptional set is null for μHE[n+1]⌞M_j. So it lies in a Borel Z with H^{n+1}(Z ∩ M_j) = 0 (MeasureTheory.exists_measurable_superset_of_null). Replace M_j by M_j ∖ Z and Y_j by Y_j ∖ ψ_j⁻¹(Z). The new Y_j is still Borel, because ψ_j is continuous on the closed set C_j ⊇ Y_j. Countably many deletions preserve: Borel measurability, disjointness, M_j ⊆ M, ψ_j(Y_j) = M_j, Y_j ⊆ C_j, f∘ψ_j = F_j on Y_j, and H^{n+1}(M ∖ ⋃_j M_j) = 0.

7. Tangent planes (parent Step 2; Simon Remark 1.5(2)). Fix j and work with the Borel set M_j of step 5. The tangent property is applied only to the fixed set M, so it survives the later deletions.
   - S_j := ψ_j(C'_j) is compact, S_j ⊆ ψ_j(V_j) ⊆ U, and H^{n+1}(S_j) < ∞ (Lipschitz image of a ball).
   - For y ∈ C_j ⊆ int C'_j, the sibling image_tangent (Lean dor_lmbsf_c1_image_approxTangent, with k = n+1, V = V_j, C = C'_j, χ = ψ_j) shows that S_j has approximate tangent space Q_j(y) at ψ_j(y). Its hypotheses hold: ψ_j is C¹ on V_j, injective on C'_j ⊆ V_j, and Dψ_j(y) is injective.
   - Apply (TL) with (U, A, B) = (U, M_j, S_j): M_j ⊆ E_j ⊆ S_j ⊆ U, both sets are Borel, and H^{n+1}(S_j ∩ K) < ∞. So for H^{n+1}-a.e. x = ψ_j(y) ∈ M_j, M_j has approximate tangent space Q_j(y).
   - Apply (TL) with (U, A, B) = (U, M_j, M): M is Borel, M ⊆ U, and H^{n+1}(M ∩ K) < ∞ by hypothesis. So for H^{n+1}-a.e. x ∈ M_j, M has approximate tangent space Q_j(y) iff M_j does.
   - Hence M has approximate tangent space Q_j(y) at H^{n+1}-a.e. x = ψ_j(y) ∈ M_j. Delete the exceptional set (step 6). Afterwards, for every remaining y ∈ Y_j, M has approximate tangent space Q_j(y) at ψ_j(y). This gives (d); the intermediate statement about M_j is not used again.

8. Gradient bound at density points (parent Step 3(a)).
   - By the Lebesgue density theorem (Mathlib Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet for the closed set C_j and L^{n+1}), L^{n+1}-a.e. point of C_j is a density point of C_j: L^{n+1}(C_j ∩ B̄_r(y))/L^{n+1}(B̄_r(y)) → 1 as r ↓ 0. The non-density points of C_j form an L^{n+1}-null set, whose ψ_j-image is H^{n+1}-null (ψ_j is Lipschitz on C_j); delete it (step 6). Every remaining y ∈ Y_j is a density point of C_j.
   - Claim: |DF_j(y)e| ≤ L|Dψ_j(y)e| for every remaining y ∈ Y_j and every e ∈ ℝ^{n+1}. We may assume |e| = 1. By the sibling density_directions (Lean dor_lmbsf_density_directions, with Z := C_j, v := e) there are y_i ∈ C_j ∖ {y} with y_i → y and (y_i − y)/|y_i − y| → e.
   - On all of C_j ⊆ B̄ ∩ {u = G_k} we have F_j = u = f∘ψ_j. Hence |F_j(y_i) − F_j(y)| = |f(ψ_j(y_i)) − f(ψ_j(y))| ≤ L|ψ_j(y_i) − ψ_j(y)|.
   - Divide by |y_i − y| and let i → ∞, using differentiability of F_j and ψ_j at y. This gives |DF_j(y)e| ≤ L|Dψ_j(y)e|.

9. Definition of g (parent Step 3). On V_j let Γ_j(y) := Dψ_j(y)ᵀDψ_j(y) (invertible, continuous) and Φ_j(y) := Dψ_j(y)Γ_j(y)⁻¹∇F_j(y) (continuous on V_j). For x ∈ M_j = ψ_j(Y_j) let y_j(x) be the unique y ∈ Y_j with ψ_j(y) = x (ψ_j is injective on V_j) and put g(x) := Φ_j(y_j(x)); put g(x) := 0 for x ∉ ⋃_j M_j (well defined since the M_j are disjoint).
   - Defining property: g(ψ_j(y)) = Dψ_j(y)w with w = Γ_j⁻¹∇F_j, so it lies in Q_j(y), and ⟨g(ψ_j(y)), Dψ_j(y)e⟩ = ⟨Γ_j w, e⟩ = ⟨∇F_j(y), e⟩ = DF_j(y)e.
   - g is Borel. The inverse of the continuous bijection ψ_j|_{C_j} : C_j → E_j is continuous (compact domain, Hausdorff target). So h_j := Φ_j ∘ (ψ_j|_{C_j})⁻¹ is continuous on the compact set E_j, and g = h_j on the Borel set M_j ⊆ E_j. For Borel B ⊆ ℝ^P, g⁻¹(B) = ⋃_j (M_j ∩ h_j⁻¹(B)) ∪ ((ℝ^P ∖ ⋃_j M_j) if 0 ∈ B), which is Borel.
   - |g| ≤ L: for x = ψ_j(y) ∈ M_j write g(x) = Dψ_j(y)e. By step 8, |g(x)|² = ⟨g(x), Dψ_j(y)e⟩ = DF_j(y)e ≤ L|Dψ_j(y)e| = L|g(x)|, so |g(x)| ≤ L. Off ⋃_j M_j, g = 0.

10. With the final V_j, ψ_j, C_j, Y_j, F_j and g, properties (a)–(e) hold: (a) by step 2; (b) by steps 4–6; (c) by steps 4–6, since ψ_j(Y_j) = M_j; (d) by steps 5 and 7; (e) by step 9. ∎

## Key steps

1. c1_cover: M ⊆ N₀ ∪ ⋃ N_l with N_l embedded C¹ (n+1)-submanifolds.
2. Lindelöf gives countably many charts ψ: V → U, C¹, injective, with injective derivative.
3. On rational balls B̄ with B̄_{2r} ⊆ V, use c1_approx for (a Lipschitz extension of) f∘ψ. C_j = B̄ ∩ {f∘ψ = G_k} and F_j = G_k cover M up to a null set.
4. Disjointify (Remark 1.3): M_j and Y_j = C_j ∩ ψ_j⁻¹(M_j). Delete null sets through Borel null supersets.
5. Tangent planes: image_tangent for ψ_j(C'_j), then (TL) twice, (M_j, ψ_j(C'_j)) and (M_j, M), give T_xM = Dψ_j(y)(ℝ^{n+1}).
6. At density points of C_j, where F_j = f∘ψ_j on all of C_j, density_directions gives |DF_j(y)e| ≤ L|Dψ_j(y)e|.
7. g := Dψ_j Γ_j⁻¹∇F_j on ψ_j(Y_j), 0 elsewhere. It is Borel, satisfies the defining relation, and |g| ≤ L.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `python3 -I transitive import scan of the Contract's Poincare.SimonGMT imports (public import ...)`
- `grep -n '^theorem |^def ' simongmt Chapter03/Rectifiable.lean, Chapter02/{AreaFormula,WeightedArea,AreaCritical,AreaLipschitz,AreaDomain,CoareaProjection,CoareaLinear,WhitneyExtension,WhitneyJet,Lipschitz}.lean, Chapter03/{SubmanifoldCover,DisjointCover,Differential}.lean, Chapter06/{Forms,Currents}.lean`
- `grep -rn 'HasApproximateTangentSpaceAt.unique|exists_contDiff_one_extension_of_whitney|HasWhitneyC1Compatibility|area_image_criticalSet_eq_zero|integral_area_formula_of_injective_derivative|weighted_area_formula_of_injective_derivative|map_withDensity_areaJacobian_eq|integrableOn_image_iff_integrableOn_areaJacobian_smul|exists_isClosed_continuousOn_of_measurable|countablyRectifiable_iUnion' simongmt`
- `grep -rn 'ae_tendsto_measure_inter_div_of_measurableSet|LipschitzWith.integral_lineDeriv_mul_eq|Lp.dense_hasCompactSupport_contDiff|tendsto_tsum_of_dominated_convergence|alternatizeUncurryFin_apply|AlternatingMap.eq_smul_basis_det|det_to_matrix_orthonormalBasis_real|volume_preserving_piFinSuccAbove|PiLp.volume_preserving_ofLp|Measurable.lintegral_prod_right|exists_cthickening_subset_open|tendstoUniformlyOn_of_ae_tendsto|euclideanHausdorffMeasure_eq_volume|norm_alternatizeUncurryFin_le' mathlib`
- `#check probes in contract scope: ContinuousAlternatingMap.alternatizeUncurryFin, innerSL, ContinuousLinearMap.smulRight, (ℝ ∙ v)ᗮ, ‖v‖ₑ, GeometricCurrentOn.boundary, exists_measurable_superset_of_null`
- `dag.json scans: regex 'co-?area|area formula|Rademacher|tangential gradient|C¹ approx|Lusin|Jacobian|implicit function' over node statements; lean_name collision check for dor_lmbsf_* (1022 nodes, none)`
- `git grep dor_lmbsf_ over all local branches (no match)`
- `python3 -I verifier lean_contract.validate_lean_statement and gmt-compare.child_modules on the 12 statements; lake env lean /tmp/dor-sf-decomp/v2/All.lean (#print axioms DorSf.parent_from_children)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-e999363692/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/dor-sf-decomp/v2/All.lean`

Snapshot: project b4d606d, mathlib 25730c7c, simongmt 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, and the snapshot mathlib matches the package tree.

No existing declaration states a rectifiable co-area formula, a tangential gradient of a Lipschitz function, a slice family or the Lipschitz-cut-off Leibniz limit. Related nodes in other branches are unaccepted, reserved and have different types:
- codim1_rdo_c1_approximation;
- codim1_rdo_c1_piece_approxTangent;
- codim1_lur_rectifiable_area_formula;
- dimred_cs_sos_spine_coarea.
So all 12 children get fresh dor_lmbsf_ names.

Reusable library facts for the child proofs:
- SimonGMT Chapter02: injective area formulas in lintegral, Bochner and measure form (WeightedArea, AreaFormula); critical images null (AreaCritical); Whitney C¹ extension (WhitneyExtension/WhitneyJet); Rademacher and Lipschitz images (Lipschitz).
- SimonGMT Chapter01.Lusin.
- SimonGMT Chapter03: HasApproximateTangentSpaceAt.unique, countablyRectifiable_iUnion.
- Mathlib: Besicovitch density theorem, LipschitzWith.integral_lineDeriv_mul_eq, Lp.dense_hasCompactSupport_contDiff, Tannery's theorem, alternatizeUncurryFin_apply, volume-preserving coordinate splits.
- Some of these need extra imports, which are listed in the child proofs.

Lean checks:
- All 12 child types pass validate_lean_statement and elaborate in the exact comparator scope.
- The Lean assembly of the exact frozen parent type from tangential_gradient, slice_imreps and lipschitz_leibniz compiles with only propext, Classical.choice and Quot.sound.
- Interface checks (chart_pieces → piece lemmas; Besicovitch → density_directions) compile.
- MultiVector lacks SecondCountable/FiniteDimensional instance synthesis, so the child proofs use StronglyMeasurable compositions.
