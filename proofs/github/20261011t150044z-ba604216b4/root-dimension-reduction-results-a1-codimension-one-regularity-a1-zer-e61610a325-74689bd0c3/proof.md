# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_blowup_limit-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_blowup_limit-a1.graph_representation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 8 of the supplied proof of the selected node (representation (H3)), together with the identities of its step 2 that it uses; Simon 7.5.5 (chapter-07.txt lines 790–901). The two deep inputs of that step are blowup_region (η_#∂[[E]] = ∂[[η(E)]]) and graph_area (the area formula for C¹ graphs). Both are siblings of the parent node that are not yet accepted, so this lemma takes their conclusions as hypotheses (ii) and (iii). The selected node discharges them by applying Submission.codim1_zsl_blowUp_isBoundaryOfRegion and Submission.codim1_zsl_graph_area_formula. Departure: the supplied step (8b) also shows that Y = G(F' ∩ B_R) is measurable; that is not needed, since only η(E) must be measurable, so it is omitted. The set F' equals the supplied F'_i = {w ∈ D_i : G_i(w) ∈ η_i(E)} by (4.1) below.

Notation. |·| Euclidean norm. B_r := ball(0, r) in ℝ^{n+1} (in ℝ^k or ℝ^P where indicated). η(z) = −λ^{−1}y + λ^{−1}z = λ^{−1}(z − y). D := {w : s + λw ∈ B_{δ₁}}. dω := exteriorDerivative ω. For a linear map L and an (n+1)-covector α, α(Le) := α(Le_0, …, Le_n).

1. (Measurability of F'.) By (v), u is continuous on B_{δ₁}, hence so is Γ. The function Γ̂ equal to Γ on B_{δ₁} and to 0 outside is Borel measurable (ContinuousOn.measurable_piecewise: B_{δ₁} is measurable and a constant is continuous on the complement). Thus A₀ := {v ∈ B_{δ₁} : Γ(v) ∈ E} = B_{δ₁} ∩ Γ̂^{−1}(E) is measurable, by (i). F' is the preimage of A₀ under the continuous map w ↦ s + λw, so it is measurable.
Now fix R ∈ ℝ with |s| + λR < δ₁, |t| + λR < δ₂ and ball(y, λR) ⊆ U, and ω ∈ 𝒟^n(ℝ^P) with tsupport ω ⊆ ball(0, R).
2. (The dilation.) For all z, e ∈ ℝ^P, η(y + λz) = z and y + λη(e) = e (λ ≠ 0). Hence η(E) = {z : y + λz ∈ E}, which is measurable as the preimage of E under a continuous map. Also ball(0, R) ⊆ η(U): if |z| < R, then |(y + λz) − y| = λ|z| < λR, so y + λz ∈ ball(y, λR) ⊆ U and z = η(y + λz).
3. (Evaluation of the blow-up.) ω is C^∞ with compact support, and tsupport ω ⊆ ball(0, R) ⊆ η(U). By the definition of currentEval, currentEval(η_#T)(ω) = η_#T(ω̃), where ω̃ ∈ 𝒟^n(η(U)) has underlying form ω. By (ii), currentEval(η_#T)(ω) = ∫_{η(E)} f dH^{n+1}, where f(z) := ξ_N(y + λz)(dω(z)).
4. (Pythagoras and two identities.) For a ∈ ℝ^{n+1} and b ∈ ℝ^k, |ιa + ι'b|² = |a|² + |b|² by (iv) and the isometry property, so |a| ≤ |ιa + ι'b| and |b| ≤ |ιa + ι'b|. For every w ∈ ℝ^{n+1}, (viii) and linearity give
 y + λG(w) = x + ιs + ι't + ι(λw) + ι'(u(s + λw) − t) = x + ι(s + λw) + ι'u(s + λw) = Γ(s + λw).   (4.1)
Hence G(w) = η(Γ(s + λw)) by step 2.
5. (Y ⊆ η(E).) Put A := F' ∩ B_R and Y := G(A). For w ∈ A, Γ(s + λw) ∈ E, so y + λG(w) ∈ E by (4.1), i.e. G(w) ∈ η(E) by step 2.
6. (f vanishes on η(E) ∖ Y.) Let z ∈ η(E) ∖ Y.
 (a) If |z| ≥ R, then z ∉ ball(0, R) ⊇ tsupport ω ⊇ tsupport dω (tsupport_exteriorDerivative_subset). So dω(z) = 0 (image_eq_zero_of_notMem_tsupport) and f(z) = ξ_N(y + λz)(0) = 0.
 (b) The case |z| < R cannot occur. Suppose |z| < R and put e := y + λz. Then e ∈ E ⊆ N (step 2 and (i)). Write z = ιa + ι'b (iv); by step 4, |a|, |b| ≤ |z| < R. By (viii), e = x + ι(s + λa) + ι'(t + λb), where |s + λa| ≤ |s| + λ|a| < |s| + λR < δ₁ and |t + λb| < |t| + λR < δ₂. So e ∈ N ∩ {x + ιv + ι'w : |v| < δ₁, |w| < δ₂}, and (vi) gives e = Γ(v) for some v ∈ B_{δ₁}. Put w := λ^{−1}(v − s), so that s + λw = v. Then s + λw ∈ B_{δ₁} and Γ(s + λw) = e ∈ E, i.e. w ∈ F'. By (4.1), y + λG(w) = Γ(v) = e = y + λz, so G(w) = z. By step 4, |w| ≤ |ιw + ι'g(w)| = |z| < R, so w ∈ B_R. Hence w ∈ A and z = G(w) ∈ Y, a contradiction.
7. (Restriction of the integral.) η(E) is measurable (step 2), Y ⊆ η(E) (step 5) and f = 0 on η(E) ∖ Y (step 6). So ∫_{η(E)} f dH^{n+1} = ∫_Y f dH^{n+1} (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero; no integrability is needed).
8. (Area formula.) D is open, as the preimage of the open ball B_{δ₁} under a continuous map. g is C¹ on D: the affine map w ↦ s + λw maps D into B_{δ₁}, where u is C¹ (ContDiffOn.comp), and subtracting t and multiplying by λ^{−1} preserve C¹. A = F' ∩ B_R is measurable (step 1) and A ⊆ D. Hypothesis (iii) with g̃ := g, D̃ := D, Ã := A and f gives ∫_Y f dH^{n+1} = ∫_A J(w)·f(G(w)) dw, where J(w) := √det(DG(w)*∘DG(w)).
9. (The derivative of G.) Let w ∈ D and v := s + λw ∈ B_{δ₁}. u is differentiable at v (C¹ on the open ball); let L := Du(v). The affine map w ↦ s + λw has derivative λ·id. So w ↦ u(s + λw) has derivative L∘(λ·id) at w, and g has derivative λ^{−1}·(L∘(λ·id)) = L at w. Hence DG(w) = ι + ι'∘L. Likewise Γ has derivative ι + ι'∘L at v. So DG(w) = DΓ(v) as continuous linear maps.
10. (Pointwise identity.) Let w ∈ A and v := s + λw ∈ B_{δ₁}. By step 9 and (4.1), J(w) = √det(DΓ(v)*∘DΓ(v)) and f(G(w)) = ξ_N(y + λG(w))(dω(G(w))) = ξ_N(Γ(v))(α), where α := dω(G(w)). By (vii) at v with this α, J(w)·f(G(w)) = α(DΓ(v)e) = dω(G(w))(DG(w)e).
11. (Conclusion.) A is measurable, so step 10 and setIntegral_congr_fun give ∫_A J(w)·f(G(w)) dw = ∫_A dω(G(w))(DG(w)e) dw. Steps 3, 7, 8 and 11 give currentEval(η_#T)(ω) = ∫_{F'∩B_R} dω(G(w))(DG(w)e_0, …, DG(w)e_n) dw. ∎

Formalization notes (this exact frozen type was proved in a scratch build with standard axioms only). For currentEval use unfold currentEval and rw [dite_eq_left h], then apply hypothesis (ii) to ⟨ω, h⟩. For η(E) measurable use η(E) = (z ↦ y + λ•z)⁻¹(E). For Pythagoras use norm_add_sq_eq_norm_sq_add_norm_sq_real with nlinarith. For the derivatives use ContinuousLinearMap.hasFDerivAt applied to ι.toContinuousLinearMap and ι'.toContinuousLinearMap, together with HasFDerivAt.comp, .const_add, .sub_const, .const_smul, .add and .fderiv. ContDiffOn.differentiableOn takes 1 ≠ 0. The final rewrite is rw [hcur, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero …, harea'], then setIntegral_congr_fun, then rw [DG(w) = DΓ(v), (4.1)] and exact (hjac v hv _).symm.

## Key steps

1. F' is the affine preimage of {v ∈ B_{δ₁} : Γ(v) ∈ E}, which is measurable because Γ is continuous on the open ball.
2. ball(0, R) ⊆ η(U), so currentEval(η_#T)(ω) = ∫_{η(E)} ξ_N(y + λz)(dω(z)) dH^{n+1} by hypothesis (ii).
3. y + λG(w) = Γ(s + λw). The chart identity (vi) and Pythagoras put every point of η(E) ∩ ball(0, R) in Y = G(F' ∩ B_R) ⊆ η(E), and dω = 0 off ball(0, R). So the integral is over Y.
4. The area formula (iii) turns it into ∫_{F'∩B_R} J·(f∘G). DG(w) = DΓ(s + λw) and the Jacobian orientation identity (vii) turn J·(f∘G) into dω(G)(DG e).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; grep -n '"simongmt"' -A8 local-references/123e8435b4a2469b/project/lake-manifest.json`
- `sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `python3 scans of dag.json: status, lean_name and depends_on of the zero_scale_limit_plane children and of testform_correspondence-a1; lean_statement lookup of codim1_zsl_blowUp_isBoundaryOfRegion, codim1_zsl_graph_area_formula, codim1_zsl_flat_graph_limit, dtc_blowUp_testForm_corr and codim1_zsl_graph_blowup_limit (byte equality with the handoff); scan of lean statements containing 'blowUp' together with 'massOn' or 'covectorEuclideanNorm'`
- `python3 dump of the parent's decomposition-v2.json (subproblem statements and Lean types) and comparison of its testform_corr entry with the accepted node's parent-child-handoff.json (natural proof and key steps byte-equal)`
- `grep -n 'def check_source_delta' -A40 leaf_verification.py; grep -n '_existing_lean_name_problem|_solve_children|_install_parent_supplied_child_handoff|prerequisite_ids' runtime.py`
- `grep -n 'def IsTestForm|abbrev exteriorDerivative|theorem exteriorDerivative_apply|def covectorEuclideanNorm|def massAdmissibleOn|def GeometricCurrentOn.massOn|theorem GeometricCurrentOn.le_massOn|def testFormOnSubmodule|structure GeometricCurrentOn|theorem tsupport_exteriorDerivative_subset' simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents,Mass}.lean; sed -n 1,330p GMT/Ch07/Contract.lean (currentEval, ConvergesWeakly, dilation, blowUp, IsBoundaryOfRegion)`
- `grep -rn 'ContinuousOn.measurable_piecewise|setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|setIntegral_congr_fun|IsCompact.tendsto_subseq|norm_image_sub_le_of_norm_fderiv_le|ContDiffOn.continuousOn_fderiv_of_isOpen' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `lake env lean /tmp/gbl-split/Names.lean (#check of about 50 cited Mathlib/SimonGMT lemmas)`
- `lake env lean /tmp/gbl-split/FinalTypes.lean; lake env lean /tmp/gbl-split/FinalAssembly.lean (#print axioms Submission.codim1_zsl_graph_blowup_limit)`
- `lake env lean /tmp/gbl-split/proofs/{A,B,C,D}_work.lean with #print axioms (scratch proofs of the four new children)`
- `for r in $(git for-each-ref --format='%(objectname)' | sort -u): git grep -q -e codim1_zsl_gbl $r -- 'GMT/*.lean' (positive control dtc_blowUp_testForm_corr); grep -c of each new name in dag.json, .lake/packages/simongmt, .lake/packages/mathlib/Mathlib, GMT/`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0d752561a6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1-testform-correspondence-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/tmp/gbl-split/Names.lean`
- `/tmp/gbl-split/FinalTypes.lean`
- `/tmp/gbl-split/FinalAssembly.lean`
- `/tmp/gbl-split/proofs/A_work.lean`
- `/tmp/gbl-split/proofs/B_work.lean`
- `/tmp/gbl-split/proofs/C_work.lean`
- `/tmp/gbl-split/proofs/D_work.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib. The snapshot lake-manifest pins simongmt 2b366308, equal to .lake/packages/simongmt. The snapshot Contract.lean and the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
DAG.
- The selected node is 'decomposing' at depth 4, and its frozen type in dag.json equals the handoff's.
- Its dependencies blowup_region, graph_area and flat_limit are 'decomposing' under another parent. They therefore cannot be reused as children here; graph_representation takes the first two as hypotheses.
- dtc_blowUp_testForm_corr is accepted (candidate 5e184fbc), with type and statement byte-equal to the reused entry.
- No accepted node already states the needed blow-up mass bound for moving centres. The nearest are dtc_blowUp_massOn_image (fixed W, accepted) and dtc_bc_bh_blowUp_massOn_ball_bounded (fixed centre, unaccepted).
Library.
- The SimonGMT and Contract definitions match the children's proofs: IsTestForm = C^∞ ∧ compact support, TestFormOn = IsTestForm ∧ tsupport ⊆ U, exteriorDerivative = extDeriv, tsupport_exteriorDerivative_subset, massAdmissibleOn, le_massOn, covectorEuclideanNorm, and currentEval as a dite on IsTestForm ∧ tsupport ⊆ domain.
- Every cited Mathlib lemma exists in the snapshot, e.g. ContinuousOn.measurable_piecewise (BorelSpace/Basic.lean:523), setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (Bochner/Set.lean:466), setIntegral_congr_fun (Bochner/Set.lean:73), IsCompact.tendsto_subseq (Topology/Sequences.lean:298), Convex.norm_image_sub_le_of_norm_fderiv_le (MeanValue.lean:499) and ContDiffOn.continuousOn_fderiv_of_isOpen (ContDiff/Defs.lean:916). Measurable.measurableSet_preimage does not exist and is not cited.
Lean.
- All 5 child types elaborate.
- With the children and the 3 unaccepted dependencies as axioms, the selected type is proved, using only standard axioms besides those declarations.
- Scratch proofs of all 4 new children compile against their exact types without sorry.
- New names have 0 occurrences anywhere checked; the positive control was found.
