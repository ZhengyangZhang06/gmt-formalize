# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_area-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_area-a1.polar_jacobian-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, facts (F1)–(F3) and step 4 (Jacobian), made explicit in coordinates. Notation: α := ⟨x,a⟩ > 0, β := ⟨x,e⟩, A := αe − βa (this is Ax), ρ := α² + β², x̂ := x/|x|, g := A/ρ (this is ∇f(x)), F̃(y) := (|y|, arctan(⟨y,e⟩/⟨y,a⟩)), D := fderiv ℝ F̃ x, (u_k)_{k ∈ Fin(dim T)} := stdOrthonormalBasis ℝ T (vectors of T viewed in ℝ^P), Γ_kl := (Du_k)_1(Du_l)_1 + (Du_k)_2(Du_l)_2, p_T := T.starProjection, π := Q.starProjection. Goal: sqrt(det Γ) = |p_T A|/|πx|².
1. (F1: πx = αa + βe and |πx|² = ρ > 0.) The family (a, e) is orthonormal (|a| = |e| = 1, ⟨a,e⟩ = 0), hence linearly independent, and span{a,e} ⊆ Q because a, e ∈ Q; since dim span{a,e} = 2 = dim Q, span{a,e} = Q (`Submodule.eq_of_le_of_finrank_eq`, `finrank_span_eq_card`). The vector w₀ := αa + βe lies in Q, and x − w₀ is orthogonal to every w = c₀a + c₁e ∈ Q: ⟨x − w₀, c₀a + c₁e⟩ = c₀(α − α) + c₁(β − β) = 0, using ⟨a,a⟩ = ⟨e,e⟩ = 1 and ⟨a,e⟩ = 0. Hence πx = w₀ (`Submodule.eq_starProjection_of_mem_of_inner_eq_zero`), and expanding ⟨w₀, w₀⟩ gives |πx|² = α² + β² = ρ. Since α > 0, ρ ≥ α² > 0.
2. (F2: A ⊥ x.) ⟨A, x⟩ = α⟨e,x⟩ − β⟨a,x⟩ = αβ − βα = 0.
3. (F3: the derivative of F̃ at x.) x ≠ 0 since ⟨x,a⟩ > 0 = ⟨0,a⟩. (a) The norm is differentiable at x with derivative v ↦ ⟨x,v⟩/|x|: |y| = sqrt(|y|²), the derivative of |y|² at x is v ↦ 2⟨x,v⟩ (`hasStrictFDerivAt_norm_sq`), and sqrt is differentiable at |x|² ≠ 0 with derivative 1/(2|x|) (`HasFDerivAt.sqrt`). (b) y ↦ ⟨y,e⟩ and y ↦ ⟨y,a⟩ are linear with derivatives v ↦ ⟨e,v⟩ and v ↦ ⟨a,v⟩ (`innerSL`, `real_inner_comm`). Since α ≠ 0, y ↦ ⟨y,a⟩⁻¹ has derivative v ↦ −⟨a,v⟩/α² (`hasFDerivAt_inv` composed with (b)), so by the product rule (`HasFDerivAt.mul`) q(y) := ⟨y,e⟩·⟨y,a⟩⁻¹ has derivative v ↦ ⟨e,v⟩/α − β⟨a,v⟩/α². (c) arctan has derivative 1/(1+t²) (`HasFDerivAt.arctan`), so y ↦ arctan(q(y)) has derivative v ↦ (1/(1 + β²/α²))·(⟨e,v⟩/α − β⟨a,v⟩/α²) = (α⟨e,v⟩ − β⟨a,v⟩)/(α² + β²) = ⟨A, v⟩/ρ. (d) The pair has the pair of derivatives (`HasFDerivAt.prodMk`); since y ↦ (|y|, arctan(⟨y,e⟩/⟨y,a⟩)) coincides with y ↦ (|y|, arctan(⟨y,e⟩·⟨y,a⟩⁻¹)) (t/s = t·s⁻¹; transfer with `HasFDerivAt.congr_of_eventuallyEq`), fderiv ℝ F̃ x equals this derivative (`HasFDerivAt.fderiv`). Hence for every v ∈ ℝ^P: (Dv)_1 = ⟨x,v⟩/|x| = ⟨x̂, v⟩ and (Dv)_2 = ⟨A, v⟩/ρ = ⟨g, v⟩ (the last identity is field arithmetic using α ≠ 0 and ρ ≠ 0).
4. (The 2×2 Gram determinant.) For k ∈ Fin(dim T) put a_k := ⟨x̂, u_k⟩ = ⟨x,u_k⟩/|x| and c_k := ⟨g, u_k⟩ = ⟨A,u_k⟩/ρ. By step 3, Γ_kl = a_k a_l + c_k c_l. Since dim T = 2 the index type is Fin 2 (state the identity for an index type Fin n with n = 2 and substitute n = 2, or reindex along finCongr with `Matrix.det_reindex_self`), and expanding with `Matrix.det_fin_two`:
   det Γ = (a_0² + c_0²)(a_1² + c_1²) − (a_0a_1 + c_0c_1)² = (a_0² + a_1²)(c_0² + c_1²) − (a_0c_0 + a_1c_1)² = (Σ_k a_k²)(Σ_k c_k²) − (Σ_k a_k c_k)²,
   because both middle expressions expand to (a_0c_1 − a_1c_0)² (Lagrange's identity). (In the parent's language: Γ = LᵀL for the 2×2 matrix L with rows (a_k)_k and (c_k)_k, so det Γ = (det L)²; in the orthonormal basis (x̂, τ) of T, det L = ±⟨∇f(x), τ⟩ = ±⟨g, τ⟩.)
5. (Parseval in T.) (u_k) is an orthonormal basis of T, so for y, z ∈ T: Σ_k ⟨y,u_k⟩² = |y|² and Σ_k ⟨y,u_k⟩⟨u_k,z⟩ = ⟨y,z⟩ (`OrthonormalBasis.sum_sq_inner_left`, `OrthonormalBasis.sum_inner_mul_inner`, applied in T to the elements x and p_T A of T). Moreover ⟨v, u_k⟩ = ⟨p_T v, u_k⟩ for every v ∈ ℝ^P, since v − p_T v ⊥ T ∋ u_k (`Submodule.starProjection_inner_eq_zero`). The hypothesis p_T x = x means x ∈ T (`Submodule.starProjection_eq_self_iff`). Therefore:
   (i) Σ_k a_k² = |x|²/|x|² = 1;
   (ii) Σ_k a_k c_k = (Σ_k ⟨x,u_k⟩⟨p_T A,u_k⟩)/(|x|ρ) = ⟨x, p_T A⟩/(|x|ρ) = ⟨p_T x, A⟩/(|x|ρ) = ⟨x, A⟩/(|x|ρ) = 0, using that p_T is self-adjoint (`Submodule.inner_starProjection_left_eq_right`) and step 2;
   (iii) Σ_k c_k² = Σ_k ⟨p_T A, u_k⟩²/ρ² = |p_T A|²/ρ².
6. (Conclusion.) By steps 4 and 5, det Γ = 1·|p_T A|²/ρ² − 0² = (|p_T A|/ρ)², so sqrt(det Γ) = |p_T A|/ρ (`Real.sqrt_sq`, as |p_T A|/ρ ≥ 0). By step 1, ρ = |πx|², so sqrt(det Γ) = |p_T(⟨x,a⟩e − ⟨x,e⟩a)|/|Q.starProjection x|², as claimed. ∎

## Key steps

1. (a, e) is an orthonormal basis of Q, so πx = ⟨x,a⟩a + ⟨x,e⟩e, |πx|² = ρ := ⟨x,a⟩² + ⟨x,e⟩² > 0, and A := ⟨x,a⟩e − ⟨x,e⟩a ⊥ x.
2. For ⟨x,a⟩ > 0: fderiv F̃ x v = (⟨x,v⟩/|x|, ⟨A,v⟩/ρ) (norm via sqrt of norm², arctan ∘ (⟨y,e⟩·⟨y,a⟩⁻¹) via inverse, product and chain rules).
3. With a_k = ⟨x,u_k⟩/|x|, c_k = ⟨A,u_k⟩/ρ the Gram matrix is a_k a_l + c_k c_l and, as dim T = 2, det Γ = (Σa_k²)(Σc_k²) − (Σa_k c_k)² (det_fin_two, Lagrange).
4. Parseval in T with x ∈ T and ⟨v,u_k⟩ = ⟨p_T v,u_k⟩: Σa_k² = 1, Σa_k c_k = ⟨x,A⟩/(|x|ρ) = 0, Σc_k² = |p_T A|²/ρ².
5. Hence det Γ = (|p_T A|/ρ)² and sqrt(det Γ) = |p_T A|/|πx|².

## Reference use

### local-project

Queries:
- `python3 over dag.json nodes (lean_name/lean_statement/status): idtp_cse_fibre_area_identities and its siblings; idtp_carrier_area_formula (speculative-ready); accepted imrep_approxTangent_starProjection_aesm, dorag_aa_ae_finrank_approxTangentPlane, cbr_imRep_measure_basic, dpf_det_gram_stdOrthonormalBasis_eq, dpf_aestronglyMeasurable_gramJacobian; cousin idtp_cse_rc_angle_fderiv; statements containing 'finrank ℝ (approxTangentPlane', 'stdOrthonormalBasis', '!₂[' or ℝ × ℝ with fderiv`
- `grep -c idtp_cse_fa_ dag.json (0); rg -l idtp_cse_fa_ nodes/ dag.json local-references/123e8435b4a2469b/project (no match); for f in .swarm-worktrees/*/gmt-ch07/GMT/Ch07/*.lean: grep -l idtp_cse_fa_ (no match)`
- `git show db9124843c:GMT/Ch07/Submission.lean | grep dorag_aa_ae_finrank_approxTangentPlane (accepted lemmas are delivered as `theorem Submission.X` in namespace GMT.Ch07)`
- `grep -n 'HasApproximateTangentSpaceAt.finrank_eq|HasApproximateTangentSpaceAt.unique|def CountablyRectifiable|def HasApproximateTangentSpaceAt' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn '!₂\[|volume_preserving_toLp|volume_preserving_ofLp|volume_preserving_finTwoArrow' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg 'setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable|restrict_withDensity|lintegral_withDensity_eq_lintegral_mul_non_measurable|apply_continuousLinearMap|ContinuousOn.isOpen_inter_preimage|contDiffAt_norm|hasStrictFDerivAt_norm_sq|HasFDerivAt.sqrt|HasFDerivAt.arctan|HasFDerivAt.prodMk|comp_fderiv|lintegral_comp_emb|aemeasurable_comp_iff|det_fin_two|det_reindex_self|sum_inner_mul_inner|sum_repr|starProjection_eq_self_iff|HasFDerivAt.div' .lake/packages/mathlib/Mathlib (same rev 25730c7c as the snapshot; no fderiv-form real quotient rule exists at this pin)`
- `lake env lean /tmp/fa-decomp-7c1e/check/{Stmts,Parent,C1,C3,Deriv}.lean and /tmp/fa-decomp-7c1e/verify/C2.lean (+ #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-2d6a9d83f4/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-2d6a9d83f4/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-18ac87081c/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/ArctanDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/tmp/fa-decomp-7c1e/check/Stmts.lean`
- `/tmp/fa-decomp-7c1e/check/Parent.lean`
- `/tmp/fa-decomp-7c1e/check/C1.lean`
- `/tmp/fa-decomp-7c1e/check/C3.lean`
- `/tmp/fa-decomp-7c1e/check/Deriv.lean`
- `/tmp/fa-decomp-7c1e/verify/C2.lean`
- `/tmp/fa-decomp-7c1e/scripts/jac_check.py`

The pins match. The workspace Submission.lean (GMT.Ch07 namespace, frozen opens) is the compiler authority; mathlib is 25730c7c, equal to the snapshot's mathlib_commit, and SimonGMT is 2b36630.

Reusable results already in the DAG:
- Accepted: dorag_aa_ae_finrank_approxTangentPlane (R.measure-a.e. finrank T_x = n), cbr_imRep_measure_basic (μHE⌞carrier ≪ R.measure) and imrep_approxTangent_starProjection_aesm. These replace the parent's direct use of the orients field and HasApproximateTangentSpaceAt.finrank_eq.
- Pending: idtp_carrier_area_formula (speculative-ready), which child 3 uses.
- Not reusable: dpf_det_gram_stdOrthonormalBasis_eq applies only to L : Euclid P →L Euclid P. No existing node gives the area formula into ℝ × ℝ or the polar-map Jacobian. The cousin idtp_cse_rc_angle_fderiv is still pending.

All Mathlib names cited in the child proofs exist at the pin. The proofs avoid the missing fderiv-form quotient rule by using the inverse and product rules.

The proposed idtp_cse_fa_* names are unreserved. All four types elaborate. The parent is kernel-checked from the three child types plus the accepted-lemma types, with standard axioms only. Children 1 and 2 are fully proved, and child 3 is proved relative to the carrier-area-formula type.
