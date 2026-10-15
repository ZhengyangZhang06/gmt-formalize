# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1.planar_orientation_sign-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 ("Orientation") of the parent-supplied proof, which this child states separately; Simon Ch. 3, Definition 1.4 (approximate tangent space) and Ch. 6, 3.1 (orientation of an integer multiplicity current). Notation: H^n := μHE[n]; for an n-covector α (a continuous alternating n-linear form on ℝ^P) and a family σ = (σ_1, …, σ_n), α(σ) := α(σ_1, …, σ_n); η_{x,r}(y) := r^{−1}(y − x) (SimonGMT blowUpMap x r); B(q, ρ) and B̄(q, ρ) are the open and closed balls.
1. (The plane.) τ is orthonormal, hence linearly independent (Orthonormal.linearIndependent), so Q = span{τ_1, …, τ_n} is a linear subspace of dimension n (finrank_span_eq_card). Being finite-dimensional, Q is closed (Submodule.closed_of_finiteDimensional), in particular Borel.
2. (Almost every point of M lies in Q.) (H^n⌞M)(ℝ^P ∖ Q) = H^n(M ∖ Q) = 0, so x ∈ Q for H^n⌞M-a.e. x.
3. (Approximate tangent planes.) By the field `orients` of IMRep, for H^n⌞M-a.e. x there is a linear subspace Q_x with HasApproximateTangentSpaceAt n M x Q_x and IsUnitOrientationOf (ξ(x)) Q_x. Intersecting with step 2, fix from now on a point x of the full-measure set where both hold and x ∈ Q. By the definition of HasApproximateTangentSpaceAt, finrank Q_x = n and, for every f ∈ C_c(ℝ^P, ℝ), ∫_{η_{x,r}(M)} f dH^n → ∫_{Q_x} f dH^n as r ↓ 0.
4. (Q_x ⊆ Q; argument of the supplied step 4.) Suppose some q ∈ Q_x does not lie in Q. As Q is closed, d := dist(q, Q) > 0. Let f(y) := max(0, d/2 − |y − q|). Then f is continuous, f ≥ 0, f vanishes outside the compact ball B̄(q, d/2) (so f ∈ C_c(ℝ^P, ℝ)), f > 0 on B(q, d/2), and f = 0 on Q (for y ∈ Q, |y − q| ≥ d > d/2).
 (a) For r > 0, η_{x,r}(M) ⊆ η_{x,r}(M ∩ Q) ∪ η_{x,r}(M ∖ Q). Since x ∈ Q and Q is a linear subspace, η_{x,r}(M ∩ Q) ⊆ Q, where f = 0. The map η_{x,r} is a similarity of ratio r^{−1}, so H^n(η_{x,r}(M ∖ Q)) = r^{−n}H^n(M ∖ Q) = 0. Hence f = 0 H^n-a.e. on η_{x,r}(M), and ∫_{η_{x,r}(M)} f dH^n = 0 for every r > 0.
 (b) By step 3 applied to this f, ∫_{Q_x} f dH^n = lim_{r↓0} ∫_{η_{x,r}(M)} f dH^n = 0.
 (c) On the other hand finrank Q_x = n, so H^n⌞Q_x is a Radon measure whose support is all of Q_x (SimonGMT Chapter03 support_euclideanHausdorffMeasure_restrict_submodule; via an isometric parametrization of Q_x by ℝ^n, H^n⌞Q_x is Lebesgue measure). As q ∈ Q_x, (H^n⌞Q_x)(B(q, d/2)) > 0. The function f is continuous with compact support, hence H^n⌞Q_x-integrable, f ≥ 0 and f > 0 on B(q, d/2); therefore ∫_{Q_x} f dH^n > 0 (integral_pos_iff_support_of_nonneg), contradicting (b). Hence Q_x ⊆ Q.
 [This step is exactly the accepted sibling atsm_approxTangent_le_of_flat (Submission.atsm_approxTangent_le_of_flat), applied with N := Q (as a set), M := R.carrier, the point x, the plane Q_x and T := Q: its hypotheses are H^n(M ∖ Q) = 0 and the flatness of Q at x along Q, which holds trivially — for every ε > 0 take ρ := 1, and for z ∈ Q take t := z − x ∈ Q (both z and x lie in Q), so that ‖z − x − t‖ = 0 ≤ ε‖z − x‖; its conclusion is Q_x ≤ Q.]
5. (Q_x = Q.) Q_x ≤ Q and finrank Q_x = n = finrank Q (steps 1 and 3), so Q_x = Q (Submodule.eq_of_le_of_finrank_eq).
6. (Sign.) Let ξ_Q be the n-vector α ↦ α(τ) (evaluation at τ: linear in α and continuous, |α(τ)| ≤ ‖α‖·Π_i|τ_i| = ‖α‖; in Lean the continuous linear map (ContinuousMultilinearMap.apply ℝ (fun _ => Euclid P) ℝ τ).comp (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ)). ξ_Q is a unit orientation of Q: IsUnitOrientationOf ξ_Q Q holds with the orthonormal family τ itself, span(range τ) = Q and the sign +. By steps 3 and 5, ξ(x) is a unit orientation of Q as well. Two unit orientations of the same subspace agree up to sign (accepted sibling dgcr_unitOrientation_eq_or_neg; reason: if ξ(x)(α) = ±α(τ') with τ' an orthonormal basis of Q, then τ'_j = Σ_i A_{ij}τ_i with A_{ij} = ⟨τ_i, τ'_j⟩ an orthogonal matrix, so α(τ') = det(A)·α(τ) with det A = ±1 for every alternating α). Hence ξ(x) = ξ_Q or ξ(x) = −ξ_Q, i.e. ξ(x)(α) = α(τ) for every α, or ξ(x)(α) = −α(τ) for every α.
7. (Conclusion.) Steps 3–6 apply to H^n⌞M-a.e. x, which is the assertion. (The argument does not use n ≥ 1: for n = 0, Q = {0} and every n-dimensional subspace is {0}.) ∎

Formalization note (verified during the decomposition check; not part of the mathematical argument). The following single theorem proves exactly this frozen statement. It was compiled with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b36630) after `import GMT.Ch07.Submission` only, inside `namespace GMT.Ch07` with the contract opens. It uses exactly the declared dependencies Submission.atsm_approxTangent_le_of_flat, Submission.dgcr_unitOrientation_eq_or_neg (by these Submission.* names) and no import or helper declaration. In a build where those dependencies were sorry stubs, `#print axioms` showed only propext, Classical.choice and Quot.sound besides the stubs; in a fully merged build containing the dependencies' accepted code it gives exactly propext, Classical.choice and Quot.sound. It follows the numbered steps above and may be used directly as the leaf candidate:
```lean
theorem Submission.idtp_pc_orient_ae_eq_or_neg : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (τ : Fin n → Euclid P), Orthonormal ℝ τ → μHE[n] (R.carrier \ (Submodule.span ℝ (Set.range τ) : Set (Euclid P))) = 0 → ∀ᵐ x ∂(μHE[n].restrict R.carrier), (∀ α : Covector (Euclid P) n, R.orient x α = α τ) ∨ (∀ α : Covector (Euclid P) n, R.orient x α = -α τ) := by
  intro P n U R τ hτ hnull
  set Q : Submodule ℝ (Euclid P) := Submodule.span ℝ (Set.range τ) with hQ
  have hQm : MeasurableSet (Q : Set (Euclid P)) := (Submodule.closed_of_finiteDimensional _).measurableSet
  have hfin : Module.finrank ℝ Q = n := by
    rw [hQ, finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin]
  let ξQ : MultiVector P n :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euclid P) ℝ τ).comp
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ)
  have hξQ : ∀ α : Covector (Euclid P) n, ξQ α = α τ := fun α => rfl
  have hξQo : IsUnitOrientationOf ξQ Q := ⟨τ, hτ, rfl, Or.inl hξQ⟩
  have hmemQ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ (Q : Set (Euclid P)) := by
    rw [ae_restrict_iff' R.measurableSet_carrier]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hxM
    by_contra h
    exact hx ⟨hxM, h⟩
  filter_upwards [R.orients, hmemQ] with x hx hxQ
  obtain ⟨Qx, htan, hor⟩ := hx
  have hflat : ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ (Q : Set (Euclid P)), dist z x < ρ →
      ∃ t ∈ Q, ‖z - x - t‖ ≤ ε * ‖z - x‖ := by
    intro ε hε
    refine ⟨1, one_pos, fun z hz _ => ⟨z - x, Q.sub_mem hz hxQ, ?_⟩⟩
    simp only [sub_self, norm_zero]
    positivity
  have hle : Qx ≤ Q := Submission.atsm_approxTangent_le_of_flat P n Q R.carrier x Qx Q hnull hflat htan
  have heq : Qx = Q := Submodule.eq_of_le_of_finrank_eq hle (htan.1.trans hfin.symm)
  rw [heq] at hor
  rcases Submission.dgcr_unitOrientation_eq_or_neg P n Q ξQ (R.orient x) hξQo hor with h | h
  · left; intro α; rw [h]; exact hξQ α
  · right; intro α; rw [h]; rfl
```

## Key steps

1. H^n(M ∖ Q) = 0 gives x ∈ Q for H^n⌞M-a.e. x; `orients` gives Q_x with HasApproximateTangentSpaceAt n M x Q_x and ξ(x) a unit orientation of Q_x.
2. Q_x ⊆ Q: a test function f ≥ 0 vanishing on Q has ∫_{η_{x,r}(M)} f dH^n = 0, hence ∫_{Q_x} f = 0, impossible if Q_x ⊄ Q (accepted atsm_approxTangent_le_of_flat with N = T = Q).
3. finrank Q_x = n = finrank Q, so Q_x = Q.
4. ξ(x) and ξ_Q = (α ↦ α(τ)) are unit orientations of Q, so ξ(x) = ±ξ_Q (accepted dgcr_unitOrientation_eq_or_neg).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (against manifest.json)`
- `python3 scan of dag.json: accepted nodes (status, lean_name, lean_statement, candidate_commit) for dimred_*, imrep_*, atsm_*, dgcr_*, dgid_*, dgoj_*, rsdic_*, regcomp_*; duplicate lean_names; cross-branch reuse precedents (children whose parent field differs)`
- `rg -n 'idtp_pc_' over dag.json, nodes/, the snapshot and all git refs (no match)`
- `git show <candidate>:GMT/Ch07/Submission.lean for 01ae2c59, d15b5cf4, 038573e4, d5e029d5, c1d60848, dcc3f4b7, 8a6855aa; diff against the contract (added declarations, imports, removed lines)`
- `grep -n theorem/def in .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean, Chapter03/Rectifiable.lean, Chapter06/{Forms,Currents,Mass,CurrentLocalEquality}.lean`
- `rg -n 'Isometry.map_euclideanHausdorffMeasure|EuclideanSpace.euclideanHausdorffMeasure_eq_volume|exists_cthickening_subset_open|eq_of_le_of_finrank_eq|one_of_mem_closedBall' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `lake env lean /tmp/pc-decomp-k7q2/check/Probe2.lean and Names.lean (#check of the cited Mathlib/SimonGMT names after import GMT.Ch07.Submission; Chapter08 names unknown)`
- `lake env lean /tmp/pc-decomp-k7q2/check/{Types,Parent,Children}.lean and /tmp/pc-decomp-k7q2/merged/Merged.lean (#print axioms)`
- `sed -n 560,640p book/chapter-06.txt (Simon 2.34, Constancy Theorem and proof); sed -n 1830,1880p book/chapter-06.txt (deformation theorem (26)–(27))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-77d7be4677/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-77d7be4677/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/rlcr-plan-v1.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/pc-decomp-k7q2/check/Types.lean`
- `/tmp/pc-decomp-k7q2/check/Parent.lean`
- `/tmp/pc-decomp-k7q2/check/Children.lean`
- `/tmp/pc-decomp-k7q2/merged/Merged.lean`

The pins match. The snapshot is project b4d606d (equal to workspace HEAD) with mathlib 25730c7c, and SimonGMT is 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Reused accepted declarations. dimred_im_mass_measure, imrep_carrier_sdiff_support_null, atsm_approxTangent_le_of_flat, dgcr_unitOrientation_eq_or_neg, dgcr_smooth_tests_to_C1_tests and dgcr_bwd_coordinate_covector are comparator-accepted and are reused at byte-identical types. Their candidates only add pairwise-disjoint declarations to the contract.

Library support.
- Mathlib supplies Isometry.map_euclideanHausdorffMeasure and EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:141,187).
- Mathlib also supplies IsCompact.exists_cthickening_subset_open, Submodule.eq_of_le_of_finrank_eq, the ContDiffBump API and the MeasurableEmbedding transfer lemmas, all inside the frozen import closure.
- SimonGMT supplies exteriorDerivative_apply (Chapter06/Forms.lean:119) and support_euclideanHausdorffMeasure_restrict_submodule (Chapter03).
- SimonGMT's ae_eq_const_of_weak_coordinate_derivatives_zero (Chapter08/DistributionalConstancy.lean) is outside the frozen import closure. It is applied in this node's parent proof with an added import, following the accepted precedent 8a6855aa.

Names. No idtp_pc_* name occurs anywhere.

Lean. All 12 child types elaborate. The exact parent type follows from three child types plus the SimonGMT theorem. Each new child has a verified single-theorem proof from its declared dependencies. A fully merged build with the reused accepted code has no sorry, and all seven new declarations depend only on propext, Classical.choice and Quot.sound.
