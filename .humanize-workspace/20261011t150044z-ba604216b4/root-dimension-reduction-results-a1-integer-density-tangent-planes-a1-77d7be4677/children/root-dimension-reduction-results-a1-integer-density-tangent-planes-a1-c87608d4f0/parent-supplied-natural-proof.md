# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1.signed_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1, 2, 4 and 5 of the parent-supplied proof (Simon Ch. 6, 3.1–3.2 and the proof of the Constancy Theorem 2.34): the representation S = τ(M, θ, ξ), the carrier lying in Q, the orientation ±ξ_Q, and the signed integer density g := 1_M·ε·θ with μ = |g|·H^n⌞(V ∩ Q). Notation: H^n := μHE[n]; for an n-covector α, α(τ) := α(τ_1, …, τ_n); |g(x)| := ‖g x‖ₑ; 1_A is the indicator function of A.
1. (Representation.) Since S is integer multiplicity, choose R = (M, θ, ξ) ∈ IMRep V n with R.Represents S. Thus M ⊆ V is Borel, θ : ℝ^P → ℕ is measurable with θ ≥ 1 on M, ∫_{M∩K} θ dH^n < ∞ for every compact K ⊆ V (field locallyIntegrable_mult), ξ is a.e.-strongly measurable for H^n⌞M, and S(ω) = R.action(ω) = ∫_M θ(x)·ξ(x)(ω(x)) dH^n(x) for every ω ∈ 𝒟^n(V). Let μ := R.measure = (H^n⌞M).withDensity θ.
2. (Mass, supplied step 1.) By the accepted sibling dimred_im_mass_measure (part (a); V is open and R represents S), M_W(S) = μ(W) for every open W ⊆ V.
3. (Carrier in the plane, supplied step 2.) H^n(M ∖ Q) = 0. Indeed, by the accepted sibling imrep_carrier_sdiff_support_null (V open, R represents S), H^n(M ∖ spt S) = 0, and M ∖ Q ⊆ M ∖ spt S because spt S ⊆ Q. [Equivalently, by the supplied argument: every x ∈ V ∖ Q lies outside spt S, so by dimred_im_mass_measure (b) it has a ball of μ-measure 0; by Lindelöf countably many such balls cover V ∖ Q, so μ(V ∖ Q) = 0, and H^n(M ∖ Q) ≤ μ(M ∖ Q) ≤ μ(V ∖ Q) = 0 because θ ≥ 1 on M ⊆ V.]
4. (Orientation, supplied step 4.) By the sibling child planar_orientation_sign (idtp_pc_orient_ae_eq_or_neg) applied to R, τ and step 3: for H^n⌞M-a.e. x, either ξ(x)(α) = α(τ) for all n-covectors α, or ξ(x)(α) = −α(τ) for all α. Call such points x good. As M is measurable, the set of x ∈ M that are not good is H^n-null; equivalently, for H^n-a.e. x ∈ ℝ^P, x ∈ M implies that x is good (ae_restrict_iff').
5. (Sign function.) Fix an n-covector β₀ with β₀(τ) = 1: let δ be the determinant n-form of ℝ^n (δ(c_1, …, c_n) = det of the matrix with columns c_j; continuous, n-linear and alternating; δ(e_1, …, e_n) = 1), let ι* : ℝ^P → ℝ^n, ι*(y) := (⟨τ_1, y⟩, …, ⟨τ_n, y⟩) (continuous linear), and put β₀(w_1, …, w_n) := δ(ι*w_1, …, ι*w_n), i.e. β₀(w) = det(⟨τ_i, w_j⟩)_{i,j}; then β₀(τ) = δ(e_1, …, e_n) = 1 because ι*(τ_j) = e_j by orthonormality (for n = 0, β₀ is the constant 1). Put ε(x) := ξ(x)(β₀). Then ε is a.e.-strongly measurable for H^n⌞M (composition of ξ with the continuous linear evaluation at β₀), and at every good x: ε(x) = ±β₀(τ) = ±1, ε(x) ∈ {1, −1}, and ξ(x)(α) = ε(x)·α(τ) for every n-covector α.
6. (Definition of g, supplied step 5.) Let g := 1_M·θ·ε, i.e. g(x) = θ(x)ε(x) for x ∈ M and g(x) = 0 for x ∉ M. By steps 4 and 5, for H^n-a.e. x ∈ ℝ^P: (a) g(x) ∈ ℤ (g(x) = ±θ(x) at good points of M, g(x) = 0 off M); (b) |g(x)| = 1_M(x)θ(x); (c) if x ∈ M then θ(x)ξ(x)(α) = g(x)α(τ) for every α.
7. ((i)–(iii).) (i): θ is measurable and ε is a.e.-strongly measurable for H^n⌞M, so θε is a.e.-strongly measurable for H^n⌞M; as M is measurable, its extension by 0, which is g, is a.e.-strongly measurable for H^n (aestronglyMeasurable_indicator_iff), hence for H^n⌞Q. (ii): 6(a) holds H^n-a.e., hence H^n⌞Q-a.e. (iii): for compact K ⊆ V, by 6(b), ∫_{K∩Q} |g| dH^n ≤ ∫_K |g| dH^n = ∫_K 1_M θ dH^n = ∫_{M∩K} θ dH^n < ∞ (step 1).
8. ((iv), the current identity.) Let ω ∈ 𝒟^n(V) and F(x) := g(x)·ω(x)(τ). By step 1, S(ω) = ∫_M θ ξ(ω) dH^n = ∫_{ℝ^P} 1_M θ ξ(ω) dH^n, and ∫_{V∩Q} F dH^n = ∫_{ℝ^P} 1_{V∩Q} F dH^n. The two integrands agree H^n-a.e.: at H^n-a.e. x ∈ M we have x ∈ Q (step 3) and x ∈ V (M ⊆ V), so both equal θ(x)ξ(x)(ω(x)) = g(x)ω(x)(τ) by 6(c); at x ∉ M the first is 0 and the second is 0 as well, since g(x) = 0. Functions that agree a.e. have the same Bochner integral (no integrability is needed for this), so S(ω) = ∫_{V∩Q} g(x)ω(x)(τ) dH^n(x).
9. ((v), the mass identity; supplied step 5's μ = |g|·H^n⌞(V ∩ Q).) Let W ⊆ V be open. By step 2 and the definition of μ, M_W(S) = μ(W) = ∫_W θ d(H^n⌞M) = ∫_{W∩M} θ dH^n = ∫_W 1_M θ dH^n (withDensity_apply, W measurable; Measure.restrict_restrict; lintegral_indicator). By 6(b), ∫_W 1_M θ dH^n = ∫_W |g| dH^n. Finally |g| = 0 H^n-a.e. on W ∖ Q (g = 0 off M, and M ∖ Q is H^n-null by step 3), so ∫_W |g| dH^n = ∫_{W∩Q} |g| dH^n + ∫_{W∖Q} |g| dH^n = ∫_{W∩Q} |g| dH^n (lintegral_inter_add_sdiff with Q measurable). Hence M_W(S) = ∫_{W∩Q} |g| dH^n. ∎

Formalization note (verified during the decomposition check; not part of the mathematical argument). The following single theorem proves exactly this frozen statement. It was compiled with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b36630) after `import GMT.Ch07.Submission` only, inside `namespace GMT.Ch07` with the contract opens. It uses exactly the declared dependencies Submission.idtp_pc_orient_ae_eq_or_neg, Submission.dimred_im_mass_measure, Submission.imrep_carrier_sdiff_support_null (by these Submission.* names) and no import or helper declaration. In a build where those dependencies were sorry stubs, `#print axioms` showed only propext, Classical.choice and Quot.sound besides the stubs; in a fully merged build containing the dependencies' accepted code it gives exactly propext, Classical.choice and Quot.sound. It follows the numbered steps above and may be used directly as the leaf candidate:
```lean
theorem Submission.idtp_pc_signed_density : ∀ (P n : ℕ) (V : Set (Euclid P)) (S : GeometricCurrentOn V n) (τ : Fin n → Euclid P), IsOpen V → Orthonormal ℝ τ → IsIntegerMultiplicity S → S.support ⊆ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)) → ∃ g : Euclid P → ℝ, AEStronglyMeasurable g (μHE[n].restrict (Submodule.span ℝ (Set.range τ) : Set (Euclid P))) ∧ (∀ᵐ x ∂(μHE[n].restrict (Submodule.span ℝ (Set.range τ) : Set (Euclid P))), ∃ m : ℤ, g x = m) ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ V → ∫⁻ x in K ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), ‖g x‖ₑ ∂μHE[n] ≠ ∞) ∧ (∀ ω : TestFormOn V n, S ω = ∫ x in V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), g x * (ω : DifferentialForm (Euclid P) n) x τ ∂μHE[n]) ∧ ∀ W : Set (Euclid P), IsOpen W → W ⊆ V → S.massOn W = ∫⁻ x in W ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), ‖g x‖ₑ ∂μHE[n] := by
  intro P n V S τ hV hτ hS hspt
  obtain ⟨R, hR⟩ := hS
  set Q : Set (Euclid P) := (Submodule.span ℝ (Set.range τ) : Set (Euclid P)) with hQ
  have hQm : MeasurableSet Q := (Submodule.closed_of_finiteDimensional _).measurableSet
  have hMm : MeasurableSet R.carrier := R.measurableSet_carrier
  have hnull : μHE[n] (R.carrier \ Q) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_right hspt) (Submission.imrep_carrier_sdiff_support_null P n V S R hV hR)
  have hor := Submission.idtp_pc_orient_ae_eq_or_neg P n V R τ hτ hnull
  -- a covector β₀ with β₀(τ) = 1
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : Covector (Euclid P) n, β₀ τ = 1 := by
    classical
    let b : Module.Basis (Fin n) ℝ (Euclid n) := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    have hdet : ∀ c : Fin n → Euclid n, b.det c = (Matrix.of fun r l => c l r).det := by
      intro c
      rw [Module.Basis.det_apply]
      congr 1
    have hcont : Continuous (fun c : Fin n → Euclid n => b.det c) := by
      simp only [hdet]
      apply Continuous.matrix_det
      refine continuous_matrix fun r l => ?_
      exact (EuclideanSpace.proj r).continuous.comp (continuous_apply l)
    let δ : Covector (Euclid n) n := { b.det with cont := hcont }
    let Ls₀ : Euclid P →ₗ[ℝ] Euclid n :=
      { toFun := fun y => (WithLp.equiv 2 (Fin n → ℝ)).symm (fun k => inner ℝ (τ k) y)
        map_add' := fun y z => by ext k; simp [inner_add_right]
        map_smul' := fun c y => by ext k; simp [inner_smul_right] }
    let Ls : Euclid P →L[ℝ] Euclid n := LinearMap.toContinuousLinearMap Ls₀
    have hLsτ : ∀ i, Ls (τ i) = b i := by
      intro i
      ext k
      simp [Ls, Ls₀, b, orthonormal_iff_ite.mp hτ, eq_comm]
    refine ⟨δ.compContinuousLinearMap Ls, ?_⟩
    show δ (fun i => Ls (τ i)) = 1
    simp only [hLsτ]
    exact b.det_self
  set ε : Euclid P → ℝ := fun x => R.orient x β₀ with hε
  have hεm : AEStronglyMeasurable ε (μHE[n].restrict R.carrier) :=
    (ContinuousLinearMap.apply ℝ ℝ β₀).continuous.comp_aestronglyMeasurable
      R.aestronglyMeasurable_orient
  set g : Euclid P → ℝ := R.carrier.indicator (fun x => (R.mult x : ℝ) * ε x) with hg
  have hgood : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      (ε x = 1 ∨ ε x = -1) ∧ ∀ α : Covector (Euclid P) n, R.orient x α = ε x * α τ := by
    filter_upwards [hor] with x hx
    rcases hx with h | h
    · exact ⟨Or.inl (by simp [ε, h, hβ₀]), fun α => by simp [ε, h, hβ₀]⟩
    · exact ⟨Or.inr (by simp [ε, h, hβ₀]), fun α => by simp [ε, h, hβ₀]⟩
  have hgood' : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ R.carrier →
      ((ε x = 1 ∨ ε x = -1) ∧ ∀ α : Covector (Euclid P) n, R.orient x α = ε x * α τ) :=
    (ae_restrict_iff' hMm).mp hgood
  have hgint : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), ∃ m : ℤ, g x = m := by
    filter_upwards [hgood'] with x hx
    by_cases hxM : x ∈ R.carrier
    · rcases (hx hxM).1 with h1 | h1
      · exact ⟨R.mult x, by simp [g, hxM, h1]⟩
      · exact ⟨-(R.mult x : ℤ), by simp [g, hxM, h1]⟩
    · exact ⟨0, by simp [g, hxM]⟩
  have hgabs : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)),
      ‖g x‖ₑ = R.carrier.indicator (fun y => (R.mult y : ℝ≥0∞)) x := by
    filter_upwards [hgood'] with x hx
    by_cases hxM : x ∈ R.carrier
    · rcases (hx hxM).1 with h1 | h1
      · simp [g, hxM, h1]
      · simp [g, hxM, h1]
    · simp [g, hxM]
  have hnullae : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∉ R.carrier \ Q :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  refine ⟨g, ?_, ae_restrict_of_ae hgint, ?_, ?_, ?_⟩
  · -- (i)
    have hθm : AEStronglyMeasurable (fun x => (R.mult x : ℝ)) (μHE[n].restrict R.carrier) :=
      ((measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp R.measurable_mult).aestronglyMeasurable
    have : AEStronglyMeasurable g (μHE[n] : Measure (Euclid P)) :=
      (aestronglyMeasurable_indicator_iff hMm).mpr (hθm.mul hεm)
    exact this.restrict
  · -- (iii)
    intro K hK hKV
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKV) ?_
    calc ∫⁻ x in K ∩ Q, ‖g x‖ₑ ∂μHE[n] ≤ ∫⁻ x in K, ‖g x‖ₑ ∂μHE[n] :=
          lintegral_mono_set inter_subset_left
      _ = ∫⁻ x in K, R.carrier.indicator (fun y => (R.mult y : ℝ≥0∞)) x ∂μHE[n] :=
          lintegral_congr_ae (ae_restrict_of_ae hgabs)
      _ = ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
          rw [lintegral_indicator hMm, Measure.restrict_restrict hMm]
  · -- (iv)
    intro ω
    rw [hR ω, IMRep.action, ← integral_indicator hMm,
      ← integral_indicator (hV.measurableSet.inter hQm)]
    refine integral_congr_ae ?_
    filter_upwards [hgood', hnullae] with x hx hxn
    by_cases hxM : x ∈ R.carrier
    · have hxQ : x ∈ Q := by
        by_contra h
        exact hxn ⟨hxM, h⟩
      have hxVQ : x ∈ V ∩ Q := ⟨R.carrier_subset hxM, hxQ⟩
      rw [indicator_of_mem hxM, indicator_of_mem hxVQ, (hx hxM).2]
      simp only [g, indicator_of_mem hxM]
      ring
    · by_cases hxVQ : x ∈ V ∩ Q
      · rw [indicator_of_notMem hxM, indicator_of_mem hxVQ]
        simp [g, hxM]
      · rw [indicator_of_notMem hxM, indicator_of_notMem hxVQ]
  · -- (v)
    intro W hW hWV
    rw [(Submission.dimred_im_mass_measure P n V S R hV hR).1 W hW hWV, IMRep.measure, withDensity_apply _ hW.measurableSet,
      Measure.restrict_restrict hW.measurableSet]
    have hzero : ∫⁻ x in W \ Q, ‖g x‖ₑ ∂μHE[n] = 0 := by
      have h0 : ∀ᵐ x ∂(μHE[n].restrict (W \ Q)), ‖g x‖ₑ = 0 := by
        rw [ae_restrict_iff' (hW.measurableSet.diff hQm)]
        filter_upwards [hnullae] with x hxn hxWQ
        have hxM : x ∉ R.carrier := fun hxM => hxn ⟨hxM, hxWQ.2⟩
        simp [g, hxM]
      rw [lintegral_congr_ae h0, lintegral_zero]
    calc ∫⁻ a in W ∩ R.carrier, (R.mult a : ℝ≥0∞) ∂μHE[n]
        = ∫⁻ x in W, R.carrier.indicator (fun y => (R.mult y : ℝ≥0∞)) x ∂μHE[n] := by
          rw [lintegral_indicator hMm, Measure.restrict_restrict hMm, inter_comm]
      _ = ∫⁻ x in W, ‖g x‖ₑ ∂μHE[n] := (lintegral_congr_ae (ae_restrict_of_ae hgabs)).symm
      _ = ∫⁻ x in W ∩ Q, ‖g x‖ₑ ∂μHE[n] := by
          rw [← lintegral_inter_add_sdiff (fun x => ‖g x‖ₑ) W hQm, hzero, add_zero]
```

## Key steps

1. Represent S = τ(M, θ, ξ) by R; M_W(S) = R.measure(W) on open W ⊆ V (accepted dimred_im_mass_measure).
2. H^n(M ∖ Q) = 0 from H^n(M ∖ spt S) = 0 (accepted imrep_carrier_sdiff_support_null) and spt S ⊆ Q.
3. ξ = ±ξ_Q a.e. on M (sibling planar_orientation_sign); ε := ξ(·)(β₀) with β₀(τ) = 1 is a.e. ±1 and a.e.-strongly measurable.
4. g := 1_M θ ε is a.e. integer valued with |g| = 1_M θ, a.e.-strongly measurable and locally integrable on V ∩ Q.
5. S(ω) = ∫_M θξ(ω) = ∫_{V∩Q} g ω(τ) (integrands agree a.e.), and M_W(S) = ∫_{W∩M} θ = ∫_{W∩Q} |g|.

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
