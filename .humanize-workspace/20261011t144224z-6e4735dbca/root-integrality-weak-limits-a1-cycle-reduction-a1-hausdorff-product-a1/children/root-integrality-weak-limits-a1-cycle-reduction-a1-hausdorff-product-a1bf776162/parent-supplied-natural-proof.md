# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1.injective_pieces-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and scope. This is Steps 6–7 of the parent proof of iwl_cr_hausdorff_product_formula (node root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1).
- It reuses the piece construction of the comparator-accepted proof of rectifiability_weighted_tangent_ae (node root.rectifiability-a1.weighted_tangent_ae-a1, Lean code `hparam`/`hpart` in commit 2f36576), with dimension m + 1 replaced by m.
- It then disjointifies the pieces.
- No DAG declaration is used, and the case m = 0 needs no special treatment.

Library inputs (pinned Mathlib 25730c7c, SimonGMT 2b36630):
- (L2) Poincare.SimonGMT.Chapter02 (AreaLipschitz.lean): areaRegularSet f := {x | DifferentiableAt ℝ f x ∧ Function.Injective (fderiv ℝ f x)}.
  - measurableSet_areaRegularSet: this set is Borel.
  - area_image_compl_regularSet_eq_zero: if LipschitzWith K f, then for every s, μHE[finrank ℝ E] (f '' (s ∖ areaRegularSet f)) = 0. This is Rademacher plus the null critical image.
- (L4) exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (Mathlib/MeasureTheory/Function/Jacobian.lean:255).
  - Input: f, s, f′ with HasFDerivWithinAt f (f′ x) s x for x ∈ s, and r : (E →L[ℝ] F) → ℝ≥0 with r A ≠ 0 for all A.
  - Output: pairwise disjoint Borel t_n with s ⊆ ⋃_n t_n, and A_n with ApproximatesLinearOn f (A_n) (s ∩ t_n) (r(A_n)), i.e. ‖f x − f y − A_n(x − y)‖ ≤ r(A_n)‖x − y‖ on s ∩ t_n.
  - Moreover, if s is nonempty then ∀ n, ∃ y ∈ s, A_n = f′ y.
- (L5) MeasurableSet.image_of_continuousOn_injOn (Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:821): a Borel set in a Polish space has Borel image under a map that is continuous and injective on it.
- (L6) LinearMap.exists_antilipschitzWith: an injective linear map L on a finite-dimensional space admits K > 0 with ‖v‖ ≤ K‖L v‖.
- Also used: finrank_euclideanSpace_fin (finrank ℝ (Eucl m) = m), and disjointed, disjoint_disjointed, disjointed_subset, iUnion_disjointed, MeasurableSet.disjointed.

1. (Data.) Unfold CountablyRectifiable m A. There are M₀ ⊆ E := Eucl P with μHE[m](M₀) = 0 and maps F_j : Eucl m → E (j ∈ ℕ) with LipschitzWith K_j F_j, such that A ⊆ M₀ ∪ ⋃_j range F_j.

2. (Lower-bound constants.) For every continuous linear L : Eucl m →L[ℝ] E choose δ(L) ∈ ℝ≥0 with δ(L) > 0, and κ(L) > 0:
- If L is injective, (L6) gives K_L > 0 with ‖v‖ ≤ K_L‖L v‖ for all v. Put δ(L) := κ(L) := (2K_L)⁻¹.
- Otherwise put δ(L) := κ(L) := 1.
Claim: let L be injective, t ⊆ Eucl m and g : Eucl m → E, and suppose ‖g(b) − g(b′) − L(b − b′)‖ ≤ δ(L)‖b − b′‖ for b, b′ ∈ t. Then κ(L)‖b − b′‖ ≤ ‖g(b) − g(b′)‖ for b, b′ ∈ t. Indeed,
  ‖b − b′‖/K_L ≤ ‖L(b − b′)‖ ≤ ‖g(b) − g(b′)‖ + ‖g(b) − g(b′) − L(b − b′)‖ ≤ ‖g(b) − g(b′)‖ + (2K_L)⁻¹‖b − b′‖,
so ‖g(b) − g(b′)‖ ≥ (2K_L)⁻¹‖b − b′‖.

3. (Partition of the regular set.) Fix j and put R_j := areaRegularSet F_j, which is Borel by (L2).
- If R_j = ∅, put t_{j,l} := ∅ for all l.
- Otherwise, F_j is differentiable at each b ∈ R_j, so HasFDerivWithinAt F_j (fderiv ℝ F_j b) R_j b. Apply (L4) with f := F_j, s := R_j, f′ := fderiv ℝ F_j and r := δ; this is allowed since δ(L) ≠ 0 for all L. It gives Borel sets t′_l and continuous linear maps A_l (l ∈ ℕ) with:
  - R_j ⊆ ⋃_l t′_l;
  - ApproximatesLinearOn F_j A_l (R_j ∩ t′_l) δ(A_l);
  - since R_j ≠ ∅, A_l = fderiv ℝ F_j y_l for some y_l ∈ R_j.
  Put t_{j,l} := R_j ∩ t′_l.
- In both cases: t_{j,l} is Borel, t_{j,l} ⊆ R_j, and R_j ⊆ ⋃_l t_{j,l}.
- F_j is injective on t_{j,l}. In the nonempty case, A_l is injective because y_l ∈ R_j. Step 2 then gives κ(A_l)‖b − b′‖ ≤ ‖F_j b − F_j b′‖ on t_{j,l}, so F_j b = F_j b′ forces ‖b − b′‖ ≤ 0, i.e. b = b′.

4. (Enumeration.) For p ∈ ℕ with (j, l) := Nat.unpair p, put G_p := F_j and S_p := t_{j,l}. Then:
- G_p is LipschitzWith K_j, hence continuous;
- S_p is Borel, and G_p is injective on S_p;
- G_p is differentiable at every b ∈ S_p, because S_p ⊆ R_j;
- G_p '' S_p is Borel by (L5), since Eucl m is Polish and G_p is continuous and injective on S_p.

5. (The exceptional set.) Put N := M₀ ∪ ⋃_j F_j '' (univ ∖ R_j). By (L2) with s := univ and finrank ℝ (Eucl m) = m, μHE[m](F_j '' (univ ∖ R_j)) = 0 for every j. Together with μHE[m](M₀) = 0 and countable subadditivity, μHE[m](N) = 0.

6. (Covering.) We show A ⊆ N ∪ ⋃_p G_p '' S_p. Let x ∈ A.
- If x ∈ M₀, then x ∈ N.
- Otherwise x = F_j(b) for some j and b.
  - If b ∉ R_j, then x ∈ F_j '' (univ ∖ R_j) ⊆ N.
  - If b ∈ R_j, then b ∈ t_{j,l} for some l. With p := Nat.pair j l we have Nat.unpair p = (j, l), so x = G_p(b) ∈ G_p '' S_p.

7. (Disjointification.) Let A_p := disjointed (fun p => A ∩ G_p '' S_p) p, i.e. A_p = (A ∩ G_p '' S_p) ∖ ⋃_{q<p} (A ∩ G_q '' S_q), and B_p := S_p ∩ G_p⁻¹(A_p).
(i) A_p is Borel (MeasurableSet.disjointed; A and every G_q '' S_q are Borel), A_p ⊆ A ∩ G_p '' S_p (disjointed_subset), and the A_p are pairwise disjoint (disjoint_disjointed).
(ii) B_p is Borel, since S_p is Borel, G_p is continuous (hence measurable) and A_p is Borel. Also B_p ⊆ S_p, so G_p is injective on B_p and differentiable at each point of B_p.
(iii) G_p '' B_p = A_p. If b ∈ B_p then G_p(b) ∈ A_p by definition. Conversely, if x ∈ A_p then x ∈ G_p '' S_p, so x = G_p(b) with b ∈ S_p; then b ∈ G_p⁻¹(A_p), i.e. b ∈ B_p.
Consequently each G_p '' B_p = A_p is a Borel subset of A, and the sets G_p '' B_p are pairwise disjoint.

8. (Null remainder.) ⋃_p A_p = ⋃_p (A ∩ G_p '' S_p) by iUnion_disjointed. If x ∈ A ∖ ⋃_p A_p, then x ∉ G_p '' S_p for every p; otherwise x ∈ A ∩ G_p '' S_p ⊆ ⋃_p A_p. So x ∈ N by Step 6. Hence A ∖ ⋃_p G_p '' B_p ⊆ N, and μHE[m](A ∖ ⋃_p G_p '' B_p) = 0.

9. The family (G_p, B_p)_{p∈ℕ} has all the required properties. ∎

Appendix (Lean, verified). The declaration below proves exactly this frozen statement. It was compiled against the frozen project:
- environment: commit d8d46c9, Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b36630;
- placement: inside GMT/Ch06/Submission.lean, in `namespace GMT.Ch06` after the contract's `noncomputable section … end`, where accepted `theorem Submission.…` declarations go (the check used a scratch file that imports GMT.Ch06.Submission and replays the contract's namespace and `open` commands);
- `#print axioms` reports [propext, Classical.choice, Quot.sound].
Extra imports to add at the top of GMT/Ch06/Submission.lean: Poincare.SimonGMT.Chapter02.AreaLipschitz, Mathlib.MeasureTheory.Function.Jacobian, Mathlib.MeasureTheory.Constructions.Polish.Basic. The proof uses no auxiliary top-level declarations.

theorem Submission.iwl_cr_hp_injective_pieces : ∀ (P m : ℕ) (A : Set (Eucl P)), MeasurableSet A → CountablyRectifiable m A → ∃ (G : ℕ → Eucl m → Eucl P) (B : ℕ → Set (Eucl m)), (∀ p, ∃ K : ℝ≥0, LipschitzWith K (G p)) ∧ (∀ p, MeasurableSet (B p)) ∧ (∀ p, InjOn (G p) (B p)) ∧ (∀ p, ∀ b ∈ B p, DifferentiableAt ℝ (G p) b) ∧ (∀ p, G p '' B p ⊆ A) ∧ (∀ p, MeasurableSet (G p '' B p)) ∧ Pairwise (Function.onFun Disjoint fun p => G p '' B p) ∧ (μHE[m] : Measure (Eucl P)) (A \ ⋃ p, G p '' B p) = 0 := by
  intro P m A hA hM
  obtain ⟨M₀, hM₀, F, hF, hcover⟩ := hM
  -- Step 2: lower-bound constants for injective linear maps
  have hchoice : ∀ L : Eucl m →L[ℝ] Eucl P, ∃ δ : ℝ≥0, 0 < δ ∧ ∃ k : ℝ, 0 < k ∧
      (Function.Injective L → ∀ (t : Set (Eucl m)) (g : Eucl m → Eucl P),
        ApproximatesLinearOn g L t δ → ∀ b ∈ t, ∀ b' ∈ t, k * ‖b - b'‖ ≤ ‖g b - g b'‖) := by
    intro L
    by_cases hL : Function.Injective L
    · obtain ⟨K, hKpos, hK⟩ := (L : Eucl m →ₗ[ℝ] Eucl P).exists_antilipschitzWith
        (LinearMap.ker_eq_bot.mpr hL)
      have hK0 : (0 : ℝ) < K := hKpos
      refine ⟨(2 * K)⁻¹, by positivity, (2 * (K : ℝ))⁻¹, by positivity,
        fun _ t g hg b hb b' hb' => ?_⟩
      have h1 : ‖b - b'‖ ≤ K * ‖L (b - b')‖ := by
        have := hK.le_mul_dist b b'
        simpa only [dist_eq_norm, ContinuousLinearMap.coe_coe, map_sub] using this
      have h2 : ‖g b - g b' - L (b - b')‖ ≤ ((2 * K)⁻¹ : ℝ≥0) * ‖b - b'‖ := hg b hb b' hb'
      have h3 : ‖L (b - b')‖ ≤ ‖g b - g b'‖ + ‖g b - g b' - L (b - b')‖ := by
        have := norm_sub_le (g b - g b') (g b - g b' - L (b - b'))
        simpa using this
      push_cast at h2
      have h4 : ‖b - b'‖ / K ≤ ‖L (b - b')‖ := by
        rw [div_le_iff₀ hK0]; linarith
      have h5 : (2 * (K : ℝ))⁻¹ * ‖b - b'‖ = ‖b - b'‖ / K - (2 * (K : ℝ))⁻¹ * ‖b - b'‖ := by
        field_simp; ring
      linarith
    · exact ⟨1, one_pos, 1, one_pos, fun h => (hL h).elim⟩
  choose δ hδpos k hkpos hk using hchoice
  -- Step 3: partition of the regular set into injective pieces
  have hpart : ∀ j, ∃ (t : ℕ → Set (Eucl m)),
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ Poincare.SimonGMT.Chapter02.areaRegularSet (F j)) ∧
      Poincare.SimonGMT.Chapter02.areaRegularSet (F j) ⊆ ⋃ i, t i ∧
      ∀ i, InjOn (F j) (t i) := by
    intro j
    set R := Poincare.SimonGMT.Chapter02.areaRegularSet (F j) with hRdef
    have hRmeas : MeasurableSet R := Poincare.SimonGMT.Chapter02.measurableSet_areaRegularSet _
    rcases eq_empty_or_nonempty R with hR | hR
    · refine ⟨fun _ => ∅, fun _ => MeasurableSet.empty, fun _ => empty_subset _,
        by rw [hR]; exact empty_subset _, fun i => injOn_empty _⟩
    obtain ⟨t, Al, -, ht, hcov, happrox, hactual⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (F j) R (fderiv ℝ (F j))
        (fun x hx => hx.1.hasFDerivAt.hasFDerivWithinAt) δ (fun L => (hδpos L).ne')
    refine ⟨fun i => R ∩ t i, fun i => hRmeas.inter (ht i), fun i => inter_subset_left, ?_, ?_⟩
    · intro b hb
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hb)
      exact mem_iUnion.2 ⟨i, hb, hi⟩
    · intro i b hb b' hb' hbb
      obtain ⟨y, hy, hAy⟩ := hactual hR i
      have hlow := hk (Al i) (hAy ▸ hy.2) (R ∩ t i) (F j) (happrox i) b hb b' hb'
      rw [hbb, sub_self, norm_zero] at hlow
      have h0 : ‖b - b'‖ ≤ 0 := by
        have := hkpos (Al i)
        nlinarith [norm_nonneg (b - b')]
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
  choose t ht_meas ht_sub ht_cov ht_inj using hpart
  have hfin : Module.finrank ℝ (Eucl m) = m := finrank_euclideanSpace_fin
  -- Step 4: enumeration
  set Gp : ℕ → Eucl m → Eucl P := fun p => F p.unpair.1 with hGpdef
  set Sp : ℕ → Set (Eucl m) := fun p => t p.unpair.1 p.unpair.2 with hSpdef
  have hGpL : ∀ p, ∃ K : ℝ≥0, LipschitzWith K (Gp p) := fun p => hF _
  have hSpm : ∀ p, MeasurableSet (Sp p) := fun p => ht_meas _ _
  have hSpinj : ∀ p, InjOn (Gp p) (Sp p) := fun p => ht_inj _ _
  have hSpdiff : ∀ p, ∀ b ∈ Sp p, DifferentiableAt ℝ (Gp p) b := fun p b hb => (ht_sub _ _ hb).1
  have hGpc : ∀ p, Continuous (Gp p) := fun p => by
    obtain ⟨K, hK⟩ := hGpL p; exact hK.continuous
  have himgm : ∀ p, MeasurableSet (Gp p '' Sp p) := fun p =>
    (hSpm p).image_of_continuousOn_injOn (hGpc p).continuousOn (hSpinj p)
  -- Step 5: the exceptional null set
  set N := M₀ ∪ ⋃ j, F j '' (univ \ Poincare.SimonGMT.Chapter02.areaRegularSet (F j)) with hNdef
  have hN : (μHE[m] : Measure (Eucl P)) N = 0 := by
    refine measure_union_null hM₀ (measure_iUnion_null fun j => ?_)
    obtain ⟨K, hK⟩ := hF j
    have := Poincare.SimonGMT.Chapter02.area_image_compl_regularSet_eq_zero hK univ
    rwa [hfin] at this
  -- Step 6: covering
  have hcov2 : A ⊆ N ∪ ⋃ p, Gp p '' Sp p := by
    intro x hx
    rcases hcover hx with h0 | h1
    · exact Or.inl (Or.inl h0)
    · obtain ⟨j, b, rfl⟩ := mem_iUnion.1 h1
      by_cases hb : b ∈ Poincare.SimonGMT.Chapter02.areaRegularSet (F j)
      · obtain ⟨i, hi⟩ := mem_iUnion.1 (ht_cov j hb)
        refine Or.inr (mem_iUnion.2 ⟨Nat.pair j i, ?_⟩)
        simp only [hGpdef, hSpdef, Nat.unpair_pair]
        exact ⟨b, hi, rfl⟩
      · exact Or.inl (Or.inr (mem_iUnion.2 ⟨j, b, ⟨mem_univ _, hb⟩, rfl⟩))
  -- Steps 7–8: disjointification and null remainder
  set Ap : ℕ → Set (Eucl P) := disjointed fun p => A ∩ Gp p '' Sp p with hApdef
  set Bp : ℕ → Set (Eucl m) := fun p => Sp p ∩ Gp p ⁻¹' Ap p with hBpdef
  have hApm : ∀ p, MeasurableSet (Ap p) :=
    MeasurableSet.disjointed fun p => hA.inter (himgm p)
  have hApsub : ∀ p, Ap p ⊆ A ∩ Gp p '' Sp p := fun p => disjointed_subset _ p
  have himgB : ∀ p, Gp p '' Bp p = Ap p := by
    intro p
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩; exact hb.2
    · intro hx
      obtain ⟨b, hb, rfl⟩ := ((hApsub p) hx).2
      exact ⟨b, ⟨hb, hx⟩, rfl⟩
  refine ⟨Gp, Bp, hGpL, fun p => (hSpm p).inter ((hApm p).preimage (hGpc p).measurable),
    fun p => (hSpinj p).mono inter_subset_left,
    fun p b hb => hSpdiff p b hb.1, fun p => by rw [himgB p]; exact fun x hx => ((hApsub p) hx).1,
    fun p => by rw [himgB p]; exact hApm p, ?_, ?_⟩
  · intro p q hpq
    simp only [Function.onFun, himgB]
    exact disjoint_disjointed _ hpq
  · simp only [himgB]
    rw [hApdef, iUnion_disjointed]
    refine measure_mono_null ?_ hN
    intro x ⟨hxA, hxU⟩
    rcases hcov2 hxA with hxN | hxG
    · exact hxN
    · exfalso
      obtain ⟨p, hp⟩ := mem_iUnion.1 hxG
      exact hxU (mem_iUnion.2 ⟨p, hxA, hp⟩)

## Key steps

1. Unfold CountablyRectifiable m A: Lipschitz F_j : ℝ^m → ℝ^P cover A up to the H^m-null set M₀.
2. For injective linear L with ‖v‖ ≤ K_L‖Lv‖, approximation within (2K_L)⁻¹ forces ‖g b − g b′‖ ≥ (2K_L)⁻¹‖b − b′‖.
3. Partition areaRegularSet F_j with Mathlib's exists_partition_approximatesLinearOn_of_hasFDerivWithinAt. The approximating maps are actual (injective) derivatives, so each Borel piece t_{j,l} carries F_j injectively.
4. Enumerate the pieces by Nat.unpair; the images are Borel (Lusin–Souslin). The non-regular images F_j(ℝ^m ∖ R_j) are null (area_image_compl_regularSet_eq_zero); together with M₀ they form an H^m-null set N with A ⊆ N ∪ ⋃_p G_p(S_p).
5. Disjointify: A_p := disjointed(A ∩ G_p(S_p)), B_p := S_p ∩ G_p⁻¹(A_p). Then G_p(B_p) = A_p are disjoint Borel subsets of A, and A ∖ ⋃_p A_p ⊆ N.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json  (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `python3: read /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/{parent-child-handoff.json, parent-supplied-natural-proof.json, parent-supplied-natural-proof.md, parent-supplied-plan.md}`
- `python3: dag.json node statuses and lean_names (lpf_raf_*, lpf_countably_rectifiable_c1_cover, rectifiability_weighted_tangent_ae, iwl_cr_*); grep -r 'iwl_cr_hp_' over the run directory (no match)`
- `grep -n 'theorem hausdorffMeasure_apply|hausdorffMeasure_le_liminf_tsum|hausdorffMeasure_zero_singleton' Mathlib/MeasureTheory/Measure/Hausdorff.lean; grep 'euclideanHausdorffMeasure_def|euclideanHausdorffMeasure_zero|addHaarScalarFactor_volume_hausdorffMeasure_ne_zero' Mathlib/Geometry/Euclidean/Volume/Measure.lean (snapshot)`
- `sed -n 250,275p Mathlib/MeasureTheory/Function/Jacobian.lean (exists_partition_approximatesLinearOn_of_hasFDerivWithinAt); grep measurePreserving_piFinSuccAbove Mathlib/MeasureTheory/Constructions/Pi.lean; grep 'PiLp.volume_preserving_ofLp|PiLp.volume_preserving_toLp' Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean; grep det_succ_row_zero Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean; grep exists_measurable_subset_ae_eq Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `sed -n 290,320p Mathlib/Analysis/InnerProductSpace/NormDet.lean (LinearMap.normDet_sq_eq_det_gram, any Fintype index)`
- `grep -rn 'setLIntegral_comp_preimage|theorem prod_restrict|theorem lintegral_prod |Measurable.lintegral_prod_right'|MeasurePreserving.prod|LipschitzWith.prodMk' Mathlib/ (snapshot)`
- `grep -rn 'ediam_le|edist_le_ediam_of_mem|ediam_empty|ediam_le_of_forall_dist_le' Mathlib/Topology/EMetricSpace/Diam.lean Mathlib/Topology/MetricSpace/Bounded.lean (snapshot)`
- `simongmt: cat Chapter02/AreaLipschitz.lean; sed Chapter02/Area.lean, Chapter02/AreaParametrization.lean, Chapter02/AreaApproximation.lean; grep -rn 'theorem areaJacobianAt'; sed -n 28,80p Chapter03/Rectifiable.lean (CountablyRectifiable, CountablyRectifiable.mono)`
- `git show 2f36576:GMT/Ch06/Submission.lean (accepted rectifiability_weighted_tangent_ae, hparam/hpart piece construction); git show a46aa05:GMT/Ch06/Submission.lean and accepted candidate diffs (declaration conventions)`
- `verifier: gmt-compare.py contract_scope/child_modules and lean_contract.validate_lean_statement; python3 -I /tmp/hp_decomp/scripts/gen.py children_v1.json -> NodeChallenge files; lake env lean on each (all elaborate)`
- `lake env lean /tmp/hp_decomp/T0.lean (areaJacobianAt, weighted_area_formula_lipschitz_injOn and LinearMap.normDet_sq_eq_det_gram unknown under frozen imports; MeasurableSet.image_of_continuousOn_injOn, measurePreserving_piFinSuccAbove available)`
- `lake env lean /tmp/hp_decomp/scratch/{Assembly,JacBridge,LiftGram,PieceProduct,Pieces,Cyl}.lean and /tmp/hp_decomp/final/{All,Check_iwl_cr_hp_*}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/speculative-prompt-v3.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaParametrization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/hp_decomp/T0.lean`
- `/tmp/hp_decomp/scratch/Assembly.lean`
- `/tmp/hp_decomp/scratch/JacBridge.lean`
- `/tmp/hp_decomp/scratch/LiftGram.lean`
- `/tmp/hp_decomp/scratch/PieceProduct.lean`
- `/tmp/hp_decomp/scratch/Pieces.lean`
- `/tmp/hp_decomp/scratch/Cyl.lean`
- `/tmp/hp_decomp/final/All.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_cylinder_null.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_injective_pieces.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_lift_gram_det.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_piece_product.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c; the frozen contract is Contract.lean, and Submission.lean is identical to it at the dispatch base.

Library inputs found (all with standard axioms):
- Mathlib supplies:
  - Hausdorff measure: hausdorffMeasure_apply (ediam form), hausdorffMeasure_zero_singleton, euclideanHausdorffMeasure_def/_zero, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero;
  - pieces: exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (root namespace), MeasurableSet.image_of_continuousOn_injOn;
  - linear algebra: LinearMap.normDet_sq_eq_det_gram (any Fintype index, so EuclideanSpace.basisFun works), Matrix.det_succ_row_zero;
  - integration: measurePreserving_piFinSuccAbove, PiLp.volume_preserving_ofLp/toLp, MeasurePreserving.setLIntegral_comp_preimage, Measure.prod_restrict, lintegral_prod, Measurable.lintegral_prod_right', NullMeasurableSet.exists_measurable_subset_ae_eq;
  - diameters: Metric.ediam_le_of_forall_dist_le, edist_le_ediam_of_mem.
- SimonGMT 2b36630 supplies weighted_area_formula_lipschitz_injOn, area_image_compl_regularSet_eq_zero, measurableSet_areaRegularSet, measurable_areaJacobianAt, areaJacobianAt_eq_normDet/_nonneg, CountablyRectifiable (F_j : EuclideanSpace ℝ (Fin n) → E) and CountablyRectifiable.mono.
- Neither library has a Hausdorff product formula for rectifiable sets; only hausdorffMeasure_pi_real/prod_real exist.
- No DAG node supplies the needed lemmas with compatible types:
  - the lpf_raf_* area lemmas are chart/fibre-sum forms;
  - lpf_countably_rectifiable_c1_cover is only speculative-ready.
  So the split relies on library theorems only.

Scope check: areaJacobianAt, the SimonGMT area formula and LinearMap.normDet are NOT visible after `import GMT.Ch06.Submission` with the frozen imports. Hence lift_gram_det is stated with Gram determinants (Matrix.of … inner ℝ … EuclideanSpace.single). All four child statements elaborate in verifier-generated challenge modules.

Lean results:
- Scratch proofs of all four children with exactly the proposed types, and of the parent's exact frozen type from them, compile with only propext, Classical.choice and Quot.sound, and with zero warnings.
- Per-child compiles succeed with the minimal imports listed in each appendix.
- The accepted hparam/hpart code (commit 2f36576) was reused for injective_pieces.
- No name collisions with dag.json.
