# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1.glue-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1.glue-a1.glue_pieces-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4–8 of the selected node's supplied proof: the glued data (M, θ), the measure identity μ = (Hᵏ⌞M).withDensity θ, its consequences 6(a)–(d), the orientation step 7 and the glued IMRep of step 8. They are stated for an arbitrary countable family of pairwise disjoint Borel pieces A_i. The glued orientation is ξ itself, exactly as in the supplied proof. The orientation step is the sibling cbrg_ae_orient_iUnion.

Notation: Hᵏ := μHE[k]. For i ∈ ι write M_i := (R i).carrier, θ_i := (R i).mult and ξ_i := (R i).orient, so that R_i.measure = (Hᵏ⌞M_i).withDensity θ_i (contract IMRep.measure). Put N_i := M_i ∩ A_i and M := ⋃_i N_i. The hypotheses are those of the statement: (IMC)(a); ι countable; U open; W_i open with W_i ⊆ U; A_i Borel and pairwise disjoint; μ((⋃_i A_i)ᶜ) = 0; μ⌞A_i = (R_i.measure)⌞A_i; μ(K) < ∞ for compact K ⊆ U; ξ is a.e. strongly measurable for μ; and ξ = ξ_i holds Hᵏ⌞N_i-a.e.

1. (Glued multiplicity.) Define θ : ℝ^P → ℕ as follows. If x ∈ A_j for some j, pick such a j (classical choice) and set θ(x) := θ_j(x). Otherwise set θ(x) := 0. In Lean: θ x := if h : ∃ i, x ∈ A i then (R h.choose).mult x else 0.

2. (θ = θ_i on A_i.) Let x ∈ A_i, and let j be the index chosen in step 1. Then x ∈ A_j. If j ≠ i, then x ∈ A_j ∩ A_i = ∅ by pairwise disjointness, which is impossible. So j = i and θ(x) = θ_i(x). Also, θ(x) = 0 whenever x lies in no A_i.

3. (The carrier.) Each N_i = M_i ∩ A_i is Borel (field measurableSet_carrier of R_i, and A_i Borel). So M = ⋃_i N_i is Borel as a countable union. Moreover M ⊆ U, because N_i ⊆ M_i ⊆ W_i ⊆ U by the field carrier_subset and the hypothesis W_i ⊆ U.

4. (θ is measurable.) ℕ is countable with the discrete σ-algebra, so it suffices that every fibre θ⁻¹({n}) is Borel (Mathlib measurable_to_countable'). By step 2,
θ⁻¹({n}) = ⋃_i (A_i ∩ θ_i⁻¹({n})) ∪ ((⋃_i A_i)ᶜ ∩ E_n),
where E_n = ℝ^P if n = 0 and E_n = ∅ otherwise. Each θ_i⁻¹({n}) is Borel by the field measurable_mult. So the right side is Borel.

5. (θ ≥ 1 on M.) If x ∈ M, then x ∈ N_i = M_i ∩ A_i for some i. So θ(x) = θ_i(x) > 0 by step 2 and the field mult_pos of R_i.

6. (M is countably k-rectifiable.) Each N_i ⊆ M_i is countably k-rectifiable by the field rectifiable of R_i and CountablyRectifiable.mono.
- If ι is empty, then M = ∅. This set is Hᵏ-null, hence countably k-rectifiable (countablyRectifiable_of_measure_zero).
- Otherwise there is a surjection s : ℕ → ι (exists_surjective_nat). Then M = ⋃_n N_{s(n)} (Function.Surjective.iUnion_comp), which is countably k-rectifiable by SimonGMT countablyRectifiable_iUnion.

7. (μ = Σ_i (R_i.measure)⌞A_i.) Since μ((⋃_i A_i)ᶜ) = 0, μ-a.e. point lies in ⋃_i A_i. So μ⌞(⋃_i A_i) = μ (restrict_eq_self_of_ae_mem). The A_i are pairwise disjoint Borel sets, so μ⌞(⋃_i A_i) = Σ_i μ⌞A_i (Measure.restrict_iUnion). By hypothesis μ⌞A_i = (R_i.measure)⌞A_i.

8. (The measure identity (Hᵏ⌞M).withDensity θ = μ.) The N_i are Borel and pairwise disjoint (N_i ⊆ A_i). So Hᵏ⌞M = Σ_i Hᵏ⌞N_i (Measure.restrict_iUnion), and therefore (Hᵏ⌞M).withDensity θ = Σ_i (Hᵏ⌞N_i).withDensity θ (withDensity_sum). For each i:
- (R_i.measure)⌞A_i = ((Hᵏ⌞M_i).withDensity θ_i)⌞A_i = (Hᵏ⌞(A_i ∩ M_i)).withDensity θ_i = (Hᵏ⌞N_i).withDensity θ_i (restrict_withDensity, Measure.restrict_restrict, commutativity of ∩);
- θ = θ_i holds Hᵏ⌞N_i-a.e., by step 2 and N_i ⊆ A_i, so (Hᵏ⌞N_i).withDensity θ = (Hᵏ⌞N_i).withDensity θ_i (withDensity_congr_ae).
Summing over i and using step 7 gives (Hᵏ⌞M).withDensity θ = Σ_i (R_i.measure)⌞A_i = μ.

9. (Local integrability.) Let K ⊆ U be compact, hence closed, hence Borel. Then ∫_{M∩K} θ dHᵏ = ((Hᵏ⌞M).withDensity θ)(K) (withDensity_apply, Measure.restrict_restrict). By step 8 this equals μ(K), which is < ∞ by hypothesis.

10. (Local finiteness of M.) For compact K ⊆ U, Hᵏ(M ∩ K) = ∫_{M∩K} 1 dHᵏ (setLIntegral_one). This is at most ∫_{M∩K} θ dHᵏ, by step 5 and setLIntegral_mono (θ is measurable by step 4). By step 9 this is < ∞.

11. (ξ is Hᵏ⌞M-measurable.) θ ≠ 0 holds Hᵏ⌞M-a.e., since Hᵏ⌞M-a.e. point lies in the Borel set M and θ > 0 on M (step 5). So Hᵏ⌞M ≪ (Hᵏ⌞M).withDensity θ (withDensity_absolutelyContinuous'), and this measure is μ by step 8. Since ξ is a.e. strongly measurable for μ, it is a.e. strongly measurable for Hᵏ⌞M (AEStronglyMeasurable.mono_ac).

12. (Orientation.) Apply the sibling cbrg_ae_orient_iUnion, with (IMC)(a), ι, P, k, U, the families W, N, R and ξ. Its hypotheses hold:
- U is open and every W_i is open;
- every N_i is Borel, and N_i ⊆ M_i;
- M = ⋃_i N_i ⊆ U (step 3);
- Hᵏ(M ∩ K) ≠ ∞ for compact K ⊆ U (step 10);
- ξ = ξ_i holds Hᵏ⌞N_i-a.e. (hypothesis).
It yields: for Hᵏ⌞M-a.e. x there is a subspace Q with HasApproximateTangentSpaceAt k M x Q and IsUnitOrientationOf (ξ x) Q.

13. (The glued IMRep.) Let R' := (M, θ, ξ). Its fields are justified as follows:
- measurableSet_carrier and carrier_subset: step 3;
- rectifiable: step 6;
- measurable_mult: step 4;
- mult_pos: step 5;
- locallyIntegrable_mult: step 9;
- aestronglyMeasurable_orient: step 11;
- orients: step 12.
So R' is an IMRep in U. By construction R'.carrier = ⋃_i (M_i ∩ A_i) and R'.orient = ξ. By definition R'.measure = (Hᵏ⌞M).withDensity θ, which is μ by step 8. ∎

Remark on step 11. In Lean, measurability of ξ on Hᵏ⌞M cannot be obtained from the pieces with aestronglyMeasurable_iUnion_iff. That lemma needs a PseudoMetrizableSpace instance for MultiVector P k = Covector →L[ℝ] ℝ, and in this environment instance synthesis does not find one: the strong topology ContinuousLinearMap.topologicalSpace is not definitionally the metric topology. This is why the hypothesis AEStronglyMeasurable ξ μ is used, as in the supplied proof's step 6(d).

Appendix (verified Lean realization of the numbered proof above). The declaration below compiles with Lean v4.35.0-rc3 and Mathlib 25730c7c (lake env lean in the gmt-ch07 workspace). It was placed after `import GMT.Ch07.Submission` in the child comparator scope, i.e. inside `namespace GMT.Ch07` with the frozen contract's `open` commands (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `open Poincare.SimonGMT.Chapter06`, `open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)`), after the contract's `noncomputable section ... end`. The only non-library declaration it uses is the sibling `Submission.cbrg_ae_orient_iUnion`, with exactly its frozen type. `#print axioms` reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.cbrg_imRep_glue_disjoint : (∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) → ∀ (ι : Type) [Countable ι] (P k : ℕ) (U : Set (Euclid P)) (W A : ι → Set (Euclid P)) (R : (i : ι) → IMRep (W i) k) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k), IsOpen U → (∀ i, IsOpen (W i)) → (∀ i, W i ⊆ U) → (∀ i, MeasurableSet (A i)) → Pairwise (fun i j => Disjoint (A i) (A j)) → μ (⋃ i, A i)ᶜ = 0 → (∀ i, μ.restrict (A i) = (R i).measure.restrict (A i)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ i, ∀ᵐ y ∂(μHE[k].restrict ((R i).carrier ∩ A i)), ξ y = (R i).orient y) → ∃ R' : IMRep U k, R'.carrier = ⋃ i, (R i).carrier ∩ A i ∧ R'.orient = ξ ∧ R'.measure = μ := by
  classical
  intro hIMC ι _ P k U W A R μ ξ hU hWo hWU hAm hAd hAc hμA hfin hξm hξ
  -- pieces `Nᵢ = Mᵢ ∩ Aᵢ` and multiplicities `mᵢ = θᵢ`
  let N : ι → Set (Euclid P) := fun i => (R i).carrier ∩ A i
  let m : ι → Euclid P → ℕ := fun i => (R i).mult
  -- glued multiplicity: `θ = θᵢ` on `Aᵢ`, `0` off `⋃ Aᵢ`
  let θ : Euclid P → ℕ := fun x => if h : ∃ i, x ∈ A i then m h.choose x else 0
  have hθA : ∀ i, ∀ x ∈ A i, θ x = (R i).mult x := by
    intro i x hx
    have h : ∃ j, x ∈ A j := ⟨i, hx⟩
    have hj : h.choose = i := by
      by_contra hne
      exact (Set.disjoint_left.1 (hAd hne)) h.choose_spec hx
    show (if h' : ∃ j, x ∈ A j then m h'.choose x else 0) = m i x
    rw [dite_eq_left h, hj]
  have hθ0 : ∀ x, (¬ ∃ i, x ∈ A i) → θ x = 0 := by
    intro x hx
    show (if h' : ∃ j, x ∈ A j then m h'.choose x else 0) = 0
    rw [dite_eq_right hx]
  have hNm : ∀ i, MeasurableSet (N i) := fun i => (R i).measurableSet_carrier.inter (hAm i)
  have hMm : MeasurableSet (⋃ i, N i) := MeasurableSet.iUnion hNm
  have hMU : (⋃ i, N i) ⊆ U :=
    iUnion_subset fun i => inter_subset_left.trans ((R i).carrier_subset.trans (hWU i))
  have hθm : Measurable θ := by
    refine measurable_to_countable' fun n => ?_
    have hpre : θ ⁻¹' {n} = (⋃ i, A i ∩ (R i).mult ⁻¹' {n}) ∪ ((⋃ i, A i)ᶜ ∩ {_x | 0 = n}) := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_union, mem_iUnion, mem_inter_iff,
        mem_compl_iff, mem_ofPred_eq]
      constructor
      · intro hx
        by_cases h : ∃ i, x ∈ A i
        · obtain ⟨i, hi⟩ := h
          exact Or.inl ⟨i, hi, by rw [← hθA i x hi]; exact hx⟩
        · exact Or.inr ⟨h, by rw [← hθ0 x h]; exact hx⟩
      · rintro (⟨i, hi, hx⟩ | ⟨h, hn⟩)
        · rw [hθA i x hi]; exact hx
        · rw [hθ0 x h]; exact hn
    rw [hpre]
    refine (MeasurableSet.iUnion fun i =>
      (hAm i).inter ((R i).measurable_mult (measurableSet_singleton n))).union
      ((MeasurableSet.iUnion hAm).compl.inter ?_)
    by_cases hn : 0 = n
    · simp [hn]
    · simp [hn]
  have hθpos : ∀ x ∈ ⋃ i, N i, 0 < θ x := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.1 hx
    rw [hθA i x hxi.2]
    exact (R i).mult_pos x hxi.1
  have hMrect : CountablyRectifiable k (⋃ i, N i) := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · rw [iUnion_of_empty]
      exact Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty
    · obtain ⟨s, hs⟩ := exists_surjective_nat ι
      rw [← hs.iUnion_comp N]
      exact Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion _
        fun n => (R (s n)).rectifiable.mono inter_subset_left
  -- `μ = Σᵢ μ⌞Aᵢ = Σᵢ (θᵢ Hᵏ⌞Mᵢ)⌞Aᵢ`
  have hμsum : μ = Measure.sum (fun i => ((R i).measure).restrict (A i)) := by
    have h1 : μ.restrict (⋃ i, A i) = μ := by
      refine Measure.restrict_eq_self_of_ae_mem ?_
      rw [ae_iff]
      simpa [compl_def] using hAc
    calc μ = μ.restrict (⋃ i, A i) := h1.symm
      _ = Measure.sum (fun i => μ.restrict (A i)) := Measure.restrict_iUnion hAd hAm
      _ = Measure.sum (fun i => ((R i).measure).restrict (A i)) := by
          congr 1
          funext i
          exact hμA i
  -- the measure identity `θ Hᵏ⌞M = μ`
  have hmeas : (μHE[k].restrict (⋃ i, N i)).withDensity (fun x => (θ x : ℝ≥0∞)) = μ := by
    have hNd : Pairwise (fun i j => Disjoint (N i) (N j)) :=
      fun i j hij => (hAd hij).mono inter_subset_right inter_subset_right
    rw [hμsum, Measure.restrict_iUnion hNd hNm, withDensity_sum]
    congr 1
    funext i
    rw [IMRep.measure, restrict_withDensity (hAm i), Measure.restrict_restrict (hAm i),
      inter_comm (A i)]
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem (hNm i)] with x hx
    rw [hθA i x hx.2]
  have hlint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in (⋃ i, N i) ∩ K, (θ x : ℝ≥0∞) ∂μHE[k] ≠ ∞ := by
    intro K hK hKU
    have h1 : ∫⁻ x in (⋃ i, N i) ∩ K, (θ x : ℝ≥0∞) ∂μHE[k] =
        ((μHE[k].restrict (⋃ i, N i)).withDensity (fun x => (θ x : ℝ≥0∞))) K := by
      rw [withDensity_apply _ hK.measurableSet, Measure.restrict_restrict hK.measurableSet,
        inter_comm]
    rw [h1, hmeas]
    exact (hfin K hK hKU).ne
  have hMfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[k] ((⋃ i, N i) ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (hlint K hK hKU) ?_
    calc μHE[k] ((⋃ i, N i) ∩ K) = ∫⁻ _ in (⋃ i, N i) ∩ K, (1 : ℝ≥0∞) ∂μHE[k] := by
          rw [setLIntegral_one]
      _ ≤ ∫⁻ x in (⋃ i, N i) ∩ K, (θ x : ℝ≥0∞) ∂μHE[k] := by
          refine setLIntegral_mono (measurable_from_nat.comp hθm) ?_
          intro x hx
          exact_mod_cast hθpos x hx.1
  -- `Hᵏ⌞M ≪ θ Hᵏ⌞M = μ`, so `ξ` is `Hᵏ⌞M`-measurable
  have hac : μHE[k].restrict (⋃ i, N i) ≪ μ := by
    rw [← hmeas]
    refine withDensity_absolutelyContinuous' (measurable_from_nat.comp hθm).aemeasurable ?_
    filter_upwards [ae_restrict_mem hMm] with x hx
    exact_mod_cast (hθpos x hx).ne'
  have hξM : AEStronglyMeasurable ξ (μHE[k].restrict (⋃ i, N i)) := hξm.mono_ac hac
  -- orientation: sibling `cbrg_ae_orient_iUnion`
  have horient := Submission.cbrg_ae_orient_iUnion hIMC ι P k U W N R ξ hU hWo hNm
    (fun i => inter_subset_left) hMU hMfin hξ
  exact ⟨{ carrier := ⋃ i, N i
           mult := θ
           orient := ξ
           measurableSet_carrier := hMm
           carrier_subset := hMU
           rectifiable := hMrect
           measurable_mult := hθm
           mult_pos := hθpos
           locallyIntegrable_mult := hlint
           aestronglyMeasurable_orient := hξM
           orients := horient }, rfl, rfl, hmeas⟩
```

## Key steps

1. Glue θ := θ_i on A_i (unique index by disjointness), 0 off ⋃ A_i; M := ⋃_i (M_i ∩ A_i) is Borel, ⊆ U, countably k-rectifiable; θ is measurable (fibres) and θ ≥ 1 on M.
2. μ = Σ_i μ⌞A_i = Σ_i (R_i.measure)⌞A_i = Σ_i (Hᵏ⌞(M_i ∩ A_i)).withDensity θ = (Hᵏ⌞M).withDensity θ (restrict_iUnion, withDensity_sum, restrict_withDensity, withDensity_congr_ae).
3. Hence ∫_{M∩K} θ dHᵏ = μ(K) < ∞ and Hᵏ(M ∩ K) < ∞ on compacts K ⊆ U; Hᵏ⌞M ≪ μ gives AEStronglyMeasurable ξ (Hᵏ⌞M).
4. Orientation of M by ξ a.e. is the sibling cbrg_ae_orient_iUnion applied to the pieces N_i = M_i ∩ A_i.
5. R' := (M, θ, ξ) is an IMRep in U with R'.carrier = ⋃_i (M_i ∩ A_i), R'.orient = ξ and R'.measure = μ.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean (identical); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `rg -n in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib for: theorem isOpen_iUnion_countable; protected theorem MeasurableSet.disjointed; theorem iUnion_disjointed; theorem disjoint_disjointed; theorem disjointed_subset; theorem biUnion_range; theorem Countable.exists_eq_range; theorem exists_surjective_nat; theorem iUnion_comp; theorem ae_restrict_iUnion_iff; theorem ae_restrict_of_ae_restrict_of_subset; theorem ae_restrict_iff'; theorem restrict_iUnion; theorem restrict_eq_self_of_ae_mem; theorem restrict_restrict_of_subset; theorem withDensity_sum; theorem restrict_withDensity; theorem withDensity_congr_ae; lemma withDensity_absolutelyContinuous'; lemma mono_ac; theorem measurable_to_countable'; theorem setLIntegral_mono; theorem setLIntegral_one; aestronglyMeasurable_iUnion_iff; PseudoMetrizableSpace instances (Topology/Metrizable/Basic.lean); ContinuousAlternatingMap instNormedAddCommGroup`
- `grep -n in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean for def CountablyRectifiable, countablyRectifiable_of_measure_zero, CountablyRectifiable.mono, countablyRectifiable_iUnion (ℕ-indexed only), def HasApproximateTangentSpaceAt; sed of Chapter06/Forms.lean (Covector E n := E [⋀^Fin n]→L[ℝ] ℝ)`
- `lake env lean instance probes: #synth NormedAddCommGroup/MetricSpace (MultiVector P k) succeed; #synth TopologicalSpace.PseudoMetrizableSpace (MultiVector P k) fails (strong topology ContinuousLinearMap.topologicalSpace is not defeq to the metric topology)`
- `python3 -I scans of /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json: lean_statements mentioning carrier ∩ K, IsUnitOrientationOf, ⋃, tangent locality, IMRep; status/candidate_commit of rsd_imrep_compact_measure_ne_top, rsdic_imrep_ae_tangent_orient_of_subset, fvmb_imrep_ae_unitOrientation_approxTangentPlane, regcomp_approx_tangent_locality, rsdic_ae_tangent_iff_of_subset, dtc_approxTangent_of_null_diff; cross-branch dependency count (240 edges); lean_name collision scan for cbrg_exists_countable_disjoint_refinement, cbrg_ae_orient_iUnion, cbrg_imRep_glue_disjoint, rsd_imrep_compact_measure_ne_top (re-run at 981 nodes); exact-type equality of the selected node, cbr_imRep_measure_basic and rsd_imrep_compact_measure_ne_top`
- `git show 702e7082a5a7012f7a8f6efd9d272697e426f50b:GMT/Ch07/Submission.lean (theorem Submission.rsd_imrep_compact_measure_ne_top with the frozen type) and its accepted parent-child-handoff.json`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint, _install_parent_supplied_child_handoff, child id mapping by lean_name) and store.py ensure: accepted same-type declarations are reused by name and left untouched`
- `lake env lean /tmp/glue-decomp/Types.lean, Assembly.lean, Children2.lean, Final.lean, Appendix.lean; python3 -I /tmp/glue-decomp-scripts/lexcheck.py, extract_check.py, final_checks.py (validate_lean_statement from /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py)`
- `sed -n 733,753p and 2305,2320p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt (Simon 6.3.1 Definition; Remark 8.3(1)); web: Simon, Introduction to GMT (public copy https://web.stanford.edu/class/math285/ts-gmt.pdf), Ch. 3 §1 and Ch. 6 §3`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Lattice/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Lattice/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/Countable/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-f6cee6c8d7/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-imrep-local-finiteness-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/glue-decomp/Types.lean`
- `/tmp/glue-decomp/Assembly.lean`
- `/tmp/glue-decomp/Children2.lean`
- `/tmp/glue-decomp/Final.lean`
- `/tmp/glue-decomp/Appendix.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean. Neither the Mathlib snapshot, SimonGMT nor the DAG contains a countable disjoint refinement of a local cover, an orientation-locality lemma for countable unions of IMRep pieces, or an IMRep gluing lemma (no match); these are the three new children. Local finiteness of IMRep carriers is the accepted rsd_imrep_compact_measure_ne_top (candidate 702e7082), reused with its identical frozen type. Unconditional tangent-locality declarations also exist (regcomp_approx_tangent_locality, rsdic_ae_tangent_iff_of_subset, rsdic_imrep_ae_tangent_orient_of_subset). They are not needed, because the selected node carries (IMC)(a) as a hypothesis and the children pass it on. Every cited Mathlib name exists in the pinned snapshot. SimonGMT countablyRectifiable_iUnion is ℕ-indexed, so glue_pieces reindexes through exists_surjective_nat. aestronglyMeasurable_iUnion_iff is unusable for MultiVector P k: no PseudoMetrizableSpace instance is synthesized, because the strong topology of Covector →L[ℝ] ℝ is not definitionally the metric topology. glue_pieces therefore uses AEStronglyMeasurable ξ μ and Hᵏ⌞M ≪ μ, as in the supplied step 6(d). All child types elaborate and pass the lexical check. A hypothesis-only Lean proof derives the exact frozen parent type from the child types and cbr_imRep_measure_basic's type. Every child is fully proved in Lean from its declared dependencies. All of these checks use only the axioms propext, Classical.choice and Quot.sound.
