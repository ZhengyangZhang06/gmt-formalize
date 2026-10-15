# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1.shell_series-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3, 6, 7, 10(a)–(b), 11 and 13 of the parent-supplied proof of the selected node dimred_mbl_dtsd_shell_decomposition, stated for a general current represented by a finite measure (the parent applies it to (T, μ_T, ξ, A_{r_j}, W_j) and to (∂T, μ_∂, ξ_∂, B_{r_j}, D_j)); Simon, Introduction to GMT, Ch. 6, §5, proof of the deformation theorem 5.1, displays (8)–(10) (book/chapter-06.txt lines 1725–1740). Sibling used: EB = eval_mass_bound (cmr_abs_apply_le_massOn: if M_W(Z) ≠ ∞, tsupport ω ⊆ W and |ω(x)| ≤ c for all x, then |Z(ω)| ≤ c·M_W(Z).toReal).
Notation. For ω ∈ 𝒟^k(ℝ^P) put f_ω(x) := ξ(x)(ω(x)). Put E_0 := {x : r_0 ≤ d(x)} and E_{j+1} := {x : r_{j+1} ≤ d(x) ∧ d(x) < r_j}. As d is continuous, {d < t} is open, {t ≤ d} is closed, and all these sets are Borel (measurableSet_lt, measurableSet_le).
1. (Bound for a test form.) Fix ω ∈ 𝒟^k(ℝ^P). The map x ↦ |ω(x)| is continuous: ω is smooth, hence continuous, and α ↦ |α| = √(Σ_I [I strictly increasing] α(e_{I(1)}, …, e_{I(k)})²) is continuous because each evaluation α ↦ α(v) is continuous (continuous_eval_const) and finite sums, squares and Real.sqrt are continuous. It vanishes outside the compact set tsupport ω (|0| = 0, covectorEuclideanNorm_zero; HasCompactSupport.comp_left). Hence it is bounded (Continuous.bounded_above_of_compact_support): there is c_ω with |ω(x)| ≤ c_ω for every x, and c_ω ≥ |ω(0)| ≥ 0.
2. (Integrability.) f_ω is μ-a.e. strongly measurable, as the image of the pair (ξ, ω), with ξ μ-a.e. strongly measurable and ω continuous, under the continuous evaluation map (L, α) ↦ L(α) (Continuous.comp_aestronglyMeasurable₂ with isBoundedBilinearMap_apply.continuous). For μ-a.e. x, |f_ω(x)| ≤ |ω(x)| ≤ c_ω by the a.e. bound on ξ and step 1. As μ is finite, f_ω is μ-integrable (Integrable.of_bound), hence integrable on every set.
3. ((a) Shell integrals.) j = 0: {d < r_0}ᶜ = {r_0 ≤ d} = E_0, so by integral_add_compl (step 2) Y_0(ω) = X(ω) − A_0(ω) = ∫ f_ω dμ − ∫_{d<r_0} f_ω dμ = ∫_{E_0} f_ω dμ. j + 1: as r_{j+1} < r_j, {d < r_{j+1}} ⊆ {d < r_j}, and {d < r_j} \ {d < r_{j+1}} = {r_{j+1} ≤ d ∧ d < r_j} = E_{j+1}; so by setIntegral_sdiff (step 2) Y_{j+1}(ω) = ∫_{d<r_j} f_ω dμ − ∫_{d<r_{j+1}} f_ω dμ = ∫_{E_{j+1}} f_ω dμ. This is (a); thus Y_j(ω) = ∫_{E_j} f_ω dμ for every j.
4. (Shell geometry.) E_j ⊆ {r_j ≤ d} for every j. If i < j then j = j′ + 1 with j′ ≥ i, and E_j ⊆ {d < r_{j′}} ⊆ {d < r_i} since r is decreasing. Hence for i < j no x lies in E_i ∩ E_j (it would satisfy r_i ≤ d(x) < r_i): the E_j are pairwise disjoint Borel sets.
5. ((d) Masses.) By ML with U := ℝ^P, E := E_j and V := ℝ^P (the a.e. bound on ξ and the formula of step 3), M(Y_j) = M_{ℝ^P}(Y_j) ≤ μ(E_j ∩ ℝ^P) = μ(E_j); likewise, by ML with E := {d < r_j} and the hypothesis on A_j, M(A_j) ≤ μ({d < r_j}). In particular M(Y_0) ≤ μ(E_0) ≤ μ(ℝ^P) and M(Y_{j+1}) ≤ μ(E_{j+1}) ≤ μ({d < r_j}) because E_{j+1} ⊆ {d < r_j}. This is (d).
6. (Evaluation bound.) Let Z ∈ 𝒟_k(ℝ^P) and G ⊆ ℝ^P with M(Z) ≤ μ(G). Then M(Z) ≤ μ(G) < ∞ (μ finite), so EB with U = W := ℝ^P, r := c_ω (tsupport ω ⊆ ℝ^P, step 1) gives |Z(ω)| ≤ c_ω·M(Z).toReal ≤ c_ω·μ(G).toReal (ENNReal.toReal_mono, c_ω ≥ 0).
7. (Summability.) By step 4 and countable additivity (measure_iUnion), Σ_j μ(E_j) = μ(⋃_j E_j) ≤ μ(ℝ^P) < ∞, so (μ(E_j).toReal)_j is summable (ENNReal.summable_toReal). By steps 5 and 6, |Y_j(ω)| ≤ c_ω·μ(E_j).toReal, so (Y_j(ω))_j is summable (Summable.of_norm_bounded).
8. (Partial sums.) By induction on N, Σ_{j=0}^{N} Y_j(ω) = X(ω) − A_N(ω): for N = 0 this is the hypothesis on Y_0, and Σ_{j=0}^{N+1} Y_j(ω) = (X(ω) − A_N(ω)) + (A_N(ω) − A_{N+1}(ω)) = X(ω) − A_{N+1}(ω) (Finset.sum_range_succ).
9. (A_N(ω) → 0.) By steps 5 and 6, |A_N(ω)| ≤ c_ω·μ({d < r_N}).toReal. Since μ({d < r_N}) → 0 and toReal is continuous at 0 (ENNReal.tendsto_toReal), c_ω·μ({d < r_N}).toReal → c_ω·0 = 0, so A_N(ω) → 0 (squeeze_zero_norm).
10. ((b) HasSum.) By steps 8 and 9, Σ_{j<N+1} Y_j(ω) = X(ω) − A_N(ω) → X(ω) as N → ∞; shifting the index (tendsto_add_atTop_iff_nat 1), the partial sums Σ_{j<N} Y_j(ω) tend to X(ω). As (Y_j(ω))_j is summable (step 7), Summable.hasSum_iff_tendsto_nat gives HasSum (j ↦ Y_j(ω)) (X(ω)). This is (b).
11. (Vanishing lemma.) Since μ(ℝ^P \ spt X) = 0, μ-a.e. x lies in spt X (measure_eq_zero_iff_ae_notMem). Let G be Borel, F ⊆ ℝ^P with G ⊆ F, and ω ∈ 𝒟^k(ℝ^P) with tsupport ω disjoint from spt X ∩ F. For μ⌞G-a.e. x we have x ∈ G (ae_restrict_mem) and x ∈ spt X (ae_restrict_of_ae), hence x ∈ spt X ∩ F, x ∉ tsupport ω, ω(x) = 0 (image_eq_zero_of_notMem_tsupport) and f_ω(x) = ξ(x)(0) = 0. Hence ∫_G f_ω dμ = 0 (integral_eq_zero_of_ae).
12. ((c) Supports.) spt X is closed by S (ii) and {r_j ≤ d} is closed, so K_j := spt X ∩ {r_j ≤ d} is closed. If tsupport ω is disjoint from K_j, then Y_j(ω) = ∫_{E_j} f_ω dμ = 0 by step 11 with G := E_j ⊆ F := {r_j ≤ d} (step 4); so spt Y_j ⊆ K_j by S (i). If tsupport ω is disjoint from spt X = spt X ∩ ℝ^P, then A_j(ω) = ∫_{d<r_j} f_ω dμ = 0 by step 11 with G := {d < r_j} and F := ℝ^P; so spt A_j ⊆ spt X by S (i) (spt X closed). This is (c). ∎

Appendix (verified Lean realization of the numbered proof above; not part of the proof). The declaration `theorem Submission.dimred_mbl_dtsd_sh_shell_series : T := by` followed by the tactic block below, where T is this child's frozen Lean type (field lean_statement) verbatim, was compiled in this decomposition session with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b366308. It was placed after `import GMT.Ch07.Submission` in the child comparator scope (inside `namespace GMT.Ch07` with the frozen contract's `open` commands, after its `noncomputable section ... end`) and uses the sibling declaration Submission.cmr_abs_apply_le_massOn (eval_mass_bound) (available as a declaration of its frozen type). The antecedents of the statement are hypotheses of the theorem, so no other DAG declaration is used. The comparator solution `exact Submission.dimred_mbl_dtsd_sh_shell_series` closes the frozen challenge type, and `#print axioms` reports only propext, Classical.choice and Quot.sound beyond those sibling declarations.

```lean
  intro hS hML P k X A Y μ ξ d r hμ hξm hξb hnull hd hr htend hX hA hY0 hYs
  have hdm : Measurable d := hd.measurable
  -- Step 1: the integrand `x ↦ ξ x (ω x)` is bounded, a.e. strongly measurable, integrable
  have hcont : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      Continuous (ω : DifferentialForm (Euclid P) k) := fun ω => ω.property.1.1.continuous
  have hnormcont : Continuous (fun α : Covector (Euclid P) k => covectorEuclideanNorm α) := by
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    by_cases hI : StrictMono I
    · simp only [hI, ite_true]; exact (continuous_eval_const _).pow 2
    · simp only [hI, ite_false]; exact continuous_const
  have hbound : ∀ ω : TestFormOn (univ : Set (Euclid P)) k, ∃ c : ℝ,
      ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ c := by
    intro ω
    obtain ⟨c, hc⟩ := (hnormcont.comp (hcont ω)).bounded_above_of_compact_support
      (ω.property.1.2.comp_left (covectorEuclideanNorm_zero P k))
    exact ⟨c, fun x => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hc x)⟩
  have hfm : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      AEStronglyMeasurable (fun x => ξ x ((ω : DifferentialForm (Euclid P) k) x)) μ := fun ω =>
    Continuous.comp_aestronglyMeasurable₂
      (g := fun (L : MultiVector P k) (α : Covector (Euclid P) k) => L α)
      isBoundedBilinearMap_apply.continuous hξm (hcont ω).aestronglyMeasurable
  have hfi : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) k) x)) μ := fun ω => by
    obtain ⟨c, hc⟩ := hbound ω
    exact Integrable.of_bound (hfm ω) c
      (hξb.mono fun x hx => by rw [Real.norm_eq_abs]; exact (hx _).trans (hc x))
  -- Step 2: the shell integral formulas
  have hlt : ∀ j, MeasurableSet {x | d x < r j} := fun j => measurableSet_lt hdm measurable_const
  have hge : ∀ j, MeasurableSet {x | r j ≤ d x} := fun j => measurableSet_le measurable_const hdm
  have hY0' : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      Y 0 ω = ∫ x in {x | r 0 ≤ d x}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ := by
    intro ω
    rw [hY0, hX, hA, ← integral_add_compl (hlt 0) (hfi ω)]
    have h : {x | d x < r 0}ᶜ = {x | r 0 ≤ d x} := by ext x; simp
    rw [h]; ring
  have hYs' : ∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k),
      Y (j + 1) ω = ∫ x in {x | r (j + 1) ≤ d x ∧ d x < r j},
        ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ := by
    intro j ω
    have hsub : {x | d x < r (j + 1)} ⊆ {x | d x < r j} :=
      fun x hx => lt_trans hx (hr (Nat.lt_succ_self j))
    have hset : {x | d x < r j} \ {x | d x < r (j + 1)} = {x | r (j + 1) ≤ d x ∧ d x < r j} := by
      ext x; simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_lt]; exact and_comm
    rw [hYs, hA, hA, ← setIntegral_sdiff (hlt (j + 1)) (hfi ω).integrableOn hsub, hset]
  -- the shells as one family
  obtain ⟨E, hE0, hEs⟩ : ∃ E : ℕ → Set (Euclid P), E 0 = {x | r 0 ≤ d x} ∧
      ∀ i, E (i + 1) = {x | r (i + 1) ≤ d x ∧ d x < r i} :=
    ⟨fun j => match j with
      | 0 => {x | r 0 ≤ d x}
      | i + 1 => {x | r (i + 1) ≤ d x ∧ d x < r i}, rfl, fun _ => rfl⟩
  have hEm : ∀ j, MeasurableSet (E j) := by
    intro j
    cases j with
    | zero => rw [hE0]; exact hge 0
    | succ i => rw [hEs]; exact (hge (i + 1)).inter (hlt i)
  have hEge : ∀ j, E j ⊆ {x | r j ≤ d x} := by
    intro j
    cases j with
    | zero => rw [hE0]
    | succ i => rw [hEs]; exact fun x hx => hx.1
  have hElt : ∀ i j, i < j → E j ⊆ {x | d x < r i} := by
    intro i j hij
    cases j with
    | zero => omega
    | succ j =>
      rw [hEs]
      exact fun x hx => lt_of_lt_of_le hx.2 (hr.antitone (by omega))
  have hdisj : Pairwise (Disjoint on E) := by
    intro i j hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact Set.disjoint_left.2 fun x hxi hxj =>
        absurd (show r i ≤ d x from hEge i hxi) (not_le.2 (hElt i j h hxj))
    · exact Set.disjoint_left.2 fun x hxi hxj =>
        absurd (show r j ≤ d x from hEge j hxj) (not_le.2 (hElt j i h hxi))
  have hYE : ∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k),
      Y j ω = ∫ x in E j, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ := by
    intro j ω
    cases j with
    | zero => rw [hE0]; exact hY0' ω
    | succ i => rw [hEs]; exact hYs' i ω
  -- Step 3: masses (ML)
  have hmassY : ∀ j, (Y j).massOn univ ≤ μ (E j) := fun j =>
    (hML P k univ (Y j) μ ξ (E j) univ hξb (hYE j)).trans (measure_mono inter_subset_left)
  have hmassA : ∀ j, (A j).massOn univ ≤ μ {x | d x < r j} := fun j =>
    (hML P k univ (A j) μ ξ _ univ hξb (hA j)).trans (measure_mono inter_subset_left)
  -- Step 4: evaluation bound (EB + ML)
  have hEB : ∀ (Z : GeometricCurrentOn (univ : Set (Euclid P)) k) (S : Set (Euclid P))
      (ω : TestFormOn (univ : Set (Euclid P)) k) (c : ℝ),
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ c) →
      Z.massOn univ ≤ μ S → |Z ω| ≤ c * (μ S).toReal := by
    intro Z S ω c hc hZ
    have hne : Z.massOn univ ≠ ∞ := (hZ.trans_lt (measure_lt_top μ S)).ne
    have h0c : 0 ≤ c := (covectorEuclideanNorm_nonneg _).trans (hc 0)
    calc |Z ω| ≤ c * (Z.massOn univ).toReal :=
          Submission.cmr_abs_apply_le_massOn P k univ univ Z ω c hne (subset_univ _) hc
      _ ≤ c * (μ S).toReal :=
          mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top μ S) hZ) h0c
  -- Step 5: HasSum
  have hpart : ∀ (ω : TestFormOn (univ : Set (Euclid P)) k) (N : ℕ),
      ∑ j ∈ Finset.range (N + 1), Y j ω = X ω - A N ω := by
    intro ω N
    induction N with
    | zero => simp [hY0]
    | succ N ih => rw [Finset.sum_range_succ, ih, hYs]; ring
  have hsum : ∀ ω : TestFormOn (univ : Set (Euclid P)) k, HasSum (fun j => Y j ω) (X ω) := by
    intro ω
    obtain ⟨c, hc⟩ := hbound ω
    have hsumE : ∑' j, μ (E j) ≠ ∞ := by
      rw [← measure_iUnion hdisj hEm]; exact measure_ne_top μ _
    have hsummable : Summable (fun j => Y j ω) := by
      refine Summable.of_norm_bounded ((ENNReal.summable_toReal hsumE).mul_left c) (fun j => ?_)
      rw [Real.norm_eq_abs]; exact hEB (Y j) (E j) ω c hc (hmassY j)
    rw [hsummable.hasSum_iff_tendsto_nat, ← tendsto_add_atTop_iff_nat 1]
    simp only [hpart]
    have hbd : ∀ n, ‖A n ω‖ ≤ c * (μ {x | d x < r n}).toReal := fun n => by
      rw [Real.norm_eq_abs]; exact hEB (A n) _ ω c hc (hmassA n)
    have hto : Tendsto (fun n => c * (μ {x | d x < r n}).toReal) atTop (𝓝 0) := by
      have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htend).const_mul c
      simpa using h
    simpa using tendsto_const_nhds.sub (squeeze_zero_norm hbd hto)
  -- Step 6: supports (S(i), S(ii))
  have hae : ∀ᵐ x ∂μ, x ∈ X.support := by
    have h := measure_eq_zero_iff_ae_notMem.1 hnull
    exact h.mono fun x hx => by simpa using hx
  have hvanish : ∀ (S F : Set (Euclid P)) (ω : TestFormOn (univ : Set (Euclid P)) k),
      MeasurableSet S → S ⊆ F →
      Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (X.support ∩ F) →
      ∫ x in S, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ = 0 := by
    intro S F ω hSm hSF hdisj
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_restrict_mem hSm, ae_restrict_of_ae hae] with x hxS hxX
    have hx : x ∉ tsupport (ω : DifferentialForm (Euclid P) k) :=
      fun h => Set.disjoint_left.1 hdisj h ⟨hxX, hSF hxS⟩
    simp [image_eq_zero_of_notMem_tsupport hx]
  have hsptY : ∀ j, (Y j).support ⊆ X.support ∩ {x | r j ≤ d x} := by
    intro j
    refine (hS P k).1 _ _ (((hS P k).2.1 X).inter (isClosed_le continuous_const hd))
      (fun ω hω => ?_)
    rw [hYE j]
    exact hvanish (E j) _ ω (hEm j) (hEge j) hω
  have hsptA : ∀ j, (A j).support ⊆ X.support := by
    intro j
    refine (hS P k).1 _ _ ((hS P k).2.1 X) (fun ω hω => ?_)
    rw [hA j]
    exact hvanish _ univ ω (hlt j) (subset_univ _) (by rwa [inter_univ])
  refine ⟨hY0', hYs', hsum, hsptY, hsptA, (hmassY 0).trans (measure_mono (subset_univ _)),
    fun j => (hmassY (j + 1)).trans (measure_mono ?_)⟩
  rw [hEs]
  exact fun x hx => hx.2
```

## Key steps

1. Each test form is bounded, |ω(x)| ≤ c_ω, so f_ω = ξ(ω) is μ-a.e. strongly measurable, bounded and μ-integrable.
2. integral_add_compl and setIntegral_sdiff give Y_j(ω) = ∫_{E_j} ξ(ω) dμ over the half-open shells E_j.
3. The E_j are pairwise disjoint Borel sets; ML gives M(Y_j) ≤ μ(E_j) and M(A_j) ≤ μ({d < r_j}).
4. EB with ML: |Y_j(ω)| ≤ c_ω μ(E_j) and |A_N(ω)| ≤ c_ω μ({d < r_N}); Σ μ(E_j) ≤ μ(ℝ^P) < ∞ gives summability.
5. Partial sums telescope to X(ω) − A_N(ω) → X(ω), hence HasSum.
6. μ is carried by spt X, so the integrands vanish a.e. when tsupport ω misses spt X ∩ {r_j ≤ d}; S (i), (ii) give the supports.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db, mathlib_commit 25730c7c); git rev-parse HEAD (b4d606db); git -C .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); cmp .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical)`
- `rg -n "def boundaryMassOn|structure IMRep|def IMRep.Represents|def IsIntegerMultiplicity|def IMRep.measure|def IMRep.action|instance : Sub \(GeometricCurrentOn|def CompactlyContained|abbrev MultiVector" .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean (lines 48, 61, 79, 83, 88, 92, 96, 120, 127)`
- `rg -n "isOpen_zeroRegion|boundary_boundary|massOn_mono|le_massOn|zero_apply|boundary_apply" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean (GeometricCurrentOn.zero_apply, boundary_apply, boundary_boundary in Currents.lean 317/333/365; massOn_mono, le_massOn in Mass.lean 81/90; isOpen_zeroRegion in CurrentLocalEquality.lean 119)`
- `rg -n "theorem integral_add_compl|theorem setIntegral_sdiff|theorem summable_toReal|theorem measure_iUnion|theorem strictAnti_nat_of_succ_lt|theorem tendsto_pow_atTop_nhds_zero_of_lt_one|theorem integral_eq_zero_of_ae|theorem integral_zero_measure|theorem tendsto_add_atTop_iff_nat|theorem measure_eq_zero_iff_ae_notMem" .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib (all found)`
- `rg -n -i -l "shell|dyadic|good_radius|goodRadius" .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT -g "*.lean" (no match, exit 1); rg -n -i "theorem .*slice|def .*slice" .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT -g "*.lean" (only the specification definitions IsSlice in Ch06 Contract/Submission line 129, not imported by Ch07, and SlicesAreRectifiable in Ch03 line 262)`
- `rg -n "dimred_mbl_dtsd_sh_" .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/.. (no match, exit 1); python3 -I scan of .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json (2138 nodes): no lean_name equals a fresh name or starts with dimred_mbl_dtsd_sh_; the reused names are accepted nodes with byte-identical frozen types`
- `python3 -I scan of .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json: the selected frozen type is byte-identical to the twin node's; the twin's ten child types (decomposition-v1.json of the twin node directory) are reused verbatim; the six resolved dependencies of the selected node have frozen types byte-identical to the twin's six; no accepted node other than the twin's unaccepted children carries any of the seven new types`
- `sed of /runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py (_decompose, _existing_lean_name_problem, _accepted_checkpoint, _solve_children, _install_parent_supplied_child_handoff, _render_parent_supplied_natural) and inherited.py (cited, cited_inherited); python3 -I check with that cited() that no new child proof, key step or this ledger names a not-yet-accepted dependency of the selected node or of its ancestors`
- `lake-env lean GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/EndToEnd.lean (the twin's verified file renamed to this branch's names, accepted ML proof of commit 1041782e inlined; #print axioms: children only propext, Classical.choice, Quot.sound; selected theorem additionally only the two unaccepted resolved dependencies); python3 -I GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/scripts/compare_types.py (all declared types byte-identical to the frozen ones)`
- `lake-env lean GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/AssemblyAx.lean (selected type from the ten child and six dependency types as axioms); lean GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/isolated/Iso_*.lean (each new child with only its declared siblings as axioms, then the comparator solution exact Submission.X)`
- `python3 -I GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/scripts/build_challenges.py with the verifier's child_modules(contract mode) and lean GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/chal/Challenge_*.lean (11 files, 0 errors, one sorry warning each); python3 -I GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/scripts/validate.py (runtime and verifier validate_lean_statement: all accepted unchanged)`
- `git show ae810e9b/ea5c1199/7a706164/1041782e:GMT/Ch07/Submission.lean + #print axioms, compiled with lean (errors 0; propext, Classical.choice, Quot.sound only)`
- `sed -n 1700,1800p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt (Simon 6.5.1 displays (8)–(10) at lines 1725–1740)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Monotone/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-303188e8d1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-691b18cd91/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-691b18cd91/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-691b18cd91/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-9b75b9802b/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_shell_decomposition_split/EndToEnd.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/EndToEnd.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/AssemblyAx.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/types.json`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/inherited.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`

Pins match (project b4d606db, Mathlib 25730c7c), and Submission.lean is byte-identical to the frozen contract. The snapshot project has no shell, dyadic or good-radius declaration; "slice" occurs there only in the specification definitions IsSlice (Ch06, not imported by Ch07) and SlicesAreRectifiable (Ch03), so no snapshot lemma can replace a child. The fresh prefix dimred_mbl_dtsd_sh_ occurs nowhere in the project, Mathlib, SimonGMT or the DAG. Every Mathlib and SimonGMT lemma that the child proofs cite exists at the pinned revisions. The twin node's audited split applies verbatim, because its frozen type and its six resolved-dependency types are byte-identical to the selected node's. Its seven new child types are reused unchanged under fresh names, since its own child names are reserved and unaccepted. Its three reused declarations are accepted with identical types and recompile from their accepted commits with standard axioms. In this session:
- the children's proofs and the assembly compile;
- each new child compiles alone with only its declared siblings;
- the comparator challenge modules elaborate, and both statement validators accept every type unchanged;
- the assembly proves the exact selected type from the child and dependency types;
- no new child proof, key step or this ledger cites a not-yet-accepted inherited prerequisite.
