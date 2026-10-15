# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.im_series-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.im_series-a1.common_orientation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps (5c) and (5d) of the supplied proof. These are the Borel modification of the ξ_i, the common approximate tangent space Q(x) of N, the reference orientation η(x) := ξ_{ι(x)}(x) with ι(x) := min{i : x ∈ M_i}, and the signs s_i. Here (IMC)(a) combined with the orientation field is the reused sibling tangent_transfer, and (L3) is the reused sibling orientation_sign. Stated for an arbitrary open U and degree n.

Notation: μ := Hⁿ = μHE[n]; M_i := R_i.carrier, ξ_i := R_i.orient, N := ⋃_i M_i.

1. (Sets.) Each M_i is Borel and M_i ⊆ U (IMRep fields), so N is Borel and N ⊆ U.
2. (Borel versions.) ξ_i is a.e. strongly measurable for μ⌞M_i. Let ξ'_i := AEStronglyMeasurable.mk ξ_i: ξ'_i is strongly measurable and ξ'_i = ξ_i μ-a.e. on M_i.
3. (Disjoint pieces.) D_i := M_i ∖ ⋃_{j<i} M_j (Mathlib disjointed). The D_i are Borel and pairwise disjoint, D_i ⊆ M_i, and ⋃_i D_i = N.
4. (Reference orientation.) η(x) := Σ'_i 1_{D_i}(x)·ξ'_i(x). At most one term is nonzero, so η = ξ'_j on D_j (tsum_eq_single) and η = 0 off N. For x ∈ N with ι(x) = min{i : x ∈ M_i}, x ∈ D_{ι(x)} and η(x) = ξ'_{ι(x)}(x). η is strongly measurable. Define g_0 := 0 and g_{k+1}(x) := ξ'_k(x) if x ∈ D_k and g_k(x) otherwise. Each g_k is strongly measurable (piecewise definition on a Borel set). If x ∈ D_j, then g_k(x) = ξ'_j(x) = η(x) for all k > j. If x ∉ N, then g_k(x) = 0 = η(x) for all k. So g_k → η pointwise, and η is strongly measurable as a pointwise limit of strongly measurable functions into the metrizable space MultiVector P n (stronglyMeasurable_of_tendsto).
5. (Signs.) s_i(x) := 1 if ξ'_i(x) = η(x) and s_i(x) := −1 otherwise. The set {ξ'_i = η} is Borel, being the equality set of two strongly measurable maps into a metrizable space (StronglyMeasurable.measurableSet_eq_fun). So s_i is measurable and takes only the values ±1.
6. (Tangent planes along N.) Fix j. Apply tangent_transfer to R_j with B := M_j and C := N. Its hypotheses hold: M_j and N are Borel, M_j ⊆ M_j, M_j ⊆ N ⊆ U, and N is locally finite by hypothesis. So for μ-a.e. x ∈ M_j there is Q with HasApproximateTangentSpaceAt n N x Q and IsUnitOrientationOf (ξ_j(x)) Q. Since ξ'_j = ξ_j a.e. on M_j, also IsUnitOrientationOf (ξ'_j(x)) Q a.e. on M_j. As M_j is Borel, this reads: for μ⌞N-a.e. x, x ∈ M_j implies that statement (ae_restrict_iff'). By countability (ae_all_iff), for μ⌞N-a.e. x: for every j with x ∈ M_j there is Q_j with HasApproximateTangentSpaceAt n N x Q_j and IsUnitOrientationOf (ξ'_j(x)) Q_j. (†)
7. (Signs a.e. on N.) Let x ∈ N satisfy (†). Then x ∈ D_j for some j (step 3), hence x ∈ M_j and η(x) = ξ'_j(x). So (†) gives Q_j with HasApproximateTangentSpaceAt n N x Q_j and IsUnitOrientationOf (η(x)) Q_j; this is conclusion (a) at x. Let i be any index with x ∈ M_i. By (†), Q_i is also an approximate tangent space of N at x, so Q_i = Q_j (SimonGMT HasApproximateTangentSpaceAt.unique). Thus η(x) and ξ'_i(x) are unit orientations of the same Q_j, and orientation_sign gives ξ'_i(x) = η(x) or ξ'_i(x) = −η(x). Hence for μ⌞N-a.e. x, (a) holds and ξ'_i(x) = ±η(x) for every i with x ∈ M_i.
8. (Conclusion (b).) Fix i. Since M_i ⊆ N, μ⌞M_i-a.e. statements follow from μ⌞N-a.e. ones (ae_restrict_of_ae_restrict_of_subset). So for μ-a.e. x ∈ M_i both ξ_i(x) = ξ'_i(x) and ξ'_i(x) = ±η(x) hold. If ξ'_i(x) = η(x), then s_i(x) = 1 and ξ_i(x) = η(x) = 1·η(x). Otherwise ξ'_i(x) ≠ η(x), so ξ'_i(x) = −η(x) and s_i(x) = −1; then ξ_i(x) = −η(x) = (−1)·η(x) (neg_one_smul). Together with steps 4, 5 and 7, all conclusions hold. ∎

Lean notes (pinned toolchain): instance search does not find TopologicalSpace.MetrizableSpace, ContinuousAdd or ContinuousNeg for MultiVector P n. The operator-norm topology is definitionally the strong topology, so MetrizableSpace can be built by hand as below, as in accepted repository code. The approximants are built with ite only, which needs no ContinuousAdd. −η is reached through neg_one_smul.

Lean reference implementation. It was kernel-checked in the decomposition session after import GMT.Ch07.Submission, inside namespace GMT.Ch07 with the contract's opens. #print axioms gives propext, Classical.choice, Quot.sound and the two sibling declarations only. An identical copy is in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcdt_im_series_decomposition/Reference.lean.

theorem Submission.cmcdt_ims_common_orientation : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : ℕ → IMRep U n), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] ((⋃ i, (R i).carrier) ∩ K) ≠ ∞) → ∃ (η : Euclid P → MultiVector P n) (s : ℕ → Euclid P → ℝ), StronglyMeasurable η ∧ (∀ i, Measurable (s i)) ∧ (∀ i x, s i x = 1 ∨ s i x = -1) ∧ (∀ᵐ x ∂(μHE[n].restrict (⋃ i, (R i).carrier)), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n (⋃ i, (R i).carrier) x Q ∧ IsUnitOrientationOf (η x) Q) ∧ ∀ i, ∀ᵐ x ∂(μHE[n].restrict (R i).carrier), (R i).orient x = s i x • η x := by
  intro P n U R hU hfin
  classical
  set M : ℕ → Set (Euclid P) := fun i => (R i).carrier with hMdef
  set N : Set (Euclid P) := ⋃ i, M i with hNdef
  have hMmeas : ∀ i, MeasurableSet (M i) := fun i => (R i).measurableSet_carrier
  have hNmeas : MeasurableSet N := MeasurableSet.iUnion hMmeas
  have hNU : N ⊆ U := iUnion_subset fun i => (R i).carrier_subset
  -- Borel versions of the orientations
  set ξ' : ℕ → Euclid P → MultiVector P n := fun i => (R i).aestronglyMeasurable_orient.mk (R i).orient
  have hξ'sm : ∀ i, StronglyMeasurable (ξ' i) := fun i => (R i).aestronglyMeasurable_orient.stronglyMeasurable_mk
  have hξ'ae : ∀ i, ∀ᵐ x ∂(μHE[n].restrict (M i)), (R i).orient x = ξ' i x :=
    fun i => (R i).aestronglyMeasurable_orient.ae_eq_mk
  -- the disjoint pieces
  set D : ℕ → Set (Euclid P) := disjointed M with hDdef
  have hDmeas : ∀ i, MeasurableSet (D i) := MeasurableSet.disjointed hMmeas
  have hDsub : ∀ i, D i ⊆ M i := disjointed_subset M
  have hDdisj : Pairwise (Disjoint on D) := disjoint_disjointed M
  have hDunion : ⋃ i, D i = N := iUnion_disjointed
  -- the reference orientation
  set η : Euclid P → MultiVector P n := fun x => ∑' i, (D i).indicator (ξ' i) x with hηdef
  have hη_eq : ∀ j x, x ∈ D j → η x = ξ' j x := by
    intro j x hx
    simp only [hηdef]
    rw [tsum_eq_single j]
    · exact indicator_of_mem hx _
    · intro i hij
      have : x ∉ D i := fun hxi => (hDdisj hij).ne_of_mem hxi hx rfl
      exact indicator_of_notMem this _
  haveI hmetr : TopologicalSpace.MetrizableSpace (MultiVector P n) :=
    { toPseudoMetrizableSpace := ⟨⟨PseudoMetricSpace.toUniformSpace, rfl,
        Metric.uniformity_basis_dist_inv_nat_succ.isCountablyGenerated⟩⟩
      toT0Space := inferInstance }
  have hη_zero : ∀ x, (∀ i, x ∉ D i) → η x = 0 := by
    intro x hx
    simp only [hηdef]
    have h0 : ∀ i, (D i).indicator (ξ' i) x = 0 := fun i => indicator_of_notMem (hx i) _
    simp [h0]
  -- finite-stage approximants, built with `ite` only
  let g : ℕ → Euclid P → MultiVector P n := fun k => Nat.rec (fun _ => 0)
    (fun j gj => fun x => if x ∈ D j then ξ' j x else gj x) k
  have hg_succ : ∀ k x, g (k + 1) x = if x ∈ D k then ξ' k x else g k x := fun k x => rfl
  have hg_sm : ∀ k, StronglyMeasurable (g k) := by
    intro k
    induction k with
    | zero => exact stronglyMeasurable_const
    | succ k ih =>
      have : g (k + 1) = fun x => if x ∈ D k then ξ' k x else g k x := funext (hg_succ k)
      rw [this]
      exact StronglyMeasurable.ite (hDmeas k) (hξ'sm k) ih
  have hg_eq : ∀ k x, (∀ i, i < k → x ∉ D i) → g k x = 0 := by
    intro k
    induction k with
    | zero => intro x _; rfl
    | succ k ih =>
      intro x hx
      rw [hg_succ, if_neg (hx k (Nat.lt_succ_self k))]
      exact ih x fun i hi => hx i (Nat.lt_succ_of_lt hi)
  have hg_mem : ∀ j x, x ∈ D j → ∀ k, j < k → g k x = ξ' j x := by
    intro j x hj k
    induction k with
    | zero => intro h; omega
    | succ k ih =>
      intro hk
      rw [hg_succ]
      by_cases hjk : j = k
      · subst hjk; rw [if_pos hj]
      · have hxk : x ∉ D k := fun hxk => (hDdisj (Ne.symm hjk) ).ne_of_mem hxk hj rfl
        rw [if_neg hxk]
        exact ih (by omega)
  have hη_sm : StronglyMeasurable η := by
    refine stronglyMeasurable_of_tendsto atTop hg_sm ?_
    rw [tendsto_pi_nhds]
    intro x
    by_cases hx : ∃ j, x ∈ D j
    · obtain ⟨j, hj⟩ := hx
      apply tendsto_atTop_of_eventually_const (i₀ := j + 1)
      intro k hk
      rw [hη_eq j x hj]
      exact hg_mem j x hj k (by omega)
    · push_neg at hx
      rw [hη_zero x hx]
      apply tendsto_atTop_of_eventually_const (i₀ := 0)
      intro k _
      exact hg_eq k x fun i _ => hx i
  -- signs
  set s : ℕ → Euclid P → ℝ := fun i x => if ξ' i x = η x then 1 else -1 with hsdef
  have hs_meas : ∀ i, Measurable (s i) := by
    intro i
    exact Measurable.ite ((hξ'sm i).measurableSet_eq_fun hη_sm) measurable_const measurable_const
  have hs_val : ∀ i x, s i x = 1 ∨ s i x = -1 := by
    intro i x
    simp only [hsdef]
    split_ifs <;> simp
  -- tangent planes along N, for each piece
  have hP : ∀ j, ∀ᵐ x ∂(μHE[n].restrict (M j)), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n N x Q ∧ IsUnitOrientationOf (ξ' j x) Q := by
    intro j
    have h1 := Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (M j) N (R j) hU (hMmeas j) hNmeas subset_rfl (subset_iUnion M j) hNU hfin
    filter_upwards [h1, hξ'ae j] with x hx1 hx2
    obtain ⟨Q, hQ1, hQ2⟩ := hx1
    exact ⟨Q, hQ1, hx2 ▸ hQ2⟩
  have hPN : ∀ᵐ x ∂(μHE[n].restrict N), ∀ j, x ∈ M j → ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n N x Q ∧ IsUnitOrientationOf (ξ' j x) Q := by
    rw [ae_all_iff]
    intro j
    have := (ae_restrict_iff' (hMmeas j)).mp (hP j)
    exact ae_restrict_of_ae this
  have hgood : ∀ᵐ x ∂(μHE[n].restrict N), (∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n N x Q ∧ IsUnitOrientationOf (η x) Q) ∧
      ∀ i, x ∈ M i → (ξ' i x = η x ∨ ξ' i x = -η x) := by
    have hmemN : ∀ᵐ x ∂(μHE[n].restrict N), x ∈ N := ae_restrict_mem hNmeas
    filter_upwards [hPN, hmemN] with x hx hxN
    rw [← hDunion] at hxN
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxN
    obtain ⟨Qj, hQj1, hQj2⟩ := hx j (hDsub j hj)
    rw [← hη_eq j x hj] at hQj2
    refine ⟨⟨Qj, hQj1, hQj2⟩, fun i hi => ?_⟩
    obtain ⟨Qi, hQi1, hQi2⟩ := hx i hi
    have hQ : Qi = Qj := hQi1.unique hQj1
    rw [hQ] at hQi2
    exact Submission.rsdic_unitOrientation_eq_or_eq_neg P n (η x) (ξ' i x) Qj hQj2 hQi2
  refine ⟨η, s, hη_sm, hs_meas, hs_val, hgood.mono fun x hx => hx.1, fun i => ?_⟩
  have hgoodi : ∀ᵐ x ∂(μHE[n].restrict (M i)), x ∈ M i → (ξ' i x = η x ∨ ξ' i x = -η x) :=
    ae_restrict_of_ae_restrict_of_subset (subset_iUnion M i) (hgood.mono fun x hx => hx.2 i)
  have hmemi : ∀ᵐ x ∂(μHE[n].restrict (M i)), x ∈ M i := ae_restrict_mem (hMmeas i)
  filter_upwards [hgoodi, hmemi, hξ'ae i] with x hx hxM hxe
  rw [hxe]
  rcases hx hxM with h | h
  · simp [hsdef, h]
  · by_cases h' : ξ' i x = η x
    · simp [hsdef, h']
    · simp only [hsdef, h', if_false]
      rw [h]
      exact (neg_one_smul ℝ (η x)).symm

## Key steps

1. Replace each ξ_i by a strongly measurable ξ'_i equal to it a.e. on M_i, and disjointify the carriers: D_i := M_i ∖ ⋃_{j<i} M_j.
2. η := Σ_i 1_{D_i}ξ'_i equals ξ'_{ι(x)} on N; it is strongly measurable as the pointwise limit of ite-built approximants.
3. tangent_transfer for M_j ⊆ N: a.e. on N, every ξ'_j(x) with x ∈ M_j is a unit orientation of an approximate tangent space of N at x.
4. Uniqueness of approximate tangent spaces and orientation_sign give, a.e. on N, a tangent plane oriented by η(x) and ξ'_i(x) = ±η(x) whenever x ∈ M_i.
5. With the measurable signs s_i := (1 if ξ'_i = η else −1), ξ_i = s_iη a.e. on M_i.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest)`
- `rg -n "theorem hasSum_integral_of_dominated_convergence|theorem Measurable.tsum|theorem enorm_tsum_le_tsum_enorm|theorem stronglyMeasurable_of_tendsto|theorem iUnion_disjointed|theorem disjoint_disjointed|theorem setIntegral_indicator|theorem HasCompactSupport.exists_bound_of_continuous|theorem ae_lt_top|theorem ENNReal.summable_toReal|theorem StronglyMeasurable.measurableSet_eq_fun|theorem Monotone.measurable|theorem Int.abs_lt_one_iff|lemma Int.abs_lt_one_iff|theorem lintegral_tsum|theorem measure_iUnion_le" mathlib/Mathlib -g '*.lean'`
- `rg -n "Measurable.tsum|stronglyMeasurable_of_tendsto\b|measurableSet_eq_fun|exists_bound_of_continuous\b|isBoundedBilinearMap_apply\b|theorem tsum_eq_sum\b|theorem lintegral_indicator\b|theorem withDensity_apply\b" mathlib/Mathlib -g '*.lean'; rg -n tprod mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean; rg -n ennreal_tsum mathlib/Mathlib -g '*.lean'; rg -n abs_lt_one_iff mathlib/Mathlib -g '*.lean'`
- `rg -n -i "countable sum|series of currents|integer multiplicity" project/GMT -g '*.lean'; rg -n "IMRep|imrep" project/GMT -g '*.lean'; rg -n cmcdt_ims project mathlib/Mathlib (no match)`
- `grep -n 'theorem countablyRectifiable_iUnion|theorem CountablyRectifiable.mono|theorem HasApproximateTangentSpaceAt.unique' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; reading Chapter06/{Currents,Mass,CurrentLocalEquality,Forms,FormSupNorm}.lean`
- `python3 -I scans of runs/20261011T150044Z-ba604216b4/dag.json (902 then about 980 nodes): statuses, candidate commits and frozen types of rsd_mw_tfa_norm_props, dpf_pfc_testFormOnConverges_zero_uniform, rsdic_imrep_ae_tangent_orient_of_subset, rsdic_unitOrientation_eq_or_eq_neg, rsdic_ae_tangent_iff_of_subset, unit_orientation_norm_le_one (all accepted, byte-identical); exact-type and name search for the four new children (none); comparison with cmc_fc_series_current, dor_lmb_fc_im_series, rsdic_exists_imrep_int_combination`
- `git show a02fee1b89|fe95347baa|a157a5f4f6|0325970d8b:GMT/Ch07/Submission.lean | grep 'theorem Submission.<name>'; git show 2af75d6921:GMT/Ch07/Submission.lean (hand-built MetrizableSpace (MultiVector P n) instance)`
- `sed of /runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/runtime.py (_existing_lean_name_problem, _solve_children node bound, _overlay_accepted_children, _accepted_checkpoint, _install_parent_supplied_child_handoff) and store.py ensure; max_nodes in .humanize/swarm-configs (newest: 5000)`
- `python3 -I /tmp/cmcdt_ims/scripts/gen_challenges.py /runtime/flows/gmt-claude-1e66f8f4bfb6 (gmt-compare.py child_modules + contract_scope + lean_contract.validate_lean_statement on all ten statements); lake env lean Challenge_*.lean (10 files, only the expected sorry)`
- `lake env lean Types.lean, Assembly.lean, C.lean, D.lean, IM1.lean, Support.lean, SeriesCurrentFull.lean (copy of GMT/Scratch/cmc_fc_series_current_decomposition/Full.lean), Reference.lean; #print axioms = propext, Classical.choice, Quot.sound plus only the declared reused siblings`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/InfiniteSum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Group/Unbundled/Int.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-im-series-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-series-current-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-imrep-tangent-transfer-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-orientation-sign-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-tangent-locality-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-tangent-growth-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1-orie-c3a822a8f5/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmc_fc_series_current_decomposition/Full.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcdt_im_series_decomposition/Reference.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcdt_im_series_decomposition/Reference.out`

The snapshot (project b4d606d, Mathlib 25730c7c) has a Ch07 contract byte-identical to the workspace Contract.lean and Submission.lean. The snapshot project has no lemma on series of currents, countable sums of IMReps or integer densities: its Ch06 statements are sorry-frozen, use different types and are not imported by Ch07; cmcdt_ims gives no match. Mathlib supplies every tool the new children cite: hasSum_integral_of_dominated_convergence (MeasureTheory/Integral/DominatedConvergence.lean:77), Measurable.tsum (additive form of Measurable.tprod, Constructions/Polish/Basic.lean:1035), enorm_tsum_le_tsum_enorm (Analysis/Normed/Group/InfiniteSum.lean:133), stronglyMeasurable_of_tendsto and StronglyMeasurable.measurableSet_eq_fun (Function/StronglyMeasurable/Basic.lean:789,1028), disjointed/iUnion_disjointed/disjoint_disjointed (Order/Disjointed.lean), setIntegral_indicator (Integral/Bochner/Set.lean:194), ae_lt_top, lintegral_tsum, ENNReal.summable_toReal, Int.abs_lt_one_iff, Monotone.measurable, isBoundedBilinearMap_apply, withDensity_apply and HasCompactSupport.exists_bound_of_continuous. SimonGMT supplies countablyRectifiable_iUnion, CountablyRectifiable.mono and HasApproximateTangentSpaceAt.unique. The six reused DAG declarations are accepted with byte-identical frozen types and candidate commits. The four new names and types are fresh. All ten child types compile as exact comparator challenges. The assembly of the exact selected type and the proofs of the four new children compile, depending only on standard axioms and the declared reused siblings.
