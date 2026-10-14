# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.im_series-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.im_series-a1.density_imrep-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps (5e) and (5g) of the supplied proof: the IMRep (N', |m|, sign(m)η) built from an integer multiplicity m and an orientation η of N. Tangent planes pass from N to N' by locality, which is (IMC)(a), here the reused sibling tangent_locality. Stated for an arbitrary open U and degree n; the supplied proof's removal of a null set Z is unnecessary because the IMRep fields are a.e. conditions.

Notation: μ := Hⁿ = μHE[n].

1. (Carrier.) N' := N ∩ {x : m(x) ≠ 0}. It is Borel: N is Borel and m is measurable, so {m ≠ 0} = m⁻¹(ℝ ∖ {0}) is Borel. Also N' ⊆ N ⊆ U.
2. (Multiplicity.) mult(x) := ⌊|m(x)|⌋₊ ∈ ℕ (Nat.floor). For every x, m(x) = z for some z ∈ ℤ, and |m(x)| = |z| is the natural number natAbs z, so (mult(x) : ℝ) = |m(x)|. mult is measurable as the composition of the measurable m, the continuous |·| and the monotone, hence measurable, ⌊·⌋₊ : ℝ → ℕ (Monotone.measurable). For x ∈ N', m(x) ≠ 0, so mult(x) = |m(x)| > 0.
3. (Orientation.) orient(x) := −η(x) if m(x) < 0, and orient(x) := η(x) otherwise. It is strongly measurable: η and −η = (−1)•η are strongly measurable, {m < 0} is Borel, and the piecewise combination is strongly measurable (StronglyMeasurable.ite). In particular orient is a.e. strongly measurable for μ⌞N'.
4. (Rectifiability, local integrability.) N' ⊆ N, so N' is countably n-rectifiable (CountablyRectifiable.mono). For compact K ⊆ U: ∫_{N'∩K} mult dμ ≤ ∫_{N∩K} mult dμ = ∫_{N∩K} |m| dμ < ∞, by monotonicity in the set, step 2 and the hypothesis.
5. (Orientation field.) Apply sibling tangent_locality with open U, small set N' and large set N. Here N' ⊆ N ⊆ U are Borel and N is locally finite by hypothesis. So for μ⌞N'-a.e. x and every Q: HasApproximateTangentSpaceAt n N x Q ⟺ HasApproximateTangentSpaceAt n N' x Q. The hypothesis on η holds μ⌞N-a.e., hence μ⌞N'-a.e., since N' ⊆ N. Take x outside both exceptional null sets and Q from the hypothesis. Then HasApproximateTangentSpaceAt n N' x Q, and orient(x) ∈ {η(x), −η(x)} is a unit orientation of Q. Indeed, if η(x)(α) = α(τ) for all α (resp. −α(τ)), with τ orthonormal spanning Q, then −η(x)(α) = −α(τ) (resp. α(τ)); IsUnitOrientationOf allows either sign with the same τ.
6. Steps 1–5 verify every field of IMRep (measurableSet_carrier, carrier_subset, rectifiable, measurable_mult, mult_pos, locallyIntegrable_mult, aestronglyMeasurable_orient, orients). So R := (N', mult, orient) is an IMRep in U.
7. (Action.) Let ω be any n-form. For x ∈ N:
   - if m(x) = 0, then x ∉ N' and 1_{N'}(x)·mult(x)·orient(x)(ω(x)) = 0 = m(x)·η(x)(ω(x));
   - if m(x) ≠ 0, then x ∈ N' and mult(x)·orient(x)(ω(x)) = |m(x)|·(±η(x)(ω(x))) = m(x)·η(x)(ω(x)), the sign being that of m(x).
   So the functions 1_{N'}·mult·orient(ω) and m·η(ω) agree at every point of N. Hence R.action(ω) = ∫_{N'} mult·orient(ω) dμ = ∫_{N ∩ N'} mult·orient(ω) dμ (since N ∩ N' = N') = ∫_N 1_{N'}·mult·orient(ω) dμ (setIntegral_indicator) = ∫_N m·η(ω) dμ (setIntegral_congr_fun). No integrability is needed: Bochner integrals over N of functions that agree pointwise on N coincide. ∎

Lean notes (pinned toolchain): Measurable.nat_floor is outside the import closure of GMT.Ch07.Submission; use (Nat.floor_mono.measurable).comp (continuous_abs.measurable.comp hm). ContinuousNeg (MultiVector P n) is not found by instance search; obtain strong measurability of −η from hη.const_smul (−1 : ℝ) and neg_one_smul.

Lean reference implementation. It was kernel-checked in the decomposition session after import GMT.Ch07.Submission, inside namespace GMT.Ch07 with the contract's opens. #print axioms gives propext, Classical.choice, Quot.sound and the sibling declaration only. An identical copy is in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcdt_im_series_decomposition/Reference.lean.

theorem Submission.cmcdt_ims_imrep_of_int_density : ∀ (P n : ℕ) (U N : Set (Euclid P)) (η : Euclid P → MultiVector P n) (m : Euclid P → ℝ), IsOpen U → MeasurableSet N → N ⊆ U → CountablyRectifiable n N → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (N ∩ K) ≠ ∞) → StronglyMeasurable η → Measurable m → (∀ x, ∃ z : ℤ, m x = z) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∫⁻ x in N ∩ K, ‖m x‖ₑ ∂μHE[n] ≠ ∞) → (∀ᵐ x ∂(μHE[n].restrict N), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n N x Q ∧ IsUnitOrientationOf (η x) Q) → ∃ R : IMRep U n, ∀ ω : DifferentialForm (Euclid P) n, R.action ω = ∫ x in N, m x * η x (ω x) ∂μHE[n] := by
  intro P n U N η m hU hN hNU hrect hfin hη hm hint hloc hor
  classical
  -- the carrier
  set N' : Set (Euclid P) := N ∩ {x | m x ≠ 0} with hN'def
  have hN'meas : MeasurableSet N' :=
    hN.inter ((measurableSet_singleton (0 : ℝ)).preimage hm).compl
  have hN'N : N' ⊆ N := inter_subset_left
  -- multiplicity and orientation
  set mult : Euclid P → ℕ := fun x => ⌊|m x|⌋₊ with hmultdef
  set orient : Euclid P → MultiVector P n := fun x => if m x < 0 then -η x else η x with horientdef
  have hmult_cast : ∀ x, ((mult x : ℕ) : ℝ) = |m x| := by
    intro x
    obtain ⟨z, hz⟩ := hint x
    simp only [hmultdef, hz]
    rw [show |(z : ℝ)| = ((z.natAbs : ℕ) : ℝ) by simp [Nat.cast_natAbs]]
    rw [Nat.floor_natCast]
  have hmult_meas : Measurable mult := (Nat.floor_mono.measurable).comp (continuous_abs.measurable.comp hm)
  have hmult_pos : ∀ x ∈ N', 0 < mult x := by
    intro x hx
    have hx0 : m x ≠ 0 := hx.2
    have h1 : (0 : ℝ) < ((mult x : ℕ) : ℝ) := by
      rw [hmult_cast]; exact abs_pos.mpr hx0
    exact_mod_cast h1
  have horient_sm : StronglyMeasurable orient := by
    have hset : MeasurableSet {x | m x < 0} := measurableSet_lt hm measurable_const
    have hneg : StronglyMeasurable (fun x => -η x) := by
      have := hη.const_smul (-1 : ℝ)
      convert this using 1
      funext x
      exact (neg_one_smul ℝ (η x)).symm
    exact StronglyMeasurable.ite hset hneg hη
  -- local integrability
  have hloc' : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in N' ∩ K, (mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (hloc K hK hKU) ?_
    calc ∫⁻ x in N' ∩ K, (mult x : ℝ≥0∞) ∂μHE[n]
        ≤ ∫⁻ x in N ∩ K, (mult x : ℝ≥0∞) ∂μHE[n] :=
          lintegral_mono_set (inter_subset_inter_left _ hN'N)
      _ ≤ ∫⁻ x in N ∩ K, ‖m x‖ₑ ∂μHE[n] := by
          refine lintegral_mono fun x => ?_
          rw [Real.enorm_eq_ofReal_abs, ← hmult_cast x, ENNReal.ofReal_natCast]
  -- orientation
  have hor' : ∀ᵐ x ∂(μHE[n].restrict N'), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n N' x Q ∧ IsUnitOrientationOf (orient x) Q := by
    have h1 := Submission.rsdic_ae_tangent_iff_of_subset P n U N' N hU hN'meas hN hN'N hNU hfin
    have h2 : ∀ᵐ x ∂(μHE[n].restrict N'), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n N x Q ∧ IsUnitOrientationOf (η x) Q :=
      ae_restrict_of_ae_restrict_of_subset hN'N hor
    filter_upwards [h1, h2] with x hx1 hx2
    obtain ⟨Q, hQ1, hQ2⟩ := hx2
    refine ⟨Q, (hx1 Q).1 hQ1, ?_⟩
    simp only [horientdef]
    split_ifs
    · obtain ⟨τ, hτ, hspan, hξ⟩ := hQ2
      refine ⟨τ, hτ, hspan, ?_⟩
      rcases hξ with h | h
      · right; intro α; simp [h]
      · left; intro α; simp [h]
    · exact hQ2
  let R : IMRep U n :=
    { carrier := N'
      mult := mult
      orient := orient
      measurableSet_carrier := hN'meas
      carrier_subset := hN'N.trans hNU
      rectifiable := hrect.mono hN'N
      measurable_mult := hmult_meas
      mult_pos := hmult_pos
      locallyIntegrable_mult := hloc'
      aestronglyMeasurable_orient := horient_sm.aestronglyMeasurable
      orients := hor' }
  refine ⟨R, ?_⟩
  intro ω
  show ∫ x in N', (mult x : ℝ) * orient x (ω x) ∂μHE[n] = ∫ x in N, m x * η x (ω x) ∂μHE[n]
  have hpt : ∀ x ∈ N, N'.indicator (fun x => (mult x : ℝ) * orient x (ω x)) x = m x * η x (ω x) := by
    intro x hx
    by_cases hx0 : m x = 0
    · have : x ∉ N' := fun h => h.2 hx0
      simp [this, hx0]
    · have hxN' : x ∈ N' := ⟨hx, hx0⟩
      rw [indicator_of_mem hxN', hmult_cast]
      simp only [horientdef]
      split_ifs with hneg
      · rw [abs_of_neg hneg]; simp
      · rw [abs_of_nonneg (not_lt.mp hneg)]
  calc ∫ x in N', (mult x : ℝ) * orient x (ω x) ∂μHE[n]
      = ∫ x in N ∩ N', (mult x : ℝ) * orient x (ω x) ∂μHE[n] := by
        rw [inter_eq_right.mpr hN'N]
    _ = ∫ x in N, N'.indicator (fun x => (mult x : ℝ) * orient x (ω x)) x ∂μHE[n] :=
        (setIntegral_indicator hN'meas).symm
    _ = ∫ x in N, m x * η x (ω x) ∂μHE[n] := setIntegral_congr_fun hN hpt

## Key steps

1. Carrier N' := N ∩ {m ≠ 0} (Borel), multiplicity ⌊|m|⌋₊ = |m| (measurable, positive on N'), orientation sign(m)·η (strongly measurable).
2. N' ⊆ N gives rectifiability; ∫_{N'∩K} |m| ≤ ∫_{N∩K} |m| < ∞ gives local integrability.
3. tangent_locality for N' ⊆ N moves the oriented approximate tangent planes of N to N'; ±η(x) is still a unit orientation.
4. 1_{N'}·|m|·sign(m)η(ω) = m·η(ω) pointwise on N, so R.action(ω) = ∫_N m·η(ω) dHⁿ for every form ω.

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
