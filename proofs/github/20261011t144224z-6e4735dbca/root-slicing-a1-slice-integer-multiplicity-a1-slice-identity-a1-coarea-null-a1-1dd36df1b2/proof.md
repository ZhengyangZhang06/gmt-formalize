# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.coarea_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Steps 1 and 2. Step 1 is Simon's remark after (4) in the proof of Ch. 6, Lemma 4.5(2): ∇^M f = 0 Hⁿ-a.e. on {x ∈ M : f(x) = c} for every constant c. Step 2 is the null-transfer property used for the slice triple. Both are stated for arbitrary measures μ, ν. The parent takes μ = H^{m+1}, ν = H^m, and (CA) is the conclusion of its sibling dependency slicing_im_coarea, which has exactly this shape.

Notation. For S ⊆ ℝ^P, ∫_S h dν is the integral against the restricted measure ν⌞S. This is defined for arbitrary S. For a Borel set A and an arbitrary S, ∫_S 1_A dν = (ν⌞S)(A) = ν(A ∩ S). L¹ denotes Lebesgue measure on ℝ. (CA) is the hypothesis: for every Borel g : ℝ^P → [0, ∞], t ↦ ∫_{M∩f⁻¹{t}} g dν is L¹-a.e.-measurable and ∫_ℝ ∫_{M∩f⁻¹{t}} g dν dt = ∫_M |G| g dμ.

Part (i). Fix c ∈ ℝ.
1. A_c := f⁻¹{c} is Borel because f is Borel. Apply (CA) to g := 1_{A_c}. With φ_c(t) := ∫_{M∩f⁻¹{t}} 1_{A_c} dν this gives ∫_ℝ φ_c(t) dt = ∫_M |G|·1_{A_c} dμ.
2. For t ≠ c, φ_c(t) = ν(A_c ∩ (M ∩ f⁻¹{t})) = ν(∅) = 0, because no x has both f(x) = c and f(x) = t.
3. The singleton {c} is L¹-null, so φ_c = 0 L¹-a.e. Hence ∫_ℝ φ_c dt = 0.
4. Therefore ∫_M |G|·1_{A_c} dμ = 0. The integrand x ↦ |G(x)|·1_{A_c}(x) is a nonnegative Borel function (G and f are Borel). A nonnegative measurable function with zero integral vanishes almost everywhere, so |G(x)|·1_{A_c}(x) = 0 for μ⌞M-a.e. x.
5. At such an x with f(x) = c we have 1_{A_c}(x) = 1, so |G(x)| = 0, i.e. G(x) = 0. This proves (i).
Part (ii). Let Z ⊆ M with μ(Z) = 0.
6. Choose a Borel set Z' ⊇ Z with μ(Z') = μ(Z) = 0, e.g. the measurable hull (toMeasurable).
7. Apply (CA) to g := 1_{Z'}. Then ψ(t) := ∫_{M∩f⁻¹{t}} 1_{Z'} dν = ν(Z' ∩ (M ∩ f⁻¹{t})) is L¹-a.e.-measurable, and ∫_ℝ ψ dt = ∫_M |G|·1_{Z'} dμ.
8. Since μ(Z') = 0, 1_{Z'} = 0 μ-a.e., hence also μ⌞M-a.e. (μ⌞M ≤ μ). So the right side of step 7 is 0.
9. ψ ≥ 0 is a.e.-measurable with ∫ψ = 0, so ψ(t) = 0 for L¹-a.e. t.
10. For such t, Z ∩ f⁻¹{t} ⊆ Z' ∩ (M ∩ f⁻¹{t}), because Z ⊆ Z' and Z ⊆ M. Hence ν(Z ∩ f⁻¹{t}) ≤ ψ(t) = 0. This proves (ii). ∎

Formalization notes (a complete Lean proof of exactly this statement was checked in a scratch build of the frozen commit d8d46c9: written as `theorem Submission.<lean_name>` inside `namespace GMT.Ch06` of a file importing GMT.Ch06.Submission, with the comparator-form restatement `theorem _root_.X : (<lean_statement>) := by exact Submission.<lean_name>` also checked; axioms propext, Classical.choice, Quot.sound; the verified proof is appended at the end):
- (i): `lintegral_indicator_one hmc` and `Measure.restrict_apply hmc`, where hmc : MeasurableSet (f ⁻¹' {c}). Get `∀ᵐ t, t ≠ c` from `simp [ae_iff, measure_singleton]`. Then `lintegral_congr_ae`, and `lintegral_eq_zero_iff'` with `(hG.enorm.mul (measurable_one.indicator hmc)).aemeasurable`. Finish with `indicator_of_mem`, `mul_one`, `enorm_eq_zero`.
- (ii): `measurableSet_toMeasurable`, `measure_toMeasurable`, `measure_eq_zero_iff_ae_notMem`, `ae_restrict_of_ae`, `lintegral_eq_zero_iff'` with the AEMeasurable part of (CA), `lintegral_indicator_one`, `Measure.restrict_apply`, `measure_mono_null`, `subset_toMeasurable`.

Verified Lean proof (scratch build of d8d46c9; place it in GMT/Ch06/Submission.lean after the contract's closing `end` of the noncomputable section and before `theorem main_theorem`, inside `namespace GMT.Ch06`; it uses only the frozen imports):
```lean
theorem Submission.slicing_im_si_coarea_null_sets :
    ∀ (P : ℕ) (μ ν : Measure (Eucl P)) (M : Set (Eucl P)) (f : Eucl P → ℝ) (G : Eucl P → Eucl P), Measurable f → Measurable G → (∀ g : Eucl P → ℝ≥0∞, Measurable g → AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂ν) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂ν) ∂(volume : Measure ℝ) = ∫⁻ x in M, ‖G x‖ₑ * g x ∂μ) → (∀ c : ℝ, ∀ᵐ x ∂(μ.restrict M), f x = c → G x = 0) ∧ ∀ Z : Set (Eucl P), Z ⊆ M → μ Z = 0 → ∀ᵐ t ∂(volume : Measure ℝ), ν (Z ∩ f ⁻¹' {t}) = 0 := by
  intro P μ ν M f G hf hG CA
  constructor
  · intro c
    have hmc : MeasurableSet (f ⁻¹' {c}) := hf (measurableSet_singleton c)
    obtain ⟨-, hCA⟩ := CA ((f ⁻¹' {c}).indicator 1) (measurable_one.indicator hmc)
    -- the slice integrals vanish for `t ≠ c`
    have hslice : ∀ t, t ≠ c → ∫⁻ x in M ∩ f ⁻¹' {t}, (f ⁻¹' {c}).indicator 1 x ∂ν = 0 := by
      intro t ht
      rw [lintegral_indicator_one hmc, Measure.restrict_apply hmc]
      convert measure_empty (μ := ν)
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false,
        not_and]
      intro hxc _ hxt
      exact ht (hxt.symm.trans hxc)
    have hL : ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, (f ⁻¹' {c}).indicator 1 x ∂ν) ∂(volume : Measure ℝ) = 0 := by
      have : (fun t => ∫⁻ x in M ∩ f ⁻¹' {t}, (f ⁻¹' {c}).indicator 1 x ∂ν) =ᵐ[volume] 0 := by
        have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ c := by
          simp [ae_iff, measure_singleton]
        filter_upwards [hne] with t ht
        exact hslice t ht
      rw [lintegral_congr_ae this]
      simp
    rw [hL] at hCA
    have hmeas : AEMeasurable (fun x => ‖G x‖ₑ * (f ⁻¹' {c}).indicator 1 x) (μ.restrict M) :=
      (hG.enorm.mul (measurable_one.indicator hmc)).aemeasurable
    have h0 := (lintegral_eq_zero_iff' hmeas).1 hCA.symm
    filter_upwards [h0] with x hx hfx
    have hxc : x ∈ f ⁻¹' {c} := hfx
    simp only [Pi.zero_apply, indicator_of_mem hxc, Pi.one_apply, mul_one, enorm_eq_zero] at hx
    exact hx
  · intro Z hZM hZ
    have hZ'm : MeasurableSet (toMeasurable μ Z) := measurableSet_toMeasurable μ Z
    have hZ'0 : μ (toMeasurable μ Z) = 0 := by rw [measure_toMeasurable]; exact hZ
    obtain ⟨hae, hCA⟩ := CA ((toMeasurable μ Z).indicator 1) (measurable_one.indicator hZ'm)
    have hR : ∫⁻ x in M, ‖G x‖ₑ * (toMeasurable μ Z).indicator 1 x ∂μ = 0 := by
      have hnull : ∀ᵐ x ∂μ, x ∉ toMeasurable μ Z := measure_eq_zero_iff_ae_notMem.1 hZ'0
      have : (fun x => ‖G x‖ₑ * (toMeasurable μ Z).indicator 1 x) =ᵐ[μ.restrict M] 0 := by
        filter_upwards [ae_restrict_of_ae hnull] with x hx
        simp [indicator_of_notMem hx]
      rw [lintegral_congr_ae this]
      simp
    rw [hR] at hCA
    have h0 := (lintegral_eq_zero_iff' hae).1 hCA
    filter_upwards [h0] with t ht
    simp only [Pi.zero_apply] at ht
    rw [lintegral_indicator_one hZ'm, Measure.restrict_apply hZ'm] at ht
    refine measure_mono_null (fun x hx => ?_) ht
    exact ⟨subset_toMeasurable μ Z hx.1, hZM hx.1, hx.2⟩
```

## Key steps

1. (CA) with g = 1_{f⁻¹{c}}: the slice integrals vanish for t ≠ c, so ∫_M |G| 1_{f=c} dμ = 0 and G = 0 μ⌞M-a.e. on {f = c}
2. for μ-null Z ⊆ M take a Borel null hull Z' ⊇ Z; (CA) with g = 1_{Z'} has right side 0
3. hence ν(Z' ∩ M ∩ f⁻¹{t}) = 0 for a.e. t, and ν(Z ∩ f⁻¹{t}) ≤ ν(Z' ∩ M ∩ f⁻¹{t})

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (byte-identical); read Contract.lean: IsRectifiableTriple, tauAction, IsMeasureRepresentation, IsRestriction, IsSlice`
- `grep -n 'def testFormOnSubmodule|def exteriorDerivativeTestOn|tsupport_exteriorDerivative_subset|boundary_apply' simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents}.lean`
- `python3 scan of dag.json: decomposition of root.slicing-a1.slice_integer_multiplicity-a1 (sibling types slicing_im_coarea, slicing_im_lipschitz_leibniz, statuses decomposing); accepted nodes matching 'f ⁻¹' {t}|HasDerivAt (fun s|max 0|𝓝[>] 0|toMeasurable|simpleNVector|innerSL|alternatizeUncurryFin|IsSlice' -> reusable slicing_mb_pointwise_cutoff_tendsto (012eb78d) and fiw_ims_tt_unit_bound (27af9b19)`
- `git show 012eb78d57e01b1e54de6b8f0e5cf786950b91c0:GMT/Ch06/Submission.lean; git show 27af9b191b732eae73e3d693d8903e52f89962ce:GMT/Ch06/Submission.lean (accepted proofs, isolated-comparator-result.json passed)`
- `grep -rn 'theorem ae_tendsto_average|ae_hasDerivAt_integral|tendsto_Icc_vitaliFamily_left' mathlib/Mathlib; read MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`
- `lake env lean Avail*.lean: availability under `import GMT.Ch06.Submission` of LocallyIntegrable.ae_hasDerivAt_integral (unknown constant), VitaliFamily.ae_tendsto_average, Real.tendsto_Icc_vitaliFamily_left, NullMeasurableSet.exists_measurable_subset_ae_eq, Measure.restrict_congr_set, Measure.le_restrict_apply, lintegral_eq_zero_iff', integral_eq_lintegral_pos_part_sub_lintegral_neg_part, integrable_toReal_of_lintegral_ne_top, integral_toReal, ae_lt_top', ContinuousAlternatingMap.norm_alternatizeUncurryFin_le, isBoundedBilinearMap_smulRight, Integrable.bdd_mul`
- `lake env lean /tmp/sid_split_scratch/Stmts.lean (eight child types in the exact comparator scope; #print checked)`
- `lake env lean /tmp/sid_split_scratch/Assembly.lean (parent type from child and sibling types; #print axioms)`
- `lake env lean /tmp/sid_split_scratch/Full.lean (#print axioms ParentFromUncles: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/sid_split_scratch/E2Echildren.lean (embedded child proofs verbatim + comparator-form exact; no errors, no warnings)`
- `rg 'slicing_im_si_' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project (no match); grep -rn 'slicing_im_si_' simongmt/Poincare (no match); dag.json lean_name scan for slicing_im_si_* (no match among 464 nodes)`
- `sed -n 1150,1345p book/chapter-06.txt (Simon Ch. 6, 4.1, Remark 4.2, 4.4, Lemma 4.5 and its proof)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/OneDim.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-localization-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-pointwise-a1-cutoff-tendsto-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-pointwise-a1-cutoff-tendsto-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1-unit-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1-unit-bound-a1/isolated-comparator-result.json`
- `/tmp/sid_split_scratch/Stmts.lean`
- `/tmp/sid_split_scratch/Assembly.lean`
- `/tmp/sid_split_scratch/Full.lean`
- `/tmp/sid_split_scratch/E2Echildren.lean`

The pinned snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract; Submission is byte-identical, so child types may use only contract, SimonGMT and Mathlib names in the comparator scope. SimonGMT provides TestFormOn (smooth, compact support, tsupport ⊆ U), exteriorDerivativeTestOn, tsupport_exteriorDerivative_subset and GeometricCurrentOn.boundary_apply. Neither SimonGMT nor Mathlib has co-area, slicing or cut-off tangential-gradient results; the six new children isolate exactly those steps of the supplied proof (Simon Ch. 6, Remark 4.2 and proof of 4.5(2)). Mathlib's interval Lebesgue differentiation lemma is not importable from Submission, but VitaliFamily.ae_tendsto_average and Real.tendsto_Icc_vitaliFamily_left are, so the one-sided version is proved from them. Two accepted DAG declarations are reused with byte-identical types: slicing_mb_pointwise_cutoff_tendsto (Step 9) and fiw_ims_tt_unit_bound (Fact U). All eight child types elaborate in the exact comparator scope. In scratch Lean the six new children are fully proved, and the parent's frozen type follows from the children plus the two declared sibling types slicing_im_coarea and slicing_im_lipschitz_leibniz, using only propext, Classical.choice and Quot.sound. No new name collides with the snapshot, SimonGMT or the 464 DAG nodes. These checks do not cover the proofs of the two sibling dependencies, which remain their own nodes.
