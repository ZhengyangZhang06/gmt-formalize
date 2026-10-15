# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.slice_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 5 (identification of the slice density with tauAction on M_t, using the null-transfer property NT). It is stated abstractly for measures μ, ν, a μ-null-measurable M and a Borel set S. The parent takes μ = H^{m+1}, ν = H^m, S = {G ≠ 0} and F = θ·ξ_t(ω); NT comes from the sibling coarea_null (ii).

This step closes a measure-theoretic gap in the supplied Step 5. The slice M ∩ f⁻¹{t} need not be ν-measurable. For a non-measurable set A the restricted measure ν⌞A can charge points outside A, so "g = F at every point of A outside a ν-null set" does not by itself give g = F ν⌞A-a.e. The proof below therefore first replaces M by a Borel M₁ ⊆ M with μ(M ∖ M₁) = 0, and uses NT to see that the restricted measures do not change for a.e. t.

Notation. ∫_A h dν is the Bochner integral against ν⌞A, defined for every A ⊆ ℝ^P (it is 0 if h is not integrable). Two integrands that agree ν⌞A-a.e. have the same integral, whether or not they are measurable or integrable. A =ᵐ B means ν((A ∖ B) ∪ (B ∖ A)) = 0; it implies ν⌞A = ν⌞B.

1. (Null subsets of M.) Let Z₁ := M ∩ {x : x ∈ S and g(x) ≠ F(x)}. For every set D, μ(D ∩ M) ≤ (μ⌞M)(D). With D := {x : ¬(x ∈ S ⟹ g(x) = F(x))}, which is μ⌞M-null by hypothesis, this gives μ(Z₁) = 0. Since M is μ-null-measurable, there is a Borel M₁ ⊆ M with M₁ = M μ-a.e.; put Z₂ := M ∖ M₁, so μ(Z₂) = 0. Then Z := Z₁ ∪ Z₂ ⊆ M and μ(Z) = 0.
2. (Good t.) By NT, ν(Z ∩ f⁻¹{t}) = 0 for L¹-a.e. t. Fix such a t. Since f is Borel, f⁻¹{t} is Borel.
3. (Borel replacements of the domains.)
 - Let A := M ∩ f⁻¹{t} and A₁ := M₁ ∩ f⁻¹{t}, which is Borel. Then A₁ ⊆ A and A ∖ A₁ ⊆ Z₂ ∩ f⁻¹{t} ⊆ Z ∩ f⁻¹{t}, which is ν-null. So A =ᵐ A₁ and ν⌞A = ν⌞A₁.
 - Let B := {x : x ∈ M, f(x) = t, x ∈ S} and B₁ := A₁ ∩ S, which is Borel. Then B₁ ⊆ B and B ∖ B₁ ⊆ Z₂ ∩ f⁻¹{t}, so ν⌞B = ν⌞B₁.
4. (Left side.) g = 0 off S, so g = 1_S·g everywhere. As S is Borel, ∫_A g dν = ∫_{A₁} 1_S g dν = ∫_{A₁∩S} g dν = ∫_{B₁} g dν.
5. (g = F on B₁.) If x ∈ B₁ and g(x) ≠ F(x), then x ∈ M, x ∈ S, g(x) ≠ F(x) and f(x) = t. So x ∈ Z₁ ∩ f⁻¹{t} ⊆ Z ∩ f⁻¹{t}. Thus {x ∈ B₁ : g(x) ≠ F(x)} is ν-null. Since B₁ is Borel, this means g = F ν⌞B₁-a.e., and so ∫_{B₁} g dν = ∫_{B₁} F dν.
6. (Conclusion.) ∫_A g dν = ∫_{B₁} g dν = ∫_{B₁} F dν = ∫_B F dν, using steps 4, 5 and 3. This holds for every t as in step 2, i.e. for L¹-a.e. t. ∎

Formalization notes (a complete Lean proof of exactly this statement was checked in a scratch build of the frozen commit d8d46c9: written as `theorem Submission.<lean_name>` inside `namespace GMT.Ch06` of a file importing GMT.Ch06.Submission, with the comparator-form restatement `theorem _root_.X : (<lean_statement>) := by exact Submission.<lean_name>` also checked; axioms propext, Classical.choice, Quot.sound; the verified proof is appended at the end):
- Step 1: `NullMeasurableSet.exists_measurable_subset_ae_eq`, `Measure.le_restrict_apply M _` together with `ae_iff`, `ae_eq_set` (its second component gives μ(M ∖ M₁) = 0), `measure_union_null`.
- Steps 2–3: `filter_upwards [hNT _ (union_subset inter_subset_right sdiff_subset) hZ] with t ht`. For A =ᵐ A₁, use `ae_eq_set`, `measure_mono_null` for one difference, and the empty set for the other.
- Step 4: `rw [Measure.restrict_congr_set hA, Measure.restrict_congr_set hB]`, then rewrite g as `S.indicator g` and use `setIntegral_indicator hS`.
- Step 5: `setIntegral_congr_ae ((hM₁m.inter hft).inter hS)`, `ae_iff`, `measure_mono_null`, `Classical.not_imp`.

Verified Lean proof (scratch build of d8d46c9; place it in GMT/Ch06/Submission.lean after the contract's closing `end` of the noncomputable section and before `theorem main_theorem`, inside `namespace GMT.Ch06`; it uses only the frozen imports):
```lean
theorem Submission.slicing_im_si_slice_ae_transfer :
    ∀ (P : ℕ) (μ ν : Measure (Eucl P)) (M S : Set (Eucl P)) (f g F : Eucl P → ℝ), NullMeasurableSet M μ → MeasurableSet S → Measurable f → (∀ Z : Set (Eucl P), Z ⊆ M → μ Z = 0 → ∀ᵐ t ∂(volume : Measure ℝ), ν (Z ∩ f ⁻¹' {t}) = 0) → (∀ x, x ∉ S → g x = 0) → (∀ᵐ x ∂(μ.restrict M), x ∈ S → g x = F x) → ∀ᵐ t ∂(volume : Measure ℝ), ∫ x in M ∩ f ⁻¹' {t}, g x ∂ν = ∫ x in {x | x ∈ M ∧ f x = t ∧ x ∈ S}, F x ∂ν := by
  intro P μ ν M S f g F hM hS hf hNT hg0 hgF
  obtain ⟨M₁, hM₁M, hM₁m, hM₁ae⟩ := hM.exists_measurable_subset_ae_eq
  have hZ₁ : μ ({x | ¬(x ∈ S → g x = F x)} ∩ M) = 0 :=
    le_antisymm ((Measure.le_restrict_apply M _).trans (ae_iff.1 hgF).le) (zero_le)
  have hZ₂ : μ (M \ M₁) = 0 := (ae_eq_set.1 hM₁ae).2
  have hZ : μ (({x | ¬(x ∈ S → g x = F x)} ∩ M) ∪ (M \ M₁)) = 0 := measure_union_null hZ₁ hZ₂
  filter_upwards [hNT _ (union_subset inter_subset_right sdiff_subset) hZ] with t ht
  have hft : MeasurableSet (f ⁻¹' {t}) := hf (measurableSet_singleton t)
  have hA : (M ∩ f ⁻¹' {t} : Set (Eucl P)) =ᵐ[ν] (M₁ ∩ f ⁻¹' {t} : Set (Eucl P)) := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ ht
      intro x hx
      exact ⟨Or.inr ⟨hx.1.1, fun h => hx.2 ⟨h, hx.1.2⟩⟩, hx.1.2⟩
    · rw [sdiff_eq_empty.2 (inter_subset_inter_left _ hM₁M), measure_empty]
  have hB : ({x | x ∈ M ∧ f x = t ∧ x ∈ S} : Set (Eucl P)) =ᵐ[ν] (M₁ ∩ f ⁻¹' {t} ∩ S : Set (Eucl P)) := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ ht
      rintro x ⟨⟨hxM, hxt, hxS⟩, hx⟩
      refine ⟨Or.inr ⟨hxM, fun h => hx ⟨⟨h, hxt⟩, hxS⟩⟩, hxt⟩
    · have : (M₁ ∩ f ⁻¹' {t} ∩ S : Set (Eucl P)) \ {x | x ∈ M ∧ f x = t ∧ x ∈ S} = ∅ := by
        ext x
        simp only [Set.mem_sdiff, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq,
          mem_empty_iff_false, iff_false, not_and]
        intro h1 h2
        exact h2 (hM₁M h1.1.1) h1.1.2 h1.2
      rw [this, measure_empty]
  rw [Measure.restrict_congr_set hA, Measure.restrict_congr_set hB]
  have hgS : (fun x => g x) = S.indicator g := by
    funext x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hg0 x hx]
  rw [show (∫ x in M₁ ∩ f ⁻¹' {t}, g x ∂ν) = ∫ x in M₁ ∩ f ⁻¹' {t}, S.indicator g x ∂ν by
    rw [← hgS], setIntegral_indicator hS]
  apply setIntegral_congr_ae ((hM₁m.inter hft).inter hS)
  rw [ae_iff]
  refine measure_mono_null ?_ ht
  intro x hx
  simp only [mem_ofPred_eq, Classical.not_imp] at hx
  obtain ⟨⟨⟨hxM₁, hxt⟩, hxS⟩, hne⟩ := hx
  exact ⟨Or.inl ⟨fun h => hne (h hxS), hM₁M hxM₁⟩, hxt⟩
```

## Key steps

1. Z₁ = M ∩ S ∩ {g ≠ F} is μ-null (μ(D ∩ M) ≤ μ⌞M(D)); a Borel M₁ ⊆ M has μ(M ∖ M₁) = 0; NT for Z₁ ∪ (M ∖ M₁) gives a.e. good t
2. for good t the slice M ∩ f⁻¹{t} and the set {x ∈ M : f(x) = t, x ∈ S} are ν-a.e. equal to the Borel sets M₁ ∩ f⁻¹{t} and M₁ ∩ f⁻¹{t} ∩ S, so their restricted measures coincide
3. g = 1_S g turns the left side into ∫_{M₁∩f⁻¹{t}∩S} g dν; on this Borel set g = F off Z₁ ∩ f⁻¹{t}, a ν-null set, so the integrals agree

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
