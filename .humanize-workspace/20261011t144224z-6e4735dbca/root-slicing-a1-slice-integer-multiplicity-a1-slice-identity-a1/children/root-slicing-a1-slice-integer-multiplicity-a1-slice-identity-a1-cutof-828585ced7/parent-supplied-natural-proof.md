# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.cutoff_gradient-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 7 (Simon Ch. 6, proof of Lemma 4.5(2): the piecewise-linear cut-off ψ applied to h = ψ∘f, the chain rule (4), and the remark that ∇^M f = 0 Hⁿ-a.e. on every level set {f = c}). It is stated here for an arbitrary measure μ and an arbitrary predicate Tan. In the parent, μ = H^{m+1}⌞M, Tan x Q = HasWeightedApproximateTangentSpaceAt (m+1) M θ x Q, and the two level-set hypotheses come from the sibling coarea_null (i) with c = t − ε and c = t.

Notation. For s ∈ ℝ put ψ(s) := max(0, min(1, (t − s)/ε)), so that h_ε = ψ∘f. Put E := f⁻¹((t − ε, t)) and G_ε := 1_E·(−ε⁻¹G), i.e. G_ε(x) = −ε⁻¹G(x) for x ∈ E and G_ε(x) = 0 for x ∉ E. In Lean, h_ε is `fun x => max 0 (min 1 ((t - f x) / ε))` and G_ε is `(f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y)`. (TG) denotes the tangential-gradient hypothesis: for μ-a.e. x and every subspace Q with Tan x Q, G(x) ∈ Q and s ↦ f(x + su) has derivative ⟨G(x), u⟩ at 0 for every u ∈ Q.

1. (Properties of ψ.) The map s ↦ (t − s)/ε is ε⁻¹-Lipschitz, and a ↦ min(1, a) and a ↦ max(0, a) are 1-Lipschitz. Hence |ψ(a) − ψ(b)| ≤ ε⁻¹|a − b| for all a, b. Moreover:
 - ψ(s) = 1 if s ≤ t − ε, because then (t − s)/ε ≥ 1;
 - ψ(s) = (t − s)/ε if t − ε ≤ s ≤ t, because then (t − s)/ε ∈ [0, 1];
 - ψ(s) = 0 if s ≥ t, because then (t − s)/ε ≤ 0.
2. (The constant.) Put K := ε⁻¹L ≥ 0. Since f is L-Lipschitz and ψ is ε⁻¹-Lipschitz, h_ε = ψ∘f is (ε⁻¹L)-Lipschitz, i.e. K-Lipschitz.
3. (G_ε is Borel and bounded by K.) f is Lipschitz, hence continuous, so E is open and therefore Borel. The map x ↦ −ε⁻¹G(x) is Borel because G is, so G_ε = 1_E·(−ε⁻¹G) is Borel. If x ∈ E then |G_ε(x)| = ε⁻¹|G(x)| ≤ ε⁻¹L = K. If x ∉ E then |G_ε(x)| = 0 ≤ K.
4. (Good points.) Each of (TG), "f(x) = t − ε ⟹ G(x) = 0" and "f(x) = t ⟹ G(x) = 0" holds for μ-a.e. x, so all three hold at μ-a.e. x. Fix such an x, a subspace Q with Tan x Q, and u ∈ Q. By (TG), G(x) ∈ Q and φ(s) := f(x + su) has φ'(0) = ⟨G(x), u⟩. In particular φ is continuous at 0, and φ(0) = f(x).
5. (G_ε(x) ∈ Q.) If x ∈ E then G_ε(x) = −ε⁻¹G(x) ∈ Q, because Q is a linear subspace containing G(x). If x ∉ E then G_ε(x) = 0 ∈ Q.
It remains to show that s ↦ h_ε(x + su) = ψ(φ(s)) has derivative ⟨G_ε(x), u⟩ at s = 0. We split according to the position of f(x) relative to t − ε and t.
6. (Case f(x) < t − ε.) Then x ∉ E, so ⟨G_ε(x), u⟩ = ⟨0, u⟩ = 0. Since φ is continuous at 0 and φ(0) < t − ε, there is a neighbourhood of 0 on which φ(s) < t − ε. There ψ(φ(s)) = 1 by step 1. A function that is constant near 0 has derivative 0 at 0.
7. (Case f(x) = t − ε.) Then x ∉ E, so ⟨G_ε(x), u⟩ = 0. By the choice of x, G(x) = 0, so φ'(0) = ⟨0, u⟩ = 0, i.e. φ(s) − φ(0) = o(s) as s → 0. By step 1, |ψ(φ(s)) − ψ(φ(0))| ≤ ε⁻¹|φ(s) − φ(0)| = o(s). Hence ψ∘φ has derivative 0 at 0.
8. (Case t − ε < f(x) < t.) Then x ∈ E and ⟨G_ε(x), u⟩ = ⟨−ε⁻¹G(x), u⟩ = −ε⁻¹⟨G(x), u⟩. By continuity of φ at 0 there is a neighbourhood of 0 on which t − ε < φ(s) < t, and there ψ(φ(s)) = (t − φ(s))/ε by step 1. The function s ↦ (t − φ(s))/ε has derivative −φ'(0)/ε = −ε⁻¹⟨G(x), u⟩ at 0. Since ψ∘φ agrees with it near 0, ψ∘φ has the same derivative at 0.
9. (Case f(x) = t.) As in step 7, now using "f(x) = t ⟹ G(x) = 0": x ∉ E, ⟨G_ε(x), u⟩ = 0, and ψ∘φ has derivative 0 at 0.
10. (Case f(x) > t.) Then x ∉ E and ⟨G_ε(x), u⟩ = 0. Near 0 we have φ(s) > t, so ψ(φ(s)) = 0 by step 1, and the derivative at 0 is 0.
11. (Conclusion.) Steps 6–10 cover every case: compare f(x) with t − ε, and if f(x) > t − ε, compare it with t. So for μ-a.e. x, every Q with Tan x Q and every u ∈ Q: G_ε(x) ∈ Q (step 5), and s ↦ h_ε(x + su) has derivative ⟨G_ε(x), u⟩ at 0. Together with steps 2 and 3, K = ε⁻¹L satisfies all four conclusions. ∎

Formalization notes (a complete Lean proof of exactly this statement was checked in a scratch build of the frozen commit d8d46c9: written as `theorem Submission.<lean_name>` inside `namespace GMT.Ch06` of a file importing GMT.Ch06.Submission, with the comparator-form restatement `theorem _root_.X : (<lean_statement>) := by exact Submission.<lean_name>` also checked; axioms propext, Classical.choice, Quot.sound; the verified proof is appended at the end):
- K := Kψ * L with Kψ : ℝ≥0 := ⟨ε⁻¹, inv_nonneg.2 hε.le⟩. Prove ψ Lipschitz by `LipschitzWith.of_dist_le_mul` for s ↦ (t − s)/ε, then `.const_min 1` and `.const_max 0`. Then `hψL.comp hf` gives the Lipschitz conclusion.
- Measurability: `(hG.const_smul (-ε⁻¹)).indicator (hf.continuous.measurable measurableSet_Ioo)`. Do not use `measurable_const.smul hG`: it produces a non-matching form.
- Neighbourhoods: `hd.continuousAt` with `ContinuousAt.eventually_lt` against `continuousAt_const (y := t - ε)` (resp. `y := t`), closed by `simpa`.
- Derivatives: use `HasDerivAt.congr_of_eventuallyEq` with `hasDerivAt_const`, or with `(hd.const_sub t).div_const ε` and `field_simp`. Also `real_inner_smul_left` and `inner_zero_left`.
- Edge cases: `hasDerivAt_iff_isLittleO`, `simp only [sub_zero, smul_zero]`, then `Asymptotics.IsBigO.trans_isLittleO` with `Asymptotics.IsBigO.of_bound (Kψ : ℝ)` and `hψL.dist_le_mul`. In the auxiliary statement write `fun s : ℝ => …` and `(0 : ℝ)`; otherwise ℕ is inferred.
- Case split: `lt_trichotomy (f x) (t - ε)`, then `lt_trichotomy (f x) t`.

Verified Lean proof (scratch build of d8d46c9; place it in GMT/Ch06/Submission.lean after the contract's closing `end` of the noncomputable section and before `theorem main_theorem`, inside `namespace GMT.Ch06`; it uses only the frozen imports):
```lean
theorem Submission.slicing_im_si_cutoff_tangential_gradient :
    ∀ (P : ℕ) (μ : Measure (Eucl P)) (Tan : Eucl P → Submodule ℝ (Eucl P) → Prop) (f : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P) (t ε : ℝ), 0 < ε → LipschitzWith L f → Measurable G → (∀ x, ‖G x‖ ≤ L) → (∀ᵐ x ∂μ, ∀ Q : Submodule ℝ (Eucl P), Tan x Q → G x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => f (x + s • u)) (inner ℝ (G x) u) 0) → (∀ᵐ x ∂μ, f x = t - ε → G x = 0) → (∀ᵐ x ∂μ, f x = t → G x = 0) → ∃ K : ℝ≥0, LipschitzWith K (fun x => max 0 (min 1 ((t - f x) / ε))) ∧ Measurable ((f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y)) ∧ (∀ x, ‖(f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y) x‖ ≤ K) ∧ ∀ᵐ x ∂μ, ∀ Q : Submodule ℝ (Eucl P), Tan x Q → (f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y) x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => max 0 (min 1 ((t - f (x + s • u)) / ε))) (inner ℝ ((f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y) x) u) 0 := by
  intro P μ Tan f L G t ε hε hf hG hGL hTG h1 h2
  set ψ : ℝ → ℝ := fun s => max 0 (min 1 ((t - s) / ε)) with hψdef
  set Kψ : ℝ≥0 := ⟨ε⁻¹, inv_nonneg.2 hε.le⟩ with hKψ
  have hψL : LipschitzWith Kψ ψ := by
    have hlin : LipschitzWith Kψ (fun s : ℝ => (t - s) / ε) := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      rw [Real.dist_eq, Real.dist_eq, show (t - a) / ε - (t - b) / ε = ε⁻¹ * (b - a) by ring,
        abs_mul, abs_of_pos (inv_pos.2 hε), abs_sub_comm]
      rfl
    exact (hlin.const_min 1).const_max 0
  have hfm : Measurable f := hf.continuous.measurable
  set E : Set (Eucl P) := f ⁻¹' Ioo (t - ε) t with hEdef
  have hE : MeasurableSet E := hfm measurableSet_Ioo
  refine ⟨Kψ * L, hψL.comp hf, (hG.const_smul (-ε⁻¹)).indicator hE, fun x => ?_, ?_⟩
  · by_cases hx : x ∈ E
    · rw [indicator_of_mem hx, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.2 hε)]
      simp only [hKψ]
      exact mul_le_mul_of_nonneg_left (hGL x) (inv_nonneg.2 hε.le)
    · rw [indicator_of_notMem hx, norm_zero]
      exact NNReal.coe_nonneg _
  · filter_upwards [hTG, h1, h2] with x hx hx1 hx2
    intro Q hQ
    obtain ⟨hGQ, hder⟩ := hx Q hQ
    constructor
    · by_cases hxE : x ∈ E
      · rw [indicator_of_mem hxE]; exact Q.smul_mem _ hGQ
      · rw [indicator_of_notMem hxE]; exact Q.zero_mem
    intro u hu
    have hd := hder u hu
    have hc : ContinuousAt (fun s : ℝ => f (x + s • u)) 0 := hd.continuousAt
    have hc0 : (fun s : ℝ => f (x + s • u)) 0 = f x := by simp
    -- the cut-off composed with the line
    change HasDerivAt (fun s => ψ (f (x + s • u))) _ 0
    -- at points where `G x = 0` the Lipschitz bound gives derivative `0`
    have edge : G x = 0 → HasDerivAt (fun s : ℝ => ψ (f (x + s • u))) 0 (0 : ℝ) := by
      intro hG0
      rw [hG0, inner_zero_left] at hd
      rw [hasDerivAt_iff_isLittleO] at hd ⊢
      simp only [sub_zero, smul_zero] at hd ⊢
      refine Asymptotics.IsBigO.trans_isLittleO ?_ hd
      refine Asymptotics.IsBigO.of_bound (Kψ : ℝ) (Eventually.of_forall fun s => ?_)
      have := hψL.dist_le_mul (f (x + s • u)) (f (x + (0 : ℝ) • u))
      simpa [Real.dist_eq, Real.norm_eq_abs] using this
    -- case analysis on the position of `f x`
    rcases lt_trichotomy (f x) (t - ε) with hlt | heq | hgt
    · -- below the band: locally constant `1`
      have hxE : x ∉ E := fun h => by simp [hEdef] at h; linarith [h.1]
      rw [indicator_of_notMem hxE, inner_zero_left]
      have hev : ∀ᶠ s in 𝓝 (0 : ℝ), f (x + s • u) < t - ε := by
        have := hc.eventually_lt (continuousAt_const (y := t - ε)) (by simpa using hlt)
        simpa using this
      apply (hasDerivAt_const (0 : ℝ) (1 : ℝ)).congr_of_eventuallyEq
      filter_upwards [hev] with s hs
      have : 1 ≤ (t - f (x + s • u)) / ε := by rw [le_div_iff₀ hε]; linarith
      simp only [hψdef, min_eq_left this, max_eq_right zero_le_one]
    · -- lower edge: `G x = 0`
      have hxE : x ∉ E := fun h => by simp [hEdef] at h; linarith [h.1]
      rw [indicator_of_notMem hxE, inner_zero_left]
      exact edge (hx1 heq)
    · rcases lt_trichotomy (f x) t with hlt' | heq' | hgt'
      · -- inside the band: affine with slope `-1/ε`
        have hxE : x ∈ E := by simp [hEdef]; exact ⟨hgt, hlt'⟩
        rw [indicator_of_mem hxE, real_inner_smul_left]
        have hev1 : ∀ᶠ s in 𝓝 (0 : ℝ), t - ε < f (x + s • u) := by
          have := (continuousAt_const (y := t - ε)).eventually_lt hc (by simpa using hgt)
          simpa using this
        have hev2 : ∀ᶠ s in 𝓝 (0 : ℝ), f (x + s • u) < t := by
          have := hc.eventually_lt (continuousAt_const (y := t)) (by simpa using hlt')
          simpa using this
        have hlin : HasDerivAt (fun s : ℝ => (t - f (x + s • u)) / ε) (-ε⁻¹ * inner ℝ (G x) u) 0 := by
          have := (hd.const_sub t).div_const ε
          convert this using 1
          field_simp
        apply hlin.congr_of_eventuallyEq
        filter_upwards [hev1, hev2] with s hs1 hs2
        have ha : (t - f (x + s • u)) / ε ≤ 1 := by rw [div_le_iff₀ hε]; linarith
        have hb : 0 ≤ (t - f (x + s • u)) / ε := div_nonneg (by linarith) hε.le
        simp only [hψdef, min_eq_right ha, max_eq_right hb]
      · -- upper edge: `G x = 0`
        have hxE : x ∉ E := fun h => by simp [hEdef] at h; linarith [h.2]
        rw [indicator_of_notMem hxE, inner_zero_left]
        exact edge (hx2 heq')
      · -- above the band: locally constant `0`
        have hxE : x ∉ E := fun h => by simp [hEdef] at h; linarith [h.2]
        rw [indicator_of_notMem hxE, inner_zero_left]
        have hev : ∀ᶠ s in 𝓝 (0 : ℝ), t < f (x + s • u) := by
          have := (continuousAt_const (y := t)).eventually_lt hc (by simpa using hgt')
          simpa using this
        apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
        filter_upwards [hev] with s hs
        have : (t - f (x + s • u)) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
        simp only [hψdef, max_eq_left ((min_le_right _ _).trans this)]
```

## Key steps

1. ψ(s) = max(0, min(1, (t−s)/ε)) is ε⁻¹-Lipschitz and equals 1 on s ≤ t−ε, (t−s)/ε on [t−ε, t], 0 on s ≥ t; hence h_ε = ψ∘f is (ε⁻¹L)-Lipschitz
2. G_ε = 1_{f⁻¹(t−ε,t)}·(−ε⁻¹G) is Borel (open band, Borel G) with |G_ε| ≤ ε⁻¹L
3. at μ-a.e. x, (TG) and the two level-set vanishing hypotheses hold; G_ε(x) ∈ Q since Q is a subspace containing G(x)
4. off the closed band, ψ∘φ is locally constant (derivative 0 = ⟨G_ε(x), u⟩); inside the open band ψ∘φ = (t − φ)/ε near 0, derivative −ε⁻¹⟨G(x), u⟩ = ⟨G_ε(x), u⟩
5. at f(x) ∈ {t−ε, t}, G(x) = 0 gives φ(s) − φ(0) = o(s), and the ε⁻¹-Lipschitz bound gives ψ∘φ(s) − ψ∘φ(0) = o(s), derivative 0 = ⟨G_ε(x), u⟩

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
