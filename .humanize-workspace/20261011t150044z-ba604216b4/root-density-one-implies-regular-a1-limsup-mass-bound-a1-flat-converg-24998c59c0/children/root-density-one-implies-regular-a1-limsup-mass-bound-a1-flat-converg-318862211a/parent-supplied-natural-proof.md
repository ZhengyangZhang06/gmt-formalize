# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1.mixed_point_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 3: 'Integrating over x, y ∈ Q (Fubini) bounds the i-th term'. The integrand h(a_k(x, y)) does not involve the variables x_j (j < k) or y_j (j ≥ k). Integrating them out gives the factor volume(Q_δ). This is that Fubini step, made precise by a coordinate swap. Notation: E := Euclid (m + 1), n := m + 1, μ := volume on E, Q := Q_δ.

1. The swap σ. Define σ : E × E → E × E by σ(x, y) := (a_k(x, y), c_k(x, y)), where c_k(x, y) has j-th coordinate x_j for j < k and y_j for j ≥ k. Thus σ exchanges the j-th coordinates of x and y for every j < k and fixes all other coordinates. Clearly σ(σ(p)) = p for all p. So σ is a bijection that is its own inverse, and (being measurable, step 2) a measurable equivalence; in particular it is a measurable embedding.

2. σ preserves μ ⊗ μ.
 – The coordinate map WithLp.ofLp : E → ℝ^{Fin n} preserves volume (PiLp.volume_preserving_ofLp), and so does its inverse WithLp.toLp (PiLp.volume_preserving_toLp). Taking products (MeasurePreserving.prod), it suffices to show that τ(x, y) := ((j ↦ y_j if j < k else x_j), (j ↦ x_j if j < k else y_j)) preserves volume ⊗ volume on (ℝ^{Fin n})².
 – Identify (ℝ^{Fin n})² with (ℝ × ℝ)^{Fin n}: the identification (MeasurableEquiv.arrowProdEquivProdArrow) maps the product measure ∏_j (L¹ ⊗ L¹) to (∏_j L¹) ⊗ (∏_j L¹) (measurePreserving_arrowProdEquivProdArrow).
 – In these coordinates τ acts factorwise: by the swap (s, t) ↦ (t, s) on the j-th factor ℝ × ℝ when j < k, and by the identity when j ≥ k. Each factor map preserves L¹ ⊗ L¹ (Measure.measurePreserving_swap; MeasurePreserving.id). So the factorwise map preserves the product measure (measurePreserving_pi).
 – Composing these measure-preserving maps shows that τ, and hence σ, is measure preserving.

3. σ⁻¹(Q × Q) = Q × Q. Q is the product of the same interval (δ, 1 − δ) in every coordinate. σ only exchanges coordinates between the two factors, so σ(x, y) ∈ Q × Q iff every coordinate of x and of y lies in (δ, 1 − δ), i.e. iff (x, y) ∈ Q × Q. Consequently σ preserves the restricted measure (μ ⊗ μ)⌞(Q × Q) (MeasurePreserving.restrict_preimage_emb). This measure equals (μ⌞Q) ⊗ (μ⌞Q) (Measure.prod_restrict).

4. Integrability.
 – Q is bounded (|y_i| ≤ |δ| + |1 − δ| for every coordinate), so volume(Q) < ∞ and μ⌞Q is a finite measure.
 – Since h is integrable for μ⌞Q, the function (x, y) ↦ h(x) is integrable for (μ⌞Q) ⊗ (μ⌞Q) (Integrable.comp_fst).
 – Since σ preserves this measure and is a measurable embedding (MeasurePreserving.integrable_comp_emb), (x, y) ↦ h(σ(x, y)₁) = h(a_k(x, y)) is integrable as well.

5. Computation.
 ∫_Q ∫_Q h(a_k(x, y)) dy dx
  = ∫_{Q×Q} h(σ(x, y)₁) d((μ⌞Q) ⊗ (μ⌞Q)) (Fubini, integral_prod, step 4)
  = ∫_{Q×Q} h(x) d((μ⌞Q) ⊗ (μ⌞Q))(x, y) (measure preservation, MeasurePreserving.integral_comp, step 3)
  = ∫_Q (∫_Q 1 dy) h(x) dx (Fubini, integral_prod)
  = volume(Q)·∫_Q h.
 Here ∫_Q 1 dy = volume(Q).toReal, and the constant is pulled out of the integral (integral_const, integral_const_mul). If Q = ∅ (δ ≥ 1/2) the same computation gives 0 = 0. ∎

Compiled Lean route (checked with `lake env lean` against `import GMT.Ch07.Submission` in the comparator scope; declaration `theorem Submission.dor_lmb_fcd_cp_mixed_point_integral : <frozen type> := by` followed by the block below; axioms [propext, Classical.choice, Quot.sound]):
```lean
  intro m δ k h hh
  set Q : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} with hQ
  -- the coordinate swap on `(Fin (m+1) → ℝ)²`
  have hτ : MeasurePreserving (fun p : (Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ) =>
      ((fun j => if j < k then p.2 j else p.1 j), (fun j => if j < k then p.1 j else p.2 j)))
      (volume.prod volume) (volume.prod volume) := by
    set A := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin (m + 1))
    have hA : MeasurePreserving A (Measure.pi fun _ : Fin (m + 1) => (volume : Measure ℝ).prod volume)
        ((volume : Measure (Fin (m + 1) → ℝ)).prod volume) :=
      measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (m + 1)) (fun _ => volume) (fun _ => volume)
    let f : Fin (m + 1) → ℝ × ℝ → ℝ × ℝ := fun j => if j < k then Prod.swap else id
    have hf : ∀ j, MeasurePreserving (f j) ((volume : Measure ℝ).prod volume)
        ((volume : Measure ℝ).prod volume) := by
      intro j
      by_cases hj : j < k
      · simp only [f, hj, ite_true]
        exact Measure.measurePreserving_swap
      · simp only [f, hj, ite_false]
        exact MeasurePreserving.id _
    have hP := measurePreserving_pi (fun _ : Fin (m + 1) => (volume : Measure ℝ).prod volume)
      (fun _ : Fin (m + 1) => (volume : Measure ℝ).prod volume) hf
    have hcomp := (hA.comp hP).comp hA.symm
    convert hcomp using 1
    funext p
    ext j
    · by_cases hj : j < k <;>
        simp [A, f, hj, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
    · by_cases hj : j < k <;>
        simp [A, f, hj, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
  -- the same swap on `Euclid (m+1) × Euclid (m+1)`
  set σ : Euclid (m + 1) × Euclid (m + 1) → Euclid (m + 1) × Euclid (m + 1) := fun p =>
    (WithLp.toLp 2 (fun j => if j < k then p.2 j else p.1 j),
      WithLp.toLp 2 (fun j => if j < k then p.1 j else p.2 j)) with hσdef
  have hσ : MeasurePreserving σ (volume.prod volume) (volume.prod volume) := by
    have h1 := (PiLp.volume_preserving_ofLp (Fin (m + 1))).prod (PiLp.volume_preserving_ofLp (Fin (m + 1)))
    have h2 := (PiLp.volume_preserving_toLp (Fin (m + 1))).prod (PiLp.volume_preserving_toLp (Fin (m + 1)))
    have := (h2.comp hτ).comp h1
    convert this using 1
    funext p
    rfl
  have hσσ : ∀ p, σ (σ p) = p := by
    intro p
    ext j
    · by_cases hj : j < k <;> simp [hσdef, hj]
    · by_cases hj : j < k <;> simp [hσdef, hj]
  let σe : (Euclid (m + 1) × Euclid (m + 1)) ≃ᵐ (Euclid (m + 1) × Euclid (m + 1)) :=
    { toFun := σ
      invFun := σ
      left_inv := hσσ
      right_inv := hσσ
      measurable_toFun := hσ.measurable
      measurable_invFun := hσ.measurable }
  have hemb : MeasurableEmbedding σ := σe.measurableEmbedding
  have hpre : σ ⁻¹' (Q ×ˢ Q) = Q ×ˢ Q := by
    ext p
    simp only [mem_preimage, mem_prod, hQ, mem_ofPred_eq, hσdef]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i < k
        · simpa [hi] using h2 i
        · simpa [hi] using h1 i
      · by_cases hi : i < k
        · simpa [hi] using h1 i
        · simpa [hi] using h2 i
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i < k
        · simpa [hi] using h2 i
        · simpa [hi] using h1 i
      · by_cases hi : i < k
        · simpa [hi] using h1 i
        · simpa [hi] using h2 i
  have hQm : MeasurableSet Q := by
    have : Q = ⋂ i, ({y : Euclid (m + 1) | δ < y i} ∩ {y | y i < 1 - δ}) := by
      ext y; simp [hQ]
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (by fun_prop)).inter (measurableSet_lt (by fun_prop) measurable_const)
  have hσQ : MeasurePreserving σ ((volume.prod volume).restrict (Q ×ˢ Q))
      ((volume.prod volume).restrict (Q ×ˢ Q)) := by
    have := hσ.restrict_preimage_emb hemb (Q ×ˢ Q)
    rwa [hpre] at this
  have hrestr : (volume.restrict Q).prod (volume.restrict Q) =
      ((volume : Measure (Euclid (m + 1))).prod volume).restrict (Q ×ˢ Q) :=
    Measure.prod_restrict Q Q
  have hQfin : volume Q ≠ ∞ := by
    have hb : Bornology.IsBounded Q := by
      rw [Metric.isBounded_iff_subset_closedBall (0 : Euclid (m + 1))]
      refine ⟨Real.sqrt (((m : ℝ) + 1) * (|δ| + |1 - δ|) ^ 2), fun y hy => ?_⟩
      rw [mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (|δ| + |1 - δ|) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            have := hy i
            rw [Real.norm_eq_abs]
            have h1 : |y i| ≤ |δ| + |1 - δ| := by
              rw [abs_le]
              constructor <;> cases abs_cases δ <;> cases abs_cases (1 - δ) <;> linarith [this.1, this.2]
            exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = ((m : ℝ) + 1) * (|δ| + |1 - δ|) ^ 2 := by simp
    exact hb.measure_lt_top.ne
  have hfin : IsFiniteMeasure (volume.restrict Q) := isFiniteMeasure_restrict.2 hQfin
  -- integrability of `p ↦ h p.1` on `Q × Q`
  have hint1 : Integrable (fun p : Euclid (m + 1) × Euclid (m + 1) => h p.1)
      ((volume.restrict Q).prod (volume.restrict Q)) := hh.comp_fst (volume.restrict Q)
  have hint2 : Integrable (fun p => h (σ p).1) ((volume.restrict Q).prod (volume.restrict Q)) := by
    rw [hrestr] at hint1 ⊢
    exact (hσQ.integrable_comp_emb hemb).2 hint1
  -- compute
  have e1 : ∫ x in Q, ∫ y in Q, h (WithLp.toLp 2 (fun j => if j < k then y j else x j)) =
      ∫ p, h (σ p).1 ∂((volume.restrict Q).prod (volume.restrict Q)) := by
    rw [integral_prod _ hint2]
  have e2 : ∫ p, h (σ p).1 ∂((volume.restrict Q).prod (volume.restrict Q)) =
      ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict Q)) := by
    rw [hrestr]
    exact hσQ.integral_comp hemb (fun p => h p.1)
  have e3 : ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict Q)) =
      (volume Q).toReal * ∫ x in Q, h x := by
    rw [integral_prod _ hint1]
    simp only [integral_const, Measure.real, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
      univ_inter]
    rw [integral_const_mul]
  rw [e1, e2, e3]
```

## Key steps

1. σ(x, y) := (a_k(x, y), c_k(x, y)) swaps the coordinates j < k of x and y; it is a measurable involution.
2. σ preserves volume ⊗ volume: via WithLp.ofLp/toLp and arrowProdEquivProdArrow it is a factorwise product of swaps and identities (measurePreserving_pi).
3. σ⁻¹(Q_δ × Q_δ) = Q_δ × Q_δ, so σ preserves (vol⌞Q_δ) ⊗ (vol⌞Q_δ); (x, y) ↦ h(x) and hence h(a_k(x, y)) are integrable there.
4. Fubini and measure preservation: ∫∫ h(a_k) = ∫_{Q×Q} h(x) = volume(Q_δ)·∫_{Q_δ} h.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c); cmp snapshot project/GMT/Ch07/Contract.lean with workspace GMT/Ch07/Contract.lean and Submission.lean (identical)`
- `cat nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-24998c59c0/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `sed -n 470,670p book/chapter-02.txt (Simon 2.1-2.7: BV definition, Lemma 2.5 mollification, Lemma 2.7 Poincare and its printed proof)`
- `python3 -I scans of dag.json: nodes matching oincar|median|mollif|BV; the cube_bv_median branch (cmcdt_cbm_* all decomposing, so not reusable); accepted helpers and frozen types of codim1_rdo_dg_sp_mollifier_adjoint, rsd_mw_tfa_smooth_cutoff, dgcr_stc_exists_normalized_mollifier, codim1_rdo_dg_sp_sobolev_limit, cutoff lemmas; freshness of dor_lmb_fcd_cp_* names; node depths (selected node depth 5)`
- `grep runtime.py (_decompose max_depth, _existing_lean_name_problem, _accepted_checkpoint), leaf_verification.check_source_delta (single theorem insertion, no imports), parent_verification.check_parent_git_delta; verifier/gmt-compare.py contract_scope and child_modules (comparator scope)`
- `git show ae0277d4 / b04a0309 (accepted adjoint and cutoff declarations, byte-identical types), 4c5953a5 and bff81d31e (non-leaf parents adding Mathlib imports, incl. Mathlib.Analysis.Calculus.BumpFunction.Convolution), ebf61002 (children proof base: frozen imports only)`
- `rg in snapshot mathlib: ae_convolution_tendsto_right_of_locallyIntegrable (BumpFunction/Convolution.lean:103), normed_neg/integral_normed/support_normed_eq/contDiff_normed/hasCompactSupport_normed (BumpFunction/Normed.lean), measurePreserving_arrowProdEquivProdArrow (Constructions/Pi.lean:751), volume_preserving_piFinSuccAbove (:818), measurePreserving_pi (:907), PiLp.volume_preserving_ofLp/toLp (Haar/InnerProductSpace.lean:134,139), tendsto_measure_iUnion_atTop, tendsto_setIntegral_of_monotone, lintegral_liminf_le', exists_contDiff_support_eq_eq_one_iff`
- `rg -i 'poincar[eé] inequality|median|mollif|bounded variation' in snapshot project/GMT and .lake/packages/simongmt/Poincare (only the sorry-frozen Ch02/Ch04 contract docstrings, SimonGMT Chapter02/BV.lean basics and Chapter08 mollifier convergence outside the Ch07 import closure; no proved BV Poincare)`
- `lake env lean /tmp/cp-decomp/Avail{,2,3}.lean (#check membership of ~120 declarations in the GMT.Ch07.Submission import closure)`
- `lake env lean /tmp/cp-decomp/lean/Challenge_*.lean (13 exact comparator challenges), Assembly.lean (parent from sorried children, #print axioms), Iface.lean (interface proofs), LeafCheck.lean and proofs/{Mixed2,Slice2,Grad}.lean, Snippets.lean`
- `python3 -I /tmp/cp-decomp/num/check2.py (Monte Carlo sanity check of the coordinate-step and smooth Poincare constants)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Poincare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-24998c59c0/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-24998c59c0/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-cab3e79dc1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a9900b6593/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1-smooth-cutoff-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/parent_verification.py`
- `/tmp/cp-decomp/lean/Assembly.lean`
- `/tmp/cp-decomp/lean/Iface.lean`
- `/tmp/cp-decomp/lean/LeafCheck.lean`
- `/tmp/cp-decomp/proofs/Mixed2.lean`
- `/tmp/cp-decomp/proofs/Slice2.lean`
- `/tmp/cp-decomp/proofs/Grad.lean`

Snapshot (project b4d606db, Mathlib 25730c7c): Ch07 Contract.lean equals the workspace Contract.lean and Submission.lean. No proved BV Poincare inequality exists anywhere. The snapshot's Ch02 Lemma 2.7 and Ch04 5.6 are sorry-frozen contracts of other chapters. SimonGMT Chapter02/BV.lean has only variation basics. SimonGMT's mollifier a.e.-convergence (Chapter08) and Mathlib's ContDiffBump.normed and ae_convolution_tendsto_right_of_locallyIntegrable are outside the import closure of GMT.Ch07.Submission. The closure does contain convolution smoothness and support lemmas, Lebesgue differentiation, Fubini/Tonelli, piFinSuccAbove, arrowProdEquivProdArrow, measurePreserving_pi, PiLp.volume_preserving_ofLp/toLp, Fatou and the smooth Urysohn lemma. Reuse: rsd_mw_tfa_smooth_cutoff and codim1_rdo_dg_sp_mollifier_adjoint are accepted with byte-identical frozen types, so they are taken as children. The analogous cmcdt_cbm_* nodes are only decomposing, so fresh dor_lmb_fcd_cp_* names are used; all ten are unused in dag.json. Lean checks: all 12 child types and the parent type elaborate as exact comparator challenges. The parent's frozen type follows from the sorried children with the extra parent import Mathlib.Analysis.Calculus.BumpFunction.Convolution (precedent: accepted depth-5 parent codim1_rdo_dg_sobolev_perimeter). Interface proofs compile. The mixed-point and slice identities have complete leaf-form proofs using only propext, Classical.choice and Quot.sound.
