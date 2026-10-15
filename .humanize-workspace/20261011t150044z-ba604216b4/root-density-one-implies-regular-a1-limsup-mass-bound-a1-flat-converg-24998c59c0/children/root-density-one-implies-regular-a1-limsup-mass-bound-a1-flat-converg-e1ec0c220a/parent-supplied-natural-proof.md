# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1.slice_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 3. The i-th term there is bounded by integrating |∂_i v| along the i-th coordinate segment, and then 'integrating over x, y ∈ Q (Fubini)'. This child is the Fubini identity for integrating along the k-th coordinate: the k-th coordinate of x is a dummy variable, and t takes its place. Notation: E := Euclid (m + 1), μ := volume on E, Q := Q_δ, I := (δ, 1 − δ), x[k ↦ t] := WithLp.toLp 2 (Function.update (WithLp.ofLp x) k t).

0. Degenerate case. If δ ≥ 1/2, no real number lies in I, so Q = ∅ and both sides are 0. Assume δ < 1/2. Then volume(I) = 1 − 2δ > 0 (Real.volume_Ioo).

1. The slice swap ρ. Define ρ : E × ℝ → E × ℝ by ρ(x, t) := (x[k ↦ t], x_k). Then ρ(ρ(x, t)) = (x[k ↦ t][k ↦ x_k], t) = (x, t). So ρ is its own inverse, a measurable equivalence and in particular a measurable embedding.

2. ρ preserves μ ⊗ L¹.
 – Via WithLp.ofLp/toLp (PiLp.volume_preserving_ofLp/toLp, MeasurePreserving.prod with the identity on ℝ), it suffices to show that ρ₀(x, t) := (Function.update x k t, x_k) preserves volume ⊗ volume on ℝ^{Fin (m+1)} × ℝ.
 – The splitting x ↦ (x_k, (x_{k.succAbove j})_{j ∈ Fin m}) is a measure-preserving equivalence ℝ^{Fin (m+1)} ≃ ℝ × ℝ^{Fin m} (MeasurableEquiv.piFinSuccAbove, volume_preserving_piFinSuccAbove). In these coordinates ρ₀ becomes ((a, b), c) ↦ ((c, b), a) on (ℝ × ℝ^{Fin m}) × ℝ.
 – This map is a composition of factor swaps and reassociations: ((a,b),c) ↦ ((b,a),c) ↦ (b,(a,c)) ↦ (b,(c,a)) ↦ ((b,c),a) ↦ ((c,b),a). Each step preserves the product Lebesgue measure (Measure.measurePreserving_swap, measurePreserving_prodAssoc and its inverse, MeasurePreserving.prod). Hence ρ₀, and so ρ, is measure preserving.

3. ρ⁻¹(Q × I) = Q × I. ρ exchanges the k-th coordinate of x with t, and both must lie in I for membership in Q × I. Hence ρ preserves (μ ⊗ L¹)⌞(Q × I) = (μ⌞Q) ⊗ (L¹⌞I) (MeasurePreserving.restrict_preimage_emb, Measure.prod_restrict).

4. Integrability. L¹⌞I is finite. So (x, t) ↦ h(x) is integrable for (μ⌞Q) ⊗ (L¹⌞I) (Integrable.comp_fst). By step 3, so is (x, t) ↦ h(ρ(x, t)₁) = h(x[k ↦ t]) (MeasurePreserving.integrable_comp_emb).

5. Computation.
 ∫_Q ∫_I h(x[k ↦ t]) dt dx
  = ∫_{Q×I} h(ρ(x, t)₁) (Fubini, integral_prod)
  = ∫_{Q×I} h(x) (MeasurePreserving.integral_comp, step 3)
  = ∫_Q volume(I).toReal·h(x) dx (Fubini, integral_const)
  = (1 − 2δ)·∫_Q h (ENNReal.toReal_ofReal, 1 − 2δ ≥ 0). ∎

Compiled Lean route (checked with `lake env lean` against `import GMT.Ch07.Submission` in the comparator scope; declaration `theorem Submission.dor_lmb_fcd_cp_slice_integral : <frozen type> := by` followed by the block below; axioms [propext, Classical.choice, Quot.sound]):
```lean
  intro m δ k h hh
  set Q : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} with hQ
  rcases le_or_gt (1 / 2) δ with hδ | hδ
  · -- empty cube
    have hQe : Q = ∅ := by
      ext y
      simp only [hQ, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall]
      exact ⟨0, fun h0 => by linarith [h0.1, h0.2]⟩
    simp [hQe]
  -- the slice swap on `(Fin (m+1) → ℝ) × ℝ`
  have hρ : MeasurePreserving (fun p : (Fin (m + 1) → ℝ) × ℝ => (Function.update p.1 k p.2, p.1 k))
      (volume.prod volume) (volume.prod volume) := by
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) k
    have he : MeasurePreserving e (volume : Measure (Fin (m + 1) → ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) k
    set T : (ℝ × (Fin m → ℝ)) × ℝ → (ℝ × (Fin m → ℝ)) × ℝ := fun q => ((q.2, q.1.2), q.1.1) with hTdef
    have hT : MeasurePreserving T (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume)
        (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume) := by
      have s1 : MeasurePreserving (Prod.map Prod.swap id : (ℝ × (Fin m → ℝ)) × ℝ → ((Fin m → ℝ) × ℝ) × ℝ)
          (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume)
          (((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).prod volume) :=
        Measure.measurePreserving_swap.prod (MeasurePreserving.id _)
      have s2 := measurePreserving_prodAssoc (volume : Measure (Fin m → ℝ)) (volume : Measure ℝ)
        (volume : Measure ℝ)
      have s3 : MeasurePreserving (Prod.map id Prod.swap : (Fin m → ℝ) × (ℝ × ℝ) → (Fin m → ℝ) × (ℝ × ℝ))
          ((volume : Measure (Fin m → ℝ)).prod ((volume : Measure ℝ).prod volume))
          ((volume : Measure (Fin m → ℝ)).prod ((volume : Measure ℝ).prod volume)) :=
        (MeasurePreserving.id _).prod Measure.measurePreserving_swap
      have s4 := (measurePreserving_prodAssoc (volume : Measure (Fin m → ℝ)) (volume : Measure ℝ)
        (volume : Measure ℝ)).symm
      have s5 : MeasurePreserving (Prod.map Prod.swap id : ((Fin m → ℝ) × ℝ) × ℝ → (ℝ × (Fin m → ℝ)) × ℝ)
          (((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).prod volume)
          (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume) :=
        Measure.measurePreserving_swap.prod (MeasurePreserving.id _)
      have := s5.comp (s4.comp (s3.comp (s2.comp s1)))
      convert this using 1
      funext q
      rfl
    have hE2 : MeasurePreserving (e.prodCongr (MeasurableEquiv.refl ℝ))
        ((volume : Measure (Fin (m + 1) → ℝ)).prod (volume : Measure ℝ))
        (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume) :=
      he.prod (MeasurePreserving.id _)
    have hfull := (hE2.symm.comp hT).comp hE2
    convert hfull using 1
    funext p
    ext j
    · simp only [Function.comp, e, T]
      simp [MeasurableEquiv.prodCongr, MeasurableEquiv.piFinSuccAbove_symm_apply,
        MeasurableEquiv.piFinSuccAbove_apply]
    · simp [e, T, MeasurableEquiv.prodCongr, MeasurableEquiv.piFinSuccAbove_symm_apply,
        MeasurableEquiv.piFinSuccAbove_apply]
  -- the same map on `Euclid (m+1) × ℝ`
  set ρ : Euclid (m + 1) × ℝ → Euclid (m + 1) × ℝ := fun p =>
    (WithLp.toLp 2 (Function.update (WithLp.ofLp p.1) k p.2), p.1 k) with hρdef
  have hρE : MeasurePreserving ρ (volume.prod volume) (volume.prod volume) := by
    have h1 := (PiLp.volume_preserving_ofLp (Fin (m + 1))).prod (MeasurePreserving.id (volume : Measure ℝ))
    have h2 := (PiLp.volume_preserving_toLp (Fin (m + 1))).prod (MeasurePreserving.id (volume : Measure ℝ))
    have := (h2.comp hρ).comp h1
    convert this using 1
    funext p
    rfl
  have hρρ : ∀ p, ρ (ρ p) = p := by
    intro p
    ext j
    · by_cases hj : j = k
      · subst hj; simp [hρdef]
      · simp [hρdef]
    · simp [hρdef]
  let ρe : (Euclid (m + 1) × ℝ) ≃ᵐ (Euclid (m + 1) × ℝ) :=
    { toFun := ρ
      invFun := ρ
      left_inv := hρρ
      right_inv := hρρ
      measurable_toFun := hρE.measurable
      measurable_invFun := hρE.measurable }
  have hemb : MeasurableEmbedding ρ := ρe.measurableEmbedding
  set I : Set ℝ := Ioo δ (1 - δ) with hI
  have hpre : ρ ⁻¹' (Q ×ˢ I) = Q ×ˢ I := by
    ext p
    simp only [mem_preimage, mem_prod, hQ, mem_ofPred_eq, hρdef, hI, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = k
        · subst hi; simpa using h2
        · simpa [hi] using h1 i
      · simpa using h1 k
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = k
        · subst hi; simpa using h2
        · simpa [hi] using h1 i
      · exact h1 k
  have hρQ : MeasurePreserving ρ ((volume.prod volume).restrict (Q ×ˢ I))
      ((volume.prod volume).restrict (Q ×ˢ I)) := by
    have := hρE.restrict_preimage_emb hemb (Q ×ˢ I)
    rwa [hpre] at this
  have hrestr : (volume.restrict Q).prod (volume.restrict I) =
      ((volume : Measure (Euclid (m + 1))).prod (volume : Measure ℝ)).restrict (Q ×ˢ I) :=
    Measure.prod_restrict Q I
  have hfinI : IsFiniteMeasure (volume.restrict I) := isFiniteMeasure_restrict.2 (by simp [hI])
  have hint1 : Integrable (fun p : Euclid (m + 1) × ℝ => h p.1)
      ((volume.restrict Q).prod (volume.restrict I)) := hh.comp_fst (volume.restrict I)
  have hint2 : Integrable (fun p => h (ρ p).1) ((volume.restrict Q).prod (volume.restrict I)) := by
    rw [hrestr] at hint1 ⊢
    exact (hρQ.integrable_comp_emb hemb).2 hint1
  have e1 : ∫ x in Q, ∫ t in I, h (WithLp.toLp 2 (Function.update (WithLp.ofLp x) k t)) =
      ∫ p, h (ρ p).1 ∂((volume.restrict Q).prod (volume.restrict I)) := by
    rw [integral_prod _ hint2]
  have e2 : ∫ p, h (ρ p).1 ∂((volume.restrict Q).prod (volume.restrict I)) =
      ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict I)) := by
    rw [hrestr]
    exact hρQ.integral_comp hemb (fun p => h p.1)
  have e3 : ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict I)) =
      (1 - 2 * δ) * ∫ x in Q, h x := by
    rw [integral_prod _ hint1]
    simp only [integral_const, Measure.real, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, hI, Real.volume_Ioo]
    rw [integral_const_mul, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [e1, e2, e3]
```

## Key steps

1. If δ ≥ 1/2 both sides vanish; otherwise volume(δ, 1 − δ) = 1 − 2δ.
2. ρ(x, t) := (x[k ↦ t], x_k) is a measurable involution; via ofLp and piFinSuccAbove it is ((a,b),c) ↦ ((c,b),a), a composition of swaps and reassociations, hence measure preserving.
3. ρ⁻¹(Q_δ × I) = Q_δ × I, so ρ preserves (vol⌞Q_δ) ⊗ (L¹⌞I) and h(x[k ↦ t]) is integrable there.
4. Fubini and measure preservation: ∫_{Q_δ}∫_I h(x[k ↦ t]) = ∫_{Q_δ×I} h(x) = (1 − 2δ)∫_{Q_δ} h.

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
