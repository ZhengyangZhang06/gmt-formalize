# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1.suspension_map-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2(a) (Lipschitz bound) and step 2(d) (derivative) of the parent's supplied proof, for a single map G.
Notation. ℝ^m := Euclid m = EuclideanSpace ℝ (Fin m) with Lebesgue measure volume. For z ∈ ℝ^{m+1}: z_0 := WithLp.ofLp z 0 and tail z := WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) ∈ ℝ^m. For t ∈ ℝ and x ∈ ℝ^m: ι(t, x) := WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) ∈ ℝ^{m+1}, so that ι(t, x)_0 = t, tail ι(t, x) = x and z = ι(z_0, tail z) (Fin.cons_zero, Fin.tail_cons, Fin.cons_self_tail, WithLp.ofLp_toLp, WithLp.toLp_ofLp). e₀ := EuclideanSpace.single 0 1 ∈ ℝ^{N+1}; ê_a := EuclideanSpace.single a 1 ∈ ℝ^{n+1}; e_b := EuclideanSpace.single b 1 ∈ ℝ^n; J x := ι(0, x) = WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x)) for x ∈ ℝ^N. DH(z) := fderiv ℝ H z, and DH(z)ê denotes the tuple a ↦ DH(z) ê_a. |α| := covectorEuclideanNorm α.

Proof. Fix N, n, G and Ĝ with Ĝ(z) = ι(z_0, G(tail z)) for all z.
1. (Linear pieces.) T : ℝ^{n+1} → ℝⁿ, T z := tail z, and Φ : ℝ × ℝ^N → ℝ^{N+1}, Φ(s, x) := ι(s, x), are ℝ-linear (check each coordinate; for Φ split the index by Fin.cases into 0 and succ j). On finite-dimensional spaces they are continuous linear maps (LinearMap.toContinuousLinearMap). The coordinate map π₀ : z ↦ z_0 is the continuous linear map EuclideanSpace.proj 0. Thus Ĝ(z) = Φ(π₀ z, G(T z)) for every z, i.e. Ĝ = Φ ∘ (π₀, G ∘ T).
2. (Norm identity.) For m ∈ ℕ, s ∈ ℝ, x ∈ ℝ^m: ‖ι(s, x)‖² = s² + ‖x‖² (EuclideanSpace.norm_sq_eq and Fin.sum_univ_succ). Every z ∈ ℝ^{n+1} equals ι(z_0, T z), so ‖z‖² = z_0² + ‖T z‖².
3. (Part (a).) Let G be L-Lipschitz and M := max(1, L), so 1 ≤ M and L ≤ M. Let x, y ∈ ℝ^{n+1}. Coordinatewise, Ĝ x − Ĝ y = ι(x_0 − y_0, G(T x) − G(T y)), hence ‖Ĝ x − Ĝ y‖² = (x_0 − y_0)² + ‖G(T x) − G(T y)‖² by step 2. Also x − y = ι(x_0 − y_0, T x − T y) (T is linear), so ‖x − y‖² = (x_0 − y_0)² + ‖T x − T y‖². Now (x_0 − y_0)² ≤ M²(x_0 − y_0)² because M² ≥ 1, and ‖G(T x) − G(T y)‖ ≤ L‖T x − T y‖ ≤ M‖T x − T y‖ gives ‖G(T x) − G(T y)‖² ≤ M²‖T x − T y‖². Adding, ‖Ĝ x − Ĝ y‖² ≤ M²‖x − y‖² = (M‖x − y‖)². Both sides being squares of nonnegative numbers, ‖Ĝ x − Ĝ y‖ ≤ M‖x − y‖, i.e. dist(Ĝ x, Ĝ y) ≤ M·dist(x, y). By LipschitzWith.of_dist_le_mul, Ĝ is M-Lipschitz.
4. (Part (b).) Ĝ(ι(t, u)) = ι(ι(t, u)_0, G(tail ι(t, u))) = ι(t, G(u)), since ι(t, u)_0 = t and tail ι(t, u) = u.
5. (Derivative.) Let G be differentiable at u and put z := ι(t, u), so T z = u. By the chain rule, HasFDerivAt (G ∘ T) (DG(u) ∘ T) z (G is differentiable at T z = u and T is continuous linear). Pairing with π₀ (HasFDerivAt.prodMk) and composing with the continuous linear map Φ gives HasFDerivAt Ĝ (Φ ∘ (π₀ × (DG(u) ∘ T))) z, where Ĝ is rewritten as z ↦ Φ(π₀ z, G(T z)) by step 1. Hence (HasFDerivAt.fderiv) DĜ(z) ζ = ι(ζ_0, DG(u)(T ζ)) for every ζ ∈ ℝ^{n+1}.
6. (Part (c).) Evaluate on the basis vectors, splitting a ∈ Fin (n+1) by Fin.cases. For a = 0: (ê_0)_0 = 1 and T ê_0 = 0 (every coordinate of the tail of ê_0 is [succ j = 0] = 0), so DĜ(z) ê_0 = ι(1, DG(u) 0) = ι(1, 0) = e₀, checking coordinates by Fin.cases. For a = succ b: (ê_{succ b})_0 = 0 and T ê_{succ b} = e_b (coordinate j of the tail is [succ j = succ b] = [j = b]), so DĜ(z) ê_{succ b} = ι(0, DG(u) e_b) = J(DG(u) e_b). Thus a ↦ DĜ(z) ê_a agrees with Fin.cons e₀ (b ↦ J(DG(u) e_b)) at a = 0 (Fin.cons_zero) and at every a = succ b (Fin.cons_succ), which is the asserted equality of tuples. ∎

Appendix (supplementary; the numbered argument above is complete without it). The following Lean proof of exactly this frozen statement was checked with `lake env lean` after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's opens and `noncomputable section`, with the declaration named Submission.X as in accepted nodes. Its axioms are propext, Classical.choice and Quot.sound only, and sibling theorems are referenced by their Submission. names.
Lean tactic block for `theorem Submission.cmcdt_lpi_cyl_suspension_map`, whose type is exactly the frozen lean_statement of this child (it follows `:= by`):
  intro N n G Gh hGh
  let T : Euclid (n + 1) →L[ℝ] Euclid n := LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))
      map_add' := fun x y => by ext i; simp [Fin.tail]
      map_smul' := fun c x => by ext i; simp [Fin.tail] }
  let Φ : ℝ × Euclid N →L[ℝ] Euclid (N + 1) := LinearMap.toContinuousLinearMap
    { toFun := fun p => WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2))
      map_add' := fun x y => by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
      map_smul' := fun c x => by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp }
  have hT : ∀ z, T z = WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) := fun z => rfl
  have hΦ : ∀ p, Φ p = WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) := fun p => rfl
  have hGh' : Gh = fun z => Φ (EuclideanSpace.proj (0 : Fin (n + 1)) z, G (T z)) := by
    funext z; rw [hGh]; rfl
  have hnorm : ∀ (m : ℕ) (t : ℝ) (x : Euclid m),
      ‖(WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (m + 1))‖ ^ 2 = t ^ 2 + ‖x‖ ^ 2 := by
    intro m t x
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
    simp
  have hsplit : ∀ z : Euclid (n + 1), z = WithLp.toLp 2 (Fin.cons (WithLp.ofLp z 0) (WithLp.ofLp (T z))) := by
    intro z; simp [hT]
  refine ⟨?_, ?_, ?_⟩
  · intro L hL
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    have hxy : ‖x - y‖ ^ 2 = (WithLp.ofLp x 0 - WithLp.ofLp y 0) ^ 2 + ‖T x - T y‖ ^ 2 := by
      rw [hsplit (x - y), hnorm]; simp [map_sub]
    have hG2 : ‖Gh x - Gh y‖ ^ 2 = (WithLp.ofLp x 0 - WithLp.ofLp y 0) ^ 2 + ‖G (T x) - G (T y)‖ ^ 2 := by
      rw [hGh x, hGh y, ← hT, ← hT]
      have : (WithLp.toLp 2 (Fin.cons (WithLp.ofLp x 0) (WithLp.ofLp (G (T x)))) : Euclid (N + 1)) -
          WithLp.toLp 2 (Fin.cons (WithLp.ofLp y 0) (WithLp.ofLp (G (T y)))) =
          WithLp.toLp 2 (Fin.cons (WithLp.ofLp x 0 - WithLp.ofLp y 0) (WithLp.ofLp (G (T x) - G (T y)))) := by
        ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
      rw [this, hnorm]
    have hGL : ‖G (T x) - G (T y)‖ ≤ L * ‖T x - T y‖ := by
      have := hL.dist_le_mul (T x) (T y); rwa [dist_eq_norm, dist_eq_norm] at this
    have h1 : (1 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by simp
    have h2 : (L : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by simp
    have hM0 : (0 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := NNReal.coe_nonneg _
    have hsq : ‖Gh x - Gh y‖ ^ 2 ≤ (((max 1 L : NNReal) : ℝ) * ‖x - y‖) ^ 2 := by
      rw [hG2, mul_pow, hxy]
      have hA : (WithLp.ofLp x 0 - WithLp.ofLp y 0) ^ 2 ≤ ((max 1 L : NNReal) : ℝ) ^ 2 * (WithLp.ofLp x 0 - WithLp.ofLp y 0) ^ 2 := by
        have : (1 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) ^ 2 := one_le_pow₀ h1
        nlinarith [sq_nonneg (WithLp.ofLp x 0 - WithLp.ofLp y 0)]
      have hB : ‖G (T x) - G (T y)‖ ^ 2 ≤ ((max 1 L : NNReal) : ℝ) ^ 2 * ‖T x - T y‖ ^ 2 := by
        have h0 : 0 ≤ ‖G (T x) - G (T y)‖ := norm_nonneg _
        have h3 : ‖G (T x) - G (T y)‖ ≤ ((max 1 L : NNReal) : ℝ) * ‖T x - T y‖ :=
          hGL.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
        calc ‖G (T x) - G (T y)‖ ^ 2 ≤ (((max 1 L : NNReal) : ℝ) * ‖T x - T y‖) ^ 2 :=
              pow_le_pow_left₀ h0 h3 2
          _ = _ := by ring
      nlinarith [hA, hB]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hM0 (norm_nonneg _)) two_ne_zero).1 hsq
  · intro t u
    rw [hGh]; simp
  · intro t u hG
    set z : Euclid (n + 1) := WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) with hz
    have hTz : T z = u := by simp [hT, z]
    have h1 : HasFDerivAt (fun z => G (T z)) ((fderiv ℝ G u).comp T) z := by
      have := hG.hasFDerivAt
      rw [← hTz] at this
      exact this.comp z T.hasFDerivAt
    have hd : HasFDerivAt Gh (Φ.comp ((EuclideanSpace.proj (0 : Fin (n + 1))).prod ((fderiv ℝ G u).comp T))) z := by
      rw [hGh']
      exact Φ.hasFDerivAt.comp z ((EuclideanSpace.proj (0 : Fin (n + 1))).hasFDerivAt.prodMk h1)
    rw [hd.fderiv]
    funext a
    refine Fin.cases ?_ (fun b => ?_) a
    · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, hΦ, hT, Fin.cons_zero]
      have h0 : (WithLp.toLp 2 (Fin.tail (WithLp.ofLp (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)))) : Euclid n) = 0 := by
        ext j; simp [Fin.tail, Pi.single_apply, Fin.succ_ne_zero]
      rw [h0, map_zero]
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp
    · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, hΦ, hT, Fin.cons_succ]
      have : (WithLp.toLp 2 (Fin.tail (WithLp.ofLp (EuclideanSpace.single b.succ (1 : ℝ)))) : Euclid n) = EuclideanSpace.single b 1 := by
        ext j; simp [Fin.tail, Pi.single_apply]
      rw [this]
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp

## Key steps

1. Write Ĝ = Φ ∘ (π₀, G ∘ T) with continuous linear T = tail, π₀ = z ↦ z_0 and Φ(s, x) = ι(s, x).
2. ‖ι(s, x)‖² = s² + ‖x‖², so ‖Ĝx − Ĝy‖² = (x_0−y_0)² + ‖G(Tx) − G(Ty)‖² and ‖x − y‖² = (x_0−y_0)² + ‖Tx − Ty‖²; with 1, L ≤ max(1, L) this gives the Lipschitz bound.
3. Ĝ(ι(t, u)) = ι(t, G u) because ι(t, u)_0 = t and tail ι(t, u) = u.
4. Chain rule: DĜ(ι(t, u)) ζ = ι(ζ_0, DG(u)(tail ζ)) when G is differentiable at u.
5. On ê_0 this gives ι(1, 0) = e₀, and on ê_{succ b} it gives ι(0, DG(u)e_b) = J(DG(u)e_b), i.e. the tuple Fin.cons e₀ (J ∘ DG(u)e).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/{Submission,Contract}.lean against workspace GMT/Ch07/{Submission,Contract}.lean (both identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD = 25730c7c759d108ef87ab70af2342a196760f79d (= manifest.json and lake-manifest.json)`
- `rg -n "cmcdt_lpi_cyl|piFinSuccAbove|curryLeft|Fin.tail|cylinder" local-references/123e8435b4a2469b/project -g '*.lean' (no match)`
- `rg -n "def piFinSuccAbove" local-references/123e8435b4a2469b/mathlib/Mathlib (MeasureTheory/MeasurableSpace/Embedding.lean:566)`
- `rg -n -e 'theorem volume_preserving_piFinSuccAbove' -e 'theorem setLIntegral_comp_preimage_emb' -e 'theorem setLIntegral_prod' -e 'theorem setIntegral_prod ' -e 'theorem measurable_fderiv_apply_const' -e 'theorem norm_fderiv_le_of_lipschitz' -e 'theorem curryLeft_apply_apply' -e 'theorem enorm_integral_le_lintegral_enorm' -e 'theorem integral_Ioc_eq_integral_Ioo' -e "theorem setLIntegral_mono'" -e 'theorem measurePreserving_swap' local-references/123e8435b4a2469b/mathlib/Mathlib/{MeasureTheory,Analysis,LinearAlgebra,Topology}`
- `lake env lean /tmp/cylim/Names.lean, Names2.lean, Names3.lean (#check on the pinned Mathlib: found volume_preserving_piFinSuccAbove, EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp, MeasurePreserving.setIntegral_preimage_emb, MeasurePreserving.integrableOn_comp_preimage, Integrable.mul_bdd, continuous_eval/Continuous.eval for Covector, Real.ofReal_le_enorm, Real.enorm_eq_ofReal_abs, Fin.insertNth_zero', ContinuousAlternatingMap.le_opNorm; absent: ContinuousAlternatingMap.continuous_eval, ofReal_integral_le_lintegral_ofReal, EuclideanSpace.volume_preserving_measurableEquiv)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json: frozen types of siblings cmcdt_lpi_piece_representation and cmcdt_lpi_lipschitz_piece_im; lean_name collisions for cmcdt_lpi_cyl_* (none); lean_statement patterns MeasurePreserving, piFinSuccAbove, Fin.cons t, Fin.tail, curryLeft (accepted codim1_rdo_dg_tma_orthogonal_fubini and cbr_cipi_halfspace_partial_integral have different types; dimred_mbl_dt_lp_im_cylinder, dor_lmb_fcdp_cylinder, dor_lmb_fcdp_product_imrep are unaccepted with different types; none reused)`
- `sed/grep of SimonGMT Chapter06 Forms.lean, Currents.lean, Mass.lean (Covector, DifferentialForm, IsTestForm, TestFormOn, GeometricCurrentOn, GeometricCurrentOn.ext, covectorEuclideanNorm, massAdmissibleOn, massOn, mass) and of the contract (Euclid, IMRep, IsIntegerMultiplicity)`
- `git show a936aa93:GMT/Ch07/Submission.lean | grep '^theorem' (accepted nodes are declared as theorem Submission.<name> inside namespace GMT.Ch07)`
- `lake env lean /tmp/cylim/Stmts.lean (6 child types elaborate); /tmp/cylim/Assembly.lean (parent from sorry'd children and siblings); /tmp/cylim/val/C1.lean, C2.lean, C56.lean, /tmp/cylim/C34.lean; /tmp/cylim/FullSub.lean (all six children proved at their frozen types with axioms propext, Classical.choice, Quot.sound; parent assembly compiles, sorryAx only through the two sibling prerequisites)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-6e44182ce4/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-6e44182ce4/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/tmp/cylim/Stmts.lean`
- `/tmp/cylim/Assembly.lean`
- `/tmp/cylim/FullSub.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same Ch07 contract as the workspace. It has no cylinder/suspension/Fubini lemma in the project and no cmcdt_lpi_cyl_* declaration (rg: no match); no accepted DAG theorem has a matching type, so nothing is reused and all six names are fresh and globally unused. Mathlib supplies every tool the children need: piFinSuccAbove with volume preservation, toLp/ofLp volume preservation, set-integral change of variables along a measurable embedding, set Fubini/Tonelli, measurability of fderiv, the Lipschitz bound on fderiv, curryLeft and compContinuousLinearMap evaluation, the alternating-map operator-norm bound, continuous_eval, and the enorm and Ioc/Ioo integral lemmas. ContinuousAlternatingMap.continuous_eval and ofReal_integral_le_lintegral_ofReal do not exist; the proofs use continuous_eval/Continuous.eval and Real.ofReal_le_enorm with enorm_integral_le_lintegral_enorm instead. All six child types elaborate after import GMT.Ch07.Submission. Each child was proved at its exact frozen type as theorem Submission.<name> inside namespace GMT.Ch07, with axioms propext, Classical.choice and Quot.sound only. The parent cmcdt_lpi_cylinder_im then compiles from the six children, Submission.cmcdt_lpi_piece_representation, Submission.cmcdt_lpi_lipschitz_piece_im and its antecedents; sorryAx enters only through those two not-yet-proved sibling prerequisites.
