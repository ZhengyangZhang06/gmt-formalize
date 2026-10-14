# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1.piece_action-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2 and 3 of the parent's supplied proof, for one piece (G_i, A_i, w_i) with product piece (Ĝ_i, Â_i, ŵ_i). Uses the sibling theorems cyl_fubini (Submission.cmcdt_lpi_cyl_fubini), suspension_map (Submission.cmcdt_lpi_cyl_suspension_map) and pullback_integrable (Submission.cmcdt_lpi_cyl_pullback_integrable), whose exact statements are recalled where used.
Notation. ℝ^m := Euclid m = EuclideanSpace ℝ (Fin m) with Lebesgue measure volume. For z ∈ ℝ^{m+1}: z_0 := WithLp.ofLp z 0 and tail z := WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) ∈ ℝ^m. For t ∈ ℝ and x ∈ ℝ^m: ι(t, x) := WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) ∈ ℝ^{m+1}, so that ι(t, x)_0 = t, tail ι(t, x) = x and z = ι(z_0, tail z) (Fin.cons_zero, Fin.tail_cons, Fin.cons_self_tail, WithLp.ofLp_toLp, WithLp.toLp_ofLp). e₀ := EuclideanSpace.single 0 1 ∈ ℝ^{N+1}; ê_a := EuclideanSpace.single a 1 ∈ ℝ^{n+1}; e_b := EuclideanSpace.single b 1 ∈ ℝ^n; J x := ι(0, x) = WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x)) for x ∈ ℝ^N. DH(z) := fderiv ℝ H z, and DH(z)ê denotes the tuple a ↦ DH(z) ê_a. |α| := covectorEuclideanNorm α.

Proof. Fix the data as in the statement.
1. (Siblings.) cyl_fubini applied to n and the Borel set A gives: Â' := {z : z_0 ∈ (0, 1), tail z ∈ A} is Borel; for every Borel f ≥ 0, ∫⁻_{Â'} f = ∫⁻_{u∈A} ∫⁻_{t∈(0,1)} f(ι(t, u)) dt du (Tonelli form); and for every real f integrable on Â', ∫_{Â'} f = ∫_{u∈A} ∫_{t∈(0,1)} f(ι(t, u)) dt du (Fubini form). By hypothesis Â = Â'. suspension_map applied to G and Ĝ gives: (a) Ĝ is max(1, L)-Lipschitz because G is L-Lipschitz; (b) Ĝ(ι(t, u)) = ι(t, G u) for all t, u; (c) if G is differentiable at u then a ↦ DĜ(ι(t, u)) ê_a equals Fin.cons e₀ (b ↦ J(DG(u) e_b)) for every t. In particular Ĝ is max(1, L)-Lipschitz and Â is Borel.
2. (Measurability of ŵ.) tail is continuous (coordinates of z), hence measurable; so ŵ = w ∘ tail is measurable. Every function on ℤ is measurable, so z ↦ (ŵ(z) : ℝ) and z ↦ ‖(ŵ(z) : ℝ)‖ₑ are measurable.
3. (Integrability of ŵ on Â.) Apply the Tonelli form of step 1 to the measurable function z ↦ ‖ŵ(z)‖ₑ: ∫⁻_Â ‖ŵ‖ₑ = ∫⁻_{u∈A} ∫⁻_{t∈(0,1)} ‖ŵ(ι(t, u))‖ₑ dt du. Since tail ι(t, u) = u, ŵ(ι(t, u)) = w(u), so the inner integral equals ‖w(u)‖ₑ·λ¹((0, 1)) = ‖w(u)‖ₑ (setLIntegral_const, Real.volume_Ioo). Therefore ∫⁻_Â ‖ŵ‖ₑ = ∫⁻_A ‖w‖ₑ < ∞ because w is integrable on A. Together with step 2, ŵ (as a real function) is integrable on Â.
4. (Fubini for the action.) Fix a test form ω on ℝ^{N+1} of degree n+1 and an n-form η satisfying the slice formula. Put F(z) := ŵ(z)·ω(Ĝ z)(DĜ(z)ê). By pullback_integrable applied with Q := N+1, degree n+1, H := Ĝ (max(1, L)-Lipschitz by step 1), S := Â and g := ŵ (integrable on Â by step 3), F is integrable on Â. Hence the Fubini form of step 1 applies: ∫_Â F = ∫_{u∈A} ∫_{t∈(0,1)} F(ι(t, u)) dt du.
5. (The inner integral.) Fix u ∈ A, so G is differentiable at u. For every t: ŵ(ι(t, u)) = w(u) (tail ι(t, u) = u); Ĝ(ι(t, u)) = ι(t, G u) by step 1(b); and a ↦ DĜ(ι(t, u)) ê_a = Fin.cons e₀ (b ↦ J(DG(u) e_b)) by step 1(c). Thus F(ι(t, u)) = w(u)·ω(ι(t, G u))(Fin.cons e₀ (b ↦ J(DG(u) e_b))) for all t, and ∫_{(0,1)} F(ι(t, u)) dt = w(u)·∫_{(0,1)} ω(ι(t, G u))(Fin.cons e₀ (b ↦ J(DG(u) e_b))) dt (integral_const_mul and setIntegral_congr_fun on the measurable set (0, 1)).
6. (Slice formula.) The hypothesis on η with x := G(u) and v := (DG(u) e_b)_b gives η(G u)(DG(u)e) = ∫_0^1 ω(ι(t, G u))(Fin.cons e₀ (b ↦ J(DG(u) e_b))) dt. Since 0 ≤ 1 the interval integral is the integral over (0, 1] (intervalIntegral.integral_of_le), which equals the integral over (0, 1) because singletons are Lebesgue null (integral_Ioc_eq_integral_Ioo). By step 5, ∫_{(0,1)} F(ι(t, u)) dt = w(u)·η(G u)(DG(u)e) for every u ∈ A.
7. (Conclusion.) Since A is measurable and the inner integrals agree with w(u)·η(G u)(DG(u)e) for every u ∈ A (setIntegral_congr_fun), step 4 gives ∫_Â ŵ(z)·ω(Ĝ z)(DĜ(z)ê) dz = ∫_A w(u)·η(G u)(DG(u)e) du, which is the asserted identity. Steps 1–3 give the remaining four conclusions. ∎

Appendix (supplementary; the numbered argument above is complete without it). The following Lean proof of exactly this frozen statement was checked with `lake env lean` after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's opens and `noncomputable section`, with the declaration named Submission.X as in accepted nodes. Its axioms are propext, Classical.choice and Quot.sound only, and sibling theorems are referenced by their Submission. names.
Lean tactic block for `theorem Submission.cmcdt_lpi_cyl_piece_action`, whose type is exactly the frozen lean_statement of this child (it follows `:= by`):
  intro N n L G A w Gh Ah wh hGL hA hw hwi hGd hGh hAh hwh
  obtain ⟨hAhm, hTon, hFub⟩ := Submission.cmcdt_lpi_cyl_fubini n A hA
  obtain ⟨hLip, hval, hder⟩ := Submission.cmcdt_lpi_cyl_suspension_map N n G Gh hGh
  have htail : Continuous fun z : Euclid (n + 1) => (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) := by
    fun_prop
  have hwh' : wh = fun z => w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) := funext hwh
  have hwhm : Measurable wh := by
    rw [hwh']
    exact hw.comp htail.measurable
  have hwhi : IntegrableOn (fun z => (wh z : ℝ)) Ah := by
    have hm : Measurable fun z => ‖((wh z : ℤ) : ℝ)‖ₑ :=
      (measurable_from_top (f := fun k : ℤ => ‖(k : ℝ)‖ₑ)).comp hwhm
    refine ⟨((measurable_from_top (f := fun k : ℤ => (k : ℝ))).comp hwhm).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hAh, hTon _ hm]
    have : ∀ u : Euclid n, (∫⁻ t in Ioo (0 : ℝ) 1, ‖((wh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) : ℤ) : ℝ)‖ₑ) = ‖((w u : ℤ) : ℝ)‖ₑ := by
      intro u
      simp [hwh, setLIntegral_const, Real.volume_Ioo]
    simp_rw [this]
    exact hwi.2
  refine ⟨hLip L hGL, hAh ▸ hAhm, hwhm, hwhi, ?_⟩
  intro ω η hη
  have hint := Submission.cmcdt_lpi_cyl_pullback_integrable (N + 1) (n + 1) (max 1 L) Gh Ah (fun z => (wh z : ℝ)) ω (hLip L hGL) hwhi
  rw [hAh] at hint ⊢
  rw [hFub _ hint]
  apply setIntegral_congr_fun hA
  intro u hu
  simp only
  rw [hη (G u) (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)),
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t _
  simp only
  rw [hwh, hval, hder t u (hGd u hu)]
  simp

## Key steps

1. cyl_fubini gives that Â is Borel together with Tonelli/Fubini on (0,1) × A; suspension_map gives that Ĝ is max(1, L)-Lipschitz, Ĝ(ι(t,u)) = ι(t, Gu), and DĜ(ι(t,u))ê = Fin.cons e₀ (J ∘ DG(u)e).
2. ŵ = w ∘ tail is measurable, and Tonelli gives ∫⁻_Â |ŵ| = ∫⁻_A |w| < ∞, so ŵ is integrable on Â.
3. pullback_integrable makes ŵ·ω(Ĝ)(DĜê) integrable on Â, so Fubini reduces ∫_Â to ∫_A ∫_(0,1).
4. For u ∈ A the inner integrand is w(u)·ω(ι(t, Gu))(Fin.cons e₀ (J ∘ DG(u)e)).
5. The slice formula and ∫_0^1 = ∫_(0,1) identify the inner integral with w(u)·η(Gu)(DG(u)e).

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
