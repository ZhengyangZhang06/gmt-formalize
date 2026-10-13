# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_gradient-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_gradient-a1.gram_field-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝᵏ := EuclideanSpace ℝ (Fin k) (Lean Eucl k): a finite-dimensional, hence complete and second countable, real inner product space with inner product ⟨·,·⟩, norm |·| and its Borel σ-algebra. L(E, F) := E →L[ℝ] F with the operator norm and its Borel σ-algebra (Mathlib's instance on continuous linear maps). Hypotheses: Ω ⊆ ℝⁿ open; Φ : ℝⁿ → ℝ^P of class C¹; DΦ(w) := fderiv ℝ Φ w injective for every w ∈ Ω; h : ℝⁿ → ℝ arbitrary. Notation for w ∈ ℝⁿ: A_w := fderiv ℝ Φ w ∈ L(ℝⁿ, ℝ^P); A_w* := ContinuousLinearMap.adjoint A_w ∈ L(ℝ^P, ℝⁿ), characterised by ⟨A_w* y, x⟩ = ⟨y, A_w x⟩ (Mathlib ContinuousLinearMap.adjoint_inner_left); the Gram operator G_w := A_w* ∘ A_w ∈ L(ℝⁿ, ℝⁿ); ℓ_w := fderiv ℝ h w ∈ L(ℝⁿ, ℝ) (Mathlib's Fréchet derivative, 0 where h is not differentiable); a_w := (InnerProductSpace.toDual ℝ ℝⁿ)⁻¹(ℓ_w) ∈ ℝⁿ, the Riesz vector of ℓ_w, so ⟨a_w, u⟩ = ℓ_w(u) for every u ∈ ℝⁿ (Mathlib InnerProductSpace.toDual_symm_apply). L(ℝⁿ, ℝⁿ) is a complete normed ring (product = composition, unit = identity), and R := Ring.inverse on it (R(T) = T⁻¹ if T is a unit, R(T) = 0 otherwise). This is Steps 4–5 of the parent proof (pointwise Gram representation of the chart derivative and Borel measurability of γ), with the antilipschitz lower bound replaced by its consequence that DΦ(w) is injective for w ∈ Ω.

1. (G_w is a unit for w ∈ Ω.) Let w ∈ Ω and u ∈ ℝⁿ with G_w u = 0. Then 0 = ⟨G_w u, u⟩ = ⟨A_w*(A_w u), u⟩ = ⟨A_w u, A_w u⟩ = |A_w u|², so A_w u = 0, and u = 0 because A_w is injective. Thus G_w is an injective linear endomorphism of the finite-dimensional space ℝⁿ, hence surjective (Mathlib LinearMap.injective_iff_surjective), hence bijective, hence a unit of the ring L(ℝⁿ, ℝⁿ) (Mathlib ContinuousLinearMap.isUnit_iff_bijective; ℝⁿ is complete). In particular R(G_w) is the two-sided inverse of G_w, so G_w(R(G_w)x) = x for every x ∈ ℝⁿ.

2. (Definition of γ.) For w ∈ ℝⁿ put B_w := A_w ∘ R(G_w) ∈ L(ℝⁿ, ℝ^P); put B̃_w := B_w if w ∈ Ω and B̃_w := 0 if w ∉ Ω; and define γ(w) := B̃_w(a_w) ∈ ℝ^P. Thus γ(w) = A_w(R(G_w)a_w) = A_w(A_w*A_w)⁻¹a_w for w ∈ Ω, and γ(w) = 0 for w ∉ Ω.

3. (Range.) Let w ∈ Ω. Then γ(w) = A_w(x_w) with x_w := R(G_w)a_w ∈ ℝⁿ, so γ(w) ∈ A_w(ℝⁿ) = LinearMap.range (fderiv ℝ Φ w).

4. (Representation identity.) Let w ∈ Ω, u ∈ ℝⁿ and x_w := R(G_w)a_w. Then
 ⟨γ(w), A_w u⟩ = ⟨A_w x_w, A_w u⟩ = ⟨A_w*(A_w x_w), u⟩ = ⟨G_w x_w, u⟩ = ⟨a_w, u⟩ = ℓ_w(u) = fderiv ℝ h w u,
 by the adjoint identity, the definition of G_w, step 1 (G_w x_w = a_w) and the Riesz property of a_w.

5. (w ↦ B_w is continuous on Ω.) Since Φ is C¹, w ↦ A_w = fderiv ℝ Φ w is continuous on ℝⁿ (Mathlib ContDiff.continuous_fderiv, with 1 ≠ 0). The adjoint map L(ℝⁿ, ℝ^P) → L(ℝ^P, ℝⁿ) is a (conjugate-)linear isometric equivalence, hence continuous, and composition (S, T) ↦ S ∘ T of continuous linear maps is jointly continuous (Mathlib Continuous.clm_comp); so w ↦ G_w = A_w* ∘ A_w is continuous on ℝⁿ. Now fix w ∈ Ω. By step 1, G_w is a unit, and Ring.inverse is continuous at every unit of a complete normed ring (Mathlib NormedRing.inverse_continuousAt); since w′ ↦ G_{w′} is continuous at w, the composite w′ ↦ R(G_{w′}) is continuous at w, and then w′ ↦ B_{w′} = A_{w′} ∘ R(G_{w′}) is continuous at w (Mathlib ContinuousAt.clm_comp). Hence B is continuous at every point of Ω, in particular continuous on Ω.

6. (w ↦ B̃_w is Borel.) Ω is open, hence Borel. B̃ is the piecewise map equal to B on Ω and to the constant 0 on ℝⁿ ∖ Ω; B is continuous on Ω (step 5) and the constant map is continuous on ℝⁿ ∖ Ω, so B̃ : ℝⁿ → L(ℝⁿ, ℝ^P) is Borel measurable (Mathlib ContinuousOn.measurable_piecewise).

7. (w ↦ a_w is Borel.) For every function h : ℝⁿ → ℝ the map w ↦ ℓ_w = fderiv ℝ h w is Borel measurable (Mathlib measurable_fderiv; ℝ is complete), and (InnerProductSpace.toDual ℝ ℝⁿ)⁻¹ : L(ℝⁿ, ℝ) → ℝⁿ is a (conjugate-)linear isometric equivalence, hence continuous, hence Borel. So w ↦ a_w is Borel measurable.

8. (γ is Borel.) The evaluation map ev : L(ℝⁿ, ℝ^P) × ℝⁿ → ℝ^P, (T, x) ↦ T x, is a bounded bilinear map, hence continuous (Mathlib isBoundedBilinearMap_apply), and ℝⁿ is second countable. By Mathlib Continuous.measurable2, w ↦ ev(B̃_w, a_w) = γ(w) is Borel measurable, because B̃ (step 6) and a (step 7) are.

9. (Conclusion.) γ : ℝⁿ → ℝ^P is Borel measurable (step 8), and for every w ∈ Ω, γ(w) ∈ LinearMap.range (fderiv ℝ Φ w) (step 3) and ⟨γ(w), fderiv ℝ Φ w u⟩ = fderiv ℝ h w u for every u ∈ ℝⁿ (step 4). ∎ (The degenerate cases n = 0 or P = 0 need no separate treatment: the argument above applies verbatim; for n = 0 every endomorphism of ℝ⁰ = {0} is the identity, hence a unit.)

Lean remark. The following tactic proof was verified in the exact comparator scope (import GMT.Ch06.Submission, then the prefix replayed by verifier gmt-compare.contract_scope: open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06 with the contract's three opens; noncomputable section followed by end) as `theorem Submission.slicing_im_tg_cg_gram_field : (<frozen statement>) := by`, with toolchain Lean v4.35.0-rc3 and Mathlib 25730c7c. Axioms: propext, Classical.choice, Quot.sound.
  intro P n Φ Ω h hΩ hΦ hinj
  classical
  set A : Eucl n → (Eucl n →L[ℝ] Eucl P) := fderiv ℝ Φ with hA
  have hAc : Continuous A := hΦ.continuous_fderiv one_ne_zero
  let G : Eucl n → (Eucl n →L[ℝ] Eucl n) := fun w => (ContinuousLinearMap.adjoint (A w)).comp (A w)
  have hGc : Continuous G := by
    have h1 : Continuous fun w => ContinuousLinearMap.adjoint (A w) :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Eucl n) (F := Eucl P)).continuous.comp hAc
    exact h1.clm_comp hAc
  have hGunit : ∀ w ∈ Ω, IsUnit (G w) := by
    intro w hw
    rw [ContinuousLinearMap.isUnit_iff_bijective]
    have hi : Function.Injective (G w) := by
      rw [injective_iff_map_eq_zero]
      intro u hu
      have h1 : inner ℝ (G w u) u = ‖A w u‖ ^ 2 := by
        simp only [G, ContinuousLinearMap.coe_comp, Function.comp_apply,
          ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
      rw [hu, inner_zero_left] at h1
      have h2 : A w u = 0 := by
        have h3 : ‖A w u‖ ^ 2 = 0 := h1.symm
        exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
      exact (injective_iff_map_eq_zero _).mp (hinj w hw) u h2
    refine ⟨hi, ?_⟩
    exact (LinearMap.injective_iff_surjective
      (f := ((G w : Eucl n →L[ℝ] Eucl n) : Eucl n →ₗ[ℝ] Eucl n))).mp hi
  let B : Eucl n → (Eucl n →L[ℝ] Eucl P) := fun w => (A w).comp (Ring.inverse (G w))
  have hBc : ContinuousOn B Ω := by
    intro w hw
    apply ContinuousAt.continuousWithinAt
    have h1 : ContinuousAt (fun w => Ring.inverse (G w)) w := by
      obtain ⟨U, hU⟩ := hGunit w hw
      have h2 := NormedRing.inverse_continuousAt U
      rw [hU] at h2
      exact h2.comp hGc.continuousAt
    exact hAc.continuousAt.clm_comp h1
  let a : Eucl n → Eucl n := fun w => (InnerProductSpace.toDual ℝ (Eucl n)).symm (fderiv ℝ h w)
  have ham : Measurable a :=
    (InnerProductSpace.toDual ℝ (Eucl n)).symm.continuous.measurable.comp (measurable_fderiv ℝ h)
  let Bt : Eucl n → (Eucl n →L[ℝ] Eucl P) := Ω.piecewise B 0
  have hBtm : Measurable Bt :=
    ContinuousOn.measurable_piecewise hBc continuousOn_const hΩ.measurableSet
  refine ⟨fun w => Bt w (a w), ?_, ?_⟩
  · exact isBoundedBilinearMap_apply.continuous.measurable2 hBtm ham
  · intro w hw
    have hBt : Bt w = B w := Set.piecewise_eq_of_mem _ _ _ hw
    simp only [hBt]
    refine ⟨LinearMap.mem_range.mpr ⟨Ring.inverse (G w) (a w), rfl⟩, ?_⟩
    intro u
    obtain ⟨U, hU⟩ := hGunit w hw
    have hGR : G w (Ring.inverse (G w) (a w)) = a w := by
      rw [← hU, Ring.inverse_unit]
      show ((U : Eucl n →L[ℝ] Eucl n) * ((U⁻¹ : (Eucl n →L[ℝ] Eucl n)ˣ) : Eucl n →L[ℝ] Eucl n)) (a w)
        = a w
      rw [Units.mul_inv]
      rfl
    calc inner ℝ (B w (a w)) (A w u)
        = inner ℝ ((ContinuousLinearMap.adjoint (A w)) (A w (Ring.inverse (G w) (a w)))) u := by
          rw [ContinuousLinearMap.adjoint_inner_left]; rfl
      _ = inner ℝ (G w (Ring.inverse (G w) (a w))) u := rfl
      _ = inner ℝ (a w) u := by rw [hGR]
      _ = fderiv ℝ h w u := InnerProductSpace.toDual_symm_apply

## Key steps

1. For w ∈ Ω the Gram operator G_w = DΦ(w)*DΦ(w) is injective since ⟨G_w u, u⟩ = |DΦ(w)u|², hence (finite dimension) a unit of L(ℝⁿ, ℝⁿ).
2. Define γ(w) := DΦ(w)G_w⁻¹a_w on Ω and 0 off Ω, where a_w is the Riesz vector of fderiv ℝ h w; then γ(w) ∈ range DΦ(w).
3. Adjoint identity: ⟨γ(w), DΦ(w)u⟩ = ⟨G_w G_w⁻¹a_w, u⟩ = ⟨a_w, u⟩ = fderiv ℝ h w u.
4. w ↦ DΦ(w)G_w⁻¹ is continuous on Ω (C¹, continuity of adjoint and composition, Ring.inverse continuous at units), so its extension by 0 off the open set Ω is Borel.
5. w ↦ a_w is Borel (measurable_fderiv and the Riesz isometry), and evaluation (T, x) ↦ Tx is continuous on second-countable spaces, so γ is Borel.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (all identical; git rev-parse HEAD = d8d46c9587747dee0751a1f780fcafdba16a3886)`
- `grep -rn 'slicing_im_tg_cg' local-references/197bdd4b88278494/project (no match)`
- `rg -n 'theorem measurable_fderiv\b|theorem measurable_fderiv_apply_const\b|theorem measurableSet_of_differentiableAt\b|theorem MeasurableSet.image_of_continuousOn_injOn|theorem ContinuousOn.measurableEmbedding|theorem MeasurableEmbedding.measurable_extend|theorem NormedRing.inverse_continuousAt|theorem ContinuousOn.measurable_piecewise|theorem LipschitzOnWith.ae_differentiableWithinAt_of_mem|le_of_lip|theorem HasDerivAt.le_of_lipschitz' local-references/197bdd4b88278494/mathlib/Mathlib`
- `sed -n 330,400p Mathlib/Analysis/Calculus/FDeriv/Measurable.lean; sed -n 815,880p Mathlib/MeasureTheory/Constructions/Polish/Basic.lean; sed -n 515,535p Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean; sed -n 420,460p and grep 'def HasLineDerivAt' Mathlib/Analysis/Calculus/LineDeriv/Basic.lean (snapshot mathlib)`
- `lake env lean /tmp/cg_split_q7/Avail.lean: #check NormedRing.inverse_continuousAt, Continuous.measurable2, MeasurableEmbedding.measurable_extend, Function.Injective.extend_apply, Function.extend_apply', LipschitzWith.locallyLipschitz, LocallyLipschitz.locallyLipschitzOn, ContinuousLinearEquiv.funUnique, EuclideanSpace.equiv, ContinuousLinearMap.adjoint, adjoint_inner_left/right, InnerProductSpace.toDual, toDual_symm_apply, ContDiff.continuous_fderiv, measurable_fderiv, ContinuousOn.measurable_piecewise, HasLineDerivAt.le_of_lipschitz, LipschitzOnWith.ae_differentiableWithinAt_of_mem, injective_iff_map_eq_zero, ContinuousLinearMap.isUnit_iff_bijective, LinearMap.injective_iff_surjective, isBoundedBilinearMap_apply, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, ContinuousLinearEquiv.comp_differentiableAt_iff (all present; Measurable.clm_apply and ContinuousLinearMap.continuous_comp absent)`
- `python3 scans of dag.json: the tangential_gradient subtree (statuses and types of chart_cover, chart_gradient, chart_tangent, line_deriv); the lpf twins tangential_differential_exists, chart_chain_rule and weighted_tangent_on_c1_chart; lean_statements containing InjOn, Function.extend, inner ℝ, MeasurableEmbedding, adjoint or Ring.inverse; multi-parent and cross-branch child edges (53 multi-parent, 102 cross-branch); exact-type duplicates of the four child types; occurrences of the new names`
- `read nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-70f87b0655/decomposition-v1.json plus its scope, audit and receipt files, and nodes/root-deformation-a1-skeleton-polyhedral-a1/decomposition-v2.json (reuse-child mechanism; rule that a solution PR proves only its tracked theorem)`
- `read the parent-child-handoff.json of nodes …-char-837491fcd9 (fderiv_lower_bound), …-tangential-differential-exists-a1-ch-34870e43f7 (chart_nondiff_image_null), …-tangential-gradient-a1-5d0f3ce1cd (line_deriv) and …-tangential-gradient-a1-661abdfbe7 (selected node)`
- `git show 8cfbc487a3d10545b0ea005ad58122242bbcc072 / 019ad40a7219b394f7e3a76a9361c778b6a98739 / 32fbf107157ca3b51c06f62670856410738101f5 -- GMT/Ch06/Submission.lean (accepted Lean proofs)`
- `python3: verifier/lean_contract.validate_lean_statement on the four child types; verifier/gmt-compare.contract_scope(Contract.lean, 'GMT.Ch06.main_theorem')`
- `lake env lean /tmp/cg_split_q7/Stmts.lean, Assembly.lean, Final.lean, FinalFull.lean`
- `grep -c slicing_im_tg_cg_gram_field|slicing_im_tg_cg_borel_transfer in dag.json, DAG.md, dag.mmd, issue-workers.json, problem.json, nodes/, GMT/, lake-packages-25730c7c/simongmt/Poincare; git for-each-ref (1882 refs, no chart_gradient refs)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-661abdfbe7/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-661abdfbe7/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-ch-34870e43f7/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-5d0f3ce1cd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-70f87b0655/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-skeleton-polyhedral-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/cg_split_q7/Stmts.lean`
- `/tmp/cg_split_q7/Avail.lean`
- `/tmp/cg_split_q7/Assembly.lean`
- `/tmp/cg_split_q7/Final.lean`
- `/tmp/cg_split_q7/FinalFull.lean`
- `/tmp/cg_split_q7/proposal.json`

Snapshot and scope:
- The snapshot (project d8d46c95, the workspace HEAD; Mathlib 25730c7c) holds the frozen Ch06 contract. It is byte-identical to the workspace Contract.lean and Submission.lean.
- The child comparator scope is import GMT.Ch06.Submission plus the replayed prefix: opens, namespace GMT.Ch06, its three opens, then noncomputable section … end.
- No `slicing_im_tg_cg*` declaration exists in the snapshot project, the GMT sources, SimonGMT, dag.json (508 nodes) or any git ref.

Mathlib supplies every tool used by the new children and the assembly:
- measurable_fderiv and measurableSet_of_differentiableAt (FDeriv/Measurable.lean);
- MeasurableSet.image_of_continuousOn_injOn and ContinuousOn.measurableEmbedding, the latter producing s.domRestrict f (Polish/Basic.lean);
- ContinuousOn.measurable_piecewise and Continuous.measurable2 (BorelSpace/Basic.lean);
- MeasurableEmbedding.measurable_extend;
- NormedRing.inverse_continuousAt, ContinuousLinearMap.adjoint with adjoint_inner_left, and InnerProductSpace.toDual_symm_apply;
- ContinuousLinearMap.isUnit_iff_bijective, LinearMap.injective_iff_surjective and isBoundedBilinearMap_apply;
- HasLineDerivAt.le_of_lipschitz (LineDeriv/Basic.lean), which reduces the parent's Step 8 to a single line;
- ContinuousLinearEquiv.comp_differentiableAt_iff and EuclideanSpace.euclideanHausdorffMeasure_eq_volume.

DAG and reuse:
- Steps 1 and 2–3 are already comparator-accepted as lpf_wtc_cat_fderiv_lower_bound (candidate 8cfbc487) and lpf_tde_chart_nondiff_image_null (candidate 019ad40a). Both are reused with byte-identical types; cross-branch reuse is established in this DAG (102 edges).
- No accepted or active node has the type of gram_field or borel_transfer. lpf_tde_mcd_single_chart differs: it gives an operator-valued field with no range condition.

Kernel checks:
- All four child types pass validate_lean_statement and elaborate in the exact scope.
- Both new children are fully proved with standard axioms.
- The frozen parent type is proved from the four children and line_deriv. With the accepted proofs substituted, every declaration depends only on propext, Classical.choice and Quot.sound.
- An independent reviewer reproduced these checks with its own assembly and returned ACCEPT.
