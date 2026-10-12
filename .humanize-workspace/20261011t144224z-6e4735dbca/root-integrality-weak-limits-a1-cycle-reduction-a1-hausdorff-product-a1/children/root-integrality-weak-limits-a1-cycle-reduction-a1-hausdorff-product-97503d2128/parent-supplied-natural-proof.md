# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1.lift_gram_det-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and scope. This is Step 9(iv) of the parent proof of iwl_cr_hausdorff_product_formula (node root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1), stated with Gram determinants on the standard bases. It is the Jacobian computation for the product map (s, b) ↦ (s, G(b)) (block-diagonal Gram matrix diag(1, Gram(DG))). The Gram form uses only identifiers available under the frozen contract imports; the sibling lemma iwl_cr_hp_piece_product converts it to areaJacobianAt via LinearMap.normDet_sq_eq_det_gram. No DAG declaration is used. Write e_k := EuclideanSpace.equiv (Fin k) ℝ.

1. (Linear pieces.)
- Λ : ℝ × Eucl P → Eucl (P+1), Λ(s, x) := e_{P+1}⁻¹(Fin.cons s (e_P x)). It is ℝ-linear: check coordinatewise via Fin.cases, where coordinate 0 is s and coordinate j+1 is x_j. Being linear on a finite-dimensional space, it is continuous linear (LinearMap.toContinuousLinearMap).
- tl : Eucl (m+1) → Eucl m, tl(v) := e_m⁻¹(Fin.tail(e_{m+1} v)), so tl(v)_j = v_{j+1}. It is ℝ-linear, hence continuous linear.
- pr₀ := EuclideanSpace.proj 0 : Eucl (m+1) →L[ℝ] ℝ, so pr₀(v) = v_0.
- By the hypothesis on G̃ (funext), G̃ = (v ↦ Λ(pr₀ v, G(tl v))). By the hypothesis on b, tl(w) = b.

2. (Derivative.) Let L := fderiv ℝ G b.
- Since G is differentiable at b = tl(w), HasFDerivAt G L (tl w).
- tl is its own derivative, so the chain rule (HasFDerivAt.comp) shows that v ↦ G(tl v) has derivative L ∘L tl at w.
- pr₀ is its own derivative, so v ↦ (pr₀ v, G(tl v)) has derivative pr₀.prod (L ∘L tl) at w (HasFDerivAt.prodMk).
- Composing with the continuous linear map Λ gives HasFDerivAt G̃ (Λ ∘L pr₀.prod (L ∘L tl)) w.
- Hence fderiv ℝ G̃ w = L̃ := Λ ∘L (pr₀.prod (L ∘L tl)), i.e. L̃(v) = Λ(v_0, L(tl v)).

3. (Inner products.) For s, s′ ∈ ℝ and x, x′ ∈ Eucl P,
  ⟨Λ(s,x), Λ(s′,x′)⟩ = s·s′ + ⟨x, x′⟩.
Proof: write the EuclideanSpace inner product as a sum over Fin (P+1) (EuclideanSpace.inner_eq_star_dotProduct) and split off the 0-th term (Fin.sum_univ_succ).

4. (Basis vectors.) Let E_i := EuclideanSpace.single i 1 ∈ Eucl (m+1) and e′_j := EuclideanSpace.single j 1 ∈ Eucl m. Then:
- pr₀(E_0) = 1 and tl(E_0) = 0;
- for j : Fin m, pr₀(E_{j.succ}) = 0 because j.succ ≠ 0;
- for j : Fin m, tl(E_{j.succ}) = e′_j: coordinate k of tl(E_{j.succ}) is (E_{j.succ})_{k.succ}, which is 1 if k = j and 0 otherwise, since Fin.succ is injective.

5. (Gram matrix.) Let Γ̃_{ij} := ⟨L̃E_i, L̃E_j⟩ (i, j : Fin (m+1)) and Γ_{ij} := ⟨Le′_i, Le′_j⟩ (i, j : Fin m). By Steps 2–3,
  Γ̃_{ij} = pr₀(E_i)·pr₀(E_j) + ⟨L(tl E_i), L(tl E_j)⟩.
By Step 4 this gives:
- Γ̃_{00} = 1·1 + ⟨L0, L0⟩ = 1;
- Γ̃_{0, k.succ} = 1·0 + ⟨L0, Le′_k⟩ = 0;
- Γ̃_{i.succ, j.succ} = 0·0 + ⟨Le′_i, Le′_j⟩ = Γ_{ij}.

6. (Determinant.) Laplace expansion along row 0 (Matrix.det_succ_row_zero) gives
  det Γ̃ = Σ_{j : Fin (m+1)} (−1)^j·Γ̃_{0j}·det(Γ̃.submatrix Fin.succ j.succAbove).
- Split off j = 0 (Fin.sum_univ_succ). Every term with j = k.succ vanishes, because Γ̃_{0,k.succ} = 0.
- The j = 0 term is (−1)^0·1·det(Γ̃.submatrix Fin.succ (Fin.succAbove 0)) = det(Γ̃.submatrix Fin.succ Fin.succ), by Fin.succAbove_zero.
- By Step 5, Γ̃.submatrix Fin.succ Fin.succ = Γ entrywise. Hence det Γ̃ = det Γ.
- For m = 0 the same computation gives det Γ̃ = Γ̃_{00}·det(empty matrix) = 1 = det Γ.

This is exactly the claimed identity, since its left side is det Γ̃ and its right side is det Γ, with fderiv ℝ G̃ w = L̃ (Step 2). ∎

Appendix (Lean, verified). The declaration below proves exactly this frozen statement. It was compiled against the frozen project:
- environment: commit d8d46c9, Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b36630;
- placement: inside GMT/Ch06/Submission.lean, in `namespace GMT.Ch06` after the contract's `noncomputable section … end`, where accepted `theorem Submission.…` declarations go (the check used a scratch file that imports GMT.Ch06.Submission and replays the contract's namespace and `open` commands);
- `#print axioms` reports [propext, Classical.choice, Quot.sound].
Extra imports to add at the top of GMT/Ch06/Submission.lean: none beyond the frozen contract's imports. The proof uses no auxiliary top-level declarations.

theorem Submission.iwl_cr_hp_lift_gram_det : ∀ (P m : ℕ) (G : Eucl m → Eucl P) (Gt : Eucl (m + 1) → Eucl (P + 1)) (w : Eucl (m + 1)) (b : Eucl m), (∀ v : Eucl (m + 1), Gt v = (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons (EuclideanSpace.equiv (Fin (m + 1)) ℝ v 0) (EuclideanSpace.equiv (Fin P) ℝ (G ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ v))))))) → b = (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ w)) → DifferentiableAt ℝ G b → (Matrix.of fun i j : Fin (m + 1) => inner ℝ (fderiv ℝ Gt w (EuclideanSpace.single i 1)) (fderiv ℝ Gt w (EuclideanSpace.single j 1))).det = (Matrix.of fun i j : Fin m => inner ℝ (fderiv ℝ G b (EuclideanSpace.single i 1)) (fderiv ℝ G b (EuclideanSpace.single j 1))).det := by
  intro P m G Gt w b hGt hb hd
  -- the linear lift `Λ(s, x) = (s, x₁, …, x_P)` and the tail map, as continuous linear maps
  let Λ : (ℝ × Eucl P) →L[ℝ] Eucl (P + 1) := LinearMap.toContinuousLinearMap
    { toFun := fun q => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons q.1 (EuclideanSpace.equiv (Fin P) ℝ q.2))
      map_add' := by
        intro q q'
        ext k
        refine Fin.cases ?_ (fun j => ?_) k <;> simp
      map_smul' := by
        intro c q
        ext k
        refine Fin.cases ?_ (fun j => ?_) k <;> simp }
  have hΛ : ∀ (s : ℝ) (x : Eucl P), Λ (s, x) = (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x)) := fun s x => rfl
  have hinnerΛ : ∀ (s s' : ℝ) (x x' : Eucl P),
      inner ℝ (Λ (s, x)) (Λ (s', x')) = s * s' + inner ℝ x x' := by
    intro s s' x x'
    rw [hΛ, hΛ]
    simp only [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct, Fin.sum_univ_succ, mul_comm]
  let tl : Eucl (m + 1) →L[ℝ] Eucl m := LinearMap.toContinuousLinearMap
    { toFun := fun v => (EuclideanSpace.equiv (Fin m) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ v))
      map_add' := by intro v v'; ext k; simp [Fin.tail]
      map_smul' := by intro c v; ext k; simp [Fin.tail] }
  have htl : ∀ v : Eucl (m + 1), tl v = (EuclideanSpace.equiv (Fin m) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ v)) := fun v => rfl
  set L := fderiv ℝ G b with hLdef
  set pr0 : Eucl (m + 1) →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin (m + 1)) with hpr0
  have hGt' : Gt = fun v => Λ (pr0 v, G (tl v)) := by
    funext v; rw [hGt]; rfl
  have hb' : tl w = b := by rw [hb]; rfl
  -- the derivative of the lift
  have hinner : HasFDerivAt (fun v => (pr0 v, G (tl v))) (pr0.prod (L.comp tl)) w := by
    refine pr0.hasFDerivAt.prodMk ?_
    have hG : HasFDerivAt G L (tl w) := by rw [hb']; exact hd.hasFDerivAt
    exact hG.comp w tl.hasFDerivAt
  have hD : fderiv ℝ Gt w = Λ.comp (pr0.prod (L.comp tl)) := by
    rw [hGt']
    exact (Λ.hasFDerivAt.comp w hinner).fderiv
  rw [hD]
  -- values on the standard basis
  have hpr0_zero : pr0 (EuclideanSpace.single 0 1) = 1 := by simp [hpr0]
  have hpr0_succ : ∀ j : Fin m, pr0 (EuclideanSpace.single j.succ 1) = 0 := by
    intro j; simp [hpr0, Fin.succ_ne_zero]
  have htl_zero : tl (EuclideanSpace.single 0 1) = 0 := by
    ext k; simp [htl, Fin.tail, Fin.succ_ne_zero]
  have htl_succ : ∀ j : Fin m, tl (EuclideanSpace.single j.succ 1) = EuclideanSpace.single j 1 := by
    intro j; ext k
    rw [htl]
    by_cases hk : k = j
    · subst hk; simp [Fin.tail]
    · simp [Fin.tail, hk]
  have hentry : ∀ i j : Fin (m + 1),
      inner ℝ ((Λ.comp (pr0.prod (L.comp tl))) (EuclideanSpace.single i 1))
        ((Λ.comp (pr0.prod (L.comp tl))) (EuclideanSpace.single j 1)) =
      pr0 (EuclideanSpace.single i 1) * pr0 (EuclideanSpace.single j 1) +
        inner ℝ (L (tl (EuclideanSpace.single i 1))) (L (tl (EuclideanSpace.single j 1))) := by
    intro i j
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply]
    exact hinnerΛ _ _ _ _
  -- Laplace expansion along the first row of the block-diagonal Gram matrix
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hrest : ∀ k : Fin m, (-1 : ℝ) ^ (k.succ : ℕ) *
      (Matrix.of fun i j : Fin (m + 1) => inner ℝ ((Λ.comp (pr0.prod (L.comp tl)))
        (EuclideanSpace.single i 1)) ((Λ.comp (pr0.prod (L.comp tl))) (EuclideanSpace.single j 1)))
        0 k.succ *
      ((Matrix.of fun i j : Fin (m + 1) => inner ℝ ((Λ.comp (pr0.prod (L.comp tl)))
        (EuclideanSpace.single i 1)) ((Λ.comp (pr0.prod (L.comp tl))) (EuclideanSpace.single j 1)))
        |>.submatrix Fin.succ k.succ.succAbove).det = 0 := by
    intro k
    rw [Matrix.of_apply, hentry, hpr0_zero, hpr0_succ, htl_zero, map_zero, inner_zero_left]
    ring
  rw [Finset.sum_eq_zero (fun k _ => hrest k), add_zero]
  rw [Matrix.of_apply, hentry, hpr0_zero, htl_zero, map_zero, inner_zero_left, Fin.succAbove_zero]
  simp only [pow_zero, Fin.val_zero, mul_one, add_zero, one_mul]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.of_apply]
  rw [hentry, hpr0_succ, hpr0_succ, htl_succ, htl_succ]
  ring

## Key steps

1. Write G̃ = Λ ∘ (pr₀, G ∘ tl) with the continuous linear maps Λ(s,x) = (s,x), pr₀(v) = v_0 and tl(v) = (v_1, …, v_m).
2. Chain rule: fderiv G̃ w = Λ ∘L pr₀.prod (DG(b) ∘L tl).
3. ⟨Λ(s,x), Λ(s′,x′)⟩ = ss′ + ⟨x,x′⟩, and E_0 ↦ Λ(1,0), E_{j+1} ↦ Λ(0, DG(b)e′_j). So the Gram matrix is diag(1, Gram(DG(b))).
4. Laplace expansion along row 0 (Matrix.det_succ_row_zero, Fin.sum_univ_succ) gives det Gram(DG̃(w)) = det Gram(DG(b)).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json  (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `python3: read /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/{parent-child-handoff.json, parent-supplied-natural-proof.json, parent-supplied-natural-proof.md, parent-supplied-plan.md}`
- `python3: dag.json node statuses and lean_names (lpf_raf_*, lpf_countably_rectifiable_c1_cover, rectifiability_weighted_tangent_ae, iwl_cr_*); grep -r 'iwl_cr_hp_' over the run directory (no match)`
- `grep -n 'theorem hausdorffMeasure_apply|hausdorffMeasure_le_liminf_tsum|hausdorffMeasure_zero_singleton' Mathlib/MeasureTheory/Measure/Hausdorff.lean; grep 'euclideanHausdorffMeasure_def|euclideanHausdorffMeasure_zero|addHaarScalarFactor_volume_hausdorffMeasure_ne_zero' Mathlib/Geometry/Euclidean/Volume/Measure.lean (snapshot)`
- `sed -n 250,275p Mathlib/MeasureTheory/Function/Jacobian.lean (exists_partition_approximatesLinearOn_of_hasFDerivWithinAt); grep measurePreserving_piFinSuccAbove Mathlib/MeasureTheory/Constructions/Pi.lean; grep 'PiLp.volume_preserving_ofLp|PiLp.volume_preserving_toLp' Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean; grep det_succ_row_zero Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean; grep exists_measurable_subset_ae_eq Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `sed -n 290,320p Mathlib/Analysis/InnerProductSpace/NormDet.lean (LinearMap.normDet_sq_eq_det_gram, any Fintype index)`
- `grep -rn 'setLIntegral_comp_preimage|theorem prod_restrict|theorem lintegral_prod |Measurable.lintegral_prod_right'|MeasurePreserving.prod|LipschitzWith.prodMk' Mathlib/ (snapshot)`
- `grep -rn 'ediam_le|edist_le_ediam_of_mem|ediam_empty|ediam_le_of_forall_dist_le' Mathlib/Topology/EMetricSpace/Diam.lean Mathlib/Topology/MetricSpace/Bounded.lean (snapshot)`
- `simongmt: cat Chapter02/AreaLipschitz.lean; sed Chapter02/Area.lean, Chapter02/AreaParametrization.lean, Chapter02/AreaApproximation.lean; grep -rn 'theorem areaJacobianAt'; sed -n 28,80p Chapter03/Rectifiable.lean (CountablyRectifiable, CountablyRectifiable.mono)`
- `git show 2f36576:GMT/Ch06/Submission.lean (accepted rectifiability_weighted_tangent_ae, hparam/hpart piece construction); git show a46aa05:GMT/Ch06/Submission.lean and accepted candidate diffs (declaration conventions)`
- `verifier: gmt-compare.py contract_scope/child_modules and lean_contract.validate_lean_statement; python3 -I /tmp/hp_decomp/scripts/gen.py children_v1.json -> NodeChallenge files; lake env lean on each (all elaborate)`
- `lake env lean /tmp/hp_decomp/T0.lean (areaJacobianAt, weighted_area_formula_lipschitz_injOn and LinearMap.normDet_sq_eq_det_gram unknown under frozen imports; MeasurableSet.image_of_continuousOn_injOn, measurePreserving_piFinSuccAbove available)`
- `lake env lean /tmp/hp_decomp/scratch/{Assembly,JacBridge,LiftGram,PieceProduct,Pieces,Cyl}.lean and /tmp/hp_decomp/final/{All,Check_iwl_cr_hp_*}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/speculative-prompt-v3.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaParametrization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/hp_decomp/T0.lean`
- `/tmp/hp_decomp/scratch/Assembly.lean`
- `/tmp/hp_decomp/scratch/JacBridge.lean`
- `/tmp/hp_decomp/scratch/LiftGram.lean`
- `/tmp/hp_decomp/scratch/PieceProduct.lean`
- `/tmp/hp_decomp/scratch/Pieces.lean`
- `/tmp/hp_decomp/scratch/Cyl.lean`
- `/tmp/hp_decomp/final/All.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_cylinder_null.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_injective_pieces.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_lift_gram_det.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_piece_product.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c; the frozen contract is Contract.lean, and Submission.lean is identical to it at the dispatch base.

Library inputs found (all with standard axioms):
- Mathlib supplies:
  - Hausdorff measure: hausdorffMeasure_apply (ediam form), hausdorffMeasure_zero_singleton, euclideanHausdorffMeasure_def/_zero, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero;
  - pieces: exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (root namespace), MeasurableSet.image_of_continuousOn_injOn;
  - linear algebra: LinearMap.normDet_sq_eq_det_gram (any Fintype index, so EuclideanSpace.basisFun works), Matrix.det_succ_row_zero;
  - integration: measurePreserving_piFinSuccAbove, PiLp.volume_preserving_ofLp/toLp, MeasurePreserving.setLIntegral_comp_preimage, Measure.prod_restrict, lintegral_prod, Measurable.lintegral_prod_right', NullMeasurableSet.exists_measurable_subset_ae_eq;
  - diameters: Metric.ediam_le_of_forall_dist_le, edist_le_ediam_of_mem.
- SimonGMT 2b36630 supplies weighted_area_formula_lipschitz_injOn, area_image_compl_regularSet_eq_zero, measurableSet_areaRegularSet, measurable_areaJacobianAt, areaJacobianAt_eq_normDet/_nonneg, CountablyRectifiable (F_j : EuclideanSpace ℝ (Fin n) → E) and CountablyRectifiable.mono.
- Neither library has a Hausdorff product formula for rectifiable sets; only hausdorffMeasure_pi_real/prod_real exist.
- No DAG node supplies the needed lemmas with compatible types:
  - the lpf_raf_* area lemmas are chart/fibre-sum forms;
  - lpf_countably_rectifiable_c1_cover is only speculative-ready.
  So the split relies on library theorems only.

Scope check: areaJacobianAt, the SimonGMT area formula and LinearMap.normDet are NOT visible after `import GMT.Ch06.Submission` with the frozen imports. Hence lift_gram_det is stated with Gram determinants (Matrix.of … inner ℝ … EuclideanSpace.single). All four child statements elaborate in verifier-generated challenge modules.

Lean results:
- Scratch proofs of all four children with exactly the proposed types, and of the parent's exact frozen type from them, compile with only propext, Classical.choice and Quot.sound, and with zero warnings.
- Per-child compiles succeed with the minimal imports listed in each appendix.
- The accepted hparam/hpart code (commit 2f36576) was reused for injective_pieces.
- No name collisions with dag.json.
