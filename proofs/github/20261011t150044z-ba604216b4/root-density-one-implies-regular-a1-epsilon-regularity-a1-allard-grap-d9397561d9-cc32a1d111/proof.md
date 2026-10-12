# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1.graph_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Steps 5 and 6.
- End of Step 5: since C₈β ≤ ½, |Q(y₂ − y₁)| ≤ |P(y₂ − y₁)| and |Q(y₂ − y₁)| ≤ 2C₈βL|P(y₂ − y₁)|.
- Step 6: g₀(ι*(y − ξ)) := ι'*(y − ξ) on D, then McShane extension of each coordinate with the same constant, then truncation to [−C₆δ^ασ₀, C₆δ^ασ₀], giving |f| ≤ √k·(bound), Lip f ≤ 2√k·(cone constant) and G ⊆ F.
- Book: Simon Ch. 5, proof of Lemma 2.6, (4)–(7), and Ch. 2, Theorem 1.2. In the application, λ = C₈βL and A = C₆δ^ασ₀.
Notation: P := T₀.starProjection, Qu := u − Pu, Φ(v) := ξ + ιv + ι'f(v); write λ for lam.
1. Coordinates on G. For each y ∈ G choose (spanning hypothesis applied to y − ξ) v_y ∈ ℝⁿ and w_y ∈ ℝᵏ with y − ξ = ιv_y + ι'w_y. By the projection hypothesis P(y − ξ) = ιv_y, hence Q(y − ξ) = ι'w_y. Since ι' is an isometry, ‖w_y‖ = ‖Q(y − ξ)‖ ≤ A.
2. Two-point estimate. Let y₁, y₂ ∈ G, vᵢ := v_{yᵢ}, wᵢ := w_{yᵢ}.
   - By linearity, y₂ − y₁ = (y₂ − ξ) − (y₁ − ξ) = ι(v₂ − v₁) + ι'(w₂ − w₁).
   - By the projection hypothesis (with v := v₂ − v₁, w := w₂ − w₁), Q(y₂ − y₁) = ι'(w₂ − w₁), so ‖Q(y₂ − y₁)‖ = ‖w₂ − w₁‖.
   - By the triangle inequality, ‖y₂ − y₁‖ ≤ ‖ι(v₂ − v₁)‖ + ‖ι'(w₂ − w₁)‖ = ‖v₂ − v₁‖ + ‖w₂ − w₁‖.
   - The cone hypothesis now gives ‖w₂ − w₁‖ ≤ λ(‖v₂ − v₁‖ + ‖w₂ − w₁‖), i.e. (1 − λ)‖w₂ − w₁‖ ≤ λ‖v₂ − v₁‖.
   - Since 1 − λ ≥ 1/2 and the norms are nonnegative, ‖w₂ − w₁‖ ≤ 2λ‖v₂ − v₁‖. This is Simon's 'assuming Cβ ≤ ½ we thus have |Q(y₁) − Q(y₂)| ≤ 2CβL|P(y₁) − P(y₂)|'.
3. A function on D := {v_y : y ∈ G}.
   - By step 2, v_{y₁} = v_{y₂} forces w_{y₁} = w_{y₂}.
   - Define g : ℝⁿ → ℝᵏ by g(v) := w_{y(v)} for a chosen y(v) ∈ G with v_{y(v)} = v when v ∈ D, and g(v) := 0 otherwise.
   - By the first point, g(v_y) = w_y for every y ∈ G.
   - Hence ‖g(v) − g(v')‖ ≤ 2λ‖v − v'‖ for v, v' ∈ D (step 2), and ‖g(v)‖ ≤ A for v ∈ D (step 1).
4. McShane extension of each coordinate (Simon Ch. 2, Theorem 1.2; Mathlib LipschitzOnWith.extend_real). For j ∈ Fin k let gʲ(v) := g(v)_j. Since |a_j − b_j| ≤ ‖a − b‖ in ℝᵏ (PiLp.norm_apply_le), gʲ is 2λ-Lipschitz on D, with constant Real.toNNReal(2λ). Let hʲ : ℝⁿ → ℝ be 2λ-Lipschitz on all of ℝⁿ with hʲ = gʲ on D.
5. Truncation. This is Simon's f̃ʲ = max{min{fʲ, Cδ^{1/(2n+2)}}, −Cδ^{1/(2n+2)}}. Put fʲ := max(−A, min(A, hʲ)).
   - Since |max(−A, min(A, s)) − max(−A, min(A, s'))| ≤ |s − s'|, fʲ is 2λ-Lipschitz (LipschitzWith.const_min, LipschitzWith.max_const).
   - |fʲ| ≤ A, because A ≥ 0.
   - On D, |gʲ| ≤ ‖g‖ ≤ A, so the truncation leaves hʲ = gʲ unchanged there: fʲ = gʲ on D.
6. Assembly of f. Let f(v) ∈ ℝᵏ be the vector with coordinates fʲ(v) (WithLp.toLp 2 (fun j => fʲ v)).
   - By EuclideanSpace.norm_eq, ‖f(v) − f(w)‖² = Σ_j |fʲ(v) − fʲ(w)|² ≤ k·(2λ‖v − w‖)², hence ‖f(v) − f(w)‖ ≤ √k·2λ‖v − w‖ = 2√k·λ·‖v − w‖.
   - Likewise ‖f(v)‖² = Σ_j |fʲ(v)|² ≤ k·A², hence ‖f(v)‖ ≤ √k·A.
   - If k = 0, then ℝᵏ = {0} and both bounds read 0 ≤ 0.
7. G lies in the graph. For y ∈ G, f(v_y) = g(v_y) = w_y coordinatewise, by steps 3 and 5. Hence y = ξ + (ιv_y + ι'w_y) = ξ + ιv_y + ι'f(v_y) ∈ range Φ. ∎
Formal check. The following tactic proof of the exact frozen type compiles after import GMT.Ch07.Submission in the comparator scope, declared as Submission.dorag_lip_cone_set_graph_extension and needing no helper declarations. #print axioms gives propext, Classical.choice, Quot.sound; there are no warnings.
  intro n k T₀ ι ι' ξ G lam A hspan hproj hlam0 hlam1 hA hcone hbound
  classical
  -- Step 1: coordinates `y - ξ = ι (φ y) + ι' (ψ y)`.
  choose φ ψ hφψ using fun y : Euclid (n + k) => hspan (y - ξ)
  have hψA : ∀ y ∈ G, ‖ψ y‖ ≤ A := by
    intro y hy
    have h := hbound y hy
    rw [hφψ y, hproj, add_sub_cancel_left, LinearIsometry.norm_map] at h
    exact h
  -- Step 2: two-point estimate.
  have hdiff : ∀ y₁ y₂ : Euclid (n + k), y₂ - y₁ = ι (φ y₂ - φ y₁) + ι' (ψ y₂ - ψ y₁) := by
    intro y₁ y₂
    have e : y₂ - y₁ = (y₂ - ξ) - (y₁ - ξ) := by abel
    rw [e, hφψ y₁, hφψ y₂, map_sub, map_sub]
    abel
  have htwo : ∀ y₁ ∈ G, ∀ y₂ ∈ G, ‖ψ y₂ - ψ y₁‖ ≤ 2 * lam * ‖φ y₂ - φ y₁‖ := by
    intro y₁ hy₁ y₂ hy₂
    have h := hcone y₁ hy₁ y₂ hy₂
    rw [hdiff y₁ y₂, hproj, add_sub_cancel_left, LinearIsometry.norm_map] at h
    have h2 : ‖ι (φ y₂ - φ y₁) + ι' (ψ y₂ - ψ y₁)‖ ≤ ‖φ y₂ - φ y₁‖ + ‖ψ y₂ - ψ y₁‖ := by
      calc ‖ι (φ y₂ - φ y₁) + ι' (ψ y₂ - ψ y₁)‖
          ≤ ‖ι (φ y₂ - φ y₁)‖ + ‖ι' (ψ y₂ - ψ y₁)‖ := norm_add_le _ _
        _ = ‖φ y₂ - φ y₁‖ + ‖ψ y₂ - ψ y₁‖ := by
          rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
    have h3 := mul_le_mul_of_nonneg_left h2 hlam0
    have h4 := mul_nonneg (sub_nonneg.mpr hlam1) (norm_nonneg (ψ y₂ - ψ y₁))
    nlinarith [norm_nonneg (ψ y₂ - ψ y₁), norm_nonneg (φ y₂ - φ y₁)]
  -- Step 3: a function `g` on `D := φ '' G` with `g (φ y) = ψ y`.
  set D : Set (Euclid n) := φ '' G with hD
  let g : Euclid n → Euclid k := fun v => ψ (Function.invFunOn φ G v)
  have hg_eq : ∀ y ∈ G, g (φ y) = ψ y := by
    intro y hy
    obtain ⟨h1, h2⟩ := Function.invFunOn_pos (b := φ y) ⟨y, hy, rfl⟩
    have h := htwo y hy _ h1
    simp only [h2, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  have hgLip : ∀ v₁ ∈ D, ∀ v₂ ∈ D, ‖g v₁ - g v₂‖ ≤ 2 * lam * ‖v₁ - v₂‖ := by
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
    rw [hg_eq y₁ hy₁, hg_eq y₂ hy₂]
    exact htwo y₂ hy₂ y₁ hy₁
  -- Step 4: McShane extension of each coordinate.
  have hcoordLip : ∀ j : Fin k,
      LipschitzOnWith (Real.toNNReal (2 * lam)) (fun v => g v j) D := by
    intro j
    apply LipschitzOnWith.of_dist_le'
    intro v₁ hv₁ v₂ hv₂
    rw [Real.dist_eq, dist_eq_norm]
    calc |g v₁ j - g v₂ j| = ‖(g v₁ - g v₂) j‖ := by rw [PiLp.sub_apply, Real.norm_eq_abs]
      _ ≤ ‖g v₁ - g v₂‖ := PiLp.norm_apply_le _ j
      _ ≤ 2 * lam * ‖v₁ - v₂‖ := hgLip v₁ hv₁ v₂ hv₂
  choose h hhLip hhEq using fun j => (hcoordLip j).extend_real
  -- Step 5: truncation to `[-A, A]`.
  let F : Fin k → Euclid n → ℝ := fun j v => max (-A) (min A (h j v))
  have hFLip : ∀ j, LipschitzWith (Real.toNNReal (2 * lam)) (F j) :=
    fun j => ((hhLip j).const_min A).const_max (-A)
  have hFbound : ∀ j v, |F j v| ≤ A := by
    intro j v
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hFeq : ∀ y ∈ G, ∀ j, F j (φ y) = ψ y j := by
    intro y hy j
    have hmem : φ y ∈ D := ⟨y, hy, rfl⟩
    have e1 : h j (φ y) = g (φ y) j := (hhEq j hmem).symm
    rw [hg_eq y hy] at e1
    have hb : |ψ y j| ≤ A := by
      calc |ψ y j| = ‖ψ y j‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖ψ y‖ := PiLp.norm_apply_le _ j
        _ ≤ A := hψA y hy
    show max (-A) (min A (h j (φ y))) = ψ y j
    rw [e1, min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]
  -- Step 6: assembly.
  let f : Euclid n → Euclid k := fun v => WithLp.toLp 2 (fun j => F j v)
  have hf_apply : ∀ v j, f v j = F j v := fun v j => rfl
  have hK : ((Real.toNNReal (2 * lam) : NNReal) : ℝ) = 2 * lam :=
    Real.coe_toNNReal _ (by linarith)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro v w
    rw [EuclideanSpace.norm_eq (f v - f w)]
    have hterm : ∀ j, ‖(f v - f w) j‖ ^ 2 ≤ (2 * lam * ‖v - w‖) ^ 2 := by
      intro j
      have h1 := (hFLip j).dist_le_mul v w
      rw [hK, Real.dist_eq, dist_eq_norm] at h1
      rw [PiLp.sub_apply, hf_apply, hf_apply, Real.norm_eq_abs, sq_abs]
      exact sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
    calc √(∑ j, ‖(f v - f w) j‖ ^ 2) ≤ √(∑ _j : Fin k, (2 * lam * ‖v - w‖) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => hterm j)
      _ = √(k : ℝ) * (2 * lam * ‖v - w‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]
      _ = 2 * √(k : ℝ) * lam * ‖v - w‖ := by ring
  · intro v
    rw [EuclideanSpace.norm_eq (f v)]
    have hterm : ∀ j, ‖(f v) j‖ ^ 2 ≤ A ^ 2 := by
      intro j
      rw [hf_apply, Real.norm_eq_abs, sq_abs]
      have h1 := hFbound j v
      exact sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
    calc √(∑ j, ‖(f v) j‖ ^ 2) ≤ √(∑ _j : Fin k, A ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => hterm j)
      _ = √(k : ℝ) * A := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hA]
  · -- Step 7: `G` lies in the graph.
    intro y hy
    refine Set.mem_range.mpr ⟨φ y, ?_⟩
    have hfy : f (φ y) = ψ y := by
      apply PiLp.ext
      intro j
      rw [hf_apply]
      exact hFeq y hy j
    show ξ + ι (φ y) + ι' (f (φ y)) = y
    rw [hfy, add_assoc, ← hφψ y]
    abel

## Key steps

1. coordinates y − ξ = ιv_y + ι'w_y with Q(y − ξ) = ι'w_y, so ‖w_y‖ ≤ A
2. two-point estimate ‖w₂ − w₁‖ ≤ 2λ‖v₂ − v₁‖ from the cone condition and λ ≤ 1/2
3. well-defined g on D = {v_y} with g(v_y) = w_y, 2λ-Lipschitz on D and bounded by A
4. coordinatewise McShane extension with constant 2λ
5. truncation to [−A, A] keeps the Lipschitz constant and the values on D
6. assemble f: Lip ≤ 2√kλ, ‖f‖ ≤ √kA, f(v_y) = w_y so G ⊆ range Φ

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d; the workspace lake-manifest.json pins the same mathlib rev and simongmt 2b3663083f3fe399b6296fb8eaee52169170e197)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical)`
- `rg -n -i 'lipschitz.?approx|LipschitzApproximationLemma|LipschitzGraphCorollary|dorag_lip_' local-references/123e8435b4a2469b/project/GMT`
- `rg -c 'dorag_lip_' local-references/123e8435b4a2469b  (no match)`
- `rg -n "theorem exists_disjoint_subfamily_covering_enlargement_closedBall|theorem LipschitzOnWith.extend_real|lemma measure_compl_support|countable_of_nonempty_interior|lemma exp_le_two_add_div_two_sub|theorem withDensity_apply |theorem lintegral_add_left'|theorem lintegral_const_mul'|theorem setLIntegral_mono'|IsClosed.exists_infDist_eq_dist|lemma isClosed_support|theorem measure_toMeasurable|euclideanHausdorffMeasure_eq_volume|theorem addHaar_closedBall |norm_starProjection_apply_le|starProjection_orthogonal_val" local-references/123e8435b4a2469b/mathlib/Mathlib`
- `lean CheckNames.lean: #check of the 37 Mathlib/SimonGMT declarations cited by the children (all resolve, including Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn)`
- `python3: frozen lean_statement of the four sibling prerequisites (dorag_approxTangent_starProjection_aesm, dorag_monotonicity_density, dorag_standing_density_bounds, dorag_affine_approximation) and of dorag_lipschitz_approximation from dag.json, compared with the assembly's hypotheses and conclusion (all equal)`
- `python3 -I lean_contract.validate_lean_statement on the 8 lean_statements; scan of all 8 workspace dag.json files and GMT/ for dorag_lip_* and the dorag_lip_cone_estimate_aux_/dorag_lip_off_support_aux_ prefixes (no collision)`
- `lean ChallengeAll.lean (8 child types and the frozen parent type elaborate); lean FromFinal.lean (8 child proofs + LipApxAssembly + LipApxFromChildren regenerated from the submitted JSON, exit 0); lean perchild/Child_<key>.lean (each child with only its declared dependency); gmt-compare.py contract_scope emulation cmp/Sol_<key>.lean and cmp/Chal_<key>.lean (all exit 0)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-464a20467f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-464a20467f/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-464a20467f/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/lipapx-v2-work/FromFinal.lean`
- `/tmp/lipapx-v2-work/ChallengeAll.lean`
- `/tmp/lipapx-v2-work/CheckNames.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. The workspace builds against the same Mathlib revision. The snapshot's Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, which form the compiler context of every child.

Nothing in the snapshot proves the selected theorem or any child:
- GMT/Ch05 Contract/Submission (lines 272–309) define LipschitzApproximationLemma and LipschitzGraphCorollary only as Props for a different varifold type. They are used solely in the sorry-backed main_theorem (line 461).
- No dorag_lip_* name occurs in the snapshot.
So no comparator-approved declaration can be reused.

The tools the children cite exist at the pinned revision:
- Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall (MeasureTheory/Covering/Vitali.lean:158);
- Set.PairwiseDisjoint.countable_of_nonempty_interior (Topology/Bases.lean:493);
- LipschitzOnWith.extend_real (Topology/MetricSpace/Lipschitz.lean:308);
- IsClosed.exists_infDist_eq_dist (Topology/MetricSpace/HausdorffDistance.lean:615);
- Measure.isClosed_support and Measure.measure_compl_support (MeasureTheory/Measure/Support.lean:115, 202);
- withDensity_apply (WithDensity.lean:44);
- measure_toMeasurable (MeasureSpaceDef.lean:348);
- lintegral_add_left' and lintegral_const_mul' (Integral/Lebesgue/Add.lean:326, 420);
- setLIntegral_mono' (Integral/Lebesgue/Basic.lean:254);
- Real.exp_le_two_add_div_two_sub (Analysis/Complex/Exponential.lean:676);
- Submodule.starProjection_orthogonal_val and norm_starProjection_apply_le (InnerProductSpace/Projection/Basic.lean:203, 411);
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:187);
- Measure.addHaar_closedBall (Lebesgue/EqHaar.lean:500);
- SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn, which lies in the contract's import closure.

Lean checks:
- All 8 child types and the frozen parent type elaborate in comparator scope.
- All 8 children are fully proved, warning-free.
- The exact frozen parent type is derived from the 4 frozen sibling types plus the 8 children, using only propext, Classical.choice and Quot.sound.
- No name collides with any DAG reservation.
