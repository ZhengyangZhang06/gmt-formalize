# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.pushforward-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.pushforward-a1.pointwise_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Interface (a dependency of the parent node, exact frozen type): Submission.cmcdt_lpo_smooth_homotopy_estimate applied to (VO), (REP), (LB); call it (E). Its content: take C^∞ maps F', G', and X with compact support, M(X) < ∞ and boundaryMassOn X univ < ∞. Assume ‖fderiv ℝ F' x‖ ≤ Λ_E and ‖fderiv ℝ G' x‖ ≤ Λ_E on spt X; dist(F' x, G' x) ≤ δ on spt X; |ω(y)| ≤ a and |dω(y)| ≤ b for all y; and ηF, ηG are test forms equal to F'^#ω and G'^#ω on open sets containing spt X. Then |X(ηG) − X(ηF)| ≤ δ·(Λ_E^k·M(X).toReal·b + Λ_E^(k−1)·(boundaryMassOn X univ).toReal·a), where k − 1 is truncated subtraction. Sibling children: Submission.cmcdt_lpo_pf_form_bounds (FB) and Submission.cmcdt_lpo_pf_approx_data (AD).
Fix N, N', k, Λ, F, X, ω as in the statement. For μ ∈ ℝ put C(μ) := μ^k·M(X).toReal·b + μ^(k−1)·(boundaryMassOn X univ).toReal·a, with a, b from step 1.
1. Bounds. FB, applied to N', k, ω, gives a, b ∈ ℝ with |ω(y)| ≤ a and |dω(y)| ≤ b for all y. Since covectorEuclideanNorm ≥ 0 (covectorEuclideanNorm_nonneg), evaluating at y = 0 gives a ≥ 0 and b ≥ 0. Hence C(μ) ≥ 0 whenever μ ≥ 0, as all factors are nonnegative.
2. Mollified data. AD, applied to Λ, F and the compact set K := spt X, gives C^∞ maps G_i with ‖fderiv ℝ G_i x‖ ≤ Λ for all i, x and dist(G_i x, F x) ≤ Λ/(i + 1). Taking k and ω in AD, it also gives test forms θ_i with open W_i ⊇ spt X on which θ_i = G_i^#ω; only this first agreement clause is used. Moreover Λ/(i + 1) → 0: 1/(i + 1) → 0 by tendsto_one_div_add_atTop_nhds_zero_nat, then multiply by the constant Λ.
3. Cauchy property. For n, m ∈ ℕ apply (E) with Λ_E := Λ, δ := Λ/(n + 1) + Λ/(m + 1), the a and b above, F' := G_n, G' := G_m, ηF := θ_n, ηG := θ_m. Its hypotheses hold:
- G_n and G_m are C^∞, and X is normal.
- ‖fderiv ℝ G_n x‖ ≤ Λ and ‖fderiv ℝ G_m x‖ ≤ Λ.
- dist(G_n x, G_m x) ≤ dist(G_n x, F x) + dist(F x, G_m x) ≤ Λ/(n + 1) + Λ/(m + 1) (dist_triangle, dist_comm).
- The bounds on ω and dω, and the agreement of θ_n and θ_m with the pull-backs near spt X.
Hence |X(θ_m) − X(θ_n)| ≤ (Λ/(n + 1) + Λ/(m + 1))·C(Λ). If n, m ≥ M₀, then Λ/(n + 1) and Λ/(m + 1) are both ≤ Λ/(M₀ + 1) (div_le_div_of_nonneg_left). So dist(X(θ_n), X(θ_m)) ≤ 2·(Λ/(M₀ + 1))·C(Λ), and this bound tends to 0 as M₀ → ∞. By cauchySeq_of_le_tendsto_0 the sequence X(θ_i) is Cauchy. ℝ is complete (cauchySeq_tendsto_of_complete), so it converges to some L ∈ ℝ. This L is the one claimed.
4. Independence of the approximants. Let Λ', (F_j), (η_j) satisfy the hypotheses. Put Λ'' := max(Λ, Λ'), so Λ'' ≥ Λ ≥ 0 and C(Λ'') ≥ 0. Let ε > 0 and ε' := ε/(C(Λ'') + 1) > 0. By uniform convergence on spt X (Metric.tendstoUniformlyOn_iff) there is j₀ with dist(F x, F_j x) < ε' for all j ≥ j₀ and x ∈ spt X. Fix j ≥ j₀. For every i apply (E) with Λ_E := Λ'', δ := Λ/(i + 1) + ε', F' := G_i, G' := F_j, ηF := θ_i, ηG := η_j. Its hypotheses hold:
- On spt X, ‖fderiv ℝ G_i x‖ ≤ Λ ≤ Λ'' and ‖fderiv ℝ F_j x‖ ≤ Λ' ≤ Λ''.
- dist(G_i x, F_j x) ≤ dist(G_i x, F x) + dist(F x, F_j x) ≤ Λ/(i + 1) + ε'.
- θ_i and η_j agree with the pull-backs near spt X.
So |X(η_j) − X(θ_i)| ≤ (Λ/(i + 1) + ε')·C(Λ'') for all i. As i → ∞, the left side tends to |X(η_j) − L| and the right side to ε'·C(Λ''). Hence, by le_of_tendsto_of_tendsto', |X(η_j) − L| ≤ ε'·C(Λ'') = ε·C(Λ'')/(C(Λ'') + 1) < ε. This holds for all j ≥ j₀, so X(η_j) → L (Metric.tendsto_atTop, Real.dist_eq). □

Lean proof script. It compiled with lake env lean after import GMT.Ch07.Submission, inside namespace GMT.Ch07 with the contract's opens, against the exact frozen types of (E), FB and AD. It is the tactic body of theorem Submission.cmcdt_lpo_pf_pointwise_limit : <lean_statement> := by
  intro hVO hREP hLB N N' k Λ F X ω hF hX1 hX2 hX3
  have hE := Submission.cmcdt_lpo_smooth_homotopy_estimate hVO hREP hLB
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := Submission.cmcdt_lpo_pf_form_bounds N' k ω
  obtain ⟨G, hG, -, hDG, hdistG, -, hηG⟩ :=
    Submission.cmcdt_lpo_pf_approx_data N N' Λ F X.support hF hX1
  obtain ⟨θ, hθs⟩ := hηG k ω
  have hθ : ∀ i, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
      (θ i : DifferentialForm (Euclid N) k) x =
        ((ω : DifferentialForm (Euclid N') k) (G i x)).compContinuousLinearMap
          (fderiv ℝ (G i) x) := fun i => by
    obtain ⟨W, hW, hKW, h1, -⟩ := hθs i
    exact ⟨W, hW, hKW, h1⟩
  let Cf : ℝ → ℝ := fun μ =>
    μ ^ k * X.mass.toReal * b + μ ^ (k - 1) * (boundaryMassOn X univ).toReal * a
  have ha0 : 0 ≤ a := (covectorEuclideanNorm_nonneg _).trans (ha 0)
  have hb0 : 0 ≤ b := (covectorEuclideanNorm_nonneg _).trans (hb 0)
  have hC0 : ∀ μ : ℝ, 0 ≤ μ → 0 ≤ Cf μ := fun μ hμ => by
    simp only [Cf]
    positivity
  have hΛ0 : (0 : ℝ) ≤ Λ := Λ.2
  have hrate : Tendsto (fun i : ℕ => (Λ : ℝ) / ((i : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (Λ : ℝ)
    rw [mul_zero] at this
    exact this.congr (fun j => mul_one_div _ _)
  have hcauchy : CauchySeq (fun i => X (θ i)) := by
    refine cauchySeq_of_le_tendsto_0 (fun n : ℕ => 2 * ((Λ : ℝ) / ((n : ℝ) + 1)) * Cf Λ) ?_ ?_
    · intro n m M hn hm
      rw [Real.dist_eq, abs_sub_comm]
      have hest := hE N N' k Λ ((Λ : ℝ) / ((n : ℝ) + 1) + (Λ : ℝ) / ((m : ℝ) + 1)) a b (G n) (G m)
        X ω (θ n) (θ m) (hG n) (hG m) hX1 hX2 hX3 (fun x _ => ⟨hDG n x, hDG m x⟩)
        (fun x _ => (dist_triangle _ (F x) _).trans
          (add_le_add (hdistG n x) (by rw [dist_comm]; exact hdistG m x))) ha hb (hθ n) (hθ m)
      refine hest.trans (mul_le_mul_of_nonneg_right ?_ (hC0 _ hΛ0))
      have h1 : (Λ : ℝ) / ((n : ℝ) + 1) ≤ (Λ : ℝ) / ((M : ℝ) + 1) :=
        div_le_div_of_nonneg_left hΛ0 (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
      have h2 : (Λ : ℝ) / ((m : ℝ) + 1) ≤ (Λ : ℝ) / ((M : ℝ) + 1) :=
        div_le_div_of_nonneg_left hΛ0 (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)
      linarith
    · have := (hrate.const_mul 2).mul_const (Cf Λ)
      simpa using this
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨L, fun Λ' Fs ηs hFs hD hU hη => ?_⟩
  set Λ'' : ℝ := max (Λ : ℝ) Λ' with hΛ''def
  have hΛ'' : 0 ≤ Λ'' := le_trans hΛ0 (le_max_left _ _)
  have hC'' := hC0 Λ'' hΛ''
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' : ℝ := ε / (Cf Λ'' + 1) with hε'def
  have hε'pos : 0 < ε' := div_pos hε (by linarith)
  rw [Metric.tendstoUniformlyOn_iff] at hU
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (hU ε' hε'pos)
  refine ⟨j₀, fun j hj => ?_⟩
  have hbound : ∀ i : ℕ, |X (ηs j) - X (θ i)| ≤ ((Λ : ℝ) / ((i : ℝ) + 1) + ε') * Cf Λ'' := by
    intro i
    exact hE N N' k Λ'' _ a b (G i) (Fs j) X ω (θ i) (ηs j) (hG i) (hFs j) hX1 hX2 hX3
      (fun x hx => ⟨(hDG i x).trans (le_max_left _ _), (hD j x hx).trans (le_max_right _ _)⟩)
      (fun x hx => (dist_triangle _ (F x) _).trans (add_le_add (hdistG i x) (hj₀ j hj x hx).le))
      ha hb (hθ i) (hη j)
  have hlim : |X (ηs j) - L| ≤ ε' * Cf Λ'' := by
    have h1 : Tendsto (fun i => |X (ηs j) - X (θ i)|) atTop (𝓝 |X (ηs j) - L|) :=
      (tendsto_const_nhds.sub hL).abs
    have h2 : Tendsto (fun i : ℕ => ((Λ : ℝ) / ((i : ℝ) + 1) + ε') * Cf Λ'') atTop
        (𝓝 ((0 + ε') * Cf Λ'')) := (hrate.add_const ε').mul_const _
    rw [zero_add] at h2
    exact le_of_tendsto_of_tendsto' h1 h2 hbound
  rw [Real.dist_eq]
  calc |X (ηs j) - L| ≤ ε' * Cf Λ'' := hlim
    _ < ε := by
      rw [hε'def, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

## Key steps

1. FB gives bounds a, b ≥ 0 for |ω| and |dω|; AD gives the mollified maps G_i and the forms θ_i = G_i^#ω near spt X.
2. (E) with G_n and G_m shows that X(θ_i) is Cauchy; let L be its limit.
3. For arbitrary admissible data, (E) with G_i, F_j and Λ'' = max(Λ, Λ') gives |X(η_j) − X(θ_i)| ≤ (Λ/(i + 1) + ε')·C(Λ'') for all large j.
4. Letting i → ∞ gives |X(η_j) − L| ≤ ε'·C(Λ'') < ε, so X(η_j) → L.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Submission.lean (identical)`
- `rg -n cmcdt_lpo_pf local-references/123e8435b4a2469b/project local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n IsLipschitzPushforward local-references/123e8435b4a2469b/project -g '*.lean' (GMT/Ch06/Contract.lean:144, GMT/Ch06/Submission.lean:144)`
- `rg -n 'theorem (add_compContinuousLinearMap|smul_compContinuousLinearMap|compContinuousLinearMap_apply|zero_compContinuousLinearMap|compContinuousLinearMap_id)' mathlib/Mathlib -g '*.lean' (only ContinuousAlternatingMap.compContinuousLinearMap_apply, Topology/Algebra/Module/Alternating/Basic.lean:319)`
- `rg -n 'theorem norm_fderiv_le_of_lipschitz|theorem tendstoUniformly_iff|theorem tendstoUniformlyOn_iff|theorem TendstoUniformly.tendstoUniformlyOn' mathlib/Mathlib -g '*.lean'`
- `rg -n 'def apply|ContinuousEvalConst|continuous_eval_const' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean (instContinuousEvalConst at line 189)`
- `rg -n 'theorem continuous_if_const|theorem Continuous.if_const' mathlib/Mathlib -g '*.lean' (Topology/Piecewise.lean:116)`
- `rg -n infDist_pos mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean (IsClosed.notMem_iff_infDist_pos at line 584)`
- `rg -n 'theorem image_eq_zero_of|theorem image_eq_one_of' mathlib/Mathlib -g '*.lean' (Topology/Algebra/Support.lean:111, to_additive image_eq_zero_of_notMem_tsupport)`
- `rg -n 'theorem (IsClosed.notMem_iff_infDist_pos|infDist_le_dist_of_mem|closure_ball_subset_closedBall|ofReal_coe_nnreal|ofReal_pow|ofReal_toReal)' mathlib/Mathlib -g '*.lean'`
- `sed/grep of lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,Forms,FormSupNorm}.lean`
- `sed -n 475,530p book/chapter-06.txt (Simon 6.2.28-2.29)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json: lean_name prefix cmcdt_lpo_pf unused (rechecked before submission); selected node depth 5, max_depth 6; Lean names in the ancestors' depends_on collected so that each child cites only the interfaces it uses`
- `grep of /runtime/flows/gmt-claude-6c9908f72f7f/_recursive_lean/{inherited.py,runtime.py,prompts.py} (a child's parent-supplied-natural-proof.md is natural_proof + key steps + this ledger; ancestor-dependency names cited there become inherited prerequisites; depth >= max_depth disables further splitting)`
- `lake env lean /tmp/pf-decomp-x9/Check.lean (eleven child types elaborate; assembly_check proves the exact selected frozen type from them; #print axioms)`
- `lake env lean /tmp/pf-decomp-x9/P_<child>.lean for every child and lake env lean /tmp/pf-decomp-x9/AllAx.lean (all child proofs and the parent assembly compile with the parent-level sibling interfaces stated as axioms of their exact frozen types; per-declaration #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Piecewise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-f91696716e/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-6c9908f72f7f/_recursive_lean/inherited.py`
- `/runtime/flows/gmt-claude-6c9908f72f7f/_recursive_lean/runtime.py`
- `/tmp/pf-decomp-x9/Check.lean`
- `/tmp/pf-decomp-x9/AllAx.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) contains the same Ch07 contract as the workspace Submission.lean. Its only Lipschitz push-forward material is the unproved Ch06 specification IsLipschitzPushforward, which is stated over another Euclidean type and cannot be imported into Ch07, so no proof can be reused. No snapshot declaration and no DAG node uses the prefix cmcdt_lpo_pf, so the eleven proposed names are free. Every library fact the child proofs cite was found in the frozen import closure and confirmed by compilation. From Mathlib: norm_fderiv_le_of_lipschitz, tendsto_one_div_add_atTop_nhds_zero_nat, Metric.tendstoUniformly_iff and Metric.tendstoUniformlyOn_iff, TendstoUniformly.tendstoUniformlyOn, TendstoUniformlyOn.congr_right, Continuous.eval_const (instContinuousEvalConst), continuous_if_const, continuous_finsetSum, Continuous.bounded_above_of_compact_support, HasCompactSupport.comp_left, cauchySeq_of_le_tendsto_0, cauchySeq_tendsto_of_complete, IsClosed.notMem_iff_infDist_pos, infDist_le_dist_of_mem, image_eq_zero_of_notMem_tsupport, closure_ball_subset_closedBall, ContinuousAlternatingMap.compContinuousLinearMap_apply, fderiv_fun_id, ENNReal.ofReal_mul, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal and ENNReal.coe_pow. From SimonGMT Chapter06: GeometricCurrentOn.ext, boundary, zero_apply, le_massOn, isOpen_zeroRegion, exteriorDerivativeTestOn, exteriorDerivative_isTestForm, tsupport_exteriorDerivative_subset, exteriorDerivative_sq and covectorEuclideanNorm_zero/_neg/_nonneg. FormSupNorm.lean defines a sup norm but proves no boundedness, so form_bounds is a genuine obligation. All eleven child types elaborate, and the exact selected frozen type follows from them alone. Every child proof compiles against the exact frozen types of the parent-level sibling interfaces it cites. Simon 6.2.28-2.29 in book/chapter-06.txt matches the construction: the Lipschitz push-forward is the limit of mollified push-forwards, made Cauchy by the homotopy estimate, with spt contained in f(spt T) and the mass bound.
