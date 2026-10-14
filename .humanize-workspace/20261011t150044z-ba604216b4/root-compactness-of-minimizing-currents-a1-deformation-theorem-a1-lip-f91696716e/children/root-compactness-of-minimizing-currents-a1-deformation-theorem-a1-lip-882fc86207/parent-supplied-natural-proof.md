# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.pushforward-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.pushforward-a1.current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Interface (a dependency of the parent node, exact frozen type): Submission.cmcdt_lpo_current_toolkit applied to (VO), (REP). Two of its conjuncts are used:
- (MSB): if M(X) < ∞ and |ψ(x)| ≤ c for x ∈ spt X, then |X(ψ)| ≤ c·M(X).toReal.
- (BC): a linear T₀ with |T₀(ω)| ≤ C·c whenever |ω(y)| ≤ c for all y is represented by a current.
(L1) is the first conjunct of (LB). Sibling children: Submission.cmcdt_lpo_pf_pointwise_limit (PL, applied to (VO), (REP), (LB)) and Submission.cmcdt_lpo_pf_approx_data (AD).
Call (Λ', (F_j), (η_j)) admissible data for ω when every F_j is C^∞, ‖fderiv ℝ F_j x‖ ≤ Λ' on spt X, F_j → F uniformly on spt X, and every η_j equals F_j^#ω on an open set containing spt X. Fix N, N', k, Λ, F, X.
1. Limits. For each ω, PL gives L(ω) ∈ ℝ such that X(η_j) → L(ω) for all admissible data for ω. Choice defines the function L.
2. Common approximants. AD, applied to Λ, F and K := spt X, gives C^∞ maps G_j with ‖fderiv ℝ G_j x‖ ≤ Λ everywhere and G_j → F uniformly on ℝ^N, hence on spt X (TendstoUniformly.tendstoUniformlyOn). For every ω it also gives test forms θ_j^ω and open sets W_j^ω ⊇ spt X with θ_j^ω = G_j^#ω on W_j^ω; choose them as functions of ω. Thus (Λ, (G_j), (θ_j^ω)) is admissible for ω, and X(θ_j^ω) → L(ω).
3. Additivity. Let ω₁, ω₂ and j be given. On the open set W_j^{ω₁} ∩ W_j^{ω₂} ⊇ spt X, θ_j^{ω₁} + θ_j^{ω₂} equals G_j^#(ω₁ + ω₂). Indeed, sums of test forms are pointwise sums (Submodule.coe_add, Pi.add_apply), and (α + β).compContinuousLinearMap A = α.compContinuousLinearMap A + β.compContinuousLinearMap A (check on vectors: ext; simp). So (Λ, (G_j), (θ_j^{ω₁} + θ_j^{ω₂})) is admissible for ω₁ + ω₂, and X(θ_j^{ω₁} + θ_j^{ω₂}) → L(ω₁ + ω₂). But X(θ_j^{ω₁} + θ_j^{ω₂}) = X(θ_j^{ω₁}) + X(θ_j^{ω₂}) by linearity of X.toCurrent, and this tends to L(ω₁) + L(ω₂) by step 2. By tendsto_nhds_unique, L(ω₁ + ω₂) = L(ω₁) + L(ω₂).
4. Homogeneity. For c ∈ ℝ, c·θ_j^ω equals G_j^#(c·ω) on W_j^ω, using Submodule.coe_smul, Pi.smul_apply and (c·α).compContinuousLinearMap A = c·α.compContinuousLinearMap A (ext; simp). So X(c·θ_j^ω) → L(c·ω). On the other hand X(c·θ_j^ω) = c·X(θ_j^ω) → c·L(ω). Hence L(c·ω) = c·L(ω). So L is a linear map T₀ : 𝒟^k(ℝ^{N'}) →ₗ[ℝ] ℝ.
5. Bound. Suppose |ω(y)| ≤ c for all y. For j ∈ ℕ and x ∈ spt X ⊆ W_j^ω we have θ_j^ω(x) = (ω(G_j x)).compContinuousLinearMap (fderiv ℝ G_j x). By (L1), |θ_j^ω(x)| ≤ ‖fderiv ℝ G_j x‖^k·|ω(G_j x)| ≤ Λ^k·c. This uses pow_le_pow_left₀ with ‖fderiv ℝ G_j x‖ ≤ Λ, and mul_le_mul with |ω(G_j x)| ≥ 0 and Λ^k ≥ 0. By (MSB) (M(X) < ∞), |X(θ_j^ω)| ≤ (Λ^k·c)·M(X).toReal for every j. The absolute values converge to |L(ω)|, so le_of_tendsto' gives |T₀(ω)| ≤ (Λ^k·M(X).toReal)·c.
6. Current. (BC), applied to N', k, T₀ and C := Λ^k·M(X).toReal, gives T ∈ 𝒟_k(ℝ^{N'}) with T(ω) = T₀(ω) = L(ω) for every ω. For admissible data for ω, X(η_j) → L(ω) = T(ω) by step 1. □

Lean proof script. It compiled with lake env lean after import GMT.Ch07.Submission, inside namespace GMT.Ch07 with the contract's opens, against the exact frozen types of the toolkit, PL and AD. It is the tactic body of theorem Submission.cmcdt_lpo_pf_current : <lean_statement> := by
  intro hVO hREP hLB N N' k Λ F X hF hX1 hX2 hX3
  obtain ⟨hMSB, hBC, -, -⟩ := Submission.cmcdt_lpo_current_toolkit hVO hREP
  have hL1 := hLB.1
  choose L hL using fun ω =>
    Submission.cmcdt_lpo_pf_pointwise_limit hVO hREP hLB N N' k Λ F X ω hF hX1 hX2 hX3
  obtain ⟨G, hG, -, hDG, -, hUG, hηG⟩ :=
    Submission.cmcdt_lpo_pf_approx_data N N' Λ F X.support hF hX1
  choose θ hθs using hηG k
  have hθ : ∀ ω j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
      (θ ω j : DifferentialForm (Euclid N) k) x =
        ((ω : DifferentialForm (Euclid N') k) (G j x)).compContinuousLinearMap
          (fderiv ℝ (G j) x) := fun ω j => by
    obtain ⟨W, hW, hKW, h1, -⟩ := hθs ω j
    exact ⟨W, hW, hKW, h1⟩
  have hconv : ∀ ω, Tendsto (fun j => X (θ ω j)) atTop (𝓝 (L ω)) := fun ω =>
    hL ω Λ G (θ ω) hG (fun j x _ => hDG j x) hUG.tendstoUniformlyOn (hθ ω)
  have hadd : ∀ ω₁ ω₂, L (ω₁ + ω₂) = L ω₁ + L ω₂ := by
    intro ω₁ ω₂
    have hdata : ∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
        ((θ ω₁ j + θ ω₂ j : TestFormOn (univ : Set (Euclid N)) k) :
          DifferentialForm (Euclid N) k) x =
        (((ω₁ + ω₂ : TestFormOn (univ : Set (Euclid N')) k) : DifferentialForm (Euclid N') k)
          (G j x)).compContinuousLinearMap (fderiv ℝ (G j) x) := by
      intro j
      obtain ⟨W₁, hW₁, hK₁, h₁⟩ := hθ ω₁ j
      obtain ⟨W₂, hW₂, hK₂, h₂⟩ := hθ ω₂ j
      refine ⟨W₁ ∩ W₂, hW₁.inter hW₂, subset_inter hK₁ hK₂, fun x hx => ?_⟩
      rw [Submodule.coe_add, Submodule.coe_add, Pi.add_apply, Pi.add_apply, h₁ x hx.1, h₂ x hx.2]
      ext v
      simp
    have h1 := hL (ω₁ + ω₂) Λ G (fun j => θ ω₁ j + θ ω₂ j) hG (fun j x _ => hDG j x)
      hUG.tendstoUniformlyOn hdata
    have h2 : Tendsto (fun j => X (θ ω₁ j + θ ω₂ j)) atTop (𝓝 (L ω₁ + L ω₂)) := by
      have := (hconv ω₁).add (hconv ω₂)
      refine this.congr (fun j => ?_)
      exact (X.toCurrent.map_add _ _).symm
    exact tendsto_nhds_unique h1 h2
  have hsmul : ∀ (c : ℝ) ω, L (c • ω) = c * L ω := by
    intro c ω
    have hdata : ∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
        ((c • θ ω j : TestFormOn (univ : Set (Euclid N)) k) :
          DifferentialForm (Euclid N) k) x =
        (((c • ω : TestFormOn (univ : Set (Euclid N')) k) : DifferentialForm (Euclid N') k)
          (G j x)).compContinuousLinearMap (fderiv ℝ (G j) x) := by
      intro j
      obtain ⟨W, hW, hK, h⟩ := hθ ω j
      refine ⟨W, hW, hK, fun x hx => ?_⟩
      rw [Submodule.coe_smul, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, h x hx]
      ext v
      simp
    have h1 := hL (c • ω) Λ G (fun j => c • θ ω j) hG (fun j x _ => hDG j x)
      hUG.tendstoUniformlyOn hdata
    have h2 : Tendsto (fun j => X (c • θ ω j)) atTop (𝓝 (c * L ω)) := by
      have := (hconv ω).const_mul c
      refine this.congr (fun j => ?_)
      exact (X.toCurrent.map_smul c _).symm
    exact tendsto_nhds_unique h1 h2
  let T₀ : TestFormOn (univ : Set (Euclid N')) k →ₗ[ℝ] ℝ :=
    { toFun := L
      map_add' := hadd
      map_smul' := hsmul }
  have hbound : ∀ (ω : TestFormOn (univ : Set (Euclid N')) k) (c : ℝ),
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') k) x) ≤ c) →
        |T₀ ω| ≤ ((Λ : ℝ) ^ k * X.mass.toReal) * c := by
    intro ω c hc
    have hj : ∀ j, |X (θ ω j)| ≤ (Λ : ℝ) ^ k * c * X.mass.toReal := by
      intro j
      apply hMSB N k X (θ ω j) ((Λ : ℝ) ^ k * c) hX2
      intro x hx
      obtain ⟨W, -, hKW, h⟩ := hθ ω j
      rw [h x (hKW hx)]
      refine (hL1 N N' k (fderiv ℝ (G j) x) _).trans ?_
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hDG j x) k) (hc _)
        (covectorEuclideanNorm_nonneg _) (pow_nonneg Λ.2 k)
    have hlim : |L ω| ≤ (Λ : ℝ) ^ k * c * X.mass.toReal :=
      le_of_tendsto' (hconv ω).abs hj
    show |L ω| ≤ _
    linarith
  obtain ⟨T, hT, -⟩ := hBC N' k T₀ ((Λ : ℝ) ^ k * X.mass.toReal) hbound
  refine ⟨T, fun Λ' Fs ω ηs hFs hD hU hη => ?_⟩
  rw [hT ω]
  exact hL ω Λ' Fs ηs hFs hD hU hη

## Key steps

1. PL defines L(ω) as the common limit of X(η_j) over all admissible data for ω.
2. AD gives common approximants G_j and forms θ_j^ω that are admissible for every ω.
3. Sums and scalar multiples of the θ_j^ω are admissible for ω₁ + ω₂ and c·ω, so L is linear by uniqueness of limits.
4. (L1) and (MSB) give |L(ω)| ≤ Λ^k·M(X)·c whenever |ω| ≤ c.
5. (BC) turns L into a current T, and PL gives T its approximation property.

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
