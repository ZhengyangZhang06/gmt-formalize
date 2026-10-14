# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.pushforward-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.pushforward-a1.mass_support-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Interface (a dependency of the parent node, exact frozen type): Submission.cmcdt_lpo_current_toolkit applied to (VO), (REP). Two of its conjuncts are used:
- (MSB): if M(X) < ∞ and |ψ(x)| ≤ c on spt X, then |X(ψ)| ≤ c·M(X).toReal.
- (LOC): if W is open, spt X ⊆ W and η = η' on W, then X(η) = X(η').
(L1) is the first conjunct of (LB). Sibling child: Submission.cmcdt_lpo_pf_approx_data (AD). Write T := lpush(F, X).
1. Data. AD, applied to Λ, F and K := spt X, gives C^∞ maps G_j with ‖fderiv ℝ G_j x‖ ≤ Λ everywhere, dist(G_j x, F x) ≤ Λ/(j + 1), and G_j → F uniformly on ℝ^N. For every ω it also gives test forms θ_j^ω and open sets W_j^ω ⊇ spt X on which θ_j^ω = G_j^#ω; choose them as functions of ω. By (PA) (with Λ' := Λ and uniform convergence on spt X), X(θ_j^ω) → T(ω) for every ω. Also Λ/(j + 1) → 0 (tendsto_one_div_add_atTop_nhds_zero_nat times Λ).
2. Mass. T.mass = sSup{ofReal(T(ω)) : ω admissible}. By sSup_le it suffices to show ofReal(T(ω)) ≤ (Λ : ℝ≥0∞)^k·M(X) whenever |ω(y)| ≤ 1 for all y.
- For x ∈ spt X ⊆ W_j^ω, (L1) gives |θ_j^ω(x)| = |(ω(G_j x)).compContinuousLinearMap (fderiv ℝ G_j x)| ≤ ‖fderiv ℝ G_j x‖^k·|ω(G_j x)| ≤ Λ^k·1.
- By (MSB), |X(θ_j^ω)| ≤ Λ^k·1·M(X).toReal for all j. In the limit, T(ω) ≤ |T(ω)| ≤ Λ^k·1·M(X).toReal (le_abs_self, le_of_tendsto').
- Hence ofReal(T(ω)) ≤ ofReal(Λ^k·M(X).toReal) = ofReal(((Λ^k : ℝ≥0) : ℝ)·M(X).toReal) (NNReal.coe_pow) = ((Λ^k : ℝ≥0) : ℝ≥0∞)·M(X) (ENNReal.ofReal_mul, ENNReal.ofReal_coe_nnreal, and ENNReal.ofReal_toReal using M(X) ≠ ∞) = (Λ : ℝ≥0∞)^k·M(X) (ENNReal.coe_pow).
3. Support. Let y ∈ spt T = univ \ T.zeroRegion and suppose y ∉ F(spt X). We exhibit an open B ∋ y with compact closure (closure B ⊆ univ trivially) on which T vanishes. Then y ∈ T.zeroRegion, a contradiction; hence spt T ⊆ F(spt X).
4. Case spt X = ∅. For every test form η, (LOC) with W := ∅ gives X(η) = X(0) = 0: ∅ is open, spt X ⊆ ∅, and agreement on ∅ is vacuous. So X(θ_j^ω) = 0 for all j, and by step 1 and uniqueness of limits, T(ω) = 0 for every ω. Take B := ball(y, 1). It is open and contains y, and closure B ⊆ closedBall(y, 1) (closure_ball_subset_closedBall), which is compact (isCompact_closedBall). T vanishes on B.
5. Case spt X ≠ ∅. F(spt X) is nonempty and compact (the continuous image of a compact set), hence closed. Since y ∉ F(spt X), r := infDist(y, F(spt X)) > 0 (IsClosed.notMem_iff_infDist_pos). Let B := ball(y, r/3): it is open, contains y, and its closure lies in the compact set closedBall(y, r/3). Let ω satisfy tsupport ω ⊆ B. Take any j with Λ/(j + 1) < r/3; by step 1 this holds eventually.
- O_j := {x | r/3 < dist(G_j x, y)} is open (G_j is continuous).
- O_j contains spt X. For x ∈ spt X, r ≤ dist(y, F x) = dist(F x, y) (infDist_le_dist_of_mem). Also dist(F x, y) ≤ dist(F x, G_j x) + dist(G_j x, y) and dist(G_j x, F x) ≤ Λ/(j + 1) < r/3. So dist(G_j x, y) > 2r/3 > r/3.
- For x ∈ O_j ∩ W_j^ω, G_j x ∉ ball(y, r/3) ⊇ tsupport ω, so ω(G_j x) = 0 (image_eq_zero_of_notMem_tsupport). Hence θ_j^ω(x) = (0).compContinuousLinearMap (fderiv ℝ G_j x) = 0 = (0 : test form)(x) (ext; simp).
- By (LOC) with the open set O_j ∩ W_j^ω ⊇ spt X, X(θ_j^ω) = X(0) = 0.
So X(θ_j^ω) is eventually 0 and therefore tends to 0 (Tendsto.congr' of the constant sequence). By step 1 and uniqueness of limits, T(ω) = 0. Thus T vanishes on B. □

Lean proof script. It compiled with lake env lean after import GMT.Ch07.Submission, inside namespace GMT.Ch07 with the contract's opens, against the exact frozen types of the toolkit and AD. It is the tactic body of theorem Submission.cmcdt_lpo_pf_mass_support : <lean_statement> := by
  intro hVO hREP hLB lpush hPA N N' k Λ F X hF hX1 hX2 hX3
  obtain ⟨hMSB, -, -, hLOC⟩ := Submission.cmcdt_lpo_current_toolkit hVO hREP
  have hL1 := hLB.1
  obtain ⟨G, hG, -, hDG, hdistG, hUG, hηG⟩ :=
    Submission.cmcdt_lpo_pf_approx_data N N' Λ F X.support hF hX1
  choose θ hθs using hηG k
  have hθ : ∀ ω j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
      (θ ω j : DifferentialForm (Euclid N) k) x =
        ((ω : DifferentialForm (Euclid N') k) (G j x)).compContinuousLinearMap
          (fderiv ℝ (G j) x) := fun ω j => by
    obtain ⟨W, hW, hKW, h1, -⟩ := hθs ω j
    exact ⟨W, hW, hKW, h1⟩
  have hconv : ∀ ω, Tendsto (fun j => X (θ ω j)) atTop (𝓝 (lpush N N' k F X ω)) := fun ω =>
    hPA N N' k Λ Λ F G X ω (θ ω) hF hX1 hX2 hX3 hG (fun j x _ => hDG j x)
      hUG.tendstoUniformlyOn (hθ ω)
  have hrate : Tendsto (fun i : ℕ => (Λ : ℝ) / ((i : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (Λ : ℝ)
    rw [mul_zero] at this
    exact this.congr (fun j => mul_one_div _ _)
  refine ⟨?_, ?_⟩
  · apply sSup_le
    rintro r ⟨ω, hω, rfl⟩
    have hj : ∀ j, |X (θ ω j)| ≤ (Λ : ℝ) ^ k * 1 * X.mass.toReal := by
      intro j
      apply hMSB N k X (θ ω j) ((Λ : ℝ) ^ k * 1) hX2
      intro x hx
      obtain ⟨W, -, hKW, h⟩ := hθ ω j
      rw [h x (hKW hx)]
      refine (hL1 N N' k (fderiv ℝ (G j) x) _).trans ?_
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hDG j x) k) (hω.2 _)
        (covectorEuclideanNorm_nonneg _) (pow_nonneg Λ.2 k)
    have hlim : lpush N N' k F X ω ≤ (Λ : ℝ) ^ k * 1 * X.mass.toReal :=
      (le_abs_self _).trans (le_of_tendsto' (hconv ω).abs hj)
    dsimp only
    calc ENNReal.ofReal (lpush N N' k F X ω)
        ≤ ENNReal.ofReal ((Λ : ℝ) ^ k * 1 * X.mass.toReal) := ENNReal.ofReal_le_ofReal hlim
      _ = ENNReal.ofReal (((Λ ^ k : NNReal) : ℝ) * X.mass.toReal) := by
        rw [NNReal.coe_pow, mul_one]
      _ = ((Λ ^ k : NNReal) : ℝ≥0∞) * X.mass := by
        rw [ENNReal.ofReal_mul NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_toReal hX2.ne]
      _ = (Λ : ℝ≥0∞) ^ k * X.mass := by
        rw [ENNReal.coe_pow]
  · rintro y ⟨-, hy⟩
    by_contra hyF
    apply hy
    by_cases hXe : X.support = ∅
    · have hX0 : ∀ η : TestFormOn (univ : Set (Euclid N)) k, X η = 0 := by
        intro η
        rw [hLOC N k X η 0 ∅ isOpen_empty (by rw [hXe]) (fun x hx => hx.elim), map_zero]
      have hT0 : ∀ ω, lpush N N' k F X ω = 0 := by
        intro ω
        have h := hconv ω
        simp only [hX0] at h
        exact tendsto_nhds_unique h tendsto_const_nhds
      refine ⟨ball y 1, ⟨isOpen_ball, ?_, subset_univ _, fun ω _ => hT0 ω⟩, mem_ball_self one_pos⟩
      exact (isCompact_closedBall y 1).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · have hne : (F '' X.support).Nonempty := (nonempty_iff_ne_empty.2 hXe).image F
      have hcpt : IsCompact (F '' X.support) := hX1.image hF.continuous
      have hr : 0 < infDist y (F '' X.support) :=
        (hcpt.isClosed.notMem_iff_infDist_pos hne).1 hyF
      set r := infDist y (F '' X.support) with hrdef
      refine ⟨ball y (r / 3), ⟨isOpen_ball, ?_, subset_univ _, ?_⟩, mem_ball_self (by linarith)⟩
      · exact (isCompact_closedBall y (r / 3)).of_isClosed_subset isClosed_closure
          closure_ball_subset_closedBall
      · intro ω hω
        have hev : ∀ᶠ j in atTop, X (θ ω j) = 0 := by
          filter_upwards [hrate.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < r / 3))]
            with j hj
          obtain ⟨W, hW, hKW, h⟩ := hθ ω j
          have hO : IsOpen {x | r / 3 < dist (G j x) y} :=
            isOpen_lt continuous_const ((hG j).continuous.dist continuous_const)
          have hKO : X.support ⊆ {x | r / 3 < dist (G j x) y} := by
            intro x hx
            have h1 : r ≤ dist (F x) y := by
              rw [dist_comm]
              exact infDist_le_dist_of_mem (mem_image_of_mem F hx)
            have h2 : dist (G j x) (F x) ≤ (Λ : ℝ) / ((j : ℝ) + 1) := hdistG j x
            have h3 := dist_triangle (F x) (G j x) y
            rw [dist_comm (F x) (G j x)] at h3
            show r / 3 < dist (G j x) y
            linarith
          have hzero : ∀ x ∈ {x | r / 3 < dist (G j x) y} ∩ W,
              (θ ω j : DifferentialForm (Euclid N) k) x =
                ((0 : TestFormOn (univ : Set (Euclid N)) k) : DifferentialForm (Euclid N) k) x := by
            intro x hx
            rw [h x hx.2]
            have h0 : (ω : DifferentialForm (Euclid N') k) (G j x) = 0 := by
              apply image_eq_zero_of_notMem_tsupport
              intro hmem
              have hb := hω hmem
              rw [mem_ball] at hb
              exact absurd hb (not_lt.2 hx.1.le)
            rw [h0]
            ext v
            simp
          rw [hLOC N k X (θ ω j) 0 _ (hO.inter hW) (subset_inter hKO hKW) hzero, map_zero]
        have h0 : Tendsto (fun j => X (θ ω j)) atTop (𝓝 0) :=
          tendsto_const_nhds.congr' (hev.mono fun j hj => hj.symm)
        exact tendsto_nhds_unique (hconv ω) h0

## Key steps

1. The AD data θ_j^ω satisfy X(θ_j^ω) → T(ω) by (PA).
2. (L1) and (MSB) give |X(θ_j^ω)| ≤ Λ^k·M(X) for admissible ω; take the limit and then the sSup.
3. If spt X = ∅, (LOC) with W = ∅ kills X, so T = 0.
4. Otherwise, for y ∉ F(spt X) put r = infDist > 0. For tsupport ω ⊆ ball(y, r/3), θ_j^ω vanishes near spt X for large j, so (LOC) gives X(θ_j^ω) = 0 and T(ω) = 0. Hence ball(y, r/3) ⊆ zeroRegion T.

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
