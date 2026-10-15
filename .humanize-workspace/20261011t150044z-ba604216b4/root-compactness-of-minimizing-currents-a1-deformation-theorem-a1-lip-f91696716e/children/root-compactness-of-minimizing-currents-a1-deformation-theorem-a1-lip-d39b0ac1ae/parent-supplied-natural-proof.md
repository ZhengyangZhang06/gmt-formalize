# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.pushforward-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.pushforward-a1.normal_closure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: all currents live on univ.
- spt T = T.support = univ \ T.zeroRegion. T.zeroRegion is the union of the open sets W with compact closure (closure W ⊆ univ) on which T vanishes. T.VanishesOn W means T(ω) = 0 whenever tsupport ω ⊆ W.
- M(T) = T.mass = T.massOn univ = sSup{ofReal(T(ω)) : ω ∈ massAdmissibleOn univ m univ}. Here ω is admissible when tsupport ω ⊆ univ and covectorEuclideanNorm(ω(x)) ≤ 1 for all x.
- boundaryMassOn T univ is 0 in degree 0 and T.boundary.massOn univ in degree m + 1.
- ∂T(ω) = T(dω), where dω = exteriorDerivativeTestOn univ m ω has underlying form exteriorDerivative ω.
- (X − Y)(ω) = X(ω) − Y(ω) definitionally.
1. Subadditivity. For all m and A, B ∈ 𝒟_m(ℝ^N), (A − B).massOn univ ≤ A.massOn univ + B.massOn univ. By sSup_le it suffices to bound ofReal((A − B)(ω)) for admissible ω.
- −ω is admissible: tsupport(−ω) ⊆ univ, and covectorEuclideanNorm((−ω)(x)) = covectorEuclideanNorm(−(ω x)) = covectorEuclideanNorm(ω x) ≤ 1 (covectorEuclideanNorm_neg).
- B.toCurrent is linear, so B(−ω) = −B(ω), hence (A − B)(ω) = A(ω) + B(−ω).
- Therefore ofReal((A − B)(ω)) ≤ ofReal(A(ω)) + ofReal(B(−ω)) (ENNReal.ofReal_add_le) ≤ A.massOn univ + B.massOn univ (GeometricCurrentOn.le_massOn for ω and for −ω).
2. Supports are closed. T.support = (T.zeroRegion)ᶜ, since univ \ Z = Zᶜ, and T.zeroRegion is open (GeometricCurrentOn.isOpen_zeroRegion).
3. (a) Support of X − Y. Let x ∈ spt(X − Y) and suppose x ∉ spt X ∪ spt Y. Then x ∈ X.zeroRegion and x ∈ Y.zeroRegion. So there are W₁ ∋ x and W₂ ∋ x in the defining families: open, with compact closures, X vanishing on W₁ and Y vanishing on W₂. Let W := W₁ ∩ W₂.
- W is open and contains x.
- closure W ⊆ closure W₁ (closure_mono) is closed inside a compact set, hence compact (IsCompact.of_isClosed_subset); also closure W ⊆ univ.
- X − Y vanishes on W: if tsupport ω ⊆ W, then tsupport ω ⊆ W₁ and ⊆ W₂, so (X − Y)(ω) = X(ω) − Y(ω) = 0 − 0 = 0.
So x ∈ (X − Y).zeroRegion, contradicting x ∈ spt(X − Y). Hence spt(X − Y) ⊆ spt X ∪ spt Y.
4. (a) Compactness. spt(X − Y) is closed (step 2) and contained in the compact set spt X ∪ spt Y (step 3), hence compact.
5. (a) Mass. M(X − Y) ≤ M(X) + M(Y) < ∞, by step 1 with m = k and ENNReal.add_lt_top.
6. (a) Boundary mass, by cases on k.
- k = 0: boundaryMassOn (X − Y) univ = 0 < ∞.
- k = k' + 1: boundaryMassOn (X − Y) univ = (X − Y).boundary.massOn univ. Also (X − Y).boundary = X.boundary − Y.boundary by GeometricCurrentOn.ext, since both send ω to X(dω) − Y(dω) definitionally. By step 1 with m = k', the boundary mass is ≤ X.boundary.massOn univ + Y.boundary.massOn univ = boundaryMassOn X univ + boundaryMassOn Y univ < ∞.
7. (b) Support of ∂X. Let x ∈ spt ∂X and suppose x ∈ X.zeroRegion, witnessed by W ∋ x (open, compact closure ⊆ univ, X vanishes on W). Then ∂X vanishes on W: if tsupport ω ⊆ W, then tsupport(exteriorDerivative ω) ⊆ tsupport ω ⊆ W (tsupport_exteriorDerivative_subset), so ∂X(ω) = X(dω) = 0. Thus x ∈ (∂X).zeroRegion, a contradiction. Hence spt ∂X ⊆ spt X.
8. (b) Compactness. spt ∂X is closed (step 2) and contained in the compact set spt X.
9. (b) Boundary mass, by cases on k.
- k = 0: the boundaryMassOn of a degree-0 current is 0 by definition.
- k = k' + 1: boundaryMassOn ∂X univ = (∂∂X).massOn univ. First, ∂∂X = 0 (ext): ∂∂X(ω) = X(d(dω)), and d(dω) = 0 as a test form (Subtype.ext, plus exteriorDerivative_sq applied to the smoothness ω.property.1.1), so X(d(dω)) = X(0) = 0 (map_zero). Second, (0).massOn univ = 0: every element of the defining set is ofReal(0(ω)) = ofReal 0 = 0 (GeometricCurrentOn.zero_apply), so the sSup is ≤ 0 (sSup_le), and le_antisymm with bot_le gives equality. □

Lean proof script. It compiled with lake env lean after import GMT.Ch07.Submission, inside namespace GMT.Ch07 with the contract's opens, and uses no interface. It is the tactic body of theorem Submission.cmcdt_lpo_pf_normal_closure : <lean_statement> := by
  have key : ∀ (N m : ℕ) (A B : GeometricCurrentOn (univ : Set (Euclid N)) m),
      (A - B).massOn univ ≤ A.massOn univ + B.massOn univ := by
    intro N m A B
    apply sSup_le
    rintro r ⟨ω, hω, rfl⟩
    have hneg : -ω ∈ massAdmissibleOn univ m univ := by
      refine ⟨subset_univ _, fun x => ?_⟩
      have := hω.2 x
      simpa using this
    have hval : (A - B) ω = A ω + B (-ω) := by
      show A.toCurrent ω - B.toCurrent ω = A.toCurrent ω + B.toCurrent (-ω)
      have h := B.toCurrent.map_neg ω
      linarith
    dsimp only
    rw [hval]
    exact ENNReal.ofReal_add_le.trans (add_le_add (A.le_massOn hω) (B.le_massOn hneg))
  have hclosed : ∀ (N m : ℕ) (A : GeometricCurrentOn (univ : Set (Euclid N)) m),
      IsClosed A.support := by
    intro N m A
    have : A.support = (A.zeroRegion)ᶜ := by
      simp [GeometricCurrentOn.support, compl_eq_univ_sdiff]
    rw [this]
    exact A.isOpen_zeroRegion.isClosed_compl
  refine ⟨?_, ?_⟩
  · intro N k X Y hX1 hX2 hX3 hY1 hY2 hY3
    have hsupp : (X - Y).support ⊆ X.support ∪ Y.support := by
      rintro x ⟨-, hx⟩
      by_contra hxy
      simp only [mem_union, not_or] at hxy
      have hxX : x ∈ X.zeroRegion := by
        by_contra h
        exact hxy.1 ⟨mem_univ x, h⟩
      have hxY : x ∈ Y.zeroRegion := by
        by_contra h
        exact hxy.2 ⟨mem_univ x, h⟩
      obtain ⟨W₁, ⟨hW₁o, hW₁c, -, hW₁v⟩, hxW₁⟩ := hxX
      obtain ⟨W₂, ⟨hW₂o, -, -, hW₂v⟩, hxW₂⟩ := hxY
      apply hx
      refine ⟨W₁ ∩ W₂, ⟨hW₁o.inter hW₂o, ?_, subset_univ _, ?_⟩, ⟨hxW₁, hxW₂⟩⟩
      · exact hW₁c.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
      · intro ω hω
        show X.toCurrent ω - Y.toCurrent ω = 0
        rw [show X.toCurrent ω = 0 from hW₁v ω (hω.trans inter_subset_left),
          show Y.toCurrent ω = 0 from hW₂v ω (hω.trans inter_subset_right), sub_zero]
    refine ⟨hsupp, (hX1.union hY1).of_isClosed_subset (hclosed N k _) hsupp,
      lt_of_le_of_lt (key N k X Y) (ENNReal.add_lt_top.2 ⟨hX2, hY2⟩), ?_⟩
    cases k with
    | zero => exact ENNReal.zero_lt_top
    | succ k' =>
      show (X - Y).boundary.massOn univ < ∞
      have hb : (X - Y).boundary = X.boundary - Y.boundary := by
        ext ω
        rfl
      rw [hb]
      exact lt_of_le_of_lt (key N k' _ _) (ENNReal.add_lt_top.2 ⟨hX3, hY3⟩)
  · intro N k X hX
    have hsupp : X.boundary.support ⊆ X.support := by
      rintro x ⟨-, hx⟩
      refine ⟨mem_univ x, fun hxX => hx ?_⟩
      obtain ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hxW⟩ := hxX
      refine ⟨W, ⟨hWo, hWc, hWU, fun ω hω => ?_⟩, hxW⟩
      exact hWv _ ((tsupport_exteriorDerivative_subset _).trans hω)
    refine ⟨hsupp, hX.of_isClosed_subset (hclosed N k _) hsupp, ?_⟩
    cases k with
    | zero => rfl
    | succ k' =>
      show X.boundary.boundary.massOn univ = 0
      have h0 : X.boundary.boundary = 0 := by
        ext ω
        show X.toCurrent (exteriorDerivativeTestOn univ (k' + 1)
          (exteriorDerivativeTestOn univ k' ω)) = 0
        have : exteriorDerivativeTestOn univ (k' + 1) (exteriorDerivativeTestOn univ k' ω) = 0 := by
          apply Subtype.ext
          exact exteriorDerivative_sq ω.property.1.1
        rw [this, map_zero]
      rw [h0]
      apply le_antisymm ?_ bot_le
      apply sSup_le
      rintro r ⟨ω, -, rfl⟩
      simp

## Key steps

1. massOn univ is subadditive on differences, because −ω is admissible and (A − B)(ω) = A(ω) + B(−ω).
2. Supports of currents on univ are closed, being complements of the open zero regions.
3. zeroRegion X ∩ zeroRegion Y ⊆ zeroRegion(X − Y), so spt(X − Y) ⊆ spt X ∪ spt Y, which makes it compact; its mass is finite by subadditivity.
4. ∂(X − Y) = ∂X − ∂Y gives finite boundary mass (degree 0 is trivial).
5. tsupport dω ⊆ tsupport ω gives spt ∂X ⊆ spt X, hence compactness; ∂∂X = 0 gives boundaryMassOn ∂X univ = 0.

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
