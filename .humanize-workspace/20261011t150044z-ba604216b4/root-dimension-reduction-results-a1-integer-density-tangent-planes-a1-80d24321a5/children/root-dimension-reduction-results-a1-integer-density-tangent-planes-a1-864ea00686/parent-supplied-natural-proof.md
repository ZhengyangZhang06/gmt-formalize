# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1.spine_density_integer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon 7.3.3, proof of (1), display (15) and the paragraph following it (chapter-07.txt lines 488–510), together with Lemma 3.5 (lines 410–418). This is the (H2) argument of the parent proof. The classification of 2-dimensional area minimizing cones, which the book cites to [Whi82] (lines 501–504), enters only through the prerequisite result Submission.idtp_two_dim_cone_integer_density. Let d := Module.finrank ℝ L.

1. Uniqueness of densities. For every j ∈ ℕ, C ∈ 𝒟_j(ℝ^P) (GeometricCurrentOn univ j) and a, b ∈ ℝ: if HasMassDensity C 0 a and HasMassDensity C 0 b, then a = b. Both statements say that the same ratio function ρ ↦ C.massOn(B_ρ(0))/(ω_j·ofReal(ρ^j)) tends to ofReal(a), resp. ofReal(b), along the nontrivial filter 𝓝[>] 0 in the Hausdorff space [0, ∞]; so ofReal(a) = ofReal(b) (tendsto_nhds_unique), and since a, b ≥ 0 (part of HasMassDensity), a = b (ENNReal.ofReal_eq_ofReal_iff).

2. Splitting off the spine (Lemma 3.5). Since d < n, S is minimizing in ℝ^P, BoundaryVanishes S holds and S has the stated density invariance along L, the prerequisite result Submission.dimred_invariant_cone_splitting applies and gives S₀ ∈ 𝒟_{n−d}(ℝ^P) (GeometricCurrentOn univ (n − d), natural subtraction) with:
   - IsMinimizingIn S₀ univ, BoundaryVanishes S₀ and IsConeCurrent S₀;
   - HasMassDensity S (t + y) θ ⟺ HasMassDensity S₀ y θ for all t ∈ L, y ∈ L^⊥ and θ ∈ ℝ.
   Take t := 0 ∈ L, y := 0 ∈ L^⊥ and θ := θ₀. Since 0 + 0 = 0, the hypothesis HasMassDensity S 0 θ₀ gives HasMassDensity S₀ 0 θ₀.

3. Reduction to degree 1 or 2. From d < n ≤ d + 2 in ℕ we get n − d = 1 or n − d = 2. It therefore suffices to prove the claim: for every j ∈ ℕ with j = 1 or j = 2 and every C ∈ 𝒟_j(ℝ^P) with IsMinimizingIn C univ, BoundaryVanishes C, IsConeCurrent C and HasMassDensity C 0 θ₀, there is m ∈ ℕ with θ₀ = m. The claim is then applied with j := n − d and C := S₀, whose four properties were obtained in step 2. (Stating the claim for a variable degree j and substituting j = 1, resp. j = 2, is what transports S₀ to a current of degree 1 or 2.)

4. Case j = 1. The prerequisite result Submission.dimred_one_dim_minimizing_cone, applied to C ∈ 𝒟_1(ℝ^P) (minimizing in ℝ^P, ∂C = 0, a cone), gives e ∈ ℝ^P and m ∈ ℕ with HasMassDensity C y m for every y ∈ span{e}. Since 0 ∈ span{e}, HasMassDensity C 0 m, and step 1 (with HasMassDensity C 0 θ₀) gives θ₀ = m.

5. Case j = 2. The prerequisite result Submission.idtp_two_dim_cone_integer_density, applied to C ∈ 𝒟_2(ℝ^P) (minimizing in ℝ^P, ∂C = 0, a cone), gives m ∈ ℕ with HasMassDensity C 0 m; by step 1, θ₀ = m.

Hence θ₀ = m for some m ∈ ℕ. ∎

## Key steps

1. Densities are unique: HasMassDensity C 0 a and HasMassDensity C 0 b imply a = b.
2. Submission.dimred_invariant_cone_splitting gives S₀ ∈ 𝒟_{n−d}(ℝ^P), a minimizing cone with ∂S₀ = 0 and HasMassDensity S₀ 0 θ₀ (take t = y = 0).
3. n − d ∈ {1, 2}; generalize the degree to j and substitute j = 1 or j = 2.
4. j = 1: Submission.dimred_one_dim_minimizing_cone gives an integer density m at 0; j = 2: Submission.idtp_two_dim_cone_integer_density does.
5. Uniqueness of densities gives θ₀ = m ∈ ℕ.

## Reference use

### local-project

Queries:
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with local-references/123e8435b4a2469b/manifest.json)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `git show fb9bfaa2bb3b6a2fb2c8d2c902f098a63fc92f2d:GMT/Ch07/Submission.lean (layout of the accepted theorem Submission.idtp_convergesWeakly_massOn_le)`
- `python3 scan of dag.json: lean_statement/status of dimred_im_mass_measure, dimred_minimizing_monotonicity, dimred_threshold_reduction, dimred_invariant_cone_splitting, dimred_one_dim_minimizing_cone, dtc_blowUp_massOn_image, idtp_convergesWeakly_massOn_le, idtp_imrep_measure_density_ae, idtp_two_dim_cone_integer_density, dimred_cs_mi_hasMassDensity_unique; dependency lists of the parent and grandparent nodes`
- `grep -c 'idod_' dag.json DAG.md dag.mmd issue-workers.json problem.json (all 0); grep -rl 'idod_' nodes/ decomposition-reopenings/ (only this node's decomposition-v1/audit/receipt); grep -rl 'idod_' local-references/123e8435b4a2469b/project .lake/packages/simongmt (no match); git log --all -S 'idod_' (no match)`
- `grep -rn 'theorem measure_null_of_locally_null|theorem IsCompact.eventually_forall_of_forall_eventually|theorem upperSemicontinuousOn_iff_preimage_Iio|protected lemma mul_lt_mul_iff_right|lemma withDensity_zero_left|theorem measure_ball_pos|theorem measure_ball_lt_top|theorem ofReal_div_of_pos|protected theorem Tendsto.mul|theorem le_of_tendsto|theorem mul_le_mul_right' local-references/123e8435b4a2469b/mathlib/Mathlib; grep -n 'theorem GeometricCurrentOn.massOn_mono' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `sed -n 360,520p book/chapter-07.txt (Simon 7.3.3, Remark 3.4, Lemma 3.5, proof of 3.3(1), displays (1)-(15))`
- `lake env lean /tmp/idod2/check/Probe.lean (#check of the library lemmas)`
- `lake env lean /tmp/idod2/check/Assembly.lean (#print axioms check_parent)`
- `lake env lean /tmp/idod2/check/Leaves1.lean (#print axioms check_C1, check_C2); lake env lean /tmp/idod2/check/Leaves2.lean (#print axioms check_C3, check_C4, check_C5)`
- `lake env lean /tmp/idod2/check/FromJson.lean (statements and proofs regenerated from the final JSON strings)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-80d24321a5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-80d24321a5/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-80d24321a5/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/idod2/check/DepStubs.txt`
- `/tmp/idod2/check/ChildStubs.txt`
- `/tmp/idod2/check/Assembly.lean`
- `/tmp/idod2/check/Leaves1.lean`
- `/tmp/idod2/check/Leaves2.lean`
- `/tmp/idod2/check/FromJson.lean`

Pins match: the snapshot manifest records project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d, equal to the workspace HEAD and .lake/packages/mathlib HEAD; SimonGMT is pinned at 2b3663083f3fe399b6296fb8eaee52169170e197. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, and accepted children are declared as `theorem Submission.X` inside `namespace GMT.Ch07` (checked on the accepted commit fb9bfaa2).

Library support found in the snapshot: measure_null_of_locally_null (MeasureTheory/OuterMeasure/Basic.lean:150), measure_iUnion_null, IsCompact.eventually_forall_of_forall_eventually (Topology/Compactness/Compact.lean:459), upperSemicontinuousOn_iff_preimage_Iio (Topology/Semicontinuity/Basic.lean:914), measure_ball_pos (Measure/OpenPos.lean:212), measure_ball_lt_top (Measure/Typeclasses/Finite.lean:373), withDensity_zero_left (Measure/WithDensity.lean:83), ENNReal.ofReal_div_of_pos (Basic/ENNReal/Inv.lean:960), ENNReal.mul_lt_mul_iff_right (Basic/ENNReal/Operations.lean:83), ENNReal.Tendsto.mul / Tendsto.mul_const (Topology/Instances/ENNReal/Lemmas.lean:337, 359), le_of_tendsto (Topology/Order/OrderClosed.lean:133), and SimonGMT GeometricCurrentOn.massOn_mono (Chapter06/Mass.lean:81). In this Mathlib pin the monoid lemmas are named mul_le_mul_right/mul_le_mul_left (Algebra/Order/Monoid/Unbundled/Basic.lean:58, 66) and ENNReal lives under Mathlib/Basic/ENNReal.

DAG: the cited results have these frozen types and states: dimred_im_mass_measure, dtc_blowUp_massOn_image, idtp_convergesWeakly_massOn_le and dimred_cs_mi_hasMassDensity_unique are accepted; dimred_minimizing_monotonicity, dimred_threshold_reduction, dimred_invariant_cone_splitting, dimred_one_dim_minimizing_cone, idtp_imrep_measure_density_ae and idtp_two_dim_cone_integer_density are frozen siblings of this node or of its parent. No match for idod_ in dag.json, DAG.md, dag.mmd, issue-workers.json, problem.json, the pinned project, SimonGMT or git history. The only hits are this node's own unmaterialized attempt-1 files (decomposition-v1.json, audit, receipt); the DAG lists no children for this node. The five names are therefore unreserved and are reused with identical types.

Lean checks: stubs were generated verbatim from the dag.json types. Assembly.lean proves the frozen parent type from the children with axioms [propext, Classical.choice, Quot.sound, dimred_minimizing_monotonicity, idod_local_threshold_null]. Leaves1/Leaves2 prove each child's exact type from the stubs:
- C1: standard axioms only;
- C2: dtc_blowUp_massOn_image and idtp_convergesWeakly_massOn_le;
- C3: dimred_im_mass_measure and idtp_imrep_measure_density_ae;
- C4: dimred_invariant_cone_splitting, dimred_one_dim_minimizing_cone and idtp_two_dim_cone_integer_density;
- C5: dimred_minimizing_monotonicity, dimred_threshold_reduction and C1–C4.
No sorryAx appears. An independent reviewer agent re-ran a copy (/tmp/idod2_review/FromJson.lean) with identical axiom sets and accepted the split. Inline indicators, ENNReal products, casts and scalar multiplications have their intended instances, and no matrix construction occurs.
