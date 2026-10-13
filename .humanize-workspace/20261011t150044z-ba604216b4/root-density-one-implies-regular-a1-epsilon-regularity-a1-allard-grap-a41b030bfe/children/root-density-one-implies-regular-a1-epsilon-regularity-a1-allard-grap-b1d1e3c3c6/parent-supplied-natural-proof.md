# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_height-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_height-a1.mult_one_domination-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 5 of the parent proof of dorag_tes_graph_affine_height. It formalizes the passage in Simon, Ch. 5, proof of Theorem 4.5, book/chapter-05.txt lines 963–970, from the Hⁿ-integral over B_{θρ}(τ) ∩ graph f to the μ-integral over B_{θρ}(τ); the multiplicity is controlled at line 967. It is stated here for a general measurable set B and an arbitrary ambient dimension P. That step says: N := {x ∈ M ∩ B : θ(x) ≠ 1} has μ(N) = 0, and θ ≥ 1 on M, so Hⁿ(N) ≤ ∫_N θ dHⁿ = μ(N) = 0. Hence ∫_{S'} h dμ ≤ ∫_{S'} h dHⁿ for S' ⊆ B.
1. (Data.) θ : x ↦ (R.mult x : [0, ∞]) is measurable: R.mult is measurable into ℕ, and every map out of ℕ is measurable (measurable_from_nat). M = R.carrier is measurable (R.measurableSet_carrier), and R.mult x > 0 for x ∈ M (R.mult_pos).
 By definition μ = (Hⁿ⌞M).withDensity θ. Since B is measurable, restriction commutes with taking a density (restrict_withDensity): μ⌞B = ((Hⁿ⌞M)⌞B).withDensity θ.
2. (Translate the hypothesis.) θ is measurable, so ae_withDensity_iff turns the hypothesis 'for μ-a.e. x, x ∈ B → R.mult x = 1' into: for Hⁿ⌞M-a.e. x, θ(x) ≠ 0 → (x ∈ B → R.mult x = 1). Also Hⁿ⌞M-a.e. x lies in M (ae_restrict_mem).
3. (θ = 1 a.e. on B.) Statements holding a.e. for Hⁿ⌞M also hold a.e. for (Hⁿ⌞M)⌞B (ae_restrict_of_ae). Since B is measurable, (Hⁿ⌞M)⌞B-a.e. x lies in B (ae_restrict_mem).
 So for (Hⁿ⌞M)⌞B-a.e. x: x ∈ M, x ∈ B, and the implication of step 2 holds. For such x, R.mult x ≥ 1, so θ(x) ≠ 0. The implication then gives R.mult x = 1, i.e. θ(x) = 1.
 This is the parent's remark that the exceptional set N is Hⁿ-null because θ ≥ 1 on M.
4. (Measure inequality.) By step 3, θ = 1 a.e. for (Hⁿ⌞M)⌞B. Hence ((Hⁿ⌞M)⌞B).withDensity θ = ((Hⁿ⌞M)⌞B).withDensity 1 = (Hⁿ⌞M)⌞B (withDensity_congr_ae, withDensity_one).
 Since B is measurable, (Hⁿ⌞M)⌞B = Hⁿ⌞(B ∩ M) (Measure.restrict_restrict). This is ≤ Hⁿ⌞B because B ∩ M ⊆ B (Measure.restrict_mono).
 With step 1 this gives μ⌞B ≤ Hⁿ⌞B, the first conclusion.
5. (Integral inequality.) Let A ⊆ B and h ≥ 0 be arbitrary. Since A ⊆ B, μ⌞A = (μ⌞B)⌞A and Hⁿ⌞A = (Hⁿ⌞B)⌞A (Measure.restrict_restrict_of_subset). Restriction to A is monotone in the measure (Measure.restrict_mono), so step 4 gives μ⌞A ≤ Hⁿ⌞A.
 The lower integral is monotone in the measure without any measurability hypothesis (lintegral_mono' with h ≤ h). Hence ∫⁻_A h dμ ≤ ∫⁻_A h dHⁿ. ∎

## Key steps

1. θ = R.mult is measurable, θ ≥ 1 on the measurable carrier M, and μ⌞B = ((Hⁿ⌞M)⌞B).withDensity θ for measurable B.
2. ae_withDensity_iff plus θ ≠ 0 on M turns 'θ = 1 μ-a.e. on B' into θ = 1 (Hⁿ⌞M)⌞B-a.e.
3. Then ((Hⁿ⌞M)⌞B).withDensity θ = Hⁿ⌞(B ∩ M) ≤ Hⁿ⌞B.
4. For A ⊆ B, restrict both sides to A and use lintegral_mono' to get ∫⁻_A h dμ ≤ ∫⁻_A h dHⁿ.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); grep -n 'def IMRep.measure' -A2 <snapshot>/project/GMT/Ch07/Contract.lean`
- `rg -n 'notation.*μHE|μHE\[' <snapshot>/mathlib/Mathlib --glob '*.lean'`
- `rg -n 'support_mem_ae|measure_compl_support|compl_support' <snapshot>/mathlib/Mathlib/MeasureTheory --glob '*.lean'`
- `rg -n 'ball_ae_eq_closedBall|closedBall_ae_eq|ae_eq_closedBall|addHaar_sphere' <snapshot>/mathlib/Mathlib --glob '*.lean'`
- `rg -n 'norm_fderiv_le_of_lipschitz' <snapshot>/mathlib/Mathlib --glob '*.lean'`
- `rg -n 'starProjection_minimal|starProjection_apply_mem|sub_starProjection_mem_orthogonal|finrank_add_finrank_orthogonal|eq_of_le_of_finrank_eq|finrank_range_of_inj|finrank_euclideanSpace_fin|norm_add_sq_real' <snapshot>/mathlib/Mathlib`
- `rg -n 'lintegral_union_le|lintegral_mono_set|setLIntegral_const|lintegral_const_mul'|setLIntegral_congr|lintegral_mono_ae|restrict_restrict'|restrict_restrict_of_subset|restrict_mono|restrict_union_le|pow_le_pow_left₀|mul_le_mul_right' <snapshot>/mathlib/Mathlib`
- `python3 -I lean_name scan over workspaces/*/.humanize/github-theorem-prover/runs/*/dag.json (1924 names) plus rg 'dorag_tes_[A-Za-z0-9_]+' over this run's nodes/ and dag.json: no dorag_tes_gah_* reserved`
- `lean (v4.35.0-rc3, LEAN_PATH from /tmp/tes-v2/env.sh) on /tmp/gh-split/lean/Children.lean, Assembly.lean, Frame.lean, Small.lean, EndToEnd.lean, EndToEnd3.lean with #print axioms`
- `grep -n on book/chapter-05.txt for Theorem 4.5 and its proof (lines 747, 776, 789–797, 935–974)`
- `rg 'dorag_aa_height_bounds_of_net' over this run's nodes (no-split precedent for the support-conull argument)`

Files inspected:
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `GMT/Ch07/Submission.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/AddCircle.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-a41b030bfe/parent-child-handoff.json`
- `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-609ef45196/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/gh-split/lean/Children.lean`
- `/tmp/gh-split/lean/Assembly.lean`
- `/tmp/gh-split/lean/Frame.lean`
- `/tmp/gh-split/lean/Small.lean`
- `/tmp/gh-split/lean/EndToEnd.lean`
- `/tmp/gh-split/lean/EndToEnd3.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. Its GMT/Ch07/Contract.lean is byte-identical to the workspace Submission.lean; there IMRep.measure = (μHE[n].restrict carrier).withDensity mult.

Nothing in the snapshot proves the selected node or any child, and no dorag_tes_gah_* name is reserved, so no declaration is reused.

The needed Mathlib infrastructure exists:
- Measure.support_mem_ae (hereditarily Lindelöf spaces);
- Measure.addHaar_sphere. There is no general ball/closedBall a.e. lemma; only AddCircle.closedBall_ae_eq_ball exists, so weight_ball uses ae_eq_set together with closedBall_diff_ball;
- norm_fderiv_le_of_lipschitz;
- Submodule.starProjection_minimal, starProjection_apply_mem, sub_starProjection_mem_orthogonal and finrank_add_finrank_orthogonal;
- Submodule.eq_of_le_of_finrank_eq and LinearMap.finrank_range_of_inj;
- restrict_withDensity, ae_withDensity_iff and withDensity_congr_ae;
- lintegral_union_le, lintegral_mono_set, lintegral_const_mul', setLIntegral_congr and setLIntegral_const;
- mul_le_mul_right, which is the ordered-monoid name in this Mathlib.

Lean results:
- The three child types elaborate in comparator scope.
- The exact frozen parent type is proved from them plus the frozen graph_area type (GHSplit.parent3).
- All three child types are themselves proved.
- Axioms throughout are propext, Classical.choice and Quot.sound; there is no sorryAx.

The book passage is Simon, Ch. 5, proof of Theorem 4.5, lines 960–970, with hypotheses (2)–(4) at lines 789–797. The no-split precedent in nodes/…609ef45196 justified folding the support-conull step back into the parent.
