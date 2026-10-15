# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.spine_tangency-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.spine_tangency-a1.ball_scaling-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 1 of the parent proof ("Constant ratios at points of L"). It is the scaling computation behind Simon's proof of 7.3.1 (chapter-07.txt lines 352–355: "(ω_nρ^n)^{−1}μ_C(B_ρ(0)) = Θ^n(T, x) for each ρ > 0"), transported by translation to centres z in the spine L of Lemma 7.3.5 (chapter-07.txt lines 410–419, proof "left to the reader"). Notation: B̄_r(c) := closedBall c r = {x : ‖x − c‖ ≤ r}; ρ^n in [0, ∞] means ENNReal.ofReal(ρ^n). Only the two hypotheses on μ are used; μ need not be finite or locally finite.
1. (Translation by −z.) Let z ∈ L and r ∈ ℝ. Since L is a linear subspace, −z ∈ L. For x ∈ ℝ^P we have (−z) + x = x − z, so x ∈ (fun x => (−z) + x)⁻¹'(B̄_r(0)) ⇔ ‖x − z‖ ≤ r ⇔ x ∈ B̄_r(z); that is, (fun x => (−z) + x)⁻¹'(B̄_r(0)) = B̄_r(z). The closed ball B̄_r(0) is a Borel set, so the translation hypothesis with y = −z and A = B̄_r(0) gives μ(B̄_r(z)) = μ(B̄_r(0)).
2. (Dilation by ρ.) Let ρ > 0. Then (fun x => ρ • x)''B̄_1(0) = B̄_ρ(0): if ‖x‖ ≤ 1 then ‖ρx‖ = ρ‖x‖ ≤ ρ; conversely, if ‖y‖ ≤ ρ then y = ρ(ρ^{−1}y) with ‖ρ^{−1}y‖ = ρ^{−1}‖y‖ ≤ 1 (Mathlib Set.image_smul and smul_unitClosedBall_of_nonneg). B̄_1(0) is Borel, so the homogeneity hypothesis with λ = ρ and A = B̄_1(0) gives μ(B̄_ρ(0)) = ofReal(ρ^n)·μ(B̄_1(0)).
3. (Conclusion.) By step 1 with r = ρ, then step 2, then step 1 with r = 1: μ(B̄_ρ(z)) = μ(B̄_ρ(0)) = ofReal(ρ^n)·μ(B̄_1(0)) = ofReal(ρ^n)·μ(B̄_1(z)). ∎

Lean implementation (compiled during decomposition after the frozen contract, in namespace GMT.Ch07 with the contract's opens; #print axioms: propext, Classical.choice, Quot.sound):
theorem Submission.dimred_cs_st_closedBall_measure_scaling : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (L : Submodule ℝ (Euclid P)), (∀ y ∈ L, ∀ A : Set (Euclid P), MeasurableSet A → μ ((fun x => y + x) ⁻¹' A) = μ A) → (∀ lam : ℝ, 0 < lam → ∀ A : Set (Euclid P), MeasurableSet A → μ ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * μ A) → ∀ z ∈ L, ∀ ρ : ℝ, 0 < ρ → μ (closedBall z ρ) = ENNReal.ofReal (ρ ^ n) * μ (closedBall z 1) := by
  intro P n μ L htrans hhom z hz ρ hρ
  -- translation by `-z ∈ L`: `B̄_r(z) = (x ↦ -z + x)⁻¹' B̄_r(0)`
  have htr : ∀ r : ℝ, μ (closedBall z r) = μ (closedBall 0 r) := by
    intro r
    rw [← htrans (-z) (L.neg_mem hz) (closedBall 0 r) measurableSet_closedBall]
    congr 1
    ext x
    simp only [mem_closedBall, mem_preimage, dist_eq_norm, sub_zero, neg_add_eq_sub]
  -- dilation by `ρ`: `B̄_ρ(0) = (x ↦ ρ • x) '' B̄_1(0)`
  have hsc : (fun x => ρ • x) '' closedBall (0 : Euclid P) 1 = closedBall 0 ρ := by
    rw [Set.image_smul, smul_unitClosedBall_of_nonneg hρ.le]
  rw [htr, htr 1, ← hsc, hhom ρ hρ _ measurableSet_closedBall]

## Key steps

1. −z ∈ L and (x ↦ −z + x)⁻¹'B̄_r(0) = B̄_r(z), so translation invariance gives μ(B̄_r(z)) = μ(B̄_r(0)) for every r.
2. (x ↦ ρx)''B̄_1(0) = B̄_ρ(0), so homogeneity gives μ(B̄_ρ(0)) = ρ^n μ(B̄_1(0)) for ρ > 0.
3. Combining the translation identity at radii ρ and 1 with the dilation identity: μ(B̄_ρ(z)) = ρ^n μ(B̄_1(z)).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (b4d606db…, 25730c7c…, 2b366308…)`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `python3 -I inspection of dag.json: lean_statement/status/depends_on/candidate_commit of dtc_cone_monotonicity_identity, dtc_cone_radial_tangency, stationary_imrep_radial_tangency_of_ball_ratio, imrep_univ_tangent_starProjection_aemeasurable, dtc_cone_tangentProjection_aemeasurable, doragm_radial_first_variation, doragm_radial_cutoff_hasDerivAt, dsmc_firstVariation_eq_integral, stationary_radial_imrep_weighted_moment_eq_zero`
- `git show 251e7a15:GMT/Ch07/Submission.lean | sed -n 1180,1267p (accepted proof of dtc_cone_radial_tangency from dtc_cone_monotonicity_identity); git show 4d61ba7a / 74a7d911:GMT/Ch07/Submission.lean | grep -n '^theorem'; git cat-file -t on 4d61ba7a, 74a7d911, 251e7a15, 44fd07a8`
- `isolated-comparator-result.json of nodes root-density-and-tangent-cones-a1-cone-a1-monotonicity-identity-a1 and root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1 (passed: True); their parent-supplied-natural-proof.md (accepted proofs copied verbatim)`
- `python3 -I scan of nodes/*/decomposition-v*.json and decomposition-audit-v*.json for cross-branch reuse of accepted nodes with their own dependencies (dsmc_exp_ball_mass_monotone, dor_ims_massOn_le_measure: sibling deps [], audits acceptable)`
- `grep -n 'theorem smul_unitClosedBall_of_nonneg|lemma image_smul|theorem lintegral_eq_zero_iff\'|theorem starProjection_eq_self_iff|theorem ae_all_iff|def finBasis|theorem span_eq' in the snapshot mathlib`
- `sed -n 330,440p book/chapter-07.txt (7.3.1 proof lines 352–360, Remark 7.3.4, Lemma 7.3.5); sed -n 215,335p book/chapter-04.txt (3.1–3.10); grep -n 'monotonicity formula 3.6' book/sources/chapter-07-source.txt`
- `python3 -I /tmp/st-decomp/gen_cmp.py (verifier gmt-compare.contract_scope + child_modules mode=contract, lean_contract.validate_lean_statement); lake env lean /tmp/st-decomp/cmp/Challenge_*.lean /tmp/st-decomp/cmp/SolutionSide.lean`
- `lake env lean /tmp/st-decomp/Full.lean (contract + accepted code of 4d61ba7a and 74a7d911 + both new children + parent assembly; #print axioms) and lake env lean /tmp/st-decomp/Assembly.lean`
- `grep dimred_cs_st_ in dag.json, run node JSONs, GMT, .lake/packages/{simongmt,mathlib}; git grep -e dimred_cs_st_ over all 2595 refs; grep over 1202 Lean files workspaces/.swarm-worktrees/*/gmt-ch07/GMT/{Ch07,Scratch} (no match anywhere)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-spine-tangency-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-spine-tangency-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-monotonicity-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-monotonicity-identity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-monotonicity-identity-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Group/Pointwise/Set/Scalar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Free.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Basis/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-07-source.txt`
- `/tmp/st-decomp/Full.lean`
- `/tmp/st-decomp/Assembly.lean`
- `/tmp/st-decomp/gen_cmp.py`
- `/tmp/st-decomp/cmp/SolutionSide.lean`

Pins. The snapshot is at project b4d606d (= workspace HEAD), Mathlib 25730c7c and SimonGMT 2b36630. Its Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Reusable accepted declarations. dag.json and the accepted candidates provide:
- the centre-z stationary monotonicity identity on closed balls, Submission.dtc_cone_monotonicity_identity (accepted, 4d61ba7a, comparator passed);
- the R.measure-a.e. measurability of x ↦ p_x, Submission.imrep_univ_tangent_starProjection_aemeasurable (accepted, 74a7d911, comparator passed). This is already this node's dependency.
Both are reused with byte-identical types.

Not reusable here. The accepted radial-tangency lemmas (dtc_cone_radial_tangency, stationary_imrep_radial_tangency_of_ball_ratio) cover only centre 0. Hence centre_tangency is new and mirrors the accepted proof of dtc_cone_radial_tangency at centre z.

Mathlib facts used, all present in the snapshot: Set.image_smul, smul_unitClosedBall_of_nonneg, lintegral_eq_zero_iff', Submodule.starProjection_eq_self_iff, ae_all_iff, Module.finBasis and Basis.span_eq.

Lean checks.
- All four child types pass validate_lean_statement and elaborate in the comparator's exact child scope; the solution side elaborates.
- The new children and the frozen parent compile from the accepted reuse code with only propext, Classical.choice and Quot.sound.
- The two new names have no match in the DAG, the project, SimonGMT, Mathlib, any git ref or any Ch07 swarm worktree.
