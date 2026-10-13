# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.series_limit-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.series_limit-a1.im_partial_sum-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1–2 of the parent proof. These define the sum A ⊕ B := A − ((B − B) − B), show it is integer multiplicity (IM) by (IS), and build the partial sums R^N, S^N by iterating ⊕.

Fix P, n, U and the family (Y_i). Assume (IS_U) and that every Y_i is IM.
The contract subtraction acts pointwise: its underlying functional is the difference of the two functionals. So (A − B)(ω) = A(ω) − B(ω) for all A, B ∈ 𝒟_n(U) and ω ∈ 𝒟^n(U); this holds by definition.
Write Σ_{i=0}^{N} for the sum over Finset.range (N + 1).
We prove the following claim C(N) by induction on N: there is an IM Z ∈ 𝒟_n(U) with Z(ω) = Σ_{i=0}^{N} Y_i(ω) for all ω ∈ 𝒟^n(U), and M_G(Z) ≤ Σ_{i=0}^{N} M_G(Y_i) for all G ⊆ ℝ^P.

1. (Base case N = 0.) Take Z := Y_0. It is IM by hypothesis. For every ω, Σ_{i=0}^{0} Y_i(ω) = Y_0(ω) = Z(ω). For every G, Σ_{i=0}^{0} M_G(Y_i) = M_G(Y_0) = M_G(Z), so the mass inequality holds with equality.
2. (Inductive step: set-up.) Assume C(N), witnessed by Z. Put B := Y_{N+1} and Z' := Z − ((B − B) − B) ∈ 𝒟_n(U).
3. (Z' is IM.)
   B is IM, so B − B is IM by (IS_U) applied to B and B.
   Then (B − B) − B is IM by (IS_U) applied to the IM currents B − B and B.
   Finally Z' = Z − ((B − B) − B) is IM by (IS_U) applied to the IM currents Z and (B − B) − B.
4. (Evaluation of Z'.) For every ω ∈ 𝒟^n(U), the pointwise action of subtraction gives Z'(ω) = Z(ω) − ((B(ω) − B(ω)) − B(ω)) = Z(ω) + B(ω). By C(N), Z(ω) = Σ_{i=0}^{N} Y_i(ω), so Z'(ω) = Σ_{i=0}^{N} Y_i(ω) + Y_{N+1}(ω) = Σ_{i=0}^{N+1} Y_i(ω) (Finset.sum_range_succ).
5. (Mass of Z'.) Fix G ⊆ ℝ^P.
   By step 4, Z'(ω) = Z(ω) + 1·B(ω) for every ω ∈ 𝒟^n(U), in particular for every ω with tsupport ω ⊆ G.
   Apply the sibling mass_triangle (Submission.cmc_fc_sl_massOn_le_add_of_eval_eq) with the sets U and G, the currents Z in the role of X, B in the role of Y and Z' in the role of Z, and the scalar c = 1 (|1| ≤ 1). It gives M_G(Z') ≤ M_G(Z) + M_G(B).
   By C(N), M_G(Z) ≤ Σ_{i=0}^{N} M_G(Y_i). By monotonicity of addition in [0, ∞], M_G(Z') ≤ Σ_{i=0}^{N} M_G(Y_i) + M_G(Y_{N+1}) = Σ_{i=0}^{N+1} M_G(Y_i) (Finset.sum_range_succ).
6. (Conclusion.) Steps 3–5 show that Z' witnesses C(N + 1). By induction C(N) holds for every N ∈ ℕ, which is the claim. ∎

## Key steps

1. Induction on N, with base case Z := Y_0.
2. Inductive step: Z' := Z − ((B − B) − B) with B := Y_{N+1}; three applications of (IS_U) show Z' is integer multiplicity.
3. Pointwise subtraction gives Z'(ω) = Z(ω) + B(ω) = Σ_{i=0}^{N+1} Y_i(ω) (Finset.sum_range_succ).
4. Sibling mass_triangle with c = 1, plus the induction hypothesis, gives M_G(Z') ≤ Σ_{i=0}^{N+1} M_G(Y_i).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n "massOn_add|massOn_sub|mass_add|mass_sub|massOn_le_add|triangle" project --glob '*.lean' (no match)`
- `rg -n "IsIntegerMultiplicity \(.* - .*\)|instance : Sub|boundaryMassOn" project/GMT/Ch07 --glob '*.lean'`
- `rg -n "instance : (Add|Neg|Sub|SMul)|massOn.*≤.*massOn.*\+|tsum_geometric|IsIntegerMultiplicity" project/GMT/Ch06 --glob '*.lean'`
- `rg -n "theorem (ENNReal\.)?tsum_geometric|theorem one_sub_inv_two|theorem tsum_mul_left|theorem tsum_add |theorem sum_le_tsum|theorem ofReal_add_le|theorem tsupport_smul_subset_right|theorem sqrt_sq_eq_abs|theorem sqrt_mul |theorem tendsto_nhds_unique |theorem tendsto_add_atTop_nat|theorem tendsto_atTop_mono |theorem prod_range_succ " mathlib/Mathlib --glob '*.lean'`
- `rg -n "tendsto_prod_nat|tendsto_sum_nat" mathlib/Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean; rg -n "theorem add_lt_top|theorem inv_le_one" mathlib/Mathlib/Basic/ENNReal/`
- `grep -n theorem/def massOn_mono, le_massOn, covectorEuclideanNorm_nonneg, covectorEuclideanNorm_neg, boundary_boundary, exteriorDerivativeTestOn in .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Mass,Currents}.lean (simongmt 2b366308)`
- `python3 -I scan of dag.json lean_statement/lean_name for massOn triangle or sum lemmas, collisions of cmc_fc_sl_massOn_le_add_of_eval_eq and cmc_fc_sl_im_partial_sum, and the frozen type of cmc_fc_series_current`
- `sed -n 895,915p and 2095,2140p book/chapter-06.txt (Simon 3.13 and proof of 7.2)`
- `lake env lean /tmp/sl-decomp-cmcfc/Types.lean, Children.lean, Assembly.lean, v2/TwoChildren.lean, v2/Final.lean (#print axioms); python3 -I exact-string comparison of frozen types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Tendsto.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-series-limit-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/sl-decomp-cmcfc/Types.lean`
- `/tmp/sl-decomp-cmcfc/Children.lean`
- `/tmp/sl-decomp-cmcfc/Assembly.lean`
- `/tmp/sl-decomp-cmcfc/v2/TwoChildren.lean`
- `/tmp/sl-decomp-cmcfc/v2/Final.lean`

Snapshot facts (project b4d606db, mathlib 25730c7c):
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.
- Neither the snapshot project nor the SimonGMT Chapter06 files contain a mass triangle inequality, an Add or Neg instance on GeometricCurrentOn, or a finite-sum integer multiplicity lemma. SimonGMT supplies only Zero, and the Ch07 contract supplies only Sub.
- Hence (F1) and the partial-sum construction A − ((B − B) − B) must be proved; they become the two children.

Cited tools found in the pinned sources:
- SimonGMT: GeometricCurrentOn.le_massOn, massOn_mono, covectorEuclideanNorm_nonneg, GeometricCurrentOn.boundary_boundary, exteriorDerivativeTestOn.
- Mathlib: ENNReal.ofReal_add_le, tsupport_smul_subset_right, Real.sqrt_mul, Real.sqrt_sq_eq_abs, Finset.sum_range_succ, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, ENNReal.sum_le_tsum, HasSum.tendsto_sum_nat, tendsto_add_atTop_nat, tendsto_atTop_mono, tendsto_nhds_unique.

DAG facts:
- The only related declaration is lcmp_massOn_le_add_of_eval_eq in the local_comparison branch. It is unaccepted and has the same content as child 1, so child 1 needs a fresh name.
- Both proposed names are unused.

Lean checks:
- Both child types elaborate after `import GMT.Ch07.Submission`.
- Both children are proved using only propext, Classical.choice and Quot.sound.
- The exact selected frozen type is proved from the two proved children plus the sibling cmc_fc_series_current. Its #print axioms output shows only series_current and the standard three.
