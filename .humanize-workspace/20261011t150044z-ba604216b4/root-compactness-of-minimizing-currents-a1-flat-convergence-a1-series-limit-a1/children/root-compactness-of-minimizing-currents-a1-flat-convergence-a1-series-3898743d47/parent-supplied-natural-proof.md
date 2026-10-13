# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.series_limit-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.series_limit-a1.mass_triangle-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 (F1) of the parent proof, where the admissible form ω is replaced by ±ω. Here the sign is generalized to a scalar c with |c| ≤ 1.

Fix P, n, U, G, X, Y, Z and c with |c| ≤ 1. Assume (H): Z(ω) = X(ω) + c·Y(ω) for every ω ∈ 𝒟^n(U) with tsupport ω ⊆ G. Write A_G := massAdmissibleOn U n G for the set of forms admissible for M_G.

1. (Scaling of the coefficient norm.) For every n-covector α on ℝ^P, |c·α| = |c|·|α|.
   By definition |α| = √(Σ_I s_I(α)), summed over all I : Fin n → Fin P. Here s_I(α) = (α(e_{I(1)}, …, e_{I(n)}))² if I is strictly increasing and s_I(α) = 0 otherwise, where e_j is the standard orthonormal basis (EuclideanSpace.basisFun).
   Since (c·α)(v) = c·α(v) for every tuple v, we get s_I(c·α) = c²·s_I(α) for every I: both sides are 0 when I is not strictly increasing, and (c·t)² = c²·t² otherwise.
   Summing, Σ_I s_I(c·α) = c²·Σ_I s_I(α) (Finset.mul_sum).
   Since c² ≥ 0 and Σ_I s_I(α) ≥ 0, √(c²·Σ_I s_I(α)) = √(c²)·√(Σ_I s_I(α)) = |c|·|α| (Real.sqrt_mul, Real.sqrt_sq_eq_abs).
2. (c·ω is admissible.) Let ω ∈ A_G.
   𝒟^n(U) is a real vector space (TestFormOn U n is a submodule), so c·ω ∈ 𝒟^n(U), and as a form (c·ω)(x) = c·ω(x) for every x.
   Wherever ω vanishes, c·ω vanishes too, so tsupport(c·ω) ⊆ tsupport ω ⊆ G (tsupport_smul_subset_right).
   For every x, step 1 gives |(c·ω)(x)| = |c|·|ω(x)| ≤ 1·1 = 1, using |c| ≤ 1 and 0 ≤ |ω(x)| ≤ 1 (covectorEuclideanNorm_nonneg).
   Hence c·ω ∈ A_G.
3. (Bound at one admissible form.) Let ω ∈ A_G.
   The action of Y on 𝒟^n(U) is ℝ-linear (Y.toCurrent is a linear map), so Y(c·ω) = c·Y(ω).
   Since tsupport ω ⊆ G, (H) gives Z(ω) = X(ω) + c·Y(ω) = X(ω) + Y(c·ω).
   For all real s, t, ENNReal.ofReal(s + t) ≤ ENNReal.ofReal(s) + ENNReal.ofReal(t) (ENNReal.ofReal_add_le). Hence ofReal(Z(ω)) ≤ ofReal(X(ω)) + ofReal(Y(c·ω)).
   The mass is the supremum of the admissible evaluations, so each admissible evaluation is bounded by it (GeometricCurrentOn.le_massOn). Since ω ∈ A_G, ofReal(X(ω)) ≤ M_G(X). Since c·ω ∈ A_G by step 2, ofReal(Y(c·ω)) ≤ M_G(Y).
   Adding, by monotonicity of + in [0, ∞], ofReal(Z(ω)) ≤ M_G(X) + M_G(Y).
4. (Supremum.) By definition M_G(Z) = sup{ofReal(Z(ω)) : ω ∈ A_G}. By step 3 every element of this set is ≤ M_G(X) + M_G(Y), so M_G(Z) ≤ M_G(X) + M_G(Y) (sSup_le). ∎

## Key steps

1. Scaling: covectorEuclideanNorm(c·α) = |c|·covectorEuclideanNorm(α), since c² factors out of every coefficient square and √(c²) = |c|.
2. If ω is admissible for M_G then so is c·ω: tsupport(c·ω) ⊆ tsupport ω ⊆ G and |c·ω(x)| ≤ |c|·1 ≤ 1.
3. For admissible ω, Z(ω) = X(ω) + Y(c·ω), so ofReal(Z(ω)) ≤ ofReal(X(ω)) + ofReal(Y(c·ω)) ≤ M_G(X) + M_G(Y) (ENNReal.ofReal_add_le, GeometricCurrentOn.le_massOn).
4. Take the supremum over admissible ω (sSup_le).

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
