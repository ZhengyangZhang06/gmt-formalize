# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1.measure_locality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof ("S = T on the open set ℝ^P ∖ K', so μ_S = μ_T there"), which the supplied proof derives from im_mass_measure (c) on ℝ^P ∖ K'. Here it is derived instead from Simon Ch. 6, 3.2(3) (chapter-06.txt lines 763–765: M_W(τ(M, θ, ξ)) = ∫_{M∩W} θ dH^m for open W), in the form of sibling mass_support (dor_imrep_massOn_eq_measure_and_support), plus uniqueness of measures.
1. By mass_support with U = ℝ^P (open), S.massOn G = μ_{R_S}(G) and T.massOn G = μ_{R_T}(G) for every open G ⊆ ℝ^P.
2. For every open G ⊆ O, S.massOn G = T.massOn G. By definition (Simon 6.2.5, SimonGMT massOn), massOn G is the supremum of ofReal(S(ω)) over the set 𝒜(G) (massAdmissibleOn univ m G) of test forms ω with tsupport ω ⊆ G and |ω(x)|_E ≤ 1 for all x. The set 𝒜(G) is the same for S and T. For ω ∈ 𝒜(G), tsupport ω ⊆ G ⊆ O, so S(ω) = T(ω) by hypothesis. The two sets of values coincide, and so do their suprema.
3. Put ν_S := μ_{R_S}⌞O and ν_T := μ_{R_T}⌞O. For every open G, Measure.restrict_apply (G is measurable) and steps 1–2 applied to the open set G ∩ O ⊆ O give ν_S(G) = μ_{R_S}(G ∩ O) = S.massOn(G ∩ O) = T.massOn(G ∩ O) = μ_{R_T}(G ∩ O) = ν_T(G).
4. (Local finiteness.) For every n ∈ ℕ, ν_S(B(0, n)) ≤ μ_{R_S}(B̄(0, n)) = ∫⁻_{M_S∩B̄(0,n)} θ_S dH^m < ∞. This uses the field locallyIntegrable_mult of R_S on the compact set B̄(0, n), with withDensity_apply and Measure.restrict_restrict. The same holds for ν_T.
5. The open subsets of ℝ^P form a π-system generating the Borel σ-algebra (borel_eq_generateFrom_isOpen, isPiSystem_isOpen). Moreover ℝ^P = ⋃_n B(0, n), with each B(0, n) open and of finite ν_S-measure. Two measures that agree on a generating π-system containing such a countable cover are equal (Mathlib Measure.ext_of_generateFrom_of_iUnion). By step 3, ν_S = ν_T. ∎

## Key steps

1. Mass equals weight on open sets (sibling mass_support).
2. The masses of S and T agree on open subsets of O, since the admissible forms and their values coincide.
3. So the restricted weights agree on all open sets. Both are finite on balls, hence they are equal by π-system uniqueness.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `cat nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projection-a1/{parent-child-handoff.json,decomposition-v1.json,decomposition-audit-v1.json,decomposition-review-receipt-v1.json}`
- `python3 over dag.json: status counts; lean names, types and statuses of all nodes matching tangent|bilipschitz|pushforward|area; every node whose lean_statement contains HasApproximateTangentSpaceAt; accepted nodes that construct an IMRep or IsIntegerMultiplicity. Found: dpf_approxTangent_ae_bilipschitz_piece decomposing; dpf_rectifiable_bilipschitz_pieces rlcr-lean; no accepted existence theorem for tangent planes of Lipschitz images.`
- `python3 over dag.json: statuses and byte-identity of the six reused types; scan for dimred_cs_sp_* names`
- `grep -n '^theorem|^def' over SimonGMT Chapter03/*.lean; Chapter02/{AreaBranches,AreaNoninjective,AreaLipschitz,Area,AreaApproximation,AreaNormalization,Lipschitz}.lean; Chapter01/{DensityComparison,Densities,Hausdorff}.lean`
- `sed AreaBranches.lean 1–160, AreaLipschitz.lean 1–140, Area.lean 1–110, Rectifiable.lean 20–250, DensityComparison.lean 290–420, AffineCurrentPushforward.lean 35–90, Forms.lean 25–60, Mass.lean 25–75`
- `rg -i 'approximation theorem|c1_approx' in SimonGMT Chapter02 (no match: the C^1 Approximation Theorem of Simon Ch. 2, 1.5 is absent)`
- `grep in the Mathlib snapshot: exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (MeasureTheory/Function/Jacobian.lean:255); NormDet.lean 290–440; Geometry/Euclidean/Volume/Measure.lean 125–200; Covering/DensityTheorem.lean 140–160; Determinant.lean (AlternatingMap.eq_smul_basis_det, Module.Basis.det_apply); Constructions/Polish/Basic.lean:821`
- `for f in Jacobian NormDet Volume/Measure DensityTheorem Determinant Alternating/Basic Polish/Basic FiniteDimension: cmp snapshot mathlib file vs .lake/packages/mathlib (all identical); rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|theorem normDet_comp |theorem ae_tendsto_average_norm_sub|theorem AlternatingMap.eq_smul_basis_det|theorem MeasurableSet.image_of_continuousOn_injOn' .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -i 'cauchy.binet' in the Mathlib snapshot (no match)`
- `python3 + git show <candidate_commit>:GMT/Ch07/Submission.lean for 419 accepted candidates: import headers. 407 use the contract header only; 5 add Poincare.SimonGMT.Chapter02.AreaLipschitz; 2 add Poincare.SimonGMT.Chapter01.DensityComparison.`
- `sed -n 1,200p book/chapter-03.txt; sed -n 755,880p book/chapter-06.txt; grep item line numbers in chapter-01/02/03/06`
- `lake env lean /tmp/sp-decomp-v2/Types.lean (12 child types)`
- `lake env lean /tmp/sp-decomp-v2/Assembly.lean (frozen parent type from the 12 child propositions; #print axioms)`
- `lake env lean /tmp/sp-decomp-v2/Api.lean and Api2.lean (#check of every library lemma cited by the new imrep_pushforward proof, under the contract imports plus AreaLipschitz and DensityComparison)`
- `lake env lean /tmp/sp-decomp-v2/Inst.lean (IsUnifLocDoublingMeasure instance for volume on Euclid m; affinePullbackForm unfolding; pp.coercions)`
- `grep -l dimred_cs_sp_ over nodes/, GMT/, SimonGMT and the Submission.lean files of the 3029 .swarm-worktrees`
- `independent adversarial review subagent on /tmp/sp-decomp-v2/imrep_proof.txt (verdict ACCEPT; four minor notes incorporated)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projection-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projection-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projection-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-subspace-projection-a1/decomposition-review-receipt-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaBranches.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/sp-decomp-v2/Types.lean`
- `/tmp/sp-decomp-v2/Assembly.lean`
- `/tmp/sp-decomp-v2/Api.lean`
- `/tmp/sp-decomp-v2/Api2.lean`
- `/tmp/sp-decomp-v2/Inst.lean`
- `/tmp/sp-decomp-v2/imrep_proof.txt`

Pins and contract.
- The snapshot pins match: project b4d606d (= workspace HEAD), mathlib 25730c7c, simongmt 2b36630.
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

No reusable (TF) or quantitative partition in the DAG.
- dpf_approxTangent_ae_bilipschitz_piece is still decomposing.
- dpf_rectifiable_bilipschitz_pieces is in rlcr-lean.
- No accepted DAG node proves that approximate tangent planes exist along Lipschitz images.
- So (TF) and the quantitative partition are proved inside the imrep_pushforward proof (A5–A7) and cite no DAG declaration.

Pinned library support.
- The SimonGMT injective Lipschitz area formula: weighted_area_formula_lipschitz_injOn.
- The SimonGMT regular-set facts and the Lipschitz image bound.
- The upper density theorem: simon_remark_3_7_hausdorff, with its normalization lemmas.
- Mathlib's approximately linear partition (Jacobian.lean), normDet API, Lebesgue differentiation, Lusin–Souslin and alternating-map determinant lemmas.
- Every cited name elaborates once the two extra SimonGMT imports are added, and accepted submissions already add those imports.
- SimonGMT lacks the C^1 Approximation Theorem, so Simon's own route to (TF) is unavailable; the departure is stated in the proof.

Reused declarations. The six reused declarations remain accepted, with byte-identical types.

Lean checks.
- All 12 child types elaborate.
- The frozen parent type is proved from the 12 child propositions using only the standard axioms.
- No new name collides with anything in the DAG, the project or the swarm worktrees.
