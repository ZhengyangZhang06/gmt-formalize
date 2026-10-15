# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.series_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 6–7 of the parent proof, i.e. Simon Ch. 6, proof of 7.2 (chapter-06.txt lines 2117–2131: "by 3.13 we can define integer multiplicity R^{(ℓ)}, S^{(ℓ)} by the M-absolutely convergent series R^{(ℓ)} = Σ_{r≥ℓ} R_r, S^{(ℓ)} = Σ_{r≥ℓ} S_r; then M(R^{(ℓ)}) + M(S^{(ℓ)}) ≤ 2^{−ℓ+1} and (from (5)) T − T_{j_ℓ} = ∂R^{(ℓ)} + S^{(ℓ)}"). In the parent, X_r = T'_{j_r} (the localised currents), Z_r = T_{j_r}, Y = T and V is the region where they agree. As in the parent, the identity holds only on forms supported in V. A global integer multiplicity error current comes from boundary rectifiability (parent step 7). The bound M(∂R^{(q)}) < ∞ is obtained by evaluating the telescoping identity directly; this is the same estimate that the parent obtains from lower semicontinuity.
Siblings used: (SE) dtc_bc_lc_fd_series; (BR) dtc_bc_lc_fd_boundary_im; (IC) cmc_imRep_locality_restrict_sub (c). For a current X with M(X) < ∞ and ω with |ω(x)| ≤ 1 for all x, |X(ω)| ≤ M(X): apply the definition of M to ω and to −ω.

Fix q.
1. (Masses.) M(R_r) ≤ 2^{−r} and M(S_r) ≤ 2^{−r}, and Σ_{i≥0} 2^{−(q+i)} = 2·2^{−q} < ∞.
2. (Series.) Apply (SE) in degree m + 2 = (m + 1) + 1 to (R_{q+i})_i. It gives R^{(q)} ∈ 𝒟_{n+1}(ℝ^P) with HasSum (i ↦ R_{q+i}(ω')) (R^{(q)}(ω')) for every ω' and M(R^{(q)}) ≤ Σ_i M(R_{q+i}). Also spt R^{(q)} ⊆ closure(⋃_i spt R_{q+i}) ⊆ L, since L is compact, hence closed. R^{(q)} is integer multiplicity because every R_r is. Apply (SE) in degree m + 1 to (S_{q+i})_i. It gives S^{(q)} ∈ 𝒟_n(ℝ^P) with HasSum (i ↦ S_{q+i}(ω)) (S^{(q)}(ω)) and M(S^{(q)}) ≤ Σ_i M(S_{q+i}) < ∞.
3. (Telescoping.) Let ω ∈ 𝒟ⁿ(ℝ^P). For every r, evaluating X_{r+1} − X_r − S_r = ∂R_r at ω gives R_r(dω) = X_{r+1}(ω) − X_r(ω) − S_r(ω). Summing over r = q, …, q + N − 1 gives X_{q+N}(ω) = X_q(ω) + Σ_{i<N} R_{q+i}(dω) + Σ_{i<N} S_{q+i}(ω). By step 2 and ∂R^{(q)}(ω) = R^{(q)}(dω):
 (#) X_{q+N}(ω) → X_q(ω) + ∂R^{(q)}(ω) + S^{(q)}(ω) as N → ∞, for every ω.
4. (Finite boundary mass.) Let ω be admissible for M, i.e. |ω(x)| ≤ 1. Then |X_r(ω)| ≤ M(X_r) ≤ Λ and −S^{(q)}(ω) ≤ M(S^{(q)}). By (#), X_q(ω) + ∂R^{(q)}(ω) + S^{(q)}(ω) = lim_N X_{q+N}(ω) ≤ Λ, so ∂R^{(q)}(ω) ≤ 2Λ + M(S^{(q)}). Hence M(∂R^{(q)}) ≤ 2Λ + M(S^{(q)}) < ∞.
5. (Boundary rectifiability.) spt R^{(q)} is closed, being the complement of the open zero region, and it lies in the compact set L, so it is compact. Also M(R^{(q)}) < ∞ (step 2), M(∂R^{(q)}) < ∞ (step 4) and m + 1 < P. By (BR), ∂R^{(q)} is integer multiplicity.
6. (Identity on V.) Let tsupport ω ⊆ V. Then X_r(ω) → Y(ω), so by (#) and uniqueness of limits, Y(ω) = X_q(ω) + ∂R^{(q)}(ω) + S^{(q)}(ω) = Z_q(ω) + ∂R^{(q)}(ω) + S^{(q)}(ω), using Z_q(ω) = X_q(ω). (★)
7. (The decomposition.) Put R' := R^{(q)} and S' := Y − Z_q − ∂R^{(q)}. R' is integer multiplicity (step 2). S' is integer multiplicity by (IC)(c) applied twice, since Y, Z_q and ∂R^{(q)} are integer multiplicity. For every ω, (Y − Z_q − S')(ω) = Y(ω) − Z_q(ω) − (Y(ω) − Z_q(ω) − ∂R^{(q)}(ω)) = ∂R'(ω), so Y − Z_q − S' = ∂R'.
8. (Masses on V.) Let ω be admissible for M_V (tsupport ω ⊆ V, |ω| ≤ 1). Then S'(ω) = S^{(q)}(ω) by (★), and ω is admissible for M; so M_V(S') ≤ M(S^{(q)}). Also M_V(R') ≤ M(R^{(q)}) by monotonicity. Hence M_V(R') + M_V(S') ≤ Σ_i M(R_{q+i}) + Σ_i M(S_{q+i}) = Σ_i (M(R_{q+i}) + M(S_{q+i})) ≤ Σ_i 2^{−(q+i)} = 2·2^{−q}. ∎

## Key steps

1. R^{(q)} := Σ_i R_{q+i} (integer multiplicity, spt ⊆ L) and S^{(q)} := Σ_i S_{q+i} come from the series sibling; their masses sum to at most 2·2^{−q}.
2. Telescoping: X_{q+N}(ω) → X_q(ω) + ∂R^{(q)}(ω) + S^{(q)}(ω) for every ω.
3. Hence M(∂R^{(q)}) ≤ 2Λ + M(S^{(q)}) < ∞, and boundary_im makes ∂R^{(q)} integer multiplicity.
4. On forms supported in V, Y = Z_q + ∂R^{(q)} + S^{(q)}. So S' := Y − Z_q − ∂R^{(q)} is integer multiplicity, Y − Z_q − S' = ∂R^{(q)}, and M_V(R^{(q)}) + M_V(S') ≤ M(R^{(q)}) + M(S^{(q)}) ≤ 2·2^{−q}.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c)`
- `rg -l 'DeformationTheorem|FlatConvergenceIffWeakConvergence|BoundaryRectifiability|SlicingTheorem|flatDistance' local-references/123e8435b4a2469b/project -g '*.lean' (only GMT/Ch06/Contract.lean and Submission.lean: sorry-based statements in namespace GMT.Ch06, not importable from GMT.Ch07); rg 'deform|flatDistance|IsSlice|BoundaryRectifiability' local-references/123e8435b4a2469b/project/GMT/Ch07 (no match)`
- `sed -n 95,362p local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean (formulations IsSlice, latticeFace, IsLatticeChain, DeformationTheorem, BoundaryRectifiability, FlatConvergenceIffWeakConvergence; used only as formulation reference)`
- `grep declarations in .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,Forms,WedgeForms,AffineCurrentPushforward}.lean and Chapter03/Rectifiable.lean: GeometricCurrentOn, Zero instance, boundary_apply, massAdmissibleOn, massOn, mass, le_massOn, massOn_mono, WeaklyConvergesOn.massOn_le_liminf, covectorEuclideanNorm_neg, zeroRegion/support, isOpen_zeroRegion, affinePushforward, countablyRectifiable_of_measure_zero (no deformation theorem, slicing, flat norm, completeness or boundary rectifiability)`
- `python3 -I scans of the run dag.json (995 nodes): non-accepted related nodes cmc_flat_convergence, cmc_deformation_theorem, cmc_closure_and_boundary_rectifiability, cmcdt_im_series, cmc_fc_series_current, cmc_fc_localize, cmc_fc_total_bounded, dimred_mbl_flat_convergence, dimred_mbl_deformation_theorem, dor_lmb_flat_convergence_cycles and children; accepted helpers cmc_imRep_locality_restrict_sub, dtc_mass_eq_measure, cmc_fc_cs_diagonal_subseq, dtc_vanish_off_support, rsd_cmr_support_subset_of_vanish, cmcs_slice_mass_integral (also seen, not needed: cmc_fc_cauchy_subseq, cmcs_cutoff_defect_bound, lcmp_massOn_le_of_vanish_off_compact, cmc_fc_tb_massOn_sub_le); collision check of the six dtc_bc_lc_fd_ names (none)`
- `git show <candidate commit>:GMT/Ch07/Submission.lean for the six reused declarations (2af75d6, bff81d3, b046f22, 44ef61f, 02c6122, 9dfa657); whitespace-normalised type comparison with my strings and the DAG (all identical); grep sorry/axiom (only the frozen root theorem, no axiom declarations)`
- `rg in local-references/123e8435b4a2469b/mathlib: tendsto_of_subseq_tendsto (Order/Filter/AtTopBot/CountablyGenerated.lean:125), ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (Analysis/SpecificLimits/Basic.lean:273), IsCompact.cthickening (Topology/MetricSpace/Thickening.lean:283), tendsto_add_atTop_iff_nat (Order/Filter/AtTopBot/Basic.lean:337), Real.smoothTransition (Analysis/SpecialFunctions/SmoothTransition.lean)`
- `lake env lean /tmp/fdsplit_check/Types.lean; /tmp/fdsplit_check/Challenges.lean (12 children in comparator challenge form); /tmp/fdsplit_check/Print.lean (pp.coercions); /tmp/fdsplit_check/AllChecks.lean (fd_assembly, fd_cauchy_from, fd_series_limit_from with #print axioms)`
- `sed book/chapter-06.txt lines 875-1150 (3.11-3.16), 1335-1500 (4.6-5.4), 1925-2160 (6.1-7.2), 2296-2335 (8.2-8.3); book/chapter-03.txt lines 551-606 (4.1-4.3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/WedgeForms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-21d9fb1dcd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-mass-eq-measure-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-cauchy-81bbc80940/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-mass-integral-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/fdsplit_check/stmts.json`
- `/tmp/fdsplit_check/Types.lean`
- `/tmp/fdsplit_check/Challenges.lean`
- `/tmp/fdsplit_check/AllChecks.lean`

The pinned snapshot has no deformation theorem, slicing, flat norm, completeness lemma or boundary rectifiability usable from GMT.Ch07. The snapshot's Ch06 contract only states them (sorry-based, namespace GMT.Ch06) and served as a formulation reference. SimonGMT provides currents, boundary, massOn/mass, support/zero region, weak convergence with lower semicontinuity of mass, affine push-forward and countablyRectifiable_of_measure_zero. Six accepted DAG declarations are reused with identical types and the six new names are unique. The flat-convergence, deformation and closure nodes of the cmc, dimred_mbl and dor_lmb branches are not accepted, so they are not reused. deformation, boundary_im and series are stated so that they follow from cmc_deformation_theorem, from the BR conjunct of cmc_closure_and_boundary_rectifiability and from cmcdt_im_series. All Mathlib names used in the Lean checks exist at the pin. The checks prove this node's frozen type from the children, and cauchy_subseq and series_limit from their declared siblings, using only propext, Classical.choice and Quot.sound.
