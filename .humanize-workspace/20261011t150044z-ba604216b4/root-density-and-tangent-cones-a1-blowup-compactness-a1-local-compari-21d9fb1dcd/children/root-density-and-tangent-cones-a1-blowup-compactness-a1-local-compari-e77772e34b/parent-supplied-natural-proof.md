# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.cauchy_subseq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof, i.e. Simon Ch. 6, proof of 7.2 (chapter-06.txt lines 2102–2116: "apply (1) with ε = 1, 1/2, 1/4 etc. to extract a subsequence {T_{j_r}} … such that d_W̃(T_{j_{r+1}}, T_{j_r}) < 2^{−r} and hence (5) T_{j_{r+1}} − T_{j_r} = ∂R_r + S_r … M(R_r) + M(S_r) ≤ 1/2^r"). As in the parent, the error currents S need not be integer multiplicity. The condition spt R ⊆ L is carried along for the sibling series_limit.
Siblings used: (IC) cmc_imRep_locality_restrict_sub (c); (DG) cmc_fc_cs_diagonal_subseq; (VO) dtc_vanish_off_support; (SV) rsd_cmr_support_subset_of_vanish.

1. (Nets.) For r ∈ ℕ put ε_r := 2^{−(r+1)} > 0. By hypothesis there is a finite 𝒬_r, and for every j a choice of Q_r(j) ∈ 𝒬_r, an integer multiplicity R_{r,j} with spt R_{r,j} ⊆ L and a current S_{r,j}, with X_j − Q_r(j) − S_{r,j} = ∂R_{r,j} and M(R_{r,j}) + M(S_{r,j}) ≤ 2^{−(r+1)}.
2. (Relation.) For r, j, l ∈ ℕ let C(r, j, l) be the statement: there are an integer multiplicity R with spt R ⊆ L and a current S with X_j − X_l − S = ∂R and M(R) + M(S) ≤ 2^{−r}.
3. (Pigeonhole.) Let r ∈ ℕ and let I ⊆ ℕ be infinite. Then I ⊆ ⋃_{Q∈𝒬_r} {j ∈ I : Q_r(j) = Q}, a finite union. So for some Q the set J := {j ∈ I : Q_r(j) = Q} ⊆ I is infinite.
4. (Pairs in J.) Let j, l ∈ J, so Q_r(j) = Q_r(l) = Q. Put R := R_{r,j} − R_{r,l} and S := S_{r,j} − S_{r,l}.
 (a) R is integer multiplicity by (IC)(c), since ℝ^P is open.
 (b) For every ω, evaluate the two decompositions of step 1 at ω and subtract: X_j(ω) − X_l(ω) − (S_{r,j}(ω) − S_{r,l}(ω)) = ∂R_{r,j}(ω) − ∂R_{r,l}(ω). The contract's subtraction acts pointwise, ∂ is linear, and currents are determined by their values, so X_j − X_l − S = ∂R.
 (c) If tsupport ω is disjoint from L, it is disjoint from spt R_{r,j} and from spt R_{r,l}. So R_{r,j}(ω) = R_{r,l}(ω) = 0 by (VO), and R(ω) = 0. By (SV), with L compact, spt R ⊆ L.
 (d) For any currents A, B and any set G, M_G(A − B) ≤ M_G(A) + M_G(B). Indeed, for admissible ω, ofReal(A(ω) − B(ω)) ≤ ofReal A(ω) + ofReal B(−ω), and −ω is admissible (|−α| = |α|, tsupport(−ω) = tsupport ω). Hence M(R) + M(S) ≤ (M(R_{r,j}) + M(S_{r,j})) + (M(R_{r,l}) + M(S_{r,l})) ≤ 2·2^{−(r+1)} = 2^{−r}.
 So C(r, j, l) holds for all j, l ∈ J, including j = l.
5. (Diagonal.) By steps 3 and 4 the relation C satisfies the hypothesis of (DG). (DG) gives a strictly increasing φ with C(r, φ(r + 1), φ(r)) for every r, which is the claim. ∎

## Key steps

1. For each r, choose 2^{−(r+1)}-nets 𝒬_r and decompositions X_j − Q_r(j) − S_{r,j} = ∂R_{r,j}.
2. Pigeonhole: every infinite I ⊆ ℕ contains an infinite J on which j ↦ Q_r(j) is constant.
3. For j, l ∈ J, subtract: X_j − X_l − (S_{r,j} − S_{r,l}) = ∂(R_{r,j} − R_{r,l}), integer multiplicity, support in L, total mass ≤ 2^{−r}.
4. The diagonal lemma cmc_fc_cs_diagonal_subseq gives a strictly increasing φ whose consecutive terms are related.

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
