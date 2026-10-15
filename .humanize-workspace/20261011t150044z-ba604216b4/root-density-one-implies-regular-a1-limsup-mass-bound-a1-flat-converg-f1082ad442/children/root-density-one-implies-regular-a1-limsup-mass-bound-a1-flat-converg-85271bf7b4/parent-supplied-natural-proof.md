# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.total_bounded-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.total_bounded-a1.eq_of_vanish_off-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3(d) of the parent proof. That step proves ∂Ǎ = Ž with a cutoff ζ ∈ C_c^∞(U) equal to 1 on an open V ⊇ K. Here the same cutoff argument is stated for two arbitrary currents vanishing off K and is carried out through the vanishing property instead of the integral representations.
1. Choice of the cutoff. Since K is compact, U is open and K ⊆ U, there is δ > 0 with C := cthickening δ K ⊆ U (IsCompact.exists_cthickening_subset_open). C is closed, and compact because ℝ^P is proper (IsCompact.cthickening). Also K ⊆ thickening δ K (self_subset_thickening, using δ > 0), and thickening δ K is open and contained in C (isOpen_thickening, thickening_subset_cthickening), so K ⊆ interior C (interior_maximal). K is closed. Apply the smooth Urysohn lemma on the Hausdorff, σ-compact, finite-dimensional manifold ℝ^P: Mathlib's exists_contMDiffMap_one_nhds_of_subset_interior, with model modelWithCornersSelf ℝ (Euclid P) (written 𝓘(ℝ, ℝ^P) under open scoped Manifold, which the contract scope does not open) and order ⊤ : ℕ∞, built from a smooth partition of unity. It gives a smooth f : ℝ^P → ℝ with values in [0, 1] such that f = 1 on a neighbourhood of K and f(x) = 0 for x ∉ C. Let ζ := f. Then ζ is C^∞ as a map ℝ^P → ℝ (contMDiff_iff_contDiff). The support of ζ lies in the closed set C, so tsupport ζ ⊆ C ⊆ U (closure_minimal), and ζ has compact support, being supported in the compact set C. Since {x : ζ(x) = 1} is a neighbourhood of K, there is an open set V with K ⊆ V and ζ = 1 on V (mem_nhdsSet_iff_exists).
2. Fix ω ∈ 𝒟^d(ℝ^P) with underlying form w, and put η(x) := ζ(x)·w(x). Then η is smooth (ContDiff.smul) and tsupport η ⊆ tsupport ζ (tsupport_smul_subset_left). So η has compact support and tsupport η ⊆ C ⊆ U. Hence η defines a test form η_U ∈ 𝒟^d(U), and ιη_U ∈ 𝒟^d(ℝ^P) has underlying form η.
3. The test form ω − ιη_U ∈ 𝒟^d(ℝ^P) has underlying form x ↦ w(x) − ζ(x)w(x) = (1 − ζ(x))·w(x), which is 0 at every x ∈ V. So its support lies in the closed set ℝ^P ∖ V, and so does its tsupport (closure_minimal). Since K ⊆ V, its tsupport is disjoint from K.
4. X is linear and vanishes off K, so by step 3, X(ω) = X(ιη_U) + X(ω − ιη_U) = X(ιη_U). In the same way, Y(ω) = Y(ιη_U).
5. By the definition of restrictDomain and the hypothesis X⌞U = Y⌞U, X(ιη_U) = (X⌞U)(η_U) = (Y⌞U)(η_U) = Y(ιη_U). With step 4, X(ω) = Y(ω).
6. Since ω ∈ 𝒟^d(ℝ^P) was arbitrary, X = Y (GeometricCurrentOn.ext). ∎

## Key steps

1. Choose δ > 0 with cthickening δ K ⊆ U, and by the smooth Urysohn lemma a smooth ζ: ℝ^P → [0, 1] with ζ = 1 on an open V ⊇ K and ζ = 0 off cthickening δ K; then ζ has compact support in U.
2. For ω ∈ 𝒟^d(ℝ^P), ζω is a test form supported in U, and ω − ζω vanishes on V, so its tsupport misses K.
3. Since X and Y vanish off K, X(ω) = X(ζω) = (X⌞U)(ζω) = (Y⌞U)(ζω) = Y(ζω) = Y(ω); conclude by extensionality.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean GMT/Ch07/Submission.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (all identical)`
- `rg -n 'theorem exists_.*zero_one|theorem exists_.*_one_of_isClosed|theorem exists_msmooth|theorem exists_contMDiff' local-references/123e8435b4a2469b/mathlib/Mathlib (exists_contMDiffMap_one_nhds_of_subset_interior at Geometry/Manifold/PartitionOfUnity.lean:526)`
- `rg -n 'cthickening_subset_open|exists_thickening_subset_open|IsCompact.cthickening|isCompact_cthickening' local-references/123e8435b4a2469b/mathlib/Mathlib (Topology/MetricSpace/Thickening.lean:283, 426)`
- `rg -n 'theorem exists_contDiff_tsupport_subset|theorem IsOpen.exists_contDiff_support_eq' local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `rg -n 'theorem norm_apply_le' local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean (line 713)`
- `grep -n 'restrictDomain|testFormOnInclusion|GeometricCurrentOn.ext|zero_apply|boundary_apply|tsupport_exteriorDerivative_subset|exteriorDerivativeTestOn|def massOn|def mass|massAdmissibleOn|abbrev Covector|abbrev DifferentialForm|def IsTestForm' simongmt/Poincare/SimonGMT/Chapter06/{Currents,CurrentLocalEquality,Mass,Forms}.lean`
- `grep -n 'def CountablyRectifiable|theorem countablyRectifiable_of_measure_zero' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `python3 -I scans of runs/20261011T150044Z-ba604216b4/dag.json: frozen types and status of dor_lmb_fc_total_bounded, dor_lmb_fc_deformation, dor_lmb_fc_deformation_top (decomposing), dor_imrep_massOn_eq_measure_and_support, cmc_imRep_locality_restrict_sub, dtc_restrictDomain_isIntegerMultiplicity (accepted; byte-identical types); related accepted dtc_extend_by_zero, dtc_imrep_of_null_off_compact, dtc_imrep_current, dtc_massOn_eq_of_agreeOn, dtc_vanish_off_support, imrep_carrier_sdiff_support_null, dgcr_bwd_normal_cutoff; grep of the six dor_lmb_fc_tb_* names in dag.json, nodes/, GMT/, simongmt (no match)`
- `python3 -I parse of nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/decomposition-v2.json and nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-total-bounded-a1/decomposition-v1.json (reuse-entry format for imrep_mass, im_calculus, restrict_im)`
- `sed -n 2040,2095p book/chapter-06.txt (Simon Ch. 6, proof of Theorem 7.2, (1)-(3))`
- `verifier/gmt-compare.py contract_scope/child_modules replay + lean_contract.validate_lean_statement -> /tmp/tb-decomp/lean/Challenge_*.lean; lake env lean on each (0 errors)`
- `lake env lean /tmp/tb-decomp/lean/All.lean with #print axioms (components TBCheck.lean, FCheck.lean, ACheck.lean, B.lean, CCheck.lean, DE.lean); independent reviewer replay /tmp/tb-review/Faithful.lean in the exact comparator scope (exit 0)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-f1082ad442/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-total-bounded-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1-restrict-im-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/tb-decomp/lean/All.lean`
- `/tmp/tb-decomp/lean/Challenge_cell_chains_finite.lean`
- `/tmp/tb-decomp/lean/Challenge_extend_univ.lean`
- `/tmp/tb-decomp/lean/Challenge_eq_of_vanish_off.lean`
- `/tmp/tb-decomp/lean/Challenge_extend_boundary.lean`
- `/tmp/tb-decomp/lean/Challenge_zero_im.lean`
- `/tmp/tb-decomp/lean/Challenge_high_degree_zero.lean`
- `/tmp/tb-decomp/lean/Challenge_restrict_im.lean`

Snapshot: project b4d606db and mathlib 25730c7c. The snapshot's Contract.lean and Submission.lean are byte-identical to the workspace files.

Neither SimonGMT nor the snapshot has extension-by-zero, cutoff-uniqueness, cube-chain finiteness, zero-IM or high-degree-vanishing lemmas for GeometricCurrentOn. The DAG has related accepted declarations (dtc_extend_by_zero, dtc_imrep_of_null_off_compact, dtc_massOn_eq_of_agreeOn), but their types differ: support-based hypotheses, no mass bound. The only exact matches are the three reused accepted declarations dor_imrep_massOn_eq_measure_and_support, cmc_imRep_locality_restrict_sub and dtc_restrictDomain_isIntegerMultiplicity, whose types are byte-identical.

Mathlib in the snapshot supplies everything the child proofs cite:
- exists_contMDiffMap_one_nhds_of_subset_interior with model modelWithCornersSelf ℝ (Euclid P), and contMDiff_iff_contDiff;
- IsCompact.exists_cthickening_subset_open and IsCompact.cthickening;
- PiLp.norm_apply_le, Set.Finite.pi and Set.Finite.of_finite_image;
- LinearIndependent.fintype_card_le_finrank and AlternatingMap.map_linearDependent;
- countablyRectifiable_of_measure_zero (SimonGMT Chapter03).

The six new names are fresh. All nine child types elaborate as exact comparator challenges with 0 errors. All.lean shows that the children, together with deformation and deformation_top, imply the exact frozen selected type. Four children are fully proved with standard axioms, and sorry appears only in the five assumed external declarations. An independent reviewer returned ACCEPT.
