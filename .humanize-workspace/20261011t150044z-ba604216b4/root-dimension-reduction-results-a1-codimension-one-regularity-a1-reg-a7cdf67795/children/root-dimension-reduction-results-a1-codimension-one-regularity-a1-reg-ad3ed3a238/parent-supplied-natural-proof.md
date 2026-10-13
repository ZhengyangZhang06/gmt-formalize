# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.bv_compactness-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.bv_compactness-a1.close_subset-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof step 4 ('every sequence in a totally bounded subset has a Cauchy … subsequence'): this is the pigeonhole step behind it, in the form required by the diagonal lemma (sibling diagonal_subseq). Measures are extended reals (ENNReal); no measurability is needed (only monotonicity and subadditivity of the outer measure).

1. Apply the hypothesis with R := r + 1 > 0 and θ := (1/2)^{r+1} > 0. This gives a finite S ⊆ ℕ and, choosing for each k one such i, a function c : ℕ → ℕ with c(k) ∈ S and L((F_k Δ F_{c(k)}) ∩ B_{r+1}) < ENNReal.ofReal((1/2)^{r+1}) = 2^{−(r+1)} for all k.
2. I ⊆ ⋃_{s∈S} (I ∩ c⁻¹({s})) because c(k) ∈ S for every k. If each of these finitely many sets were finite, their union, and hence I, would be finite. So there is s ∈ S such that J := I ∩ c⁻¹({s}) is infinite; clearly J ⊆ I.
3. Let j, l ∈ J, so c(j) = c(l) = s. Since F_j Δ F_l ⊆ (F_j Δ F_s) ∪ (F_s Δ F_l) and F_s Δ F_l = F_l Δ F_s, monotonicity and subadditivity give L((F_j Δ F_l) ∩ B_{r+1}) ≤ L((F_j Δ F_s) ∩ B_{r+1}) + L((F_l Δ F_s) ∩ B_{r+1}) ≤ 2^{−(r+1)} + 2^{−(r+1)} = 2^{−r}. ∎

Formalization notes: choose c hcS hc using the hypothesis; Set.Finite.biUnion on S.finite_toSet (by_contra + push Not); symmDiff_triangle, symmDiff_comm; measure_mono, measure_union_le; ENNReal.ofReal_pow, ENNReal.ofReal_inv_of_pos (ofReal((1/2)^{r+1}) = 2⁻¹^{r+1}); two_mul, pow_succ, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top. Optional formalization aid: a complete machine-checked Lean proof of exactly this frozen statement (compiled after `import GMT.Ch07.Submission` in namespace GMT.Ch07 with the contract opens; sibling results are used by their `Submission.*` names) is the theorem at line 722 of /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a7cdf67795/bvc-split-lean-prototype.lean.txt (sha256 bd274b1c5aaf00c2d9facbece96054908343f66e3321434d45377655689496b8). The numbered proof above is self-contained.

## Key steps

1. Total boundedness at radius r+1 and accuracy 2^{−(r+1)} gives a finite centre set S and a centre map c.
2. Pigeonhole: some fibre J = I ∩ c⁻¹{s} is infinite.
3. Triangle inequality for symmetric differences: pairs in J are 2^{−r}-close on B_{r+1}.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean <snapshot>/project/GMT/Ch07/Contract.lean`
- `rg in snapshot mathlib: 'theorem ae_convolution_tendsto_right_of_locallyIntegrable', 'contDiff_convolution_left', 'theorem support_normed_eq', 'integral_normed', 'trace_smulRight', 'theorem extraction_forall_of_frequently', 'frequently_atTop_iff_infinite', 'uniformContinuous_of_continuous', 'theorem integral_integral_swap', 'integral_sub_left_eq_self|integral_add_right_eq_self', 'finite_cover_balls', 'ContDiff.lipschitzWith_of_hasCompactSupport', 'theorem Integrable.bdd_mul|theorem Integrable.mul_bdd', 'setIntegral_mono_on|integral_mono_of_nonneg', 'integral_prod_right', 'exists_contDiff_support_eq_eq_one_iff|exists_isOpen_lt_add|tendsto_measure_cthickening|exists_isCompact_diff_lt', 'theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le'`
- `lake env lean /tmp/bvc-split-check/Avail.lean and Avail2.lean: #check of about 70 lemma names after import GMT.Ch07.Submission to determine the frozen import closure`
- `python3 scans of dag.json (979 nodes): depth/status of the selected node; accepted statements mentioning StrictMono, Finset ℕ, indicator, symmDiff, Lipschitz; exact-type comparison of dorag_ha_rb_sup_net, dgcr_stc_exists_normalized_mollifier, cmc_fc_cs_diagonal_subseq; collision check of the 9 new codim1_rdo_dg_bvc_* names; cross-parent reuse count; proof sizes of accepted depth-6 leaves`
- `git show 043dcc28e6f06fdf02b550a807c0573e295fc4d9 / b046f226689afca88f2ceb966c9010ac5e581de0 / 376e5f482d73f6f48d00a4945533b15f784859d5 :GMT/Ch07/Submission.lean (accepted proofs to be reused)`
- `sed -n 560,640p book/chapter-02.txt (Simon 2.6 statement and printed proof)`
- `grep runtime.py (_decompose depth guard, _existing_lean_name_problem, _accepted_checkpoint, _solve_children reuse, _install_parent_supplied_child_handoff), prompts.py ('Preserve the exact target, hypotheses, imports'), verifier gmt-compare.py (candidate_inputs, dot-directory skipping)`
- `lake env lean -DautoImplicit=false /tmp/bvc-split-check/{Types,Glue3,Glue4,Glue6,LeafA,LeafAB,LeafC,LeafF,LeafJL,All,Full}.lean; final Full.lean: exit 0, 0 errors, 0 sorry, #print axioms Submission.codim1_rdo_dg_bv_set_compactness`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/Cofinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/SymmDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/lakefile.toml`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a7cdf67795/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a7cdf67795/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a7cdf67795/bvc-split-lean-prototype.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/prompts.py`
- `/tmp/bvc-split-check/Types.lean`
- `/tmp/bvc-split-check/Avail.lean`
- `/tmp/bvc-split-check/Avail2.lean`
- `/tmp/bvc-split-check/Full.lean`

Pins: the snapshot manifest (project b4d606db, Mathlib 25730c7c) equals workspace HEAD and .lake/packages/mathlib; simongmt is 2b366308; snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…). No local declaration states BV/perimeter compactness, the L¹ duality on balls, or the translation/mollification estimates ('bvc' has 0 hits in dag.json and SimonGMT). Three accepted theorems have exactly the needed types and are reused by name: Submission.dorag_ha_rb_sup_net (043dcc28), Submission.dgcr_stc_exists_normalized_mollifier (376e5f48), Submission.cmc_fc_cs_diagonal_subseq (b046f226). Import closure of GMT.Ch07.Submission (imports are frozen): absent are ContDiffBump.normed, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, ContDiffBump.convolution_tendsto_right, Integrable.exists_hasCompactSupport_integral_sub_le, Lp.boundedContinuousFunction_dense and exists_smooth_zero_one_of_isClosed. Present are exists_contDiff_support_eq_eq_one_iff (Geometry/Manifold/PartitionOfUnity.lean:789), MeasurableSet.exists_isCompact_isClosed_sdiff_lt and IsCompact.exists_isOpen_lt_add (Measure/Regular.lean:930), hasDerivAt_integral_of_dominated_loc_of_deriv_le (ParametricIntegral.lean:286), ContDiff.lipschitzWith_of_hasCompactSupport (ContDiff/RCLike.lean:156), LinearMap.trace_smulRight (LinearAlgebra/Trace.lean:272), integral_integral_swap (Integral/Prod.lean:478), integral_sub_left_eq_self/integral_add_right_eq_self, Filter.extraction_forall_of_frequently (AtTopBot/Basic.lean:123), ENNReal.tsum_geometric, and Integrable.bdd_mul/mul_bdd (L1Space/Integrable.lean:1067). Hence the duality child uses regularity plus smooth Urysohn rather than a.e. convergence of mollifiers. Simon 2.6's printed proof delegates precompactness to [GT01, 7.22], so the parent proof is a composed argument that the children specialize. Lean: all 12 child types elaborate, and the 864-line prototype proving every child and the parent's exact frozen type compiles (exit 0, no sorry; axioms propext, Classical.choice, Quot.sound).
