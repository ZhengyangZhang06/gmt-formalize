# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.localize-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.localize-a1.good_radius-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3(c) and 4 of the parent proof (Simon Ch. 6, proof of 7.2, chapter-06.txt lines 2090–2100, with 4.10 at line 1374: a good slicing radius chosen via the integrated slice bound 4.10 and an argument as in Ch. 2, 6.7(2)), stated for an abstract sequence of measures μ_j. The parent applies it to the weights μ_j = ℛ_j.measure of the integer multiplicity currents T_j.
Siblings used: (DM) dtc_bc_lc_fd_lz_dini_measurable; (SI) cmcs_slice_mass_integral.

Notation. |x| is the Euclidean norm and B_s := ball(0, s). For t ∈ ℝ, D_j(t) := liminf_{h→0+} ofReal(h⁻¹)·μ_j({x : t − h < |x| < t}), the liminf along 𝓝[>]0 in [0, ∞]. Let ν be Lebesgue measure on ℝ restricted to (r₀, r₀ + 1).

1. (Measurability.) For each j, D_j : ℝ → [0, ∞] is Borel measurable. This is (DM) applied to μ_j; its hypothesis μ_j(B_r) < ∞ for every r ∈ ℝ is part of ours.
2. (Integral bound, 4.10.) Fix j. Apply (SI) with μ := μ_j, f := |·| (continuous, hence measurable), W := ℝ^P (MeasurableSet.univ), L := 1, m := D_j and (a, b) := (r₀, r₀ + 1). Its pointwise hypothesis holds with equality: for t ∈ (r₀, r₀ + 1) and every h, ℝ^P ∩ {t − h < |x| < t} = {t − h < |x| < t} (univ_inter), and 1·liminf(…) = D_j(t) (one_mul). Hence ∫⁻_{(r₀, r₀+1)} D_j(t) dt ≤ 1·μ_j(ℝ^P ∩ {r₀ < |x| < r₀ + 1}). The set {r₀ < |x| < r₀ + 1} lies in B_{r₀+1}, so by measure_mono and the hypothesis, ∫⁻ D_j dν ≤ μ_j(B_{r₀+1}) ≤ Λ₀.
3. (Fatou.) Put G(t) := liminf_{j→∞} D_j(t) ∈ [0, ∞]. G is measurable (Measurable.liminf with step 1). By Fatou's lemma (lintegral_liminf_le with step 1), ∫⁻ G dν ≤ liminf_j ∫⁻ D_j dν. Every term of this sequence is ≤ Λ₀ by step 2, so the liminf is ≤ Λ₀ (liminf_le_of_frequently_le'). Hence ∫⁻ G dν ≤ Λ₀ < ∞.
4. (A good radius.) By ae_lt_top (G measurable, ∫⁻ G dν ≠ ∞), G(t) < ∞ for ν-a.e. t. By ae_restrict_iff' (measurableSet_Ioo), for Lebesgue-a.e. t, t ∈ (r₀, r₀ + 1) implies G(t) < ∞. Suppose G(t) = ∞ for every t ∈ (r₀, r₀ + 1). Then (r₀, r₀ + 1) is contained in the Lebesgue null set {t : ¬(t ∈ (r₀, r₀ + 1) → G(t) < ∞)}, which contradicts volume((r₀, r₀ + 1)) = 1 ≠ 0 (measure_mono_null, Real.volume_Ioo). So there is t₀ ∈ (r₀, r₀ + 1) with G(t₀) < ∞.
5. (Subsequence.) Put C := G(t₀).toNNReal + 1 ∈ [0, ∞). Since G(t₀) < ∞, G(t₀) = ↑(G(t₀).toNNReal) < ↑C (ENNReal.coe_toNNReal). So liminf_j D_j(t₀) < C, and by Filter.frequently_lt_of_liminf_lt, D_j(t₀) < C for frequently many j in atTop. By Filter.extraction_of_frequently_atTop there is a strictly increasing φ : ℕ → ℕ with D_{φ(j)}(t₀) < C for every j. In particular D_{φ(j)}(t₀) ≤ C for every j. ∎

Lean check made during decomposition (not a proof step). The file /tmp/lzsplit_k3v9/val/good_radius/Val.lean proves exactly this statement, as theorem GMT.Ch07.val_good_radius, with the frozen types of the listed siblings taken as hypotheses H_dini_measurable, H_slice_mass_integral. It compiles at Lean v4.35.0-rc3 / Mathlib 25730c7c, and #print axioms reports only propext, Classical.choice and Quot.sound. To reuse it, replace each hypothesis by the corresponding Submission.<sibling> declaration.

## Key steps

1. Each D_j is measurable (dini_measurable).
2. cmcs_slice_mass_integral with f = |·|, W = ℝ^P, L = 1 gives ∫_{r₀}^{r₀+1} D_j ≤ μ_j(B_{r₀+1}) ≤ Λ₀.
3. By Fatou, ∫_{r₀}^{r₀+1} liminf_j D_j ≤ Λ₀, so liminf_j D_j(t₀) < ∞ for some t₀ ∈ (r₀, r₀+1).
4. With C := liminf_j D_j(t₀) + 1, D_j(t₀) < C for infinitely many j; extract a strictly increasing φ.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5, mathlib 25730c7c)`
- `rg -l 'liminf|Dini|withDensity|alternatizeUncurryFin|smoothTransition|IMRep' local-references/123e8435b4a2469b/project -g '*.lean' (only the chapter Contract/Submission files); sed -n 105,145p project/GMT/Ch06/Contract.lean (IsRestriction, IsSlice: formulations in namespace GMT.Ch06, not importable from GMT.Ch07); diff project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); rg 'dtc_bc_lc_fd_lz|good_radius|dini' project (no match)`
- `grep '^theorem|^def' local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/{Basic,VectorField}.lean (extDeriv_add/_smul/_apply/_pullback only; no Leibniz rule for a function times a form)`
- `grep declarations in .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,Forms,WedgeForms,CurrentLocalEquality}.lean: GeometricCurrentOn, TestFormOn, exteriorDerivativeTestOn, boundary_apply, tsupport_exteriorDerivative_subset, massAdmissibleOn, massOn, mass, le_massOn, covectorEuclideanNorm(_neg, _zero), wedgeForm (no cut-off, restriction, slicing or Dini lemma)`
- `python3 -I scans of the run dag.json: accepted declarations whose types mention exteriorDerivative, alternatizeUncurryFin, Real.sqrt, cutoff, R.measure or massOn; the subtree root.compactness_of_minimizing_currents-a1.slicing-a1.*; accepted split parents with depends_on outside their children (74, e.g. dtc_cone_of_constant_density); collision check of the six dtc_bc_lc_fd_lz_ names (none)`
- `git show <commit>:GMT/Ch07/Submission.lean for 2af75d6, bff81d3, 9dfa657, 02c6122, 81485ce, 19f5e19, 6c9a074, b621818 (whitespace-normalised comparison of `theorem Submission.X` with dag.json: all identical; grep sorry/axiom: only the frozen root theorem, no axioms) and 47d40434 (dtc_cone_of_constant_density calls Submission.dtc_mass_eq_measure, a depends_on entry that is not a child)`
- `#check of every cited Mathlib/SimonGMT name at the pin (/tmp/lzsplit_k3v9/Names.lean, Names2.lean): Filter.HasBasis.liminf_eq_iSup_iInf, nhdsGT_basis, Monotone.measurable, MeasureTheory.measure_sdiff, Measurable.iInf/iSup/liminf, MeasureTheory.lintegral_liminf_le, MeasureTheory.ae_lt_top, Filter.frequently_lt_of_liminf_lt, Filter.extraction_of_frequently_atTop, MeasureTheory.restrict_withDensity, Measure.restrict_restrict, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, enorm_integral_le_lintegral_enorm, lintegral_withDensity_eq_lintegral_mul_non_measurable, lintegral_indicator_const_le, Monotone.map_liminf_of_continuousAt, Ioo_mem_nhdsGT (all resolve)`
- `lake env lean /tmp/lzsplit_k3v9/Challenges.lean, Print.lean (pp.coercions), Assembly.lean, and /tmp/lzsplit_k3v9/val/<key>/Val.lean for the six new children (all compile; #print axioms: propext, Classical.choice, Quot.sound)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement on the 12 statements (all accepted unchanged); verifier/gmt-compare.py contract_scope for the replayed challenge scope`
- `sed book/chapter-06.txt lines 1355–1402 (4.9–4.11, proof with the cut-off) and 2088–2102 (proof of 7.2, localisation step)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LeftRightNhds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/WedgeForms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-e8f543fe44/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-21d9fb1dcd/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-21d9fb1dcd/speculative-prompt-v1.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-mass-integral-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-level-cutoff-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-cutoff-defect-a-9dbb42610d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-wedge-norm-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-mass-pointwise-78bf1bcbb0/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/lzsplit_k3v9/Challenges.lean`
- `/tmp/lzsplit_k3v9/Print.lean`
- `/tmp/lzsplit_k3v9/Assembly.lean`
- `/tmp/lzsplit_k3v9/val/dini_measurable/Val.lean`
- `/tmp/lzsplit_k3v9/val/good_radius/Val.lean`
- `/tmp/lzsplit_k3v9/val/truncate/Val.lean`
- `/tmp/lzsplit_k3v9/val/action_bound/Val.lean`
- `/tmp/lzsplit_k3v9/val/cutoff_estimate/Val.lean`
- `/tmp/lzsplit_k3v9/val/boundary_mass/Val.lean`

The pinned snapshot has none of this node's lemmas in a form importable from GMT.Ch07: no Dini-derivative measurability, no good-radius extraction, no integer multiplicity restriction lemma and no boundary-mass estimate. The snapshot's Ch06 contract states IsRestriction and IsSlice only as formulations in namespace GMT.Ch06, which GMT.Ch07 cannot import. Its Ch07 contract is byte-identical to the workspace's. Mathlib at 25730c7c has no Leibniz rule for extDeriv of a function times a form. SimonGMT provides currents, test forms, exteriorDerivativeTestOn, massOn/mass/le_massOn and covectorEuclideanNorm. The analytic tools the proof needs are accepted DAG declarations, reused with identical types (checked against their candidate commits): Simon 4.10, smooth level cut-offs, the Leibniz rule, |β∧γ| ≤ ‖β‖|γ| and dominated convergence for cut-offs from the slicing branch, plus the integer multiplicity calculus. The node's other inherited dependencies, dtc_mass_eq_measure and rsd_cmr_support_subset_of_vanish, are used only by the parent assembly; the accepted split parent dtc_cone_of_constant_density sets a precedent for this. Every cited Mathlib name exists at the pin. measure_diff and setIntegral_eq_of_subset_of_forall_diff_eq_zero are deprecated aliases of measure_sdiff and setIntegral_eq_of_subset_of_forall_sdiff_eq_zero. Lean checks prove the parent's frozen type from the children plus the two inherited dependencies. They also prove each new child from exactly its declared siblings. Everything uses only propext, Classical.choice and Quot.sound.
