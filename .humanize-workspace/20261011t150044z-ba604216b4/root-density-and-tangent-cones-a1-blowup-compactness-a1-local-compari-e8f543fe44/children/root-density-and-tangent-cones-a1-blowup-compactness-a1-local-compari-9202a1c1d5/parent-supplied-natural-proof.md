# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.localize-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.localize-a1.cutoff_estimate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 9(b)–(d) of the parent proof, i.e. Simon's identity 4.11, T(g dη) = ∂T(gη) − T(dg ∧ η) (Ch. 6, chapter-06.txt lines 1378–1386), with the two estimates of 9(c) and 9(d), for a general cut-off g. The parent's bound √(m+1)|Dg||η| for |dg ∧ η| (Cauchy–Schwarz, step 9(d)) is replaced by the sharper accepted bound ‖Dg‖|η| of cmcs_wedge_norm_le. The parent's 0 ≤ g ≤ 1 is replaced by |g| ≤ a.
Siblings used: (AB) dtc_bc_lc_fd_lz_action_bound; (LB) cmcs_cd_extDeriv_smul_leibniz; (WN) cmcs_wedge_norm_le.

Notation. |α| := covectorEuclideanNorm α; d := exteriorDerivative (Mathlib's extDeriv); Dg(x) := fderiv ℝ g x; 𝒜 := ContinuousAlternatingMap.alternatizeUncurryFin. A test form and its underlying form are denoted alike. μ_R := R.measure. M_V := massOn V.

0. (Preliminaries.)
 (i) ℝ^P contains 0, so a ≥ |g(0)| ≥ 0 and c ≥ ‖Dg(0)‖ ≥ 0.
 (ii) (Homogeneity.) For s ∈ ℝ and a covector α, |s·α| = |s|·|α|. Each coefficient satisfies (sα)(e_I) = s·α(e_I), so the sum of squares in covectorEuclideanNorm is multiplied by s², and √(s²Q) = |s|√Q (Real.sqrt_mul, Real.sqrt_sq_eq_abs).
 (iii) (Products are test forms.) Let φ : ℝ^P → ℝ be C^∞ and ζ ∈ 𝒟^k(U). Then x ↦ φ(x)ζ(x) is C^∞ (ContDiff.smul) and has compact support (HasCompactSupport.smul_left). Its topological support lies in tsupport ζ ⊆ U (tsupport_smul_subset_right) and in tsupport φ (tsupport_smul_subset_left). So it is an element of 𝒟^k(U) = TestFormOn U k.
1. (Three test forms.) By 0(iii), ω₁ := gη ∈ 𝒟^m(U). Next dη := exteriorDerivativeTestOn U m η ∈ 𝒟^{m+1}(U), whose underlying form is exteriorDerivative η, so ω₂ := g·dη ∈ 𝒟^{m+1}(U), again by 0(iii). Finally E := exteriorDerivativeTestOn U m ω₁ − ω₂ ∈ 𝒟^{m+1}(U), a difference of two elements of the submodule.
2. (Leibniz rule; identity 4.11.) g is C^∞ and η is C^∞ (a test form), so both are differentiable at every x. By (LB), d(gη)(x) = g(x)·dη(x) + 𝒜((Dg(x)).smulRight(η(x))), hence E(x) = 𝒜((Dg(x)).smulRight(η(x))) for every x. T is linear, and ∂T(ω₁) = T(exteriorDerivativeTestOn U m ω₁) (GeometricCurrentOn.boundary_apply). So T(ω₂) = T(dω₁) − T(E) = ∂T(ω₁) − T(E). By R.Represents T, T(ω₂) = R.action(ω₂) = R.action(x ↦ g(x)·dη(x)), the left side of the claim. Therefore ofReal|R.action(g dη)| = ofReal|∂T(ω₁) − T(E)| ≤ ofReal|∂T(ω₁)| + ofReal|T(E)| (abs_sub, ENNReal.ofReal_add, ENNReal.ofReal_le_ofReal).
3. (Boundary term, 9(c).) Claim: ofReal|∂T(ω₁)| ≤ ofReal(a)·M_V(∂T).
 If a = 0, then g = 0 by |g| ≤ a, so ω₁ = 0 and ∂T(ω₁) = 0.
 Let a > 0 and ζ := a⁻¹·ω₁ ∈ 𝒟^m(U). Then tsupport ζ ⊆ tsupport g ⊆ V, and |ζ(x)| = a⁻¹|g(x)|·|η(x)| ≤ a⁻¹·a·1 = 1 by 0(ii). So ζ ∈ massAdmissibleOn U m V, and so is −ζ (tsupport_neg, covectorEuclideanNorm_neg). By GeometricCurrentOn.le_massOn, ofReal(∂T(ζ)) ≤ M_V(∂T) and ofReal(−∂T(ζ)) = ofReal(∂T(−ζ)) ≤ M_V(∂T). Since |y| ∈ {y, −y} (abs_choice) and ∂T(−ζ) = −∂T(ζ) (map_neg), ofReal|∂T(ζ)| ≤ M_V(∂T). As ∂T(ω₁) = a·∂T(ζ) by linearity, ofReal|∂T(ω₁)| = ofReal(a)·ofReal|∂T(ζ)| ≤ ofReal(a)·M_V(∂T).
4. (Wedge term, 9(d).) Claim: ofReal|E(x)| ≤ 1_S(x)·ofReal(c) for every x.
 If x ∈ S: by (WN) and the hypotheses, |E(x)| = |𝒜((Dg(x)).smulRight(η(x)))| ≤ ‖Dg(x)‖·|η(x)| ≤ c·1 = c.
 If x ∉ S: then Dg(x) = 0 by hypothesis, so (Dg(x)).smulRight(η(x)) = 0, E(x) = 𝒜(0) = 0 (𝒜 is linear) and |E(x)| = 0 (covectorEuclideanNorm_zero).
 By (AB) applied to T, R and E, and by lintegral_mono and lintegral_indicator_const_le (valid for an arbitrary set S): ofReal|T(E)| ≤ ∫⁻ ofReal(|E(x)|) dμ_R(x) ≤ ∫⁻ 1_S·ofReal(c) dμ_R ≤ ofReal(c)·μ_R(S).
5. (Conclusion.) Steps 2–4 give ofReal|R.action(x ↦ g(x)·dη(x))| ≤ ofReal(a)·M_V(∂T) + ofReal(c)·μ_R(S). ∎

Lean check made during decomposition (not a proof step). The file /tmp/lzsplit_k3v9/val/cutoff_estimate/Val.lean proves exactly this statement, as theorem GMT.Ch07.val_cutoff_estimate, with the frozen types of the listed siblings taken as hypotheses H_action_bound, H_leibniz, H_wedge_norm. It compiles at Lean v4.35.0-rc3 / Mathlib 25730c7c, and #print axioms reports only propext, Classical.choice and Quot.sound. To reuse it, replace each hypothesis by the corresponding Submission.<sibling> declaration.

## Key steps

1. ω₁ = gη, ω₂ = g dη and E = dω₁ − ω₂ are test forms in U. By the Leibniz rule (cmcs_cd_extDeriv_smul_leibniz), E = dg ∧ η pointwise.
2. T(ω₂) = ∂T(ω₁) − T(E) (identity 4.11), and T(ω₂) = R.action(g dη).
3. a⁻¹ω₁ and its negative are admissible for M_V, so |∂T(ω₁)| ≤ a·M_V(∂T).
4. |E| ≤ ‖Dg‖|η| ≤ c·1_S (cmcs_wedge_norm_le), so |T(E)| ≤ ∫|E| dμ_R ≤ c·μ_R(S) (action_bound).

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
