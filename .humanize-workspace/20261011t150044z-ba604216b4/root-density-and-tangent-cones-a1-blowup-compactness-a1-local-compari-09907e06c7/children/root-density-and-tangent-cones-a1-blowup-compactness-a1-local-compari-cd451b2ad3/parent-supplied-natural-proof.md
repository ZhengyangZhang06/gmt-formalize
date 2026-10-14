# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.eilenberg-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 2, Theorem 1.9 and Remark 1.10 (chapter-02.txt lines 330–410, printed pp. 45–46), case m = 1, k = n, X = ℝ^P. The printed proof is copied. In dimension m = 1 the isodiametric inequality used there becomes the elementary bound L¹(S) ≤ diam S for S ⊆ ℝ (Mathlib `Real.volume_le_diam`). The upper integral of Remark 1.10 is made explicit by the measurable majorant φ. The measurability of t ↦ Hⁿ(A ∩ f⁻¹(t)), left as an exercise in the source, is not claimed and not needed. The proof works with Mathlib's unnormalised Hausdorff measure μH[d] and converts to μHE at the end. This theorem is used by the siblings chart_coarea (critical points) and coarea (the null part of a rectifiable set).

Notation. For d ≥ 0, δ > 0 and S ⊆ ℝ^P let μH[d]_δ(S) := inf Σ_i ⨆_{C_i ≠ ∅} (diam C_i)^d, the infimum over countable covers (C_i) of S with diam C_i ≤ δ. By Mathlib `hausdorffMeasure_apply`, μH[d](S) = sup_{δ>0} μH[d]_δ(S), and μH[d]_δ(S) increases as δ decreases. Let c_d := addHaarScalarFactor(volume on Euclid d, μH[d]) ∈ (0, ∞). It is nonzero by Mathlib `addHaarScalarFactor_volume_hausdorffMeasure_ne_zero`, and μHE[d] = c_d·μH[d] (`euclideanHausdorffMeasure_def`); c_d does not depend on P. Put C := c_n/c_{n+1}.

1. Extension. By McShane (Mathlib `LipschitzOnWith.extend_real`) there is f̃ : ℝ^P → ℝ, L-Lipschitz on ℝ^P, with f̃ = f on A. Since A ∩ f⁻¹(t) = A ∩ f̃⁻¹(t) for every t, we may assume that f is L-Lipschitz on ℝ^P.

2. Trivial cases.
 - If L = 0, then f is constant, say f ≡ c, and A ∩ f⁻¹(t) = ∅ for t ≠ c. Take φ := ∞·1_{{c}}: it is Borel, dominates, and ∫φ = ∞·L¹({c}) = 0 = C·0·H^{n+1}(A) (in [0, ∞], 0·∞ = 0).
 - If L > 0 and μH[n+1](A) = ∞, take φ ≡ ∞. This is allowed: C = c_n/c_{n+1} is finite and > 0 (c_n ≠ 0 and c_{n+1} ≠ 0), and μHE[n+1](A) = c_{n+1}·μH[n+1](A) = ∞, so the right side C·L·μHE[n+1](A) is ∞.
 So assume L > 0 and μH[n+1](A) < ∞.

3. Covers (Simon's sets C_ij). For k ≥ 1 put δ_k := 2^{−k}. Since μH[n+1]_{δ_k}(A) ≤ μH[n+1](A) < ∞, choose sets C_{k,i} (i ∈ ℕ) covering A with diam C_{k,i} ≤ δ_k and Σ_i ⨆_{C_{k,i}≠∅}(diam C_{k,i})^{n+1} ≤ μH[n+1](A) + 2^{−k}. Replacing each C_{k,i} by its closure keeps the cover and the diameters, so assume every C_{k,i} is closed. Let I_k := {i : C_{k,i} ≠ ∅}.

4. Simon's simple functions g_i. Put φ_k(t) := Σ_{i∈I_k} (diam C_{k,i})^n·1_{f(C_{k,i})}(t).
 - Each f(C_{k,i}) is σ-compact, hence Borel: C_{k,i} is closed in ℝ^P, hence a countable union of compact sets, and f is continuous. So φ_k is Borel.
 - L¹(f(C_{k,i})) ≤ diam f(C_{k,i}) ≤ L·diam C_{k,i} (`Real.volume_le_diam` and the Lipschitz bound). By monotone convergence, ∫φ_k ≤ L·Σ_{i∈I_k} (diam C_{k,i})^{n+1} ≤ L(μH[n+1](A) + 2^{−k}).

5. Pointwise bound (Simon's (2)). Fix t. The sets C_{k,i} ∩ A ∩ f⁻¹(t), i ∈ ℕ, cover A ∩ f⁻¹(t) and have diameter ≤ δ_k. If C_{k,i} ∩ A ∩ f⁻¹(t) ≠ ∅, then t ∈ f(C_{k,i}) and diam(C_{k,i} ∩ A ∩ f⁻¹(t)) ≤ diam C_{k,i}. Hence μH[n]_{δ_k}(A ∩ f⁻¹(t)) ≤ Σ_i ⨆_{C_{k,i}∩A∩f⁻¹(t)≠∅} (diam C_{k,i})^n ≤ φ_k(t). This also holds for n = 0, because the terms with empty intersection contribute 0.

6. Passage to the limit. Put φ⁰ := liminf_k φ_k, a Borel function.
 - For every t, μH[n](A ∩ f⁻¹(t)) = lim_k μH[n]_{δ_k}(A ∩ f⁻¹(t)) ≤ liminf_k φ_k(t) = φ⁰(t). The limit exists because the sequence is increasing in k with supremum μH[n].
 - By Fatou's lemma, ∫φ⁰ ≤ liminf_k ∫φ_k ≤ L·μH[n+1](A).

7. Normalisation. Put φ := c_n·φ⁰ (Borel). Then μHE[n](A ∩ f⁻¹(t)) = c_n·μH[n](A ∩ f⁻¹(t)) ≤ φ(t) for every t. Also ∫φ ≤ c_n·L·μH[n+1](A) = (c_n/c_{n+1})·L·μHE[n+1](A) = C·L·μHE[n+1](A). The constant C depends only on n. ∎

## Key steps

1. Extend f to an L-Lipschitz function on ℝ^P (McShane) and dispose of L = 0 and H^{n+1}(A) = ∞.
2. Choose closed δ_k-covers (C_{k,i}) of A with Σ diam^{n+1} ≤ μH[n+1](A) + 2^{−k}.
3. φ_k := Σ_i (diam C_{k,i})^n 1_{f(C_{k,i})} is Borel, dominates the δ_k-content of A ∩ f⁻¹(t), and has ∫φ_k ≤ L Σ diam^{n+1} since L¹(f(C)) ≤ L diam C.
4. φ⁰ := liminf φ_k dominates μH[n](A ∩ f⁻¹(t)); Fatou gives ∫φ⁰ ≤ L μH[n+1](A); rescale by the μHE normalising constants.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD in the snapshot project (b4d606db1) and mathlib (25730c7c); diff snapshot GMT/Ch07/Contract.lean against the workspace Contract.lean and Submission.lean (identical; Submission is a byte copy)`
- `grep -rn 'coarea\|co_area\|CoArea\|Coarea' Poincare/SimonGMT (only Chapter02/CoareaLinear*.lean, CoareaProjection.lean: linear co-area 6.1–6.2)`
- `grep -n '^theorem\|^def' on SimonGMT Chapter02/{AreaFormula,AreaLipschitz,AreaCritical,AreaNoninjective,WeightedArea,AreaLinearWeighted,WhitneyExtension,WhitneyJet,Lipschitz,LipschitzMeasurability,UpperIntegral,Submanifold,SubmanifoldCalculus}.lean, Chapter01/Lusin.lean, Chapter03/{Rectifiable,Differential,SubmanifoldCover,DisjointCover,CoordinateProjection}.lean`
- `grep 'Eilenberg\|1\.9' and 'theorem.*[Ll]usin' in SimonGMT and Mathlib (no Eilenberg inequality; Lusin only as SimonGMT IsBorelRegularOuterMeasure.exists_isClosed_continuousOn)`
- `grep in snapshot mathlib for tendstoUniformlyOn_of_ae_tendsto, exists_measurable_superset_of_null, measurable_fderiv, integral_lineDeriv_mul_eq, LocallyIntegrable.ae_hasDerivAt_integral, lintegral_image_eq_lintegral_abs_det_fderiv_mul, Real.volume_le_diam, hausdorffMeasure_apply, ae_tendsto_measure_inter_div, LipschitzOnWith.extend_real, Integrable.exists_hasCompactSupport_integral_sub_le, ContDiffAt.toOpenPartialHomeomorph, OpenPartialHomeomorph.contDiffAt_symm, AlternatingMap.eq_smul_basis_det, EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp, measurePreserving_piFinSuccAbove; sed Mathlib/Geometry/Euclidean/Volume/Measure.lean (μHE[d] = addHaarScalarFactor • μH[d])`
- `python3 -I scans of dag.json (995 nodes) for slic|coarea|Lusin|C¹ approximation|approximate tangent|tangential gradient: dor_lmb_slicing_lipschitz and its children (speculative/decomposing), cmc_slice_mass_bounds (speculative-ready) with accepted cmcs_* children, codim1_rdo_c1_approximation (waiting-children), codim1_rdo_c1_piece_approxTangent (speculative-lean), codim1_rdo_rectifiable_ae_approxTangent (speculative-ready), codim1_rdo_c1cov_lipschitz_range_c1_cover (rlcr-lean), dimred_cs_sos_spine_coarea, idtp_carrier_area_formula, dpf_area_formula_bilipschitz_rectifiable (none accepted)`
- `git show <accepted candidate commit>:GMT/Ch07/Submission.lean and whitespace-normalised comparison for cmc_imRep_locality_restrict_sub (2af75d6), cmcs_cd_defect_identity (e32f0ad), cmcs_lipschitz_smoothing (00c458d): all IDENTICAL`
- `grep -c dtc_bc_lc_sl_ dag.json (0); git log --all -S 'dtc_bc_lc_sl_' over 4526 refs (no match)`
- `lake env lean /tmp/dtcslice/Types.lean, /tmp/dtcslice/Check1.lean, /tmp/dtcslice/challenges/Challenge_<key>.lean (12 modules generated by verifier gmt-compare.py child_modules, contract mode, after lean_contract.validate_lean_statement) and /tmp/dtcslice/AssemblyFinal.lean with #print axioms`
- `sed book/chapter-06.txt lines 1140–1370 (Ch. 6 §4: 4.1–4.9); book/chapter-03.txt lines 1–170 and 320–460 (1.1–1.6, 2.1–2.10); book/chapter-02.txt lines 160–430 (1.5–1.10) and 1360–1640 (6.1–6.7)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-09907e06c7/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLinearWeighted.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/UpperIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/dtcslice/Types.lean`
- `/tmp/dtcslice/AssemblyFinal.lean`
- `/tmp/dtcslice/challenges`

The pinned SimonGMT library has the linear co-area formula, the injective, weighted and noninjective Lipschitz area formulas, null critical images, Rademacher, Lusin, the C¹ Whitney extension and the upper integral. It has no nonlinear co-area formula, no C¹ approximation theorem (Simon 2.1.5), no Eilenberg inequality (2.1.9), no Lemma 1.2 'only if', no tangential gradient of Lipschitz functions on rectifiable sets and no slicing. Mathlib supplies Egorov, Lebesgue differentiation, integration by parts for Lipschitz functions, change of variables, the inverse function theorem and the μHE normalisation. No DAG node proving the co-area formula or slicing is accepted. The closest node, dor_lmb_slicing_lipschitz, is the same theorem for open U; it is speculative, and its decomposition was reviewed and accepted with three children. So the needed results become nine new children, with the unique prefix dtc_bc_lc_sl_. Three accepted declarations are reused with identical frozen types: cmc_imRep_locality_restrict_sub, cmcs_cd_defect_identity and cmcs_lipschitz_smoothing. All 12 types pass validate_lean_statement and elaborate in the comparator's contract-mode challenge modules. A Lean assembly derives the exact frozen type of dtc_bc_lc_slice from slice_family, slice_identity, im_calculus and dtc_mass_eq_measure, with axioms propext, Classical.choice and Quot.sound only.
