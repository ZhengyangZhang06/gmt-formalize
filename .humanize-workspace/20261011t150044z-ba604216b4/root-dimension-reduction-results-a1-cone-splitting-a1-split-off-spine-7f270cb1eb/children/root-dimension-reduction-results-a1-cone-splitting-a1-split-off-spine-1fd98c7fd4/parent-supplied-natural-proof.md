# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.measure_comparison-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 9 of the selected proof (comparing μ_{S₀'} and μ₀ off K₀ = spt(S₀' − S₀)), in an additive form that needs no finiteness.
Accepted results used (dependencies of the selected node, available here because they are cited by name): imrep_represents_massOn_eq_measure (F1: M_O(T) = R.measure(O) for open O if R represents T in ℝ^P), imrep_carrier_sdiff_support_null (F6: H^j(R.carrier ∖ spt T) = 0 if R represents T in ℝ^P), rsd_isIntegerMultiplicity_int_combination (F4: integer combinations of integer multiplicity currents are integer multiplicity).
1. (The difference.) X := S₁ − S₂ satisfies X(ω) = S₁(ω) − S₂(ω) = 1·S₁(ω) + (−1)·S₂(ω) for every test form ω, so X is integer multiplicity by rsd_isIntegerMultiplicity_int_combination (U = ℝ^P open, S₁ and S₂ represented by R₁, R₂); let R_X = (M_X, θ_X, ξ_X) represent X. K := spt X is closed, being the complement in ℝ^P of the open zero region of X (GeometricCurrentOn.isOpen_zeroRegion), and K ⊆ W₀ by hypothesis.
2. (X vanishes off K.) Let ω be a test j-form with tsupport ω ∩ K = ∅. Then X(ω) = R_X.action(ω) = ∫_{M_X} θ_X·ξ_X(ω) dH^j. The integrand vanishes at every point of M_X ∩ K (there ω = 0), and M_X ∖ K is H^j-null by imrep_carrier_sdiff_support_null; hence X(ω) = 0.
3. (Equal masses away from K.) Let O be open with O ∩ K = ∅. Every form ω admissible for M_O (tsupport ω ⊆ O and Euclidean coefficient norm ≤ 1) has tsupport ω ∩ K = ∅, so S₁(ω) − S₂(ω) = X(ω) = 0 by step 2. The suprema defining M_O(S₁) = S₁.massOn O and M_O(S₂) = S₂.massOn O therefore run over the same values, so S₁.massOn O = S₂.massOn O.
4. (Equal measures away from K.) By imrep_represents_massOn_eq_measure (ℝ^P and O open): R₁.measure(O) = S₁.massOn O = S₂.massOn O = R₂.measure(O) for every open O disjoint from K. Apply this to the open sets O₁ := B ∖ K and O₂ := W₀ ∖ K (K is closed).
5. (Additivity.) K is Borel and K ⊆ W₀ ⊆ B, so for i = 1, 2: R_i.measure(B) = R_i.measure(B ∖ K) + R_i.measure(K) and R_i.measure(W₀) = R_i.measure(W₀ ∖ K) + R_i.measure(K) (measure_diff_add_inter, with B ∩ K = W₀ ∩ K = K). Hence, using R₁.measure(B ∖ K) = R₂.measure(B ∖ K) and R₂.measure(W₀ ∖ K) = R₁.measure(W₀ ∖ K) from step 4,
R₁.measure(B) + R₂.measure(W₀) = R₁.measure(B∖K) + R₁.measure(K) + R₂.measure(W₀∖K) + R₂.measure(K) = R₂.measure(B∖K) + R₂.measure(K) + R₁.measure(W₀∖K) + R₁.measure(K) = R₂.measure(B) + R₁.measure(W₀),
an identity in [0, ∞] that needs no finiteness. ∎

## Key steps

1. X = S₁ − S₂ is integer multiplicity (F4); by F6 it vanishes on test forms supported off the closed set K = spt X ⊆ W₀.
2. Hence M_O(S₁) = M_O(S₂) for every open O disjoint from K, and by F1 R₁.measure(O) = R₂.measure(O); apply to B ∖ K and W₀ ∖ K.
3. Split R_i.measure(B) and R_i.measure(W₀) at K and add.

## Reference use

### local-project

Queries:
- `cat manifest.json (project b4d606db1, mathlib 25730c7c); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `python3 over dag.json: split_off_spine nodes and statuses; ancestors and their depends_on; all 2101 accepted nodes dumped to /tmp/mt-decomp/accepted.txt and grepped for translate|massOn_le_add|measure_restrict|support|blowUp|hasDerivAt`
- `git show <candidate>:GMT/Ch07/Submission.lean for idtp_fons_cs_sos_product_current (4aa9ba8d), lcmp_massOn_le_add_of_eval_eq (c7dea4b8), dimred_cs_ti_translate_action_hasDerivAt (f899c748): declarations present, types byte-identical; product_current adds import Poincare.SimonGMT.Chapter02.AreaLipschitz`
- `read nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-60772a06fe/parent-supplied-natural-proof.md (parallel minimality_transfer with the identical frozen type, product construction moved to product_current) and the accepted proofs of the three reused nodes`
- `grep -n over runtime.py (_dependency_problem, _existing_lean_name_problem, _overlay_accepted_children) and inherited.py (cited_inherited: ancestor dependencies cited by exact Lean name)`
- `grep -n over SimonGMT Chapter06/{Currents,Mass,Forms,CurrentLocalEquality}.lean and Chapter03/Rectifiable.lean: GeometricCurrentOn.boundary(_apply), exteriorDerivativeTestOn, CurrentOn.boundary_boundary, massOn/mass/massOn_mono, zeroRegion/support, exteriorDerivative_apply, CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt`
- `grep -n over snapshot mathlib Geometry/Euclidean/Volume/Measure.lean: EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.map_euclideanHausdorffMeasure, Isometry.euclideanHausdorffMeasure_image, IsometryEquiv.measurePreserving_euclideanHausdorffMeasure`
- `rg -n over snapshot mathlib: PiLp.volume_preserving_toLp, Real.volume_pi_closedBall, Real.volume_pi_ball, measurePreserving_piFinSuccAbove, intervalIntegral.integral_eq_sub_of_hasDerivAt, continuousAt_of_dominated, setIntegral_sdiff (integral_diff deprecated alias), measure_add_measure_compl, withDensity_apply, Measure.restrict_restrict, Measure.integrableOn_of_bounded, Fin.append_left, fderiv_comp_add_left, finrank_span_eq_card, Submodule.eq_of_le_of_finrank_eq, ENNReal.le_of_add_le_add_left, lintegral_indicator_const, Fin.removeNth`
- `rg -n "Cartesian product of currents|slice of a current|cartesianProduct" snapshot mathlib (no match)`
- `lake env lean /tmp/mt-decomp/check/{Types,Assembly,CubeCycle,CompMass}.lean (Lean v4.35.0-rc3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-7f270cb1eb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-7f270cb1eb/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-60772a06fe/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-da13543666/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-mass-triangle-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-translation-inv-37aaf335d9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/inherited.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/models.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/mt-decomp/check/Types.lean`
- `/tmp/mt-decomp/check/Assembly.lean`
- `/tmp/mt-decomp/check/CubeCycle.lean`
- `/tmp/mt-decomp/check/CompMass.lean`

Pins match. The snapshot manifest records project b4d606db1 (= workspace HEAD) and mathlib 25730c7c; the snapshot Contract.lean equals the workspace Contract.lean and Submission.lean.

Library gaps. Simon leaves Lemma 7.3.5 to the reader (book/chapter-07.txt), so the supplied proof is the project's own argument. SimonGMT has:
- no general Cartesian products of currents;
- no slicing;
- no translation lemma for currents.
Snapshot mathlib has no currents at all ("Cartesian product of currents|slice of a current": no match).

Accepted reuse. dag.json has 2101 accepted declarations. Three fit this proof with byte-identical frozen types, present in their candidate commits:
- idtp_fons_cs_sos_product_current (4aa9ba8d): exactly the I.3 product construction; it also carries the AreaLipschitz import;
- lcmp_massOn_le_add_of_eval_eq (c7dea4b8): the mass triangle inequality;
- dimred_cs_ti_translate_action_hasDerivAt (f899c748): the derivative of s ↦ R.action(ω(sv + ·)).
These are reused as children. Inherited by exact-name citation (inherited.py): dtc_imrep_current, imrep_represents_massOn_eq_measure, imrep_carrier_sdiff_support_null, rsd_isIntegerMultiplicity_int_combination and dimred_im_mass_measure.

Mathlib facts the child proofs need are present in the snapshot, among them:
- μHE[k] = volume on EuclideanSpace and the isometry push-forward Isometry.map_euclideanHausdorffMeasure;
- PiLp.volume_preserving_toLp, Real.volume_pi_closedBall / volume_pi_ball and measurePreserving_piFinSuccAbove;
- the FTC integral_eq_sub_of_hasDerivAt, continuousAt_of_dominated and setIntegral_sdiff;
- finrank_span_eq_card and Submodule.eq_of_le_of_finrank_eq;
- SimonGMT exteriorDerivative_apply, GeometricCurrentOn.boundary_apply and the CountablyRectifiable / HasApproximateTangentSpaceAt definitions via blowUpMap images.

Lean checks. All 12 child types elaborate. The parent's frozen type compiles from the child stubs and its own dependency stubs (axioms: propext, sorryAx from stubs only, Classical.choice, Quot.sound). Skeletons of cube_cycle and competitor_mass compile against their sibling stubs. The runtime gates (ScopedDecomposition validation, _dependency_problem, _existing_lean_name_problem) pass on dag.json. The parallel node idtp_fons_cs_sos_minimality_transfer has the identical frozen type but is not accepted, so it is not reused.
