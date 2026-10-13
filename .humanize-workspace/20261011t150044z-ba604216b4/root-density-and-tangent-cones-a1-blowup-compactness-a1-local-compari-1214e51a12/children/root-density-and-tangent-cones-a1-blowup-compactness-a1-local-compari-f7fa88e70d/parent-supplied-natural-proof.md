# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.slice_family-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.slice_family-a1.coarea_signed-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the supplied proof of the parent node slice_family, steps 8 and 9(c): "Apply (CF) to q⁺ and q⁻ and subtract (all quantities finite)". This is Simon Ch. 6, the last part of Lemma 4.1 (book/chapter-06.txt ll. 1156–1183), applied to the positive and negative parts of the signed integrand. Simon does this in the proof of 4.5(1) (l. 1245) and in "we use 4.2 with g = ⟨ξ⌞∇^M f/|∇^M f|, ω⟩" at the end of the proof of 4.5(2) (ll. 1317–1323).

Notation: S_t := M ∩ f⁻¹(t). For real r, r⁺ := max{r, 0} and r⁻ := max{−r, 0}, so r = r⁺ − r⁻ and |r| = r⁺ + r⁻. Put A⁺(t) := ∫_{S_t} q⁺ dHⁿ, A⁻(t) := ∫_{S_t} q⁻ dHⁿ, A(t) := ∫_{S_t} |q| dHⁿ, with values in [0, ∞] (in Lean the [0, ∞]-valued integrands are ENNReal.ofReal q, ENNReal.ofReal(−q), ENNReal.ofReal|q|). Put F(t) := ∫_{S_t} q dHⁿ (Bochner integral).

1. The functions q⁺, q⁻ and |q| are Borel because q is. By (CF), A⁺, A⁻ and A are a.e.-measurable on ℝ, ∫_ℝ A dt = ∫_M |G||q| dH^{n+1} < ∞, and ∫_ℝ A^± dt = ∫_M |G| q^± dH^{n+1} ≤ ∫_M |G||q| dH^{n+1} < ∞.
2. Since A is a.e.-measurable with finite integral, A(t) < ∞ for L¹-a.e. t (Mathlib ae_lt_top'). For such t, q is Hⁿ-integrable on S_t: it is Borel, hence a.e. strongly measurable, and ∫_{S_t} |q| dHⁿ = A(t) < ∞. This proves (1). For the same t, A^±(t) ≤ A(t) < ∞.
3. For such t, F(t) = A⁺(t).toReal − A⁻(t).toReal (Mathlib integral_eq_lintegral_pos_part_sub_lintegral_neg_part, applied to the integrable function q on S_t). Thus F agrees L¹-a.e. with t ↦ A⁺(t).toReal − A⁻(t).toReal. That function is a.e.-measurable, being a difference of real parts of a.e.-measurable [0, ∞]-valued functions. Hence F is a.e. strongly measurable.
4. For every t, |F(t)| ≤ ∫_{S_t} |q| dHⁿ = A(t). This is the norm bound for Bochner integrals when q is integrable on S_t; otherwise F(t) = 0. Hence ∫_ℝ |F| dt ≤ ∫_ℝ A dt < ∞, and F is Lebesgue integrable on ℝ. This proves (2).
5. The functions t ↦ A^±(t).toReal are nonnegative, a.e.-measurable, and have finite integral (at most ∫_ℝ A^± dt < ∞), so they are integrable. Since A^± < ∞ L¹-a.e., ∫_ℝ A^±(t).toReal dt = (∫_ℝ A^± dt).toReal (Mathlib integral_toReal).
6. By steps 3 and 5, ∫_ℝ F dt = ∫_ℝ A⁺.toReal dt − ∫_ℝ A⁻.toReal dt = (∫_ℝ A⁺ dt).toReal − (∫_ℝ A⁻ dt).toReal = (∫_M |G| q⁺ dH^{n+1}).toReal − (∫_M |G| q⁻ dH^{n+1}).toReal. The last equality is (CF) for q⁺ and q⁻.
7. The function x ↦ |G(x)|q(x) is Borel and integrable for H^{n+1}⌞M, since ∫_M ||G|q| dH^{n+1} = ∫_M |G||q| dH^{n+1} < ∞. Because |G| ≥ 0, its positive and negative parts are |G|q⁺ and |G|q⁻ (ENNReal.ofReal(|G|q) = ENNReal.ofReal|G|·ENNReal.ofReal q, and likewise for −q). By integral_eq_lintegral_pos_part_sub_lintegral_neg_part again, ∫_M |G| q dH^{n+1} = (∫_M |G| q⁺ dH^{n+1}).toReal − (∫_M |G| q⁻ dH^{n+1}).toReal.
8. Comparing steps 6 and 7 gives ∫_ℝ ∫_{S_t} q dHⁿ dt = ∫_M |G| q dH^{n+1}. This proves (3). ∎

## Key steps

1. (CF) for |q|, q⁺, q⁻ gives a.e.-measurable slice integrals A, A⁺, A⁻ with ∫A = ∫_M |G||q| < ∞.
2. A(t) < ∞ for a.e. t, so q is integrable on a.e. slice and F(t) = A⁺(t).toReal − A⁻(t).toReal there.
3. |F| ≤ A gives integrability of F on ℝ.
4. ∫F = (∫A⁺).toReal − (∫A⁻).toReal = (∫_M|G|q⁺).toReal − (∫_M|G|q⁻).toReal = ∫_M |G|q.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1, mathlib 25730c7c); diff -q snapshot project/GMT/Ch07/Contract.lean vs workspace GMT/Ch07/Contract.lean (identical; Submission.lean is a byte copy)`
- `rg -n 'theorem alternatizeUncurryFin_apply|eq_smul_basis_det|theorem det_to_matrix_orthonormalBasis_real|theorem finrank_add_inf_finrank_orthogonal|theorem exists_measurable_superset_of_null|theorem integral_eq_lintegral_pos_part_sub_lintegral_neg_part|theorem integral_toReal|theorem ae_lt_top|theorem lintegral_eq_zero_iff|lemma norm_alternatizeUncurryFin_le|theorem le_opNorm' over snapshot mathlib/Mathlib (all found)`
- `rg -n 'coarea|co-area|Coarea' project/GMT --glob '*.lean' (only GMT/Ch02/Submission.lean coareaJacobian / CoareaFormula, a Ch02 contract Prop not imported by GMT.Ch07); rg -n 'alternatizeUncurryFin ((innerSL|smulRight' project/GMT/Ch07 project/GMT/Ch06 (no match)`
- `grep -n 'theorem HasApproximateTangentSpaceAt.unique|theorem CountablyRectifiable.mono|theorem countablyRectifiable_of_measure_zero' in the pinned simongmt Poincare/SimonGMT/Chapter03/Rectifiable.lean (found at lines 232, 55, 45); sed Chapter06/Forms.lean, Currents.lean, Mass.lean (Covector, DifferentialForm, TestFormOn, covectorEuclideanNorm)`
- `#synth probes after import GMT.Ch07.Submission: FiniteDimensional ℝ (Covector (Euclid P) n), SecondCountableTopology (MultiVector P n), TopologicalSpace (Covector →L[ℝ] Euclid P →L[ℝ] Covector) fail; NormedAddCommGroup/NormedSpace of Covector and of Covector →L[ℝ] Covector succeed`
- `python3 -I scans of dag.json: lean_statement/status of coarea, lipschitz_leibniz, slice_identity, im_calculus; lean_name patterns interior_product|orient_opNorm|norm_le_one; all nodes under root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1 (no accepted node equal to a proposed child)`
- `git show 2af75d6921b01a9c889a45103692ca0af95ea394:GMT/Ch07/Submission.lean line 1760 vs dag.json im_calculus lean_statement (whitespace-normalised identical); grep -c dtc_bc_lc_sl_sf_ dag.json (0); git log --all -S dtc_bc_lc_sl_sf_ over 6418 refs (no match)`
- `lake env lean on /tmp/sfdecomp/lean/challenges/Challenge_<key>.lean (generated by verifier gmt-compare.py child_modules after lean_contract.validate_lean_statement), /tmp/sfdecomp/lean/Assembly.lean and AssemblyAx.lean (#print axioms), /tmp/sfdecomp/val_unit/Proof.lean, /tmp/sfdecomp/val_rest/All.lean`
- `sed -n 1140,1330p book/chapter-06.txt (Simon Ch. 6 §4: 4.1 ll. 1156–1183, 4.2 ll. 1185–1196, 4.3 ll. 1208–1218, 4.4 ll. 1221–1233, proof of 4.5 ll. 1245–1323)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-1214e51a12/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-09907e06c7/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/sfdecomp/lean/Assembly.lean`
- `/tmp/sfdecomp/lean/challenges`
- `/tmp/sfdecomp/val_unit/Proof.lean`
- `/tmp/sfdecomp/val_rest/All.lean`

The pinned snapshot has every Mathlib lemma cited in the child proofs:
- alternatizeUncurryFin_apply and norm_alternatizeUncurryFin_le;
- AlternatingMap.eq_smul_basis_det and OrthonormalBasis.det_to_matrix_orthonormalBasis_real;
- Submodule.finrank_add_inf_finrank_orthogonal;
- exists_measurable_superset_of_null, integral_eq_lintegral_pos_part_sub_lintegral_neg_part, integral_toReal, ae_lt_top', lintegral_eq_zero_iff';
- ContinuousAlternatingMap.le_opNorm.
The pinned SimonGMT package has HasApproximateTangentSpaceAt.unique, CountablyRectifiable.mono and countablyRectifiable_of_measure_zero.

The snapshot project has no slicing lemma, no lemma on the interior product of orientations, and no co-area lemma usable from GMT.Ch07. The only co-area item is the Ch02 contract Prop CoareaFormula, which Ch07 does not import.

No accepted DAG node equals any proposed new child. In particular dor_lmbsf_interior_product_orientation is still decomposing, so new names with the unique prefix dtc_bc_lc_sl_sf_ are used. The accepted im_calculus declaration is reused with its identical type.

Lean checks:
- All six child types elaborate in the comparator's contract-mode challenge modules.
- All five new children are proved in Lean.
- A 420-line assembly derives the exact frozen parent type from them plus coarea and lipschitz_leibniz.
- In each case the axioms are propext, Classical.choice and Quot.sound only.
