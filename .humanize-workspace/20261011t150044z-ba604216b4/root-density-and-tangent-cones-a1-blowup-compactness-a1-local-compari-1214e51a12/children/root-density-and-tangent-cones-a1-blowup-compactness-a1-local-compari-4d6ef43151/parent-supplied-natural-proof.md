# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.slice_family-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.slice_family-a1.imrep_of_subset-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the supplied proof of the parent node slice_family, step 5(a). There it is checked that Simon's slice (M₊ ∩ f⁻¹(t), θ, ξ⌞ν) of Definition 4.4 (book/chapter-06.txt ll. 1221–1233, printed p. 155; ξ₊ at ll. 1200–1205) is an integer multiplicity triple. Here it is stated for a general Borel pair A ⊆ S; in the application A = M₊ ∩ f⁻¹(t) and S = M ∩ f⁻¹(t). Dependency: im_calculus (a), the locality of approximate tangent spaces.

1. Local finiteness of S. Let K ⊆ ℝ^P be compact. K is closed, hence Borel, and θ ≥ 1 on S ∩ K because θ is a positive integer on S. Hence Hⁿ(S ∩ K) = ∫_{S∩K} 1 dHⁿ ≤ ∫_{S∩K} θ dHⁿ < ∞.
2. Locality of tangent spaces. Apply im_calculus (a) with U := ℝ^P (open), M := A and M' := S. Its hypotheses hold: A and S are Borel, A ⊆ S ⊆ ℝ^P, and Hⁿ(S ∩ K) < ∞ for every compact K by step 1. It yields: for Hⁿ-a.e. x ∈ A and every linear subspace Q, A has approximate tangent space Q at x if and only if S does.
3. Orientation property. Intersect the Hⁿ⌞A-a.e. set given by the hypothesis with the one given by step 2. For x in the intersection, take Q from the hypothesis. S has approximate tangent space Q at x, so by step 2 A has approximate tangent space Q at x; and ζ(x) is a unit orientation of Q. Hence for Hⁿ-a.e. x ∈ A there is Q with HasApproximateTangentSpaceAt n A x Q and IsUnitOrientationOf (ζ x) Q.
4. Define R : IMRep univ n by carrier := A, mult := θ, orient := ζ, and check the fields:
 - measurableSet_carrier: A is Borel;
 - carrier_subset: A ⊆ ℝ^P = univ;
 - rectifiable: S is countably n-rectifiable and A ⊆ S, so A is countably n-rectifiable (SimonGMT CountablyRectifiable.mono);
 - measurable_mult: θ is Borel;
 - mult_pos: for x ∈ A we have x ∈ S, so θ(x) > 0;
 - locallyIntegrable_mult: for compact K ⊆ ℝ^P, A ∩ K ⊆ S ∩ K, so ∫_{A∩K} θ dHⁿ ≤ ∫_{S∩K} θ dHⁿ < ∞ by monotonicity of the integral in the domain;
 - aestronglyMeasurable_orient: ζ is a.e. strongly measurable for Hⁿ⌞A by hypothesis;
 - orients: step 3.
5. By construction R.carrier = A, R.mult = θ and R.orient = ζ. ∎

## Key steps

1. θ ≥ 1 on S turns ∫_{S∩K} θ < ∞ into Hⁿ(S ∩ K) < ∞ for compact K.
2. im_calculus (a) with U = ℝ^P, M = A, M' = S: a.e. on A, A and S have the same approximate tangent spaces.
3. So a.e. on A, A has approximate tangent space Q and ζ(x) is a unit orientation of Q.
4. Assemble the IMRep fields: Borel carrier, rectifiability by monotonicity, positive Borel multiplicity, local integrability by monotonicity, measurable orientation, orients.

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
