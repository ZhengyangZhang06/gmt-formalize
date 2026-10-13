# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.slice_family-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.slice_family-a1.cutoff_gradient-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the supplied proof of the parent node slice_family, step 9(a). This is Simon Ch. 6, the chain rule (4) in the proof of 4.5(2) (book/chapter-06.txt ll. 1302–1310, printed pp. 156–157): "∇^M h = γ'(f)∇^M f H^n-a.e. on M (where we set γ'(f) = 0 when f takes the bad values t or t − ε; note that ∇^M h(x) = ∇^M f(x) = 0 for H^n-a.e. x in {x ∈ M : f(x) = c}, c any given constant)", with a = t − ε and b = t.

1. Good points. Each of the following holds for H^N⌞M-a.e. x: the three statements in (i) at x; f(x) = a ⇒ G(x) = 0; f(x) = b ⇒ G(x) = 0. A finite intersection of H^N⌞M-a.e. properties is again H^N⌞M-a.e., so for H^N⌞M-a.e. x all of them hold simultaneously. (M need not be Borel, and membership x ∈ M is never used below.) Fix such an x; we prove the three conclusions at x.
2. Tangent space. By (i), M has approximate tangent space T_xM at x.
3. H(x) ∈ T_xM. If a < f(x) < b, then H(x) = −(b − a)⁻¹G(x) is a scalar multiple of G(x) ∈ T_xM, and T_xM is a linear subspace. Otherwise H(x) = 0 ∈ T_xM.
4. Notation and claim. For δ > 0 and r > 0 put E_f(δ, r) := {y ∈ M ∩ B_r(x) : δ|y − x| < |f(y) − f(x) − ⟨G(x), y − x⟩|} and E_h(ε, r) := {y ∈ M ∩ B_r(x) : ε|y − x| < |h(y) − h(x) − ⟨H(x), y − x⟩|}. Fix ε > 0 and put δ := (b − a)ε > 0. Claim: there is r₁ > 0 such that E_h(ε, r) ⊆ E_f(δ, r) for every 0 < r < r₁.
5. Properties of γ.
 (a) γ is (b − a)⁻¹-Lipschitz on ℝ: s ↦ (b − s)/(b − a) is (b − a)⁻¹-Lipschitz, and u ↦ max{0, u} and u ↦ min{1, u} are 1-Lipschitz.
 (b) If a < s < b, then 0 < (b − s)/(b − a) < 1, so γ(s) = (b − s)/(b − a).
 (c) If s < a, then (b − s)/(b − a) > 1, so γ(s) = 1.
 (d) If s > b, then (b − s)/(b − a) < 0, so γ(s) = 0.
6. Case a < f(x) < b. Since f is continuous and (a, b) is open, there is r₁ > 0 with a < f(y) < b for all y ∈ B_{r₁}(x). For such y, by 5(b) and H(x) = −(b − a)⁻¹G(x): h(y) − h(x) − ⟨H(x), y − x⟩ = (b − f(y))/(b − a) − (b − f(x))/(b − a) + (b − a)⁻¹⟨G(x), y − x⟩ = −(b − a)⁻¹[f(y) − f(x) − ⟨G(x), y − x⟩]. Multiplying by b − a > 0, for y ∈ B_{r₁}(x) we get: ε|y − x| < |h(y) − h(x) − ⟨H(x), y − x⟩| if and only if δ|y − x| < |f(y) − f(x) − ⟨G(x), y − x⟩|. Hence E_h(ε, r) = E_f(δ, r) for 0 < r ≤ r₁.
7. Case f(x) < a. By continuity there is r₁ > 0 with f(y) < a for all y ∈ B_{r₁}(x). By 5(c), h(y) = 1 = h(x) for such y, and H(x) = 0 since a < f(x) fails. So h(y) − h(x) − ⟨H(x), y − x⟩ = 0, and ε|y − x| < 0 is false. Hence E_h(ε, r) = ∅ ⊆ E_f(δ, r) for 0 < r ≤ r₁.
8. Case f(x) > b. By continuity there is r₁ > 0 with f(y) > b for all y ∈ B_{r₁}(x). By 5(d), h(y) = 0 = h(x) for such y, and H(x) = 0. As in step 7, E_h(ε, r) = ∅ ⊆ E_f(δ, r) for 0 < r ≤ r₁.
9. Case f(x) = a or f(x) = b. By the choice of x in step 1, G(x) = 0, and H(x) = 0 because a < f(x) < b fails. By 5(a), for every y: |h(y) − h(x) − ⟨H(x), y − x⟩| = |γ(f(y)) − γ(f(x))| ≤ (b − a)⁻¹|f(y) − f(x)| = (b − a)⁻¹|f(y) − f(x) − ⟨G(x), y − x⟩|. So ε|y − x| < |h(y) − h(x) − ⟨H(x), y − x⟩| implies δ|y − x| < |f(y) − f(x) − ⟨G(x), y − x⟩|. Hence E_h(ε, r) ⊆ E_f(δ, r) for every r > 0; take r₁ := 1.
10. The four cases exhaust all possibilities for f(x), which proves the claim of step 4.
11. Limit. For 0 < r < r₁, monotonicity of H^N gives H^N(E_h(ε, r)) ≤ H^N(E_f(δ, r)). Dividing both sides in [0, ∞] by the same ENNReal.ofReal(r^N) gives H^N(E_h(ε, r))/r^N ≤ H^N(E_f(δ, r))/r^N. By (i) applied with δ > 0 in place of ε, the right side tends to 0 as r ↓ 0. The left side is ≥ 0, and the inequality holds for all r in (0, r₁), i.e. eventually along r ↓ 0 (the filter 𝓝[>] 0). By the squeeze theorem, H^N(E_h(ε, r))/r^N → 0 as r ↓ 0. Since ε > 0 was arbitrary, the third conclusion holds at x. Together with steps 1–3 this proves the statement. ∎

## Key steps

1. Restrict to the H^N⌞M-a.e. set of x where (i) holds and G(x) = 0 whenever f(x) ∈ {a, b}.
2. T_xM exists by (i); H(x) is either a multiple of G(x) ∈ T_xM or 0, so H(x) ∈ T_xM.
3. With δ := (b−a)ε, show E_h(ε,r) ⊆ E_f(δ,r) for small r in four cases. On {a<f<b} near x: h(y)−h(x)−⟨H(x),y−x⟩ = −(b−a)⁻¹[f(y)−f(x)−⟨G(x),y−x⟩]. Near {f<a} or {f>b}: h is locally constant and H(x)=0. At f(x) ∈ {a,b}: G(x)=H(x)=0 and γ is (b−a)⁻¹-Lipschitz.
4. Monotonicity of H^N and the squeeze theorem along r ↓ 0 give H^N(E_h(ε,r))/r^N → 0.

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
