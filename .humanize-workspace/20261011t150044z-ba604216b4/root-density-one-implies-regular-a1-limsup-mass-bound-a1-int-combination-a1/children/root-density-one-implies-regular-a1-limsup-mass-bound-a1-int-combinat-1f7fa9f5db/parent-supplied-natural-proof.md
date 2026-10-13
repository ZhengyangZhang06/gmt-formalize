# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.int_combination-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.int_combination-a1.mass_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the final sentence of step 5 (0 ≤ θ ≤ |p₁|θ₁1_{M₁} + |p₂|θ₂1_{M₂}) and step 8 of the supplied proof of the selected theorem. Step 8 is reproduced in step 5 below.
Departure: the supplied proof reads the multiplicity bound off its explicit formula θ = |m|, by the triangle inequality. Here R is an arbitrary IMRep satisfying the identity (†). This is what the reused construction (sibling combination_construction) exports: (†), not its formula. So the same bound is recovered Hⁿ-a.e. from (†), using the normalisation of step 1(a) in the Euclidean coefficient norm (sibling orientation_pairing). Step 8 only integrates the bound, so an a.e. bound suffices.
Notation:
 - μ := μHE[n]; for c ∈ ℤ, |c| = c.natAbs.
 - For an IMRep R' = (M', θ', ξ') in U put g_{R'} := 1_{M'}θ' : ℝ^P → ℕ and F_{R'} := 1_{M'}θ'ξ' : ℝ^P → Λₙ(ℝ^P).
 - The hypothesis reads F_R = p₁F_{R₁} + p₂F_{R₂} μ-a.e.; μ_{R'} := R'.measure = (μ⌞M').withDensity θ'.
 - |β| := covectorEuclideanNorm β.
1. Good points. M, M₁, M₂ are Borel, so the field orients of each of R, R₁, R₂ gives: for μ-a.e. x, if x ∈ M' then ξ'(x) is a unit orientation of some subspace Q (IsUnitOrientationOf (ξ' x) Q). Let G be the set of x at which these three implications and the hypothesis identity all hold. Then μ(ℝ^P ∖ G) = 0.
2. One term. Let R' be an IMRep and x a point such that x ∈ M' implies that ξ'(x) is a unit orientation of some Q. Let β be an n-covector with |β| ≤ 1. Then |F_{R'}(x)(β)| ≤ g_{R'}(x):
 - if x ∉ M', both sides are 0;
 - if x ∈ M', then F_{R'}(x)(β) = θ'(x)·ξ'(x)(β), and orientation_pairing (i) gives |ξ'(x)(β)| ≤ |β| ≤ 1, so |F_{R'}(x)(β)| ≤ θ'(x) = g_{R'}(x).
3. Pointwise multiplicity bound. Claim: for x ∈ G, g_R(x) ≤ |p₁|g_{R₁}(x) + |p₂|g_{R₂}(x) in ℕ.
 - If x ∉ M, then g_R(x) = 0.
 - If x ∈ M, then ξ(x) is a unit orientation of some Q, since x ∈ G. orientation_pairing (ii) gives an n-covector β with |β| ≤ 1 and ξ(x)(β) = 1. Evaluating the identity at β and using step 2 for R₁ and R₂ (x ∈ G):
  θ(x) = θ(x)·ξ(x)(β) = F_R(x)(β) = p₁F_{R₁}(x)(β) + p₂F_{R₂}(x)(β) ≤ |p₁|·|F_{R₁}(x)(β)| + |p₂|·|F_{R₂}(x)(β)| ≤ |p₁|g_{R₁}(x) + |p₂|g_{R₂}(x).
 This is a real inequality between natural numbers, so it holds in ℕ. Hence
 (‡) g_R ≤ |p₁|g_{R₁} + |p₂|g_{R₂} μ-a.e.
4. Measures as integrals. For an IMRep R' and a Borel set s: μ_{R'}(s) = ∫⁻_s θ' d(μ⌞M') = ∫⁻_{s∩M'} θ' dμ = ∫⁻_s g_{R'} dμ (Mathlib withDensity_apply, Measure.restrict_restrict, lintegral_indicator). Also g_{R'} is Borel, since θ' is measurable and M' is Borel.
5. Comparison (step 8). Let s be Borel. By (‡), which holds μ⌞s-a.e. since μ⌞s ≪ μ, monotonicity of the lower integral gives the first inequality below. Additivity for measurable integrands and constants pulled out of ∫⁻ give the next equality, and step 4 the last:
 μ_R(s) = ∫⁻_s g_R dμ ≤ ∫⁻_s (|p₁|g_{R₁} + |p₂|g_{R₂}) dμ = |p₁|∫⁻_s g_{R₁} dμ + |p₂|∫⁻_s g_{R₂} dμ = |p₁|μ_{R₁}(s) + |p₂|μ_{R₂}(s).
 The right-hand side is (|p₁|•μ_{R₁} + |p₂|•μ_{R₂})(s), where the scalars |pᵢ| ∈ [0, ∞) act on measures. Two measures that compare on all Borel sets compare as measures (Mathlib Measure.le_iff). Hence R.measure ≤ (p₁.natAbs : ℝ≥0∞) • R₁.measure + (p₂.natAbs : ℝ≥0∞) • R₂.measure. ∎

## Key steps

1. A.e. on ℝ^P the hypothesis identity holds and the orientations of R, R₁, R₂ are unit orientations on their carriers.
2. For |β| ≤ 1 and a.e. x, |(1_{M'}θ'ξ')(x)(β)| ≤ 1_{M'}θ'(x), by orientation_pairing (i).
3. At a.e. x ∈ M pick β with |β| ≤ 1 and ξ(x)(β) = 1 (orientation_pairing (ii)); evaluating (†) at β gives θ(x) ≤ |p₁|1_{M₁}θ₁(x) + |p₂|1_{M₂}θ₂(x).
4. μ_{R'}(s) = ∫⁻_s 1_{M'}θ' dHⁿ for Borel s; integrate the a.e. bound to get μ_R(s) ≤ |p₁|μ_{R₁}(s) + |p₂|μ_{R₂}(s), hence μ_R ≤ |p₁|μ_{R₁} + |p₂|μ_{R₂}.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606d, mathlib 25730c7c)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical)`
- `rg -c -g '*.lean' 'rsdic_|regcomp_|dor_lmb_' local-references/123e8435b4a2469b/project (no match, exit 1: accepted DAG declarations live on branches, not in the frozen snapshot)`
- `rg -n 'structure IMRep|def IMRep.measure|def IMRep.action|def IsUnitOrientationOf' local-references/123e8435b4a2469b/project`
- `rg -n 'theorem le_iff\b|theorem withDensity_apply\b|theorem lintegral_indicator\b|theorem lintegral_mono_ae\b|theorem lintegral_const_mul\b|theorem lintegral_add_left\b|theorem restrict_restrict\b|theorem smul_apply\b' local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory`
- `rg -n 'det_to_matrix_orthonormalBasis|eq_smul_basis_det|euclideanHausdorffMeasure_smul₀|hausdorffMeasure_smul₀|exists_orthonormalBasis_extension|theorem le_opNorm|theorem ae_restrict_iff|theorem ae_eq_mk' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -n 'def HasApproximateTangentSpaceAt|theorem HasApproximateTangentSpaceAt.unique|theorem CountablyRectifiable.mono|theorem countablyRectifiable_iUnion|def blowUpMap' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'theorem simon_theorem_3_6|theorem simon_remark_3_7_hausdorff' simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean; rg 'simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure' simongmt (Chapter02/AreaLiteral.lean)`
- `grep -n 'def covectorEuclideanNorm|abbrev Covector' simongmt/Poincare/SimonGMT/Chapter06/{Mass,Forms}.lean`
- `dag.json scan: lean_name/lean_statement/status of rsdic_ae_tangent_iff_of_subset, rsdic_unitOrientation_eq_or_eq_neg, rsdic_exists_imrep_int_combination, rsdic_imrep_action_int_combination, regcomp_unit_orientation_pairing (all accepted, identical); dor_lmb_ic_measure_le_of_weighted_orient_eq unreserved; duplicate-lean_name scan and cross-branch reuse precedent (im_calculus decomposition-v1)`
- `git show {a157a5f,fe95347,0af9ed5,faacb9c,2a16c5a}:GMT/Ch07/Submission.lean; git merge-base --is-ancestor checks`
- `python3 -I: verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py contract_scope/child_modules on all six lean_statements`
- `lake env lean /tmp/ic-decomp/Types.lean, /tmp/ic-decomp/Assembly.lean, /tmp/ic-decomp/cmp/*_NodeChallenge.lean, /tmp/ic-decomp/ChildCand.lean, /tmp/ic-decomp/ParentMerged.lean, ParentMerged6.lean, ParentMergedAlt.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/CompleteLattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Module.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-int-combination-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-tangent-locality-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/decomposition-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/decomposition-v1.json`
- `/tmp/ic-decomp/Types.lean`
- `/tmp/ic-decomp/Assembly.lean`
- `/tmp/ic-decomp/ChildCand.lean`
- `/tmp/ic-decomp/ParentMerged6.lean`

Snapshot: project b4d606d, mathlib 25730c7c. Its Contract.lean is byte-identical to the workspace contract, which defines IMRep, IsUnitOrientationOf, IMRep.action, IMRep.Represents and IMRep.measure.

The snapshot contains no rsdic_/regcomp_/dor_lmb_ declarations. The accepted ones are on DAG branches; their candidate commits a157a5f, fe95347, 0af9ed5, faacb9c and 2a16c5a were inspected with git show.

Library facts used in the child proofs:
- Mathlib Measure.le_iff, withDensity_apply, lintegral_indicator, Measure.restrict_restrict, lintegral_const_mul, lintegral_add_left, lintegral_mono_ae, Measure.smul_apply.
- Mathlib ContinuousAlternatingMap.le_opNorm, OrthonormalBasis.det_to_matrix_orthonormalBasis_real, AlternatingMap.eq_smul_basis_det, Orthonormal.exists_orthonormalBasis_extension, Measure.euclideanHausdorffMeasure_smul₀.
- SimonGMT HasApproximateTangentSpaceAt (and .unique), CountablyRectifiable.mono, countablyRectifiable_iUnion, blowUpMap, covectorEuclideanNorm.
- The Upper Density Theorem (Simon Ch. 1, 3.6), formalized as simon_theorem_3_6.

No library lemma gives the mass bound for an integer combination; it is the one new child.

Lean checks:
- All six types elaborate in the exact comparator scope and pass validate_lean_statement.
- The new child and the parent assembly have complete proofs using only standard axioms.
- The simulated overlay merge compiles.
