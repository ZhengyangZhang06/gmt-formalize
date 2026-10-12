# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.cone-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.cone-a1.wedge_vanishes-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Sources.
- Proof of Simon 7.3.1 (chapter-07.txt lines 358–359): "That is x ∈ T_x spt C for μ_C-a.e. x, so in particular x ∧ C⃗ = 0 μ_C-a.e." This is step 5 of the parent proof.
- Simon Ch. 6, 3.1 (chapter-06.txt lines 733–742): ξ(x) = τ₁∧⋯∧τₙ for an orthonormal basis τ of T_xM.

Notation. M = R.carrier, ξ = R.orient, μ = R.measure. T_x = approxTangentPlane n M x and p_x is its starProjection. ι_xβ := ContinuousAlternatingMap.curryLeft β x, so (ι_xβ)(v_1, …, v_n) = β(x, v_1, …, v_n).

1. Choosing good points. μ = (Hⁿ⌞M).withDensity θ ≪ Hⁿ⌞M, so the Hⁿ⌞M-a.e. property `orients` also holds μ-a.e. Together with the hypothesis: for μ-a.e. x there is Q with HasApproximateTangentSpaceAt n M x Q and IsUnitOrientationOf (ξ x) Q, and also p_x x = x. Fix such an x and an (n+1)-covector β.

2. x ∈ Q. The `if` in approxTangentPlane is satisfied (witness Q). The chosen subspace Q' satisfies HasApproximateTangentSpaceAt n M x Q', and HasApproximateTangentSpaceAt.unique gives Q' = Q. So T_x = Q and p_Q x = x. An orthogonal projection fixes exactly the vectors of its range (Submodule.starProjection_eq_self_iff), so x ∈ Q.

3. Orientation data. IsUnitOrientationOf (ξ x) Q means: there is an orthonormal τ : Fin n → ℝ^P with span(range τ) = Q, and either ξ(x)(α) = α(τ) for all α, or ξ(x)(α) = −α(τ) for all α.

4. Vanishing on Q.
- The map y ↦ (ι_yβ)(τ) = β(y, τ_0, …, τ_{n−1}) is linear in y, because curryLeft β is a continuous linear map.
- For y = τ_b, the (n+1)-tuple (τ_b, τ_0, …, τ_{n−1}) has equal entries at the distinct positions 0 and b+1. Since β is alternating, β vanishes on it.
- Hence the linear map vanishes on span(range τ) = Q (span induction over generators, 0, sums and scalar multiples). In particular it vanishes at y = x ∈ Q.

5. Conclusion. ξ(x)(ι_xβ) = ±(ι_xβ)(τ) = ±β(x, τ) = 0. As β was arbitrary, the conclusion holds at μ-a.e. x. The case n = 0 is included: then Q = span ∅ = {0} and x = 0. ∎

Implementation note. A complete Lean proof of this exact statement compiled during decomposition, using withDensity_absolutelyContinuous, Measure.AbsolutelyContinuous.ae_le, dif_pos with Exists.choose_spec and HasApproximateTangentSpaceAt.unique, Submodule.starProjection_eq_self_iff, Submodule.span_induction, and ContinuousAlternatingMap.map_eq_zero_of_eq at positions 0 and b.succ.

## Key steps

1. μ ≪ Hⁿ⌞M transfers `orients` to μ-a.e. x.
2. Uniqueness of approximate tangent planes identifies approxTangentPlane with the oriented plane Q, and p_Q x = x gives x ∈ Q.
3. y ↦ β(y, τ) is linear and vanishes on each τ_b (repeated entry), hence on Q ∋ x.
4. Therefore ξ(x)(ι_xβ) = ±β(x, τ) = 0 for every β.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp … GMT/Ch07/Submission.lean (identical); git rev-parse HEAD = b4d606db; git -C lake-packages-25730c7c/simongmt rev-parse HEAD = 2b366308; git -C lake-packages-25730c7c/mathlib rev-parse HEAD = 25730c7c`
- `grep -nE '^(theorem|def)' simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean (IsStationaryIn.satisfiesStationaryMonotonicity, SatisfiesStationaryMonotonicity, normalizedBallMass, monotonicityDefect, radialNormalSq_eq, tangentialDivergence_integrable_of_isAdmissible); sed -n 1,230p Chapter04/Basic.lean (structure RectifiableVarifold); sed -n 1,80p Chapter04/MultiplicityBridge.lean (weight_eq_carrier_withDensity, ae_weight_iff_ae_carrier)`
- `grep -nE '^(theorem|def)' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.unique, approximateTangentField_ae_eq, IsLocallyIntegrableMultiplicity)`
- `cat simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents,AffineCurrentPushforward,CurrentLocalEquality}.lean; sed -n 100,200p Chapter06/FormsDuality.lean (wedgeCovectors, wedgeCovectors_apply_det); sed -n 20,60p Chapter06/Mass.lean (covectorEuclideanNorm)`
- `grep -rln Binet mathlib/Mathlib (only GoldenRatio, CrossProduct: no Cauchy–Binet); Mathlib/Analysis/Normed/Module/Alternating/Curry.lean (curryLeft, curryLeftLI, curryLeft_same); grep theorem Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean (alternatizeUncurryFin_apply, alternatizeUncurryFin_curryLeft, map_insertNth); grep 'def extDeriv' Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean; head Mathlib/Analysis/Calculus/DifferentialForm/VectorField.lean; grep theorem Mathlib/Analysis/InnerProductSpace/NormDet.lean; grep det_mul Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean; grep 'lemma removeNth_' Mathlib/Data/Fin/Tuple/Basic.lean`
- `inventory of all lean_name values in runs/20261011T150044Z-ba604216b4 (dag.json and node JSON files): 100 reserved names; grep -rl for each of the six proposed names: 0 hits`
- `sed -n 300,370p book/chapter-07.txt (7.3.1 and proof, lines 326-360); sed -n 85,112p, 430,480p, 540,580p, 733,760p book/chapter-06.txt (1.5-1.7, 2.25-2.27, 2.33, 3.1); sed -n 205,320p book/chapter-04.txt (3.1-3.6); grep -n 'approximate tangent' book/chapter-03.txt (1.4-1.5)`
- `python3 -I scripts/gen.py: verifier gmt-compare.contract_scope + child_modules(mode=contract) and lean_contract.validate_lean_statement on the six child types; lake env lean Check/Ch_*.lean and Check/Sol_*.lean`
- `lake env lean Check/Types.lean, Check/Assembly.lean, Check/Cartan.lean, Check/Wedge.lean, Check/Unfold.lean, Check/Mono.lean, Check/Radial.lean, each with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-radial-tangency-of-ball-ratio-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/MultiplicityBridge.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/VectorField.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/cone-decomp-iFw2Y3/proj/Check/Types.lean`
- `/tmp/cone-decomp-iFw2Y3/proj/Check/Assembly.lean`
- `/tmp/cone-decomp-iFw2Y3/proj/Check/Cartan.lean`
- `/tmp/cone-decomp-iFw2Y3/proj/Check/Wedge.lean`
- `/tmp/cone-decomp-iFw2Y3/proj/Check/Unfold.lean`
- `/tmp/cone-decomp-iFw2Y3/proj/Check/Mono.lean`
- `/tmp/cone-decomp-iFw2Y3/proj/Check/Radial.lean`
- `/tmp/cone-decomp-iFw2Y3/scripts/gen.py`
- `/tmp/cone-decomp-iFw2Y3/scripts/children.json`

The snapshot contract (project b4d606d, Mathlib 25730c7c, simongmt 2b36630) is byte-identical to the workspace Contract.lean and Submission.lean, so all six child types elaborate after `import GMT.Ch07.Submission` in the contract scope (namespace GMT.Ch07 with its opens).

SimonGMT supplies:
- the exact stationary monotonicity identity (Chapter04 RectifiableVarifold.IsStationaryIn.satisfiesStationaryMonotonicity, closed balls, all n);
- the weight bridge weight_eq_carrier_withDensity;
- HasApproximateTangentSpaceAt.unique;
- wedgeCovectors_apply_det;
- the proper affine push-forward used by blowUp.
The monotonicity results are stated for the strengthened RectifiableVarifold, whose tangent-projection measurability field is exactly what child 1 provides; a scratch bridge proved child 2 from child 1 with standard axioms. The submission may import Chapter04.FirstVariation and MultiplicityBridge (the comparator only byte-checks frozen inputs).

Mathlib supplies extDeriv = alternatizeUncurryFin ∘ fderiv, ContinuousAlternatingMap.curryLeft/curryLeftLI and alternatizeUncurryFin_curryLeft; with these the Euler-field Cartan identity (child 5) and the x ∧ ξ = 0 lemma (child 4) were proved outright. Mathlib has no Cauchy–Binet theorem and no Lie derivative or Cartan formula, so child 1 proves its Gram identity by the Leibniz expansion.

The conditional assembly of the selected type from dtc_mass_eq_measure and children 3, 4 and 6 compiles with propext, Classical.choice and Quot.sound only. None of the six names occurs anywhere else in the run.
