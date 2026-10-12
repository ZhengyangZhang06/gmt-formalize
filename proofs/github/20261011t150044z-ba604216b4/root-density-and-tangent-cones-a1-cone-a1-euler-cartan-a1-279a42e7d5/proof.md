# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.cone-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.cone-a1.euler_cartan-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the Cartan formula behind Simon's homotopy formula (Ch. 6, 2.25–2.26, chapter-06.txt lines 441–456) and Lemma 2.33 (lines 557–567), in the form used in step 6 of the parent proof: L_Xβ = d(ι_Xβ) + ι_X dβ for X(x) = x, where L_Xβ(y) = (m+1)β(y) + Dβ(y)[y] for an (m+1)-form β.

Conventions (Mathlib).
- dω(x) = alternatizeUncurryFin(Dω(x)).
- alt := alternatizeUncurryFin satisfies (alt f)(v_0, …, v_k) = Σ_{i=0}^{k} (−1)^i f(v_i)(v_0, …, v̂_i, …, v_k).
- (f.curryLeft x)(v) = f(x, v).
Let B := Dβ(y) = fderiv ℝ β y : ℝ^P →L Λ^{m+1}, and ψ(z) := β(z).curryLeft z.

1. Derivative of ψ. Φ(f, z) := f.curryLeft z is continuous and bilinear, since curryLeft is a linear isometry Λ^{m+1} → L(ℝ^P, Λ^m). Since ψ(z) = Φ(β(z), z) and β is differentiable at y, the product rule gives Dψ(y)[u] = (Bu).curryLeft y + β(y).curryLeft u. That is, Dψ(y) = K + β(y).curryLeft with K(u) := (Bu).curryLeft y.

2. dψ(y). By additivity of alt, dψ(y) = alt(Dψ(y)) = alt(K) + alt(β(y).curryLeft) = A + (m+1)β(y).
- Here A := alt(K), so A(v) = Σ_{i=0}^{m} (−1)^i (Bv_i)(y, v_0, …, v̂_i, …, v_m).
- alt(f.curryLeft) = (m+1)f because Σ_i (−1)^i f(v_i, v_0, …, v̂_i, …) = Σ_i f(v): moving the i-th entry to the front is a cyclic permutation of sign (−1)^i (Mathlib alternatizeUncurryFin_curryLeft).

3. ι_y dβ(y). Let v = (v_0, …, v_m) and w := (y, v_0, …, v_m). Then dβ(y)(w) = Σ_{k=0}^{m+1} (−1)^k B(w_k)(w with w_k removed).
- The k = 0 term is B(y)(v).
- For k = i+1, removing entry i+1 of (y, v) leaves (y, v without v_i), so the term is (−1)^{i+1}(Bv_i)(y, v_0, …, v̂_i, …, v_m).
Hence (dβ(y)).curryLeft y = B(y) − A.

4. Conclusion. Adding steps 2 and 3: dψ(y) + (dβ(y)).curryLeft y = A + (m+1)β(y) + B(y) − A = (m+1)·β(y) + Dβ(y)[y]. ∎

Implementation note. This exact statement was proved in Lean during decomposition (about 30 lines, standard axioms):
- ContinuousLinearMap.hasFDerivAt_of_bilinear with Φ := (ContinuousAlternatingMap.curryLeftLI (n := m)).toContinuousLinearMap and hasFDerivAt_id;
- unfold exteriorDerivative and extDeriv; rewrite with alternatizeUncurryFin_add and alternatizeUncurryFin_curryLeft;
- ext v; alternatizeUncurryFin_apply; Fin.sum_univ_succ on the Fin (m+2) sum; Fin.removeNth_zero;
- the auxiliary identity Fin.removeNth i.succ (Matrix.vecCons y v) = Matrix.vecCons y (Fin.removeNth i v), proved by funext and Fin.cases with Fin.removeNth_apply and Fin.succ_succAbove_succ;
- finish with simp and ring.

## Key steps

1. Product rule: Dψ(y)u = (Dβ(y)u).curryLeft y + β(y).curryLeft u for ψ(z) = β(z).curryLeft z.
2. dψ(y) = alt(u ↦ (Dβ(y)u).curryLeft y) + (m+1)β(y), by alternatizeUncurryFin_curryLeft.
3. (dβ(y)).curryLeft y = Dβ(y)y − alt(u ↦ (Dβ(y)u).curryLeft y), by splitting off the k = 0 term.
4. Adding: d(ι_Xβ)(y) + ι_y dβ(y) = (m+1)β(y) + Dβ(y)[y].

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
