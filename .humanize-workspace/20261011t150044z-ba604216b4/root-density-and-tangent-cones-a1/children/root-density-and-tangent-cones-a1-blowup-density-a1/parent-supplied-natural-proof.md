# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: proof of Simon 7.3.1, displays (1) and (4) and the sentence after (4) (chapter-07.txt lines 329–341); step 5 of the parent proof. Uses the siblings mass_eq_measure (M) and blowup_scaling (BU). Write η_j := η_{x,λ_j}, S_j := η_{j#}T, ω_n := unitBallVolume n ∈ (0, ∞) and a(ρ) := ω_nρⁿθ (θ ≥ 0 by HasMassDensity).
1. Representations. Let R represent T and R_C represent C. By BU(2), for each j there is a representation R_j of S_j with μ_{R_j}(B) = λ_j^{−n}μ_R(η_j⁻¹(B)) for Borel B. Applying MassMeasuresConverge to (R_j) and R_C: ∫f dμ_{R_j} → ∫f dμ for every f ∈ C_c(ℝ^P), where μ := μ_{R_C}. μ is finite on bounded sets (local integrability of R_C).
2. Book (1). For ρ > 0, η_j⁻¹(B_ρ(0)) = B_{λ_jρ}(x), so μ_{R_j}(B_ρ(0)) = λ_j^{−n}μ_R(B_{λ_jρ}(x)). For j large, B_{λ_jρ}(x) ⊆ U, and M gives μ_R(B_{λ_jρ}(x)) = M_{B_{λ_jρ}(x)}(T). Hence μ_{R_j}(B_ρ(0)) = ω_nρⁿ·M_{B_{λ_jρ}(x)}(T)/(ω_n(λ_jρ)ⁿ) → ω_nρⁿθ = a(ρ), because λ_jρ ↓ 0 and HasMassDensity T x θ.
3. Book (4). Let ρ > 0 with μ(∂B_ρ(0)) = 0. (i) For a compact F ⊆ B_ρ(0) choose f ∈ C_c(B_ρ(0)) with 0 ≤ f ≤ 1, f = 1 on F; then μ(F) ≤ ∫f dμ = lim∫f dμ_{R_j} ≤ liminf μ_{R_j}(B_ρ(0)); by inner regularity of the finite measure μ⌞B_ρ(0), μ(B_ρ(0)) ≤ liminf μ_{R_j}(B_ρ(0)). (ii) For δ > 0 choose g ∈ C_c(ℝ^P), 0 ≤ g ≤ 1, g = 1 on closedBall(0, ρ), spt g ⊆ B_{ρ+δ}(0); then lim sup μ_{R_j}(B_ρ(0)) ≤ lim ∫g dμ_{R_j} = ∫g dμ ≤ μ(B_{ρ+δ}(0)), and letting δ ↓ 0, lim sup μ_{R_j}(B_ρ(0)) ≤ μ(closedBall(0, ρ)) = μ(B_ρ(0)). So μ_{R_j}(B_ρ(0)) → μ(B_ρ(0)), and with step 2, μ(B_ρ(0)) = a(ρ).
4. The spheres ∂B_ρ(0), ρ > 0, are pairwise disjoint and μ is finite on each closedBall(0, m); hence μ(∂B_ρ(0)) > 0 for at most countably many ρ, and the set D of ρ > 0 with μ(∂B_ρ(0)) = 0 is dense in (0, ∞). For arbitrary ρ > 0 choose ρ_i ∈ D with ρ_i ↑ ρ; B_ρ(0) = ⋃_i B_{ρ_i}(0), so by continuity from below and step 3, μ(B_ρ(0)) = lim μ(B_{ρ_i}(0)) = lim a(ρ_i) = a(ρ) ("by monotonicity in ρ and left-continuity").
5. By M (U = ℝ^P), M_{B_ρ(0)}(C) = μ(B_ρ(0)) = ω_nρⁿθ = unitBallVolume n · ofReal(ρⁿ) · ofReal θ for every ρ > 0.
6. HasMassDensity C 0 θ: θ ≥ 0, and for every ρ > 0, M_{B_ρ(0)}(C)/(ω_n·ofReal(ρⁿ)) = ofReal θ because ω_n·ofReal(ρⁿ) ∈ (0, ∞); so the quotient is constant on (0, ∞) and tends to ofReal θ as ρ ↓ 0.

## Key steps

1. Push a representation of T forward to the blow-ups (blowup_scaling) and feed it into MassMeasuresConverge.
2. Scaling: μ_{S_j}(B_ρ(0)) = λ_j^{−n}M_{B_{λ_jρ}(x)}(T) → ω_nρⁿθ (book (1)).
3. Weak convergence of measures gives μ_{S_j}(B_ρ(0)) → μ_C(B_ρ(0)) whenever μ_C(∂B_ρ(0)) = 0 (book (4)); left continuity extends the identity to all ρ.
4. mass_eq_measure converts to M_{B_ρ(0)}(C) = ω_nρⁿθ, and the constant quotient gives HasMassDensity C 0 θ.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp … GMT/Ch07/Submission.lean (identical; snapshot project b4d606d, mathlib 25730c7c)`
- `rg -n 'def GeometricCurrentOn.massOn|massAdmissibleOn|massOn_le_liminf|def GeometricCurrentOn.support|zeroRegion|restrictDomain|affinePushforward|boundary_affinePushforward|exteriorDerivative_affinePullbackForm|instance .*Zero' simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,AffineCurrentPushforward}.lean`
- `rg -n 'structure RectifiableVarifold|exp_normalizedBallMass_monotoneOn|upperSemicontinuousOn_stationaryDensity|tendsto_densityQuotient_real' simongmt/Poincare/SimonGMT/Chapter04/{Basic,MeanCurvature,Density}.lean`
- `rg -n 'def CountablyRectifiable|CountablyRectifiable.mono|countablyRectifiable_iUnion|def HasApproximateTangentSpaceAt|HasApproximateTangentSpaceAt.unique' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; rg -n 'Upper Density|upperDensity' simongmt/Poincare/SimonGMT/Chapter01`
- `rg -n 'euclideanHausdorffMeasure_zero|euclideanHausdorffMeasure_smul₀|homothety_image' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; rg -n 'hausdorffMeasure_zero_singleton' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean; rg -n 'theorem sdiff_subset|alias diff_subset' mathlib/Mathlib/Order/BooleanAlgebra/Set.lean`
- `rg -l 'dtc_' runs/20261011T150044Z-ba604216b4 (no match) and lean_name inventory of dag.json / node JSON files (no collision)`
- `contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') from verifier/gmt-compare.py; lean_contract.validate_lean_statement on all ten child types`
- `lake build GMT.Ch07.Submission (scratch copy /tmp/dtc-decomp-kWMgQM/proj); lake env lean Check/Exact.lean; lake env lean Check/AssemblyExact.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/BooleanAlgebra/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Density.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/dtc-decomp-kWMgQM/proj/Check/Exact.lean`
- `/tmp/dtc-decomp-kWMgQM/proj/Check/AssemblyExact.lean`
- `/tmp/dtc-decomp-kWMgQM/scripts/stmts.py`

The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean. The SimonGMT library supplies the frozen objects used by the children (GeometricCurrentOn, massOn with the Euclidean coefficient norm and massAdmissibleOn, support/zeroRegion, restrictDomain, affinePushforward with boundary_affinePushforward and exteriorDerivative_affinePullbackForm, the Zero instance, WeaklyConvergesOn.massOn_le_liminf) and reusable analytic results (Chapter04 bounded-mean-curvature monotonicity exp_normalizedBallMass_monotoneOn and upperSemicontinuousOn_stationaryDensity, but for the strengthened RectifiableVarifold, so a bridge from IMRep is needed; Chapter03 CountablyRectifiable.mono, countablyRectifiable_iUnion, HasApproximateTangentSpaceAt and its uniqueness; Chapter01 Upper Density Theorem 3.6). It does not contain Federer–Fleming compactness, slicing, the flat-norm theorem 7.2, push-forward by non-affine maps, or the representation/mass identity 6.3.2(3); these are cited from Simon or proved in the children. Mathlib facts used: μHE[0] = μH[0] with μH[0]{x} = 1 (counting measure), μHE[d] scaling under homotheties, Set.sdiff_subset (Set.diff_subset is deprecated, so the Lean types use sdiff_subset). All ten child types elaborate in the comparator scope, the conditional assembly from the exact strings proves DensityAndTangentCones with only propext, Classical.choice and Quot.sound, and no dtc_ name occurs elsewhere in the run.
