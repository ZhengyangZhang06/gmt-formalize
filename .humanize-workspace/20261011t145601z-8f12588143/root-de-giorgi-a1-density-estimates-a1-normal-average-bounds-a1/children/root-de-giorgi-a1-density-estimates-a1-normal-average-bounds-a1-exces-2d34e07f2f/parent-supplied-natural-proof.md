# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.density_estimates-a1.normal_average_bounds-a1`
- Child DAG node: `root.de_giorgi-a1.density_estimates-a1.normal_average_bounds-a1.excess_cauchy_schwarz-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

(Implementation note: AEStronglyMeasurable.inner / AEStronglyMeasurable.inner_const live in Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner, which is not in the import closure of GMT.Ch03.Submission and must be imported by the proof file.)
Source: parent proof Steps 3 and 7 (Simon Ch. 3, proof of Theorem 4.3, display (2), chapter-03.txt lines 615-620: since |ν| = 1, the averages of |ν − ν_E(x)| over B_ρ tend to 0), stated for an arbitrary set S of finite measure in place of B_ρ(x). Notation: μ_S := μ restricted to S (S need not be measurable: μ_S(ℝ^N) = μ(S) for every set S); every ∫_S below is an integral with respect to μ_S; m := μ(S).toReal; I := ∫_S ⟨ν(y), e⟩ dμ(y); J := ∫_S |ν(y) − e| dμ(y); K := ∫_S |ν(y) − e|² dμ(y); √ is Real.sqrt.

1. (Finite measure and a.e. facts.) Since μ(S) < ∞, μ_S is a finite measure with total mass μ(S); hence m is the real total mass of μ_S and ∫_S c dμ = c·m for every real constant c. Because μ_S is absolutely continuous with respect to μ, |ν| = 1 holds μ_S-a.e., and ν is μ_S-a.e. strongly measurable.

2. (Integrability; parent Step 3.) The functions f(y) := |ν(y) − e|, f(y)², and g(y) := ⟨ν(y), e⟩ are μ_S-a.e. strongly measurable, being continuous functions of ν. μ_S-a.e. they are bounded: |ν − e| ≤ |ν| + |e| = 2, so 0 ≤ f ≤ 2 and 0 ≤ f² ≤ 4; and |⟨ν, e⟩| ≤ |ν||e| = 1 (Cauchy–Schwarz in ℝ^N). An a.e.-bounded, a.e.-strongly-measurable function on a finite measure space is integrable, so f, f², g are μ_S-integrable.

3. (Pointwise identity and the value of K.) μ_S-a.e., |ν − e|² = |ν|² − 2⟨ν, e⟩ + |e|² = 1 − 2⟨ν, e⟩ + 1 = 2 − 2⟨ν, e⟩. Integrating over S (the two sides agree μ_S-a.e.; linearity of the integral, step 2, and ∫_S 2 dμ = 2m): K = 2m − 2I = 2(m − I).

4. (Case m = 0.) Since μ(S) < ∞, μ(S).toReal = 0 forces μ(S) = 0. Then μ_S is the zero measure and J = 0. The right-hand side is m · √(…) = 0 · √(…) = 0. Hence J ≤ RHS (both are 0).

5. (Cauchy–Schwarz, case m > 0; parent Step 7.) We prove J² ≤ m·K. This is the Cauchy–Schwarz (Hölder with exponents 2 and 2) inequality applied to the functions 1 and f on the finite measure space (S, μ_S), as in the parent proof (Mathlib integral_mul_le_Lp_mul_Lq_of_nonneg); for completeness, here is a direct derivation. Put c := J/m. Pointwise (f − c)² ≥ 0, and (f − c)² = f² − 2c·f + c² is μ_S-integrable by step 2. By linearity of the integral and ∫_S c² dμ = c²·m,
 0 ≤ ∫_S (f − c)² dμ = K − 2c·J + c²·m = K − 2J²/m + J²/m = K − J²/m.
 Multiplying by m > 0 gives J² ≤ m·K, i.e. by step 3, J² ≤ 2m(m − I).

6. (Conclusion, case m > 0.) J ≥ 0 because f ≥ 0. Hence, by monotonicity of √ and step 5, J = √(J²) ≤ √(2m(m − I)). Since m ≠ 0, 2m(m − I) = m² · 2(1 − m⁻¹ I). Because m² ≥ 0, √(m² · t) = √(m²)·√t = m·√t for every real t (Real.sqrt_mul with non-negative first factor, and √(m²) = m as m > 0); moreover here t = 2(1 − m⁻¹I) = 2(m − I)/m ≥ J²/m² ≥ 0 by step 5, so the radicand is non-negative under any convention for √. Therefore J ≤ m·√(2(1 − m⁻¹ I)), i.e. ∫_S |ν(y) − e| dμ(y) ≤ μ(S).toReal · √(2(1 − μ(S).toReal⁻¹ ∫_S ⟨ν(y), e⟩ dμ(y))). ∎

## Key steps

1. μ_S := μ⌞S is a finite measure with real total mass m = μ(S).toReal; |ν| = 1 μ_S-a.e. and ν is μ_S-a.e. strongly measurable.
2. f = |ν − e|, f² and ⟨ν, e⟩ are μ_S-a.e. strongly measurable and μ_S-a.e. bounded by 2, 4 and 1, hence μ_S-integrable.
3. μ_S-a.e. |ν − e|² = 2 − 2⟨ν, e⟩, so K := ∫_S |ν − e|² dμ = 2(m − I) with I := ∫_S ⟨ν, e⟩ dμ.
4. If m = 0 then μ(S) = 0, so J := ∫_S |ν − e| dμ = 0 and both sides vanish.
5. If m > 0: 0 ≤ ∫_S (f − J/m)² dμ = K − J²/m, so J² ≤ mK = 2m(m − I) (Cauchy–Schwarz).
6. J = √(J²) ≤ √(m² · 2(1 − m⁻¹I)) = m √(2(1 − m⁻¹I)).

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean`
- `cmp <snapshot>/project/GMT/Ch03/Submission.lean GMT/Ch03/Submission.lean`
- `grep -rn 'reducedBoundary\|reducedNormal\|normalAverage' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -rln 'reducedBoundary\|reducedNormal\|normalAverage' <snapshot>/project/GMT`
- `rg -n 'theorem integral_inner|theorem Filter.Tendsto.limUnder_eq|theorem integral_mul_le_Lp_mul_Lq_of_nonneg|theorem AEStronglyMeasurable.inner' <snapshot>/mathlib/Mathlib`
- `rg -n 'integral_inner\b' <snapshot>/mathlib/Mathlib`
- `rg -n 'sq_integral_le|integral_sq_le|variance_nonneg|ConvexOn.map_set_average_le|ConcaveOn.le_map_integral' <snapshot>/mathlib/Mathlib`
- `#check @integral_inner, @MeasureTheory.AEStronglyMeasurable.inner, @Filter.Tendsto.limUnder_eq, @isFiniteMeasure_restrict, @setIntegral_const, @norm_sub_sq_real, @Ioo_mem_nhdsGT after `import GMT.Ch03.Submission` (GMT/Scratch/NABSplitProbe.lean)`
- `lake env lean GMT/Scratch/NABSplitDecision.lean (three children + parent assembly + #print axioms)`
- `lake env lean GMT/Scratch/NABSplitStatementsOnly.lean (child types with only import GMT.Ch03.Submission; pp.explicit inner-instance audit)`
- `python3 -I dag.json nodes[].lean_name collision check; grep -rl deGiorgiNAB over dag.json and nodes/; git grep -l deGiorgiNAB over all 835 refs`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Convex/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Probability/Moments/Variance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-normal-average-bounds-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-normal-average-bounds-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/NABSplitDecision.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/NABSplitStatementsOnly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/NABSplitProbe.lean`

The snapshot's Contract.lean and Submission.lean are byte-identical to the workspace copies (project d09bc8a, Mathlib 25730c7c).

No existing lemma covers the children:
- SimonGMT Chapter03/FinitePerimeter.lean has norm_reducedBoundaryNormal and tendsto_normalAverage_reducedBoundaryNormal. They apply only to its own FinitePerimeterRepresentation structure, whose normal is chosen with Classical.choose, not to the contract's limUnder-based reducedNormal. So they cannot be reused, and child A provides the contract-level version, plus positive mass.
- Mathlib has no ready-made (∫f)² ≤ μ(S)∫f² lemma; only Hölder (integral_mul_le_Lp_mul_Lq_of_nonneg) and Jensen or variance variants. Child B therefore gives an elementary proof by expanding a square.
- No DAG node has any of the three child statements or names.

Library facts used:
- Filter.Tendsto.limUnder_eq (Topology/Separation/Hausdorff.lean:296).
- integral_inner (MeasureTheory/Function/L2Space.lean:89), with the constant on the left: ∫⟪c, f x⟫ = ⟪c, ∫ f⟫.
- AEStronglyMeasurable.inner and inner_const (MeasureTheory/Function/StronglyMeasurable/Inner.lean:50).
- integral_mul_le_Lp_mul_Lq_of_nonneg (MeasureTheory/Integral/Bochner/Basic.lean:1230).
- isFiniteMeasure_restrict, setIntegral_const, norm_sub_sq_real and Ioo_mem_nhdsGT.

The L2Space and StronglyMeasurable.Inner modules are not in the contract's import closure (#check reports unknown identifiers), so the child proofs note which imports they need.

Lean evidence: NABSplitDecision.lean proves all three children and the frozen parent type; NABSplitStatementsOnly.lean elaborates the child types with only the contract import. All four declarations use only propext, Classical.choice and Quot.sound.
