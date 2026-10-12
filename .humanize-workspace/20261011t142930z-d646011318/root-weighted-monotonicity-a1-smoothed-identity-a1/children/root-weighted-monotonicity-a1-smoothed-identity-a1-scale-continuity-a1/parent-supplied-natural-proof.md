# Parent-supplied natural-language proof

- Parent DAG node: `root.weighted_monotonicity-a1.smoothed_identity-a1`
- Child DAG node: `root.weighted_monotonicity-a1.smoothed_identity-a1.scale_continuity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. E := Ambient n ℓ = EuclideanSpace ℝ (Fin (n+ℓ)), with its Euclidean norm and Borel σ-algebra. B := B_R(ξ) = closedBall ξ R is the closed ball, a measurable set. Put r(x) := |x − ξ| and, for τ ∈ ℝ and x ∈ E, F(τ, x) := g(x)·ψ(r(x)/τ). All integrals over E are with respect to μ.

1. (The scale is positive.) Every τ ∈ [σ, ρ] satisfies τ ≥ σ > 0, so τ ≠ 0. Since c > 0 and τ ≤ ρ, also cτ ≤ cρ < R.

2. (Vanishing off B.) Let τ ∈ [σ, ρ] and x ∉ B. Then r(x) > R > cτ by step 1. Dividing by τ > 0 gives r(x)/τ > c, so ψ(r(x)/τ) = 0 by hypothesis, and F(τ, x) = 0. Put g̃ := 1_B·g. Then F(τ, x) = g̃(x)·ψ(r(x)/τ) for every x ∈ E and every τ ∈ [σ, ρ]: for x ∈ B both sides equal g(x)ψ(r(x)/τ), and for x ∉ B both sides are 0.

3. (Bound for ψ.) ψ is continuous on the compact interval [0, R/σ], so there is M ∈ ℝ with |ψ(s)| ≤ M for all s ∈ [0, R/σ] (IsCompact.exists_bound_of_continuousOn).

4. (Integrable functions.) g is μ-integrable on B and B is measurable, so g̃ = 1_B·g is μ-integrable on E (IntegrableOn.integrable_indicator). Likewise x ↦ M·|g(x)| is integrable on B (norm and constant multiple of an integrable function). Hence the majorant b := 1_B·(M|g|) is μ-integrable on E.

5. (Measurability.) Fix τ ∈ [σ, ρ]. The map x ↦ ψ(r(x)/τ) is continuous on E, being built from subtraction of ξ, the norm, division by the constant τ, and ψ. It is therefore μ-a.e. strongly measurable. g̃ is μ-a.e. strongly measurable because it is integrable. By step 2, F(τ, ·) = g̃·ψ(r/τ) is a product of μ-a.e. strongly measurable functions, hence μ-a.e. strongly measurable.

6. (Domination.) Fix τ ∈ [σ, ρ] and x ∈ E.
   - If x ∈ B, then 0 ≤ r(x) ≤ R, so R ≥ 0. Since 0 < σ ≤ τ, we get 0 ≤ r(x)/τ ≤ R/τ ≤ R/σ. Hence |ψ(r(x)/τ)| ≤ M by step 3, and |F(τ, x)| = |g(x)|·|ψ(r(x)/τ)| ≤ M|g(x)| = b(x).
   - If x ∉ B, then |F(τ, x)| = 0 = b(x) by step 2.
   So |F(τ, x)| ≤ b(x) for all x ∈ E and all τ ∈ [σ, ρ].

7. (Continuity in the parameter.) Fix x ∈ E. On [σ, ρ], τ ↦ r(x)/τ is continuous: it is a constant divided by the identity, which does not vanish there by step 1. Since ψ is continuous, τ ↦ F(τ, x) = g(x)·ψ(r(x)/τ) is continuous on [σ, ρ]. This holds for every x, in particular μ-a.e.

8. (Conclusion.) Apply continuity of parameter-dependent integrals under domination, continuousOn_of_dominated with bound b. Its hypotheses are step 5 (measurability for τ ∈ [σ, ρ]), step 6 (bound for τ ∈ [σ, ρ]), step 4 (integrability of b) and step 7 (continuity in τ for every x). It gives that τ ↦ ∫ F(τ, x) dμ(x) = ∫ g(x)ψ(|x − ξ|/τ) dμ(x) is continuous on [σ, ρ]. ∎

## Key steps

1. For τ ∈ [σ, ρ] and x ∉ B_R(ξ): |x−ξ|/τ > c, so ψ(|x−ξ|/τ) = 0 and the integrand equals 1_B·g(x)·ψ(|x−ξ|/τ)
2. |ψ| ≤ M on the compact interval [0, R/σ]
3. 1_B·g and the majorant 1_B·M|g| are μ-integrable on E
4. For τ ∈ [σ, ρ] the integrand is μ-a.e. strongly measurable, bounded by 1_B·M|g|, and continuous in τ for every x
5. continuousOn_of_dominated gives continuity of τ ↦ ∫ g ψ(|x−ξ|/τ) dμ on [σ, ρ]

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `sha256sum <snapshot>/project/GMT/Ch04/Contract.lean GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean`
- `rg -n "theorem continuousOn_of_dominated|theorem continuous_of_dominated|theorem integral_integral_swap\b|theorem integral_eq_sub_of_hasDerivAt\b|theorem integral_eq_sub_of_hasDerivAt_of_le|theorem integral_of_le\b|theorem AEStronglyMeasurable.comp_snd|theorem Integrable.mono'|theorem integrable_prod_iff|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem ContinuousOn.intervalIntegrable\b|theorem ContinuousOn.integrableOn_Icc|theorem integral_const_mul\b|theorem integral_div\b" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem integrableOn_of_bounded|sigmaFinite_of_isFiniteMeasureOnCompacts|theorem aestronglyMeasurable_indicator_iff|theorem ContDiff.continuous_deriv\b|theorem IsCompact.exists_bound_of_continuousOn\b|theorem continuousOn_inv₀|theorem ContinuousOn.intervalIntegrable_of_Icc|theorem Filter.EventuallyEq.deriv_eq|theorem HasDerivAt.div\b|theorem hasDerivAt_pow\b|isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts|theorem IntegrableOn.integrable_indicator|lemma Integrable.of_bound" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem .*Integrable.*(prod|comp_snd|comp_fst)" <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `rg -n "quasiMeasurePreserving_fst|theorem ae \(|setIntegral_congr_fun|setIntegral_eq_zero_of_forall_eq_zero|div_le_div_of_nonneg_left|div_le_div_of_nonneg_right" <snapshot>/mathlib/Mathlib`
- `rg -n "integral_integral_swap|continuousOn_of_dominated|integral_eq_sub_of_hasDerivAt|intervalIntegral_integral_swap" lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04`
- `grep -n "3\.3|3\.4|3\.5" book/sources/chapter-04-source.txt`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/si-decomp/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/si-decomp/olean lean /tmp/si-decomp/probe/Assembly.lean (sorry'd children + sibling, parent glue)`
- `LEAN_PATH=... lean /tmp/si-decomp/val/{Cont,Fub,Ftc,Full}.lean (sorry-free child proofs, glue, exact-Submission targets, #print axioms)`
- `python3 -I /tmp/si-decomp/scripts/gen.py (gmt-compare.py child_modules contract scope + lean_contract.validate_lean_statement)`
- `LEAN_PATH=... lean /tmp/si-decomp/gen/Challenge_*.lean`
- `LEAN_PATH=... lean /tmp/si-decomp/probe/Parse.lean (set_option pp.notation false)`
- `grep -rl <proposed lean_name> <run dir>; git grep -l <proposed lean_name> over all refs (collision check)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/QuasiMeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Deriv/Pow.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Algebra/GroupWithZero.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/WeightedRadiusIntegration.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-04-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-weighted-monotonicity-a1-smoothed-identity-a1/parent-child-handoff.json`
- `/tmp/si-decomp/val/Full.lean`
- `/tmp/si-decomp/val/Cont.lean`
- `/tmp/si-decomp/val/Fub.lean`
- `/tmp/si-decomp/val/Ftc.lean`
- `/tmp/si-decomp/probe/Assembly.lean`
- `/tmp/si-decomp/probe/Parse.lean`

Snapshot and project match: the snapshot Contract.lean, the workspace Contract.lean and Submission.lean all have sha256 6e58e5dd…0f4770b (project ff75f52a, mathlib 25730c7c).

Every tool the children need exists in the snapshot Mathlib:
- continuousOn_of_dominated (Integral/Bochner/Basic.lean:467)
- integral_integral_swap (Integral/Prod.lean:478)
- AEStronglyMeasurable.comp_snd (Integral/Prod.lean:135)
- Integrable.comp_snd (Integral/Prod.lean:285)
- SigmaFinite.of_isFiniteMeasureOnCompacts (Typeclasses/SFinite.lean:701)
- Measure.quasiMeasurePreserving_fst (Measure/Prod.lean:463) with QuasiMeasurePreserving.ae (QuasiMeasurePreserving.lean:108)
- aestronglyMeasurable_indicator_iff (AEStronglyMeasurable.lean:545)
- IntegrableOn.integrable_indicator and IntegrableOn.of_bound (IntegrableOn.lean:348, 175)
- setIntegral_congr_fun and setIntegral_eq_zero_of_forall_eq_zero (Bochner/Set.lean:73, 357)
- integral_div and integral_const_mul (Bochner/Basic.lean:297, 290)
- intervalIntegral.integral_eq_sub_of_hasDerivAt (FundThmCalculus.lean:1148)
- intervalIntegral.integral_of_le and ContinuousOn.intervalIntegrable_of_Icc (IntervalIntegral/Basic.lean:677, 507)
- ContinuousOn.integrableOn_Icc (LocallyIntegrable.lean:596)
- HasDerivAt.div (Deriv/Inv.lean:173), hasDerivAt_pow (Deriv/Pow.lean:137)
- ContDiff.continuous_deriv (ContDiff/Deriv.lean:108), Filter.EventuallyEq.deriv_eq (Deriv/Basic.lean:638)
- continuousOn_inv₀ (Topology/Algebra/GroupWithZero.lean:101)
- div_le_div_of_nonneg_left/right (GroupWithZero/Basic.lean:1269, 1193)

SimonGMT has an analogous lemma, continuousOn_integral_scaledRadialCutoff_mul (WeightedRadiusIntegration.lean:69). It confirms the indicator-truncation plus continuousOn_of_dominated method, but it cannot be reused directly: it is stated for SimonGMT's own varifold weight and squared-radius cutoffs with range in [0,1]. The snapshot has no lemma matching any of the three child statements.

The book source (chapter-04-source.txt, 3.3–3.5, p. 90) is Simon's derivation of this step.

Results in /tmp/si-decomp:
- All three child types elaborate in the comparator's contract scope and pass validate_lean_statement.
- All three children have sorry-free proofs depending only on propext, Classical.choice and Quot.sound.
- The selected frozen theorem, byte-identical to dag.json, compiles from the children plus the sibling weighted_mono_cutoff_hasDerivAt stubbed with sorry at its byte-identical dag.json type.
- exact Submission.X targets compile for every child and for the selected node.
- The proposed names appear nowhere in the run directory or in any git ref.
