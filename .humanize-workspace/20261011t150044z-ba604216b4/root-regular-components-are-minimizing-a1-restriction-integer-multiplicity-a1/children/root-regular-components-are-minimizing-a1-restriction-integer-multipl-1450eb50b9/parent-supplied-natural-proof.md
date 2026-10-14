# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_components_are_minimizing-a1.restriction_integer_multiplicity-a1`
- Child DAG node: `root.regular_components_are_minimizing-a1.restriction_integer_multiplicity-a1.action_integrable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 1 ('For Hⁿ-a.e. x ∈ C, ξ(x) = ±ev_τ with τ orthonormal, so |ξ(x)(α)| ≤ ‖α‖ for all α. Hence for ω ∈ 𝒟ⁿ(U) the functions θ ξ(ω) … are bounded a.e. on C by θ ‖ω‖_∞ 1_{tsupport ω} … and are integrable on C'). This makes explicit the absolute convergence of the integral in Simon Ch. 6, 3.1 (‡) (chapter-06.txt lines 733–745), where θ is locally Hⁿ-integrable and ξ = τ₁ ∧ ⋯ ∧ τₙ with τ orthonormal.

Notation: μ := μHE[n], C := R.carrier, θ := R.mult, ξ := R.orient, f := (ω : DifferentialForm (Euclid P) n), K := tsupport f, and F(x) := (θ(x) : ℝ)·ξ(x)(f(x)).

1. (Test-form data.) ω ∈ TestFormOn U n means IsTestForm f ∧ tsupport f ⊆ U (ω.2.1 and ω.2.2). IsTestForm f means ContDiff ℝ ∞ f and HasCompactSupport f. Hence:
   - f is continuous;
   - K is compact and closed, hence measurable, and K ⊆ U;
   - f(x) = 0 for x ∉ K (image_eq_zero_of_notMem_tsupport).
   By Continuous.bounded_above_of_compact_support there is B ∈ ℝ with ‖f(x)‖ ≤ B for all x. Here ‖·‖ is the operator norm on Covector (Euclid P) n = (Euclid P) [⋀^Fin n]→L[ℝ] ℝ.

2. (Pointwise bound for ξ.) By the field R.orients, for μ⌞C-a.e. x there are a subspace Q and τ : Fin n → ℝ^P with Orthonormal ℝ τ such that either ξ(x)(α) = α(τ) for all n-covectors α, or ξ(x)(α) = −α(τ) for all α.
   - For every α, ContinuousAlternatingMap.le_opNorm gives ‖α(τ)‖ ≤ ‖α‖·∏_i ‖τ_i‖.
   - ∏_i ‖τ_i‖ = 1, since ‖τ_i‖ = 1 for each i (first component of Orthonormal). For n = 0 the product is empty and equals 1.
   - Hence |ξ(x)(α)| = |α(τ)| ≤ ‖α‖ for all α (use abs_neg in the second case).
   So for μ⌞C-a.e. x, |ξ(x)(α)| ≤ ‖α‖ for every α.

3. (Measurability.)
   - x ↦ (θ(x) : ℝ) is measurable: θ is measurable and every function on ℕ is measurable (measurable_from_nat composed with R.measurable_mult).
   - The evaluation map MultiVector P n × Covector (Euclid P) n → ℝ, (φ, α) ↦ φ(α), is continuous (Continuous.clm_apply applied to continuous_fst and continuous_snd).
   - x ↦ (ξ(x), f(x)) is a.e. strongly measurable for μ⌞C: pair R.aestronglyMeasurable_orient with the continuous f using AEStronglyMeasurable.prodMk.
   - Hence x ↦ ξ(x)(f(x)) is a.e. strongly measurable (Continuous.comp_aestronglyMeasurable), and so is F (AEStronglyMeasurable.mul).
   Formalization note: applying ContinuousLinearMap.aestronglyMeasurable_comp₂ to ContinuousLinearMap.apply ℝ ℝ fails to unify the topology instance on MultiVector P n. Composing with the continuous evaluation map, as above, works.

4. (Integrable dominating function.) Let g(x) := B * K.indicator (fun x => (θ x : ℝ)) x, i.e. g = B·1_K·θ.
   - x ↦ (θ(x) : ℝ) is integrable on K for μ⌞C. It is measurable by step 3. Its lower integral is ∫⁻_K ‖(θ(x) : ℝ)‖ₑ d(μ⌞C) = ∫⁻_{K∩C} θ dμ = ∫⁻_{C∩K} θ dμ, using Measure.restrict_restrict (K measurable) and ‖(k : ℝ)‖ₑ = (k : ℝ≥0∞) for k ∈ ℕ (hasFiniteIntegral_iff_enorm).
   - This lower integral is ≠ ∞ by R.locallyIntegrable_mult K, since K is compact and K ⊆ U.
   - Hence K.indicator θ is integrable for μ⌞C (IntegrableOn.integrable_indicator, K measurable), and so is g (Integrable.const_mul).

5. (Domination.) Let x be one of the a.e. points of step 2.
   - If x ∈ K: |F(x)| = θ(x)·|ξ(x)(f(x))| ≤ θ(x)·‖f(x)‖ ≤ θ(x)·B = g(x), using θ(x) ≥ 0, step 2 and step 1.
   - If x ∉ K: f(x) = 0, so F(x) = θ(x)·ξ(x)(0) = 0 = g(x).
   Thus ‖F(x)‖ ≤ g(x) for μ⌞C-a.e. x.

6. (Conclusion.) Integrable.mono' applies: g is integrable (step 4), F is a.e. strongly measurable (step 3), and the a.e. bound holds (step 5). Hence F is integrable for μ⌞C = μHE[n].restrict R.carrier. ∎

## Key steps

1. ω is continuous with compact support K = tsupport ω ⊆ U, so ‖ω(x)‖ ≤ B everywhere and ω = 0 off K.
2. R.orients gives ξ(x) = ±(α ↦ α(τ)) with τ orthonormal a.e. on C, so |ξ(x)(α)| ≤ ‖α‖ by le_opNorm and ∏‖τ_i‖ = 1.
3. The integrand is a.e. strongly measurable: compose the continuous evaluation map with (ξ, ω).
4. It is dominated a.e. by B·1_K·θ, which is integrable because ∫⁻_{C∩K} θ dHⁿ < ∞ (locallyIntegrable_mult).
5. Integrable.mono' concludes.

## Reference use

### local-project

Queries:
- `cmp GMT/Ch07/Submission.lean .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean (identical; manifest project b4d606d, mathlib 25730c7c)`
- `python3 summary of lean_name / lean_statement fields in dag.json (sibling frozen types regcomp_approx_tangent_locality, regcomp_imrep_mass_formula; all reserved names)`
- `grep -rl 'regcomp_rim_' over workspaces/ and lake-packages-25730c7c/simongmt (no match)`
- `grep -n 'abbrev Covector|abbrev DifferentialForm|def IsTestForm|abbrev TestFormOn|structure GeometricCurrentOn|CoeFun' simongmt/Poincare/SimonGMT/Chapter06/Forms.lean Chapter06/Currents.lean`
- `sed -n 1,140p simongmt/Poincare/SimonGMT/Chapter06/Mass.lean (covectorEuclideanNorm, massAdmissibleOn, GeometricCurrentOn.massOn)`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable, CountablyRectifiable.mono, HasApproximateTangentSpaceAt)`
- `grep -rn 'aestronglyMeasurable_comp₂|bounded_above_of_compact_support|setIntegral_congr_fun|setIntegral_indicator|integrable_indicator_iff|hasFiniteIntegral_iff_enorm|Integrable.mono|def apply' Mathlib (snapshot)`
- `#check ContinuousAlternatingMap.le_opNorm, setIntegral_indicator, withDensity_indicator, withDensity_add_left, withDensity_congr_ae, Measure.restrict_congr_set, ae_restrict_of_ae_restrict_of_subset, AEStronglyMeasurable.mono_measure, IntegrableOn.integrable_indicator (Scratch/Check1.lean)`
- `lake build GMT.Ch07.Submission in scratch copy /tmp/regcomp-rim-scratch; lake env lean Scratch/Check1.lean, Scratch/Children.lean, Scratch/Assembly.lean, Scratch/Full.lean with #print axioms`
- `sed -n 975,1030p book/chapter-07.txt (7.5.11 and proof); sed -n 724,770p book/chapter-06.txt (6.3.1, 6.3.2); sed -n 60,100p book/chapter-03.txt (3.1.4, 3.1.5)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-restriction-integer-multiplicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/regcomp-rim-scratch/Scratch/Check1.lean`
- `/tmp/regcomp-rim-scratch/Scratch/Children.lean`
- `/tmp/regcomp-rim-scratch/Scratch/Assembly.lean`
- `/tmp/regcomp-rim-scratch/Scratch/Full.lean`

The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Submission.lean. No reserved DAG name, workspace file or simongmt declaration uses regcomp_rim_*.

The proofs use these library facts:
- From the contract: IMRep fields and IMRep.measure/action. (S − T)ω = Sω − Tω holds by rfl for the contract's Sub instance.
- From simongmt: CountablyRectifiable.mono (Chapter03/Rectifiable.lean).
- From Mathlib: ContinuousAlternatingMap.le_opNorm, Continuous.bounded_above_of_compact_support, Continuous.clm_apply with Continuous.comp_aestronglyMeasurable, Integrable.mono', IntegrableOn.integrable_indicator, hasFiniteIntegral_iff_enorm, setLIntegral_mono, lintegral_mono_set, AEStronglyMeasurable.mono_measure, ae_restrict_of_ae_restrict_of_subset, withDensity_congr_ae, withDensity_add_left, withDensity_indicator, Measure.restrict_restrict, setIntegral_congr_fun, integral_add, setIntegral_indicator, Measure.restrict_congr_set.

Applying ContinuousLinearMap.aestronglyMeasurable_comp₂ to ContinuousLinearMap.apply fails to unify the topology instance on MultiVector, so the proofs compose with the continuous evaluation map instead.

The three child proofs compile using only propext, Classical.choice and Quot.sound. The parent assembly from the children compiles, with sorryAx only from the stubbed sibling dependencies regcomp_approx_tangent_locality and regcomp_imrep_mass_formula.
