# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_components_are_minimizing-a1.restriction_integer_multiplicity-a1`
- Child DAG node: `root.regular_components_are_minimizing-a1.restriction_integer_multiplicity-a1.imrep_split-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: two passages of the parent proof.
- Step 3: '(T − T₁)(ω) = ∫_C θ ξ(ω) dHⁿ − ∫_{C∩A} ξ(ω) dHⁿ = ∫_C (θ − 1_A) ξ(ω) dHⁿ = ∫_{C₂} θ₂ ξ(ω) dHⁿ … because on C the real function θ − 1_A equals θ₂ and θ₂ = 0 on C ∖ C₂'.
- Step 4: 'On C, θ = 1_A + θ₂, so by additivity of the integral of nonnegative functions, ∫_{C∩W} θ dHⁿ = Hⁿ(A ∩ C ∩ W) + ∫_{C∩W} θ₂ dHⁿ'.
Here the splitting θ = 1_{C₁}θ₁ + 1_{C₂}θ₂ is arbitrary; the parent uses C₁ = A ∩ C and θ₁ = 1. This is the computation behind 'M_W(T₁) + M_W(T − T₁) = M_W(T)' in Simon 7.5.11 (chapter-07.txt lines 990–995). The mass formula of Simon 6.3.2(3) (chapter-06.txt lines 763–767) is supplied separately by the parent.

Notation: μ := μHE[n], C := R.carrier, θ := R.mult, ξ := R.orient, and C_i := R_i.carrier, θ_i := R_i.mult for i = 1, 2.

1. (Indicator casts.) For S ⊆ ℝ^P, g : ℝ^P → ℕ and x ∈ ℝ^P:
   - ((1_S g)(x) : ℝ≥0∞) = 1_S(y ↦ (g(y) : ℝ≥0∞))(x);
   - ((1_S g)(x) : ℝ) = 1_S(y ↦ (g(y) : ℝ))(x).
   Proof: case split on x ∈ S, then simp.

2. (Measures.) By step 1 and the hypothesis, (θ(x) : ℝ≥0∞) = 1_{C₁}θ₁(x) + 1_{C₂}θ₂(x) (ℝ≥0∞-valued indicators) for every x ∈ C. Hence the identity holds μ⌞C-a.e. (ae_restrict_mem R.measurableSet_carrier). Therefore:
   R.measure = (μ⌞C).withDensity θ
   = (μ⌞C).withDensity (1_{C₁}θ₁ + 1_{C₂}θ₂)  [withDensity_congr_ae]
   = (μ⌞C).withDensity (1_{C₁}θ₁) + (μ⌞C).withDensity (1_{C₂}θ₂)  [withDensity_add_left; 1_{C₁}θ₁ is measurable as the indicator, on the measurable set C₁, of the measurable function (θ₁ : ℝ≥0∞)]
   = ((μ⌞C)⌞C₁).withDensity θ₁ + ((μ⌞C)⌞C₂).withDensity θ₂  [withDensity_indicator; C_i measurable]
   = (μ⌞(C₁ ∩ C)).withDensity θ₁ + (μ⌞(C₂ ∩ C)).withDensity θ₂  [Measure.restrict_restrict]
   = (μ⌞C₁).withDensity θ₁ + (μ⌞C₂).withDensity θ₂  [C_i ∩ C = C_i, since C_i ⊆ C]
   = R₁.measure + R₂.measure.

3. (Integrability.) Fix ω ∈ 𝒟ⁿ(U). Let f := (ω : DifferentialForm (Euclid P) n) and F_i(x) := (θ_i(x) : ℝ)·R_i.orient(x)(f(x)).
   - The sibling lemma action_integrable (regcomp_rim_action_integrable), applied to R_i and ω, shows F_i is integrable for μ⌞C_i, i.e. IntegrableOn F_i C_i μ.
   - Hence 1_{C_i}F_i is integrable for μ (IntegrableOn.integrable_indicator, C_i measurable).
   - Hence 1_{C_i}F_i is integrable for μ⌞C (Integrable.restrict).

4. (Pointwise identity on C.) For x ∈ C: (θ(x) : ℝ)·ξ(x)(f(x)) = (1_{C₁}F₁)(x) + (1_{C₂}F₂)(x). Indeed:
   - By the hypothesis and step 1, (θ(x) : ℝ) = 1_{C₁}(θ₁ : ℝ)(x) + 1_{C₂}(θ₂ : ℝ)(x).
   - Since R₁.orient = R₂.orient = ξ, distributing gives Σ_i 1_{C_i}(θ_i : ℝ)(x)·ξ(x)(f(x)).
   - Each term satisfies 1_{C_i}(θ_i : ℝ)(x)·ξ(x)(f(x)) = (1_{C_i}F_i)(x) (case split on x ∈ C_i).

5. (Actions.)
   R.action ω = ∫_C θ·ξ(f) dμ
   = ∫_C (1_{C₁}F₁ + 1_{C₂}F₂) dμ  [setIntegral_congr_fun with step 4; C measurable]
   = ∫_C 1_{C₁}F₁ dμ + ∫_C 1_{C₂}F₂ dμ  [integral_add with step 3]
   = ∫_{C∩C₁} F₁ dμ + ∫_{C∩C₂} F₂ dμ  [setIntegral_indicator; C_i measurable]
   = ∫_{C₁} F₁ dμ + ∫_{C₂} F₂ dμ  [C ∩ C_i = C_i]
   = R₁.action ω + R₂.action ω  [definition of IMRep.action]. ∎

## Key steps

1. On C, θ = 1_{C₁}θ₁ + 1_{C₂}θ₂; cast this identity into ℝ≥0∞ and into ℝ.
2. Measures: withDensity_congr_ae, withDensity_add_left, withDensity_indicator, Measure.restrict_restrict and C_i ⊆ C give R.measure = R₁.measure + R₂.measure.
3. Actions: by action_integrable, the indicator extensions of the R₁ and R₂ integrands are integrable on C; integral_add and setIntegral_indicator split ∫_C θ·ξ(ω) into R₁.action ω + R₂.action ω.

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
