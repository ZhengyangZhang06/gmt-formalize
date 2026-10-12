# Parent-supplied natural-language proof

- Parent DAG node: `root.poincare_inequality-a1`
- Child DAG node: `root.poincare_inequality-a1.gradient_chain_rule-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 3 ('∇^M h_t = ψ'(h − t)∇^M h on U (chain rule; p_x is linear)'); the parent applies it to h − t, whose gradient equals ∇h.

1. Chain rule for Fréchet derivatives: since h is differentiable at x and ψ at h(x), D(ψ∘h)(x) = Dψ(h(x)) ∘ Dh(x). For v ∈ ℝ, Dψ(h(x))(v) = v·ψ'(h(x)). Hence for w ∈ ℝ^{n+ℓ}, D(ψ∘h)(x)(w) = ψ'(h(x))·Dh(x)(w), i.e. D(ψ∘h)(x) = ψ'(h(x))·Dh(x) as linear functionals.

2. The gradient ∇f(x) is the image of Df(x) under the inverse Riesz isomorphism (InnerProductSpace.toDual)^{−1}, which is ℝ-linear. Applying it to step 1: ∇(ψ∘h)(x) = ψ'(h(x)) ∇h(x).

3. ∇^M f(x) = p_{T_xV}(∇f(x)) with p_{T_xV} = (V.tangentSpace x).starProjection linear. Applying it to step 2: ∇^M(ψ∘h)(x) = ψ'(h(x)) p_{T_xV}(∇h(x)) = ψ'(h(x)) ∇^M h(x). ∎

Formalization notes (Mathlib/Lean names used in a machine-checked transcription of the numbered argument): fderiv_comp, map_smul (of InnerProductSpace.toDual.symm and of the star projection).

Appendix (machine-checked reference transcription; the numbered argument above is the proof). The following tactic block is the proof (the text after `:= by`) of the declaration `theorem tangentialGradient_comp_of_differentiableAt` with exactly the frozen lean_statement above as its type, inside `namespace Submission` (scope `open MeasureTheory Metric Set Filter Topology`, `open scoped ENNReal ContDiff CompactlySupported`, `namespace GMT.Ch04`, `noncomputable section`, `open RectifiableVarifold`, after `import GMT.Ch04.Submission`), compiles with Lean v4.35.0-rc3 / Mathlib 25730c7c and depends only on propext, Classical.choice and Quot.sound. Extra imports: none.
```lean
  intro n ℓ V h ψ x hh hψ
  have hcomp : fderiv ℝ (fun y => ψ (h y)) x = deriv ψ (h x) • fderiv ℝ h x := by
    have := fderiv_comp x hψ hh
    simp only [Function.comp_def] at this
    rw [this]
    ext v
    simp [mul_comm]
  simp only [RectifiableVarifold.tangentialGradient, gradient, hcomp, map_smul]
```

## Key steps

1. D(ψ∘h)(x) = ψ'(h(x))·Dh(x) by the chain rule
2. the inverse Riesz map is linear, so ∇(ψ∘h)(x) = ψ'(h(x))∇h(x)
3. the orthogonal projection p_{T_xV} is linear, so ∇^M(ψ∘h)(x) = ψ'(h(x))∇^M h(x)

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `python3: read lean_name/lean_statement of every node in <run>/dag.json and every */decomposition*.json (uncle frozen types; name-collision check)`
- `rg -n 'theorem|lemma' <snapshot>/mathlib/Mathlib/Analysis/ODE/Gronwall.lean; grep -ril gronwall <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem lintegral_eq_lintegral_meas_lt|theorem lintegral_comp_eq_lintegral_meas_lt_mul|theorem lintegral_lintegral_swap|theorem lintegral_prod_swap' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem measurable_fderiv |theorem measurable_deriv |theorem measurableSet_of_differentiableAt ' <snapshot>/mathlib/Mathlib`
- `rg -n '^theorem|^lemma' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean; rg -n 'gradient_fun_const|gradient_eq' <snapshot>/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean`
- `rg -n 'Integrable.bdd_mul|support_mem_ae|norm_starProjection_apply_le|aestronglyMeasurable_comp₂|apply_continuousLinearMap|Monotone.deriv_nonneg|integral_comp_sub_left|integral_deriv_eq_sub|integral_Ioi_rpow_of_lt|integrableOn_Ioi_rpow_of_lt|rpow_inv_lt_iff_of_neg|lt_rpow_inv_iff_of_neg|continuousOn_primitive_interval_left|integral_hasDerivAt_left|monotoneOn_of_deriv_nonneg|aemeasurable_restrict_of_monotoneOn|integrableOn_of_bounded|setIntegral_mono_set|AEMeasurable.comp_snd' <snapshot>/mathlib/Mathlib`
- `grep -rniE 'gronwall|layercake|poincare|monotonicity' lake-packages-25730c7c/simongmt/Poincare; grep -n '^theorem' simongmt/Poincare/SimonGMT/Chapter04/{Poincare,PoincareKernel,PoincareTruncation,LayerCake}.lean`
- `python3: verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch04.main_theorem') and lean_contract.validate_lean_statement on all child statements`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/ch04-poincare-split/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=...:/tmp/ch04-poincare-split/olean lean /tmp/ch04-poincare-split/src/ChildTypes.lean`
- `lean /tmp/ch04-poincare-split/asm/A7.lean (parent assembly from sorried children and byte-identical uncle stubs)`
- `lean /tmp/ch04-poincare-split/kids/K1..K7.lean and /tmp/ch04-poincare-split/full/Full.lean with #print axioms`
- `HUMANIZE_RUN_DIR=/tmp/ch04-poincare-split/fakerun python3 verifier/gmt-compare.py --lean-target GMT/Ch04/Submission.lean --verifier-dir verifier --packages lake-packages-25730c7c --frozen-commit ff75f52a4c9deb3b3abbd91eb31d7b02e29a4cef --dry-run root.poincare_inequality-a1.tangentialGradient_comp_of_differentiableAt-a1`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-poincare-inequality-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/ODE/Gronwall.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/ODE/DiscreteGronwall.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Poincare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/PoincareKernel.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/PoincareTruncation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/LayerCake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ch04-poincare-split/src/ChildTypes.lean`
- `/tmp/ch04-poincare-split/asm/A7.lean`
- `/tmp/ch04-poincare-split/full/Full.lean`

The snapshot contract (sha256 6e58e5dd…0f4770b) is byte-identical to the workspace Contract.lean and Submission.lean. The Mathlib (25730c7c) and SimonGMT (2b366308) revisions match the project manifest. The pinned Mathlib has no integral-form Gronwall inequality (only Analysis/ODE/Gronwall.lean, which is differential, and DiscreteGronwall.lean), so integral_gronwall is a genuine new obligation. Mathlib supplies the other ingredients: the layer-cake formula (lintegral_eq_lintegral_meas_lt), Tonelli (lintegral_lintegral_swap), measurable_fderiv for arbitrary functions, Real.smoothTransition, improper rpow integrals (integral_Ioi_rpow_of_lt) and FTC/monotonicity lemmas. SimonGMT has an earlier Poincaré development (Chapter04/Poincare.lean, PoincareKernel.lean, PoincareTruncation.lean), but it is stated for the strengthened Chapter04.RectifiableVarifold, which the Ch04 README says needs a transport construction, so it is not reused. Its generic kernel and truncation lemmas have different hypotheses, and the children were proved without them. All seven child types elaborate in the exact comparator scope and pass the comparator's statement validator, and a comparator dry run generates the expected challenge and solution modules. All children have machine-checked Lean proofs using only propext, Classical.choice and Quot.sound. The selected frozen type compiles from the seven children plus the byte-identical uncle types, with no other sorry.
