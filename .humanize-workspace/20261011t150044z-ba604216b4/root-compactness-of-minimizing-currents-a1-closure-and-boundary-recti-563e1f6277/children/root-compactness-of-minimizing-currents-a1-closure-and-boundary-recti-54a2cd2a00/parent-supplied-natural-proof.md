# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.uniform_density-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.uniform_density-a1.ae_lusin-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 1–2 (a Borel set of good points; Lusin), which produce the closed set F of Simon Ch. 3, proof of 1.6 “⇐”, (4) (chapter-03.txt lines 168–172). The parent applies it with μ := Hⁿ, A := M, Y := L(ℝ^P) with the operator norm, f(x) := p_{Q(x)} and p(x) := “M has approximate tangent space Q(x) at x”.

1. A Borel representative. Since f is a.e. strongly measurable for μ⌞A, there is a strongly measurable g : ℝ^P → Y with f = g μ⌞A-almost everywhere (Mathlib `AEStronglyMeasurable.mk`, `stronglyMeasurable_mk`, `ae_eq_mk`). Give Y its Borel σ-algebra, so every open subset of Y is measurable. Y is pseudo-metrizable, so the strongly measurable map g (a pointwise limit of simple functions) is measurable (Mathlib `StronglyMeasurable.measurable`).
2. A Borel set of good points. Let Z := {x ∈ ℝ^P : f(x) ≠ g(x) or p(x) fails}. Both {f ≠ g} and {x : p(x) fails} are μ⌞A-null, so μ⌞A(Z) = 0. Since A is measurable, μ⌞A(Z) = μ(Z ∩ A) (Mathlib `Measure.restrict_apply'`), so μ(Z ∩ A) = 0. Choose a measurable N ⊇ Z ∩ A with μ(N) = 0 (Mathlib `exists_measurable_superset_of_null`) and put A₁ := A ∖ N. Then A₁ is measurable and μ(A₁) ≤ μ(A) < ∞. Every x ∈ A₁ satisfies f(x) = g(x) and p(x): x ∈ A and x ∉ N ⊇ Z ∩ A, so x ∉ Z.
3. Lusin. Apply the sibling lusin (Lusin's theorem, compact form) to the measure μ, the measurable set A₁ (μ(A₁) < ∞), the measurable map g : ℝ^P → Y (Y is second countable and its open sets are measurable) and the tolerance η ≠ 0. This gives a compact K ⊆ A₁ with μ(A₁ ∖ K) < η such that g is continuous on K.
4. Verification. K is compact and K ⊆ A₁ ⊆ A. Every x ∈ K lies in A₁, so p(x) holds and f(x) = g(x). Hence f and g agree on K, and f is continuous on K because g is (Mathlib `ContinuousOn.congr`). Finally A ∖ K ⊆ N ∪ (A₁ ∖ K): if x ∈ A ∖ K and x ∉ N, then x ∈ A₁ ∖ K. By subadditivity, μ(A ∖ K) ≤ μ(N) + μ(A₁ ∖ K) = 0 + μ(A₁ ∖ K) < η. ∎

## Key steps

1. Replace f by a strongly measurable, hence Borel measurable, representative g with f = g μ⌞A-a.e. (Y with its Borel σ-algebra).
2. The bad set Z = {f ≠ g} ∪ {¬p} has μ(Z ∩ A) = 0. A measurable null hull N gives A₁ := A ∖ N of full measure, on which f = g and p holds.
3. Lusin (sibling lusin) for g on A₁ with tolerance η: compact K ⊆ A₁ with μ(A₁ ∖ K) < η and g continuous on K.
4. f = g on K, so f is continuous on K; p holds on K; μ(A ∖ K) ≤ μ(N) + μ(A₁ ∖ K) < η.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `rg -n "Semicontinuous.*closedBall|closedBall.*Semicontinuous|semicontinuous_measure|measure_closedBall.*semicont|lowerSemicontinuous_measure|upperSemicontinuous_measure" <snapshot>/mathlib/Mathlib (no match)`
- `rg -n "Semicontinuous" <snapshot>/mathlib/Mathlib/MeasureTheory (only CondJensen, IntegralRNDeriv, VitaliCaratheodory; no ball- or cone-mass semicontinuity)`
- `rg -n "theorem tendsto_measure_cthickening|theorem tendsto_measure_closedBall|tendsto_measure_biInter_gt|theorem tendsto_measure_iInter_atTop|theorem tendsto_measure_iUnion_atTop|theorem lintegral_liminf_le|theorem measure_liminf_le|theorem measure_liminf_atTop_le" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem Filter.Tendsto.clm_apply|Tendsto.clm_apply|theorem ContinuousLinearMap.continuous_eval|isBoundedBilinearMap_apply|theorem Continuous.clm_apply" <snapshot>/mathlib/Mathlib (no Tendsto.clm_apply; isBoundedBilinearMap_apply at Analysis/Normed/Operator/BoundedLinearMaps.lean:391)`
- `rg -n "def unitBallVolume|HasApproximateTangentSpaceAt\)" <snapshot>/project/GMT/Ch07/Contract.lean; rg -n "theorem tendstoUniformlyOn_of_ae_tendsto" <snapshot>/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean; rg -n "theorem exists_measurable_superset_of_null|lemma isFiniteMeasure_restrict" <snapshot>/mathlib/Mathlib/MeasureTheory; rg -n "protected noncomputable def mk|theorem ae_eq_mk" <snapshot>/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean; rg -n "theorem starProjection_norm_le" <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean; rg -n "theorem IsSeqClosed.isClosed|theorem liminf_le_of_frequently_le'" <snapshot>/mathlib/Mathlib`
- `rg -n "Semicontinuous|semicontinuous" simongmt/Poincare/SimonGMT (Chapter04/Density.lean upperSemicontinuous_closedBall_mass, varifold weights only); rg -ln "Egorov|Egoroff|egorov" simongmt/Poincare/SimonGMT (only Chapter01/Lusin.lean); python3 -I import-closure scan of the contract's SimonGMT imports (Chapter01.Basic/Hausdorff/MetricCriterion, Chapter02.Lipschitz, Chapter03.Rectifiable, Chapter04.Basic, Chapter06.*; Chapter04.Density and Chapter01.Lusin excluded)`
- `python3 -I scan of dag.json lean_statement values for ContinuousOn+Measurable, closedBall+IsClosed, Semicontinuous, starProjection+IsClosed; lean_name lookup: dor_ims_lusin_measurable_continuousOn (one accepted node, candidate e4172a7b, byte-identical type), cbrr_ud_* (none), byte comparison of doragm_approxTangent_lower_density / cbrr_tangent_cone_density_zero / cbrr_uniform_density_on_large_set types`
- `sed -n 1840,1960p and 6480,6614p /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (child creation resolves accepted names; _dependency_problem; _existing_lean_name_problem); sed -n 540,640p verifier/gmt-compare.py (contract_scope, child_modules)`
- `git show e4172a7b3e6f:GMT/Ch07/Submission.lean (accepted Lusin proof); sed -n 150,230p book/chapter-03.txt (Simon Ch. 3, proof of 1.6 ⇐, (4)–(10))`
- `lake env lean /tmp/ud-decomp-q7k2/lean/{Types,Challenge,Assembly,Unif,Ball,Cone,AeLusin,E2E}.lean (#print axioms: propext, Classical.choice, Quot.sound); python3 -I validate_lean_statement (verifier/lean_contract.py) on all 5 child types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Defs/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Density.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-563e1f6277/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-f03d9c44ac/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-lusin-c-3a11b01ce9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/tmp/ud-decomp-q7k2/lean/Types.lean`
- `/tmp/ud-decomp-q7k2/lean/Challenge.lean`
- `/tmp/ud-decomp-q7k2/lean/Assembly.lean`
- `/tmp/ud-decomp-q7k2/lean/Unif.lean`
- `/tmp/ud-decomp-q7k2/lean/Ball.lean`
- `/tmp/ud-decomp-q7k2/lean/Cone.lean`
- `/tmp/ud-decomp-q7k2/lean/AeLusin.lean`
- `/tmp/ud-decomp-q7k2/lean/E2E.lean`

The snapshot contract (project b4d606d, mathlib 25730c7c) equals the workspace Contract.lean and Submission.lean. The pinned Mathlib has every lemma the child proofs cite: lintegral_liminf_le, tendsto_measure_iInter_atTop, exists_measurable_superset_of_null, isFiniteMeasure_restrict, AEStronglyMeasurable.mk/ae_eq_mk, isBoundedBilinearMap_apply, IsSeqClosed.isClosed, liminf_le_of_frequently_le' and starProjection_norm_le. It has no semicontinuity of ball or cone mass (no match) and no set-valued Egorov uniformization; Egorov.lean covers only function convergence. SimonGMT's upperSemicontinuous_closedBall_mass (Chapter04/Density.lean, varifold weights) and its Chapter01 Lusin lie outside the contract's import closure. Together these justify the four new children. The only reuse is the accepted dor_ims_lusin_measurable_continuousOn, whose type is byte-identical (candidate e4172a7b). The unaccepted cbrr_tangent_cone_density_zero is used only by the parent, through its existing dependency. The four cbrr_ud_* names are unused in the DAG. All five child types pass the lexical check and elaborate in the replayed contract scope. Scratch proofs of all four new children, and the assembly of the byte-identical parent type from them, compile with axioms propext, Classical.choice and Quot.sound only.
