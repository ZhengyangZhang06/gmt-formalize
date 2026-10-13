# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tau_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. Hᵏ := μHE[k]; ‖α‖ is the operator norm of a k-covector. By the orientation field of IsRectifiableTriple U k M θ ξ, for Hᵏ-a.e. x ∈ M, ξ(x) = ±simpleNVector τ with τ orthonormal, so |ξ(x)(α)| = |α(τ)| ≤ ‖α‖·∏|τ_i| = ‖α‖ for every k-covector α (`ContinuousAlternatingMap.le_opNorm`).
1. (Integrability.) Let ω ∈ D^k(U) and K := tsupport ω, compact and ⊆ U. The integrand F_ω(x) := θ(x)ξ(x)(ω(x)) vanishes for x ∉ K. On M ∩ K it is Hᵏ-a.e. strongly measurable (θ is a.e. strongly measurable on M ∩ K as it is integrable there, ξ is a.e. strongly measurable on M, ω is continuous, and evaluation (w, α) ↦ w(α) is continuous) and |F_ω| ≤ sup_x‖ω(x)‖·|θ| Hᵏ-a.e. on M ∩ K. Since θ ∈ L¹(Hᵏ⌞(M ∩ K)) (integrableOn field) and ω is bounded (continuous with compact support), F_ω ∈ L¹(Hᵏ⌞M) (write F_ω = 1_K·F_ω; `IntegrableOn` of M ∩ K extended by zero).
2. (Linearity.) For ω, ω' ∈ D^k(U) and a, b ∈ ℝ, F_{aω+bω'} = aF_ω + bF_{ω'} pointwise (ξ(x) is linear), so by Step 1 and linearity of the integral, tauAction k M θ ξ (aω + bω') = a·tauAction k M θ ξ ω + b·tauAction k M θ ξ ω'. Thus R₀(ω) := tauAction k M θ ξ ω defines a linear map TestFormOn U k →ₗ[ℝ] ℝ.
3. (Continuity.) Let ω_l ∈ D^k(U) with TestFormOnConverges ω 0: a compact K ⊆ U contains every tsupport ω_l and iteratedFDeriv ℝ 0 ω_l → 0 uniformly on K; since ‖iteratedFDeriv ℝ 0 ω_l x‖ = ‖ω_l(x)‖ (`norm_iteratedFDeriv_zero`), ε_l := sup_{x∈K}‖ω_l(x)‖ → 0, and ω_l = 0 off K. Then |R₀(ω_l)| ≤ ∫_{M∩K} |θ|·‖ω_l‖ dHᵏ ≤ ε_l·∫_{M∩K}|θ| dHᵏ → 0 (θ ∈ L¹(Hᵏ⌞(M∩K))).
4. (Conclusion.) R := ⟨R₀, Step 3⟩ is a GeometricCurrentOn U k, and R(ω) = tauAction k M θ ξ ω for every ω ∈ D^k(U) by construction. ∎

## Key steps

1. Unit simple orientation: |ξ(x)(α)| ≤ ‖α‖ a.e. on M.
2. θξ(ω) is integrable: supported in tsupport ω, dominated by sup‖ω‖·θ on M ∩ tsupport ω.
3. Linearity of the integral gives a linear functional on D^k(U).
4. Sequential continuity: |τ(ω_l)| ≤ sup_K‖ω_l‖·∫_{M∩K}θ → 0.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (byte-identical); read Contract.lean: IsRectifiableTriple, tauAction, IsIntegerMultiplicity, IsMeasureRepresentation, IsRestriction, IsSlice`
- `grep -n '^def |^theorem |^structure |^abbrev |^noncomputable def ' simongmt Chapter03/{Rectifiable,Differential}.lean and Chapter06/{Forms,FormsDuality,Currents,Mass,WedgeForms,CurrentLocalEquality}.lean`
- `grep -rn 'def alternatizeUncurryFinCLM|def smulRightL|def innerSL' mathlib/Mathlib`
- `grep -rn 'theorem LipschitzOnWith.extend_real|theorem ae_ball_iff|theorem LipschitzWith.ae_differentiableAt|theorem ae_tendsto_average|theorem measurable_fderiv|theorem measurableSet_of_differentiableAt|theorem exists_measurable_subset_ae_eq|theorem MeasurableSet.image_of_continuousOn_injOn|theorem lintegral_tsum|theorem restrict_congr_set|theorem norm_iteratedFDeriv_zero|theorem iteratedFDeriv_sub|theorem fderiv_smul|aestronglyMeasurable_iUnion_iff|contDiff_convolution_left' mathlib/Mathlib`
- `grep -rn 'μHE\[' mathlib/Mathlib; read Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure, euclideanHausdorffMeasure_zero)`
- `read mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean (ContinuousMap.instSecondCountableTopology)`
- `python3 contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py (child scope: namespace GMT.Ch06 + opens)`
- `lake build GMT.Ch06.Submission in scratch /tmp/sim_split (frozen d8d46c9, shared packages lake-packages-25730c7c)`
- `lake env lean Scratch/Stmts.lean (seven child types and the parent type in the exact comparator scope; 0 errors; #print output checked for binder scopes)`
- `lake env lean Scratch/Assembly.lean (parent type from children tangential_gradient, slice_triple, slice_identity, testform_determining, tau_current; #print axioms)`
- `lake env lean Scratch/Api.lean (interior-product CLM evaluates by rfl to alternatizeUncurryFin ((innerSL ℝ w).smulRight α); alternatizeUncurryFin expansion; cited lemma signatures)`
- `python3 scan of dag.json lean_name values (260 nodes) for the seven proposed names and for reusable accepted declarations (rectifiability_weighted_tangent_ae, cmb_exists_countable_dense_testForms, lpf_pic_current_of_dominated_density, lpf_weighted_tangent_on_c1_chart, lpf_countably_rectifiable_c1_cover)`
- `rg 'slicing_im_' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project (no match)`
- `sed book/chapter-06.txt §4 (4.1–4.6), chapter-03.txt §1–2 (1.2–1.9, 2.1–2.10), chapter-02.txt (1.5, 4.5–4.14, 6.1–6.7)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/WedgeForms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1/decomposition-v1.json`
- `/tmp/sim_split/Scratch/Stmts.lean`
- `/tmp/sim_split/Scratch/Assembly.lean`
- `/tmp/sim_split/Scratch/Api.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 Contract; Submission is byte-identical, so child types may use only contract, SimonGMT and Mathlib names. SimonGMT supplies currents, test forms, TestFormOnConverges, simpleNVector and the weighted approximate tangent plane with uniqueness at θ(x) ≠ 0. It has no tangential gradient for Lipschitz functions on rectifiable sets, no co-area formula beyond the linear case and no slicing; Mathlib has none of these either. Those results (Simon Ch. 2, 1.5, 4.10, 6.3–6.6; Ch. 3, 1.2–1.9, 2.1–2.10; Federer 2.10.25, 3.2.22) are therefore cited inside the child proofs. Mathlib does provide: McShane (`LipschitzOnWith.extend_real`), Rademacher (`LipschitzWith.ae_differentiableAt`), Lebesgue differentiation (`IsUnifLocDoublingMeasure.ae_tendsto_average`), `ae_ball_iff`, `measurable_fderiv`, Lusin–Souslin images, `alternatizeUncurryFinCLM`/`smulRightL`/`innerSL` and second countability of C(K, F). The interior product ξ⌞(G/|G|) is written with these CLMs and evaluates by `rfl` to ξ(ν♭∧α). All seven child types elaborate in the comparator scope with the intended binder structure. The parent type is kernel-checked from five of them (axioms propext, Classical.choice, Quot.sound). None of the seven names occurs in the snapshot project or among the 260 DAG nodes. The chart-cover and C¹-chart tangent lemmas of the lipschitz-pushforward branch are not yet accepted, so they cannot be reused; no accepted declaration has an identical type to any child. These checks do not certify the analytic proofs.
