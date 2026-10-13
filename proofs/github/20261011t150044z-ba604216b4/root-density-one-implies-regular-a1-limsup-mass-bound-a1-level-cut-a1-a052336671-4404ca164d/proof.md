# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.level_cut-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.level_cut-a1.cut_cycle-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 6 (‡), 6(a), 6(b) and 8(a) of the parent proof, i.e. Simon 7.2.4 display (3) (chapter-07.txt lines 193–196: ∂(R_j⌞W_α) = (∂R_j)⌞W_α + P_j) and Simon Ch. 6, 4.5(2) (chapter-06.txt lines 1240–1241: ⟨T, f, t⟩ = ∂[T⌞{f < t}] − (∂T)⌞{f < t}). In the parent, D = (∂R)⌞B comes from borel_restriction and Q = P_t from slicing; here only their defining formulas are used. Notation: for ω ∈ 𝒟ⁿ(U) put A(ω) := ∫_{M̂∩B} θ̂⟨dω, ξ̂⟩ dH^{n+1} and C(ω) := ∫_{M_B∩B} θ_B⟨ω, ξ_B⟩ dHⁿ (real numbers). Frozen facts used: d maps 𝒟ⁿ(U) linearly into 𝒟^{n+1}(U) with underlying form exteriorDerivative ω (exteriorDerivativeTestOn); tsupport(dω) ⊆ tsupport(ω) (tsupport_exteriorDerivative_subset); d(dω) = 0 for smooth ω (exteriorDerivative_sq, Simon 6.1.12); ∂R(ω) = R(dω) (GeometricCurrentOn.boundary_apply); a function vanishes outside its topological support.
1. Construction of X. Let X(ω) := D(ω) + Q(ω) for ω ∈ 𝒟ⁿ(U). X is linear, being the sum of the linear functionals underlying D and Q. It satisfies the continuity condition of GeometricCurrentOn: if ω_j → 0 in the test-form topology of 𝒟ⁿ(U), then D(ω_j) → 0 and Q(ω_j) → 0, so X(ω_j) → 0 + 0 = 0. Hence X ∈ 𝒟_n(U), and X(ω) = D(ω) + Q(ω) for all ω by construction.
2. The identity (‡). For every ω ∈ 𝒟ⁿ(U), X(ω) = C(ω) + (A(ω) − C(ω)) = A(ω). This is real arithmetic and needs no integrability.
3. ∂X = 0. If n = 0, BoundaryVanishes X is True (Simon's convention ∂ = 0 in degree 0). Let n = m + 1 and η ∈ 𝒟^m(U). Then dη ∈ 𝒟ⁿ(U) and, by step 2, ∂X(η) = X(dη) = A(dη) = ∫_{M̂∩B} θ̂⟨d(dη), ξ̂⟩ dH^{n+1}. Since η is smooth, d(dη) = 0, so the integrand is θ̂(x)⟨0, ξ̂(x)⟩ = 0 (ξ̂(x) is linear), and ∂X(η) = 0. As η is arbitrary, ∂X = 0 (GeometricCurrentOn.ext).
4. Vanishing off B̄. Let ω ∈ 𝒟ⁿ(U) with tsupport ω ∩ B̄ = ∅, and let x ∈ M̂ ∩ B. Then x ∈ B ⊆ B̄, so x ∉ tsupport ω ⊇ tsupport dω; hence dω(x) = 0 and the integrand of A(ω) vanishes at x. Therefore A(ω) = 0 (setIntegral_eq_zero_of_forall_eq_zero), and X(ω) = A(ω) = 0 by step 2.
5. Agreement with ∂R inside B. Let ω ∈ 𝒟ⁿ(U) with tsupport ω ⊆ B. Since R̂ represents R and dω ∈ 𝒟^{n+1}(U), ∂R(ω) = R(dω) = ∫_{M̂} θ̂⟨dω, ξ̂⟩ dH^{n+1}. If x ∈ M̂ \ (M̂ ∩ B), then x ∉ B ⊇ tsupport ω ⊇ tsupport dω, so dω(x) = 0 and the integrand vanishes at x. Since M̂ is measurable (measurableSet_carrier) and M̂ ∩ B ⊆ M̂, an integrand vanishing on M̂ \ (M̂ ∩ B) has the same integral over M̂ and over M̂ ∩ B (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero; this holds whether or not it is integrable, since integrability over M̂ and over M̂ ∩ B are then equivalent). Hence ∂R(ω) = A(ω) = X(ω) by step 2.
6. Steps 1, 3, 4 and 5 give the four assertions for X. ∎

## Key steps

1. X := D + Q is a current, and by cancellation X(ω) = ∫_{M̂∩B_t(y)} θ̂⟨dω, ξ̂⟩ dH^{n+1} for every ω (‡).
2. ∂X(η) = X(dη) involves d(dη) = 0, so ∂X = 0 (vacuous for n = 0).
3. If spt ω misses B̄_t(y), then dω = 0 on B_t(y), so X(ω) = 0.
4. If spt ω ⊆ B_t(y), then dω = 0 off B_t(y), so ∂R(ω) = R(dω) = ∫_{M̂} θ̂⟨dω, ξ̂⟩ = ∫_{M̂∩B_t(y)} θ̂⟨dω, ξ̂⟩ = X(ω).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `python3 -I: verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') -> open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section; end`
- `grep -n '^def|^structure|^theorem|^abbrev|^instance' simongmt Chapter06/Currents.lean; read Chapter06/Mass.lean, Forms.lean, CurrentLocalEquality.lean`
- `grep -rn 'instance.*Add' simongmt Chapter06 (no match: GeometricCurrentOn has no Add instance; the contract defines only Sub)`
- `rg -n in snapshot mathlib: 'protected theorem dist_left' (Topology/MetricSpace/Lipschitz.lean:142), 'theorem countable_meas_pos_of_disjoint_iUnion' (Measure/Typeclasses/SFinite.lean:305), 'theorem meas_ge_le_lintegral_div' (Integral/Lebesgue/Markov.lean:106), 'theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|theorem setIntegral_eq_zero_of_forall_eq_zero' (Integral/Bochner/Set.lean:466,357), 'theorem ball_union_sphere' (MetricSpace/Pseudo/Defs.lean:504), 'theorem le_iff'' (Measure/CompleteLattice.lean:46), 'lemma isFiniteMeasure_restrict' (Typeclasses/Finite.lean:40), 'theorem lintegral_eq_zero_iff'' (Lebesgue/Basic.lean:322), 'theorem volume_Ioo' (Measure/Lebesgue/Basic.lean:96), 'theorem ofReal_add_le' (Basic/ENNReal/Real.lean:57), 'image_eq_one_of_notMem_mulTSupport|mulTSupport_inv' (Topology/Algebra/Support.lean:111,154), 'theorem _root_.Set.Countable.measure_zero' (Typeclasses/NullSingletonClass.lean:58), 'theorem extDeriv_extDeriv ' (DifferentialForm/Basic.lean:234)`
- `python3 -I dag.json: lean_name collision scan for dor_lmb_glc_* (677 nodes, none); keyword scan of lean_statements and ids for sphere|Markov|countable|∫⁻ t|triangle|good|level`
- `git log --all -S 'dor_lmb_glc' -- GMT/Ch07/Submission.lean; git log --all -S 'dor_lmb_good_level_cut' -- GMT/Ch07/Submission.lean (no match)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement on the three lean_statement strings (accepted unchanged)`
- `lake env lean /tmp/glc-decomp/Types.lean (three child types elaborate in the comparator scope)`
- `lake env lean /tmp/glc-decomp/Children.lean (#print axioms of the three proved children: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/glc-decomp/Assembly.lean and /tmp/glc-decomp/Full.lean (#print axioms Submission.dor_lmb_good_level_cut: sorryAx only from the three sibling stubs; comparator-style `exact Submission.X` targets for each child)`
- `sed -n chapter-07.txt 180-250, chapter-06.txt 225-240 and 1215-1243, chapter-02.txt 1512-1535`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/CompleteLattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-level-cut-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-level-cut-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/decomposition-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/glc-decomp/Types.lean`
- `/tmp/glc-decomp/Children.lean`
- `/tmp/glc-decomp/Assembly.lean`
- `/tmp/glc-decomp/Full.lean`
- `/tmp/glc-decomp/children_final.json`

Snapshot: project b4d606d, mathlib 25730c7c, simongmt 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Reusable facts found:
- SimonGMT Chapter06: exteriorDerivativeTestOn, GeometricCurrentOn.boundary_apply, GeometricCurrentOn.ext, zero_apply, tsupport_exteriorDerivative_subset, exteriorDerivative_sq (d∘d = 0), massAdmissibleOn, massOn, le_massOn, massOn_mono, covectorEuclideanNorm_neg.
- Mathlib: LipschitzWith.dist_left, Measure.countable_meas_pos_of_disjoint_iUnion, meas_ge_le_lintegral_div, lintegral_eq_zero_iff', isFiniteMeasure_restrict, Set.Countable.measure_zero, Real.volume_Ioo, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, setIntegral_eq_zero_of_forall_eq_zero, ball_union_sphere, Measure.le_iff', ENNReal.ofReal_add_le, image_eq_zero_of_notMem_tsupport and tsupport_neg (additive forms of the mulTSupport lemmas).

Not available:
- No Add instance on GeometricCurrentOn, so sums of currents are built inline.
- No accepted radius-selection or mass-difference lemma. Related nodes are lcmp_massOn_le_add_of_eval_eq (decomposing; its |c| ≤ 1 general form is not accepted, so not reused), lcmp_exists_good_slice_level and cmc_fc_good_slice (decomposing, different statements), and dtc_measure_ball_eq_of_null_sphere (accepted, different statement).
- No name collisions for the three dor_lmb_glc_* identifiers.

Lean checks in the exact comparator scope:
- The three child types elaborate.
- Their full proofs compile using only propext, Classical.choice and Quot.sound.
- The exact frozen parent type compiles from them and from sorry-stubs of the sibling frozen types dor_lmb_int_combination_imrep, dor_lmb_imrep_restrict_current and dor_lmb_slicing_lipschitz. The only sorryAx comes from those stubs.
- An independent reviewer re-verified this.
