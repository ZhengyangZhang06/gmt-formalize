# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1`
- Child DAG node: `root.slicing-a1.slice_exists-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions (as in the parent proof). D^k(U) is the space of test k-forms on U (smooth, compact support, tsupport ⊆ U; `TestFormOn U k`), D_k(U) the currents (`GeometricCurrentOn U k`: linear, and X(ω_j) → 0 whenever ω_j → 0 in D^k(U), i.e. all tsupports lie in one compact K ⊆ U and every iterated derivative of ω_j tends to 0 uniformly on K). I(k,P) is the set of strictly increasing β : {1,…,k} → {1,…,P}; e_β := (e_{β_1},…,e_{β_k}); dx^β is the coordinate k-covector, dx^β(e_γ) = δ_{βγ} for β, γ ∈ I(k,P). Fact A: every k-covector α equals Σ_β α(e_β) dx^β, and |α|² = Σ_β α(e_β)², where |α| := covectorEuclideanNorm α. A k-vector is a continuous linear functional w on k-covectors (`NVector`); put w^β := w(dx^β), so w(α) = Σ_β α(e_β) w^β and |w(α)| ≤ |α|·|w| with |w| := (Σ_β (w^β)²)^{1/2} (Cauchy–Schwarz). For a form ω, ‖ω‖ := sup_x |ω(x)|. M_W(X) = X.massOn W is the supremum of X(ω) over ω ∈ D^k(U) with tsupport ω ⊆ W and |ω(x)| ≤ 1 for all x. ρ_ε is a standard mollifier (smooth, ≥ 0, supported in the closed ε-ball, ∫ρ_ε = 1); for a continuous compactly supported form φ, ρ_ε*φ (componentwise convolution) is smooth, supported in the closed ε-neighbourhood of tsupport φ, satisfies |ρ_ε*φ(x)| ≤ ‖φ‖ (|·| is a norm, hence convex) and ρ_ε*φ → φ uniformly as ε ↓ 0. All measures are Borel measures on ℝ^P = Eucl P.

Source: Simon Ch. 6, 4.6 and the parent proof's Step 1, using the sibling `slicing_mass_representation` (R1/R3) in place of the parent's preliminaries. Let P, m, U open, T ∈ D_{m+1}(U) with M_W(T) < ∞ and M_W(∂T) < ∞ for every open W with compact closure ⊆ U, f : ℝ^P → ℝ with |f(x) − f(y)| ≤ L|x − y| for x, y ∈ U, and t ∈ ℝ.

1. (The set A_t.) Let A_t := {x | x ∈ U ∧ f x < t} = U ∩ f⁻¹((−∞,t)). Since f is Lipschitz, hence continuous, on U and U is open, A_t is open (`ContinuousOn.isOpen_inter_preimage`), in particular Borel.

2. (Restriction of T.) Apply the sibling `slicing_mass_representation` to X := T (degree m+1; its hypothesis M_W(T) < ∞ for W ⊂⊂ U is the first half of ours). It gives μ, v with IsMeasureRepresentation T μ v and, by its conclusion (e) for the Borel set A_t, a current A ∈ D_{m+1}(U) with A(η) = ∫_{A_t} v(x)(η(x)) dμ(x) for every η ∈ D^{m+1}(U). Hence IsRestriction T A_t A (A_t is measurable; witnesses μ, v).

3. (Restriction of ∂T.) Apply the same sibling to X := ∂T (degree m; M_W(∂T) < ∞ for W ⊂⊂ U is the second half of our hypothesis). It gives μ′, v′ with IsMeasureRepresentation ∂T μ′ v′ and a current B ∈ D_m(U) with B(ω) = ∫_{A_t} v′(x)(ω(x)) dμ′(x) for every ω ∈ D^m(U). Hence IsRestriction ∂T A_t B.

4. (The slice.) The boundary ∂A ∈ D_m(U), ∂A(ω) = A(dω), is a current (d maps D^m(U) linearly and sequentially continuously into D^{m+1}(U); this is `GeometricCurrentOn.boundary`). Define S(ω) := ∂A(ω) − B(ω) for ω ∈ D^m(U). S is linear, and if ω_j → 0 in D^m(U) then ∂A(ω_j) → 0 and B(ω_j) → 0, so S(ω_j) → 0. Thus S ∈ D_m(U), i.e. S := ⟨toCurrent := ∂A − B, continuity from the two continuity properties⟩.

5. (Conclusion.) With the witnesses A and B of steps 2–3 and S(ω) = A.boundary(ω) − B(ω) for every ω, IsSlice T f t S holds, i.e. S = ∂(T⌞{f<t}) − (∂T)⌞{f<t} (Simon 4.6). ∎

## Key steps

1. A_t = {x ∈ U : f x < t} is open (f continuous on the open set U), hence measurable.
2. slicing_mass_representation for T gives a representation (μ, v) and a current A with A(η) = ∫_{A_t} v(η) dμ, so IsRestriction T A_t A.
3. slicing_mass_representation for ∂T gives (μ′, v′) and B with IsRestriction ∂T A_t B.
4. S := ∂A − B is linear and sequentially continuous, so it is a current; IsSlice T f t S with witnesses A, B.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp workspaces/gmt-ch06/GMT/Ch06/Contract.lean against GMT/Ch06/Submission.lean and against snapshot project/GMT/Ch06/Contract.lean (all identical)`
- `read project/GMT/Ch06/Contract.lean: IsMeasureRepresentation, IsRestriction, IsSlice, IsIntegerMultiplicity, IsRectifiableTriple, CompactlyContainedOpen, SlicingTheorem`
- `read simongmt Chapter06/{Currents,Mass,FormsDuality,CurrentLocalEquality,Forms,Representation}.lean: GeometricCurrentOn, TestFormOnConverges, GeometricCurrentOn.boundary, tsupport_exteriorDerivative_subset, massOn, massAdmissibleOn, covectorEuclideanNorm, zeroRegion, support, NVector`
- `grep -rn 'theorem simon_theorem_4_14' simongmt/Poincare/SimonGMT/Chapter01 (RadonPolarRepresentation.lean; IsLocallyBoundedCcFunctional in VectorFunctionalEnvelope.lean; IsRadonOuterMeasure in RadonOuterMeasure.lean)`
- `grep -rln 'coarea|co-area' simongmt/Poincare/SimonGMT (only linear co-area: Chapter02/CoareaLinear.lean, CoareaProjection.lean; no co-area formula for rectifiable sets)`
- `grep -n '^def |^theorem ' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable, HasWeightedApproximateTangentSpaceAt)`
- `grep -rn 'Monotone.ae_differentiableAt|MonotoneOn.intervalIntegral_deriv_mem_uIcc|MonotoneOn.intervalIntegrable_deriv' mathlib/Mathlib`
- `grep -rn 'LipschitzOnWith.extend_real|LipschitzOnWith.ae_differentiableWithinAt_of_mem|theorem measurable_deriv|theorem ext_of_generate_finite' mathlib/Mathlib`
- `grep -rln 'Lusin' mathlib/Mathlib/MeasureTheory (only Lusin–Souslin; Lusin's continuity theorem is cited from Simon Ch. 1, 1.17)`
- `python3 contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py (child scope: namespace GMT.Ch06 + opens)`
- `lake build GMT.Ch06.Submission (scratch /tmp/slicing_split_check_r1, frozen d8d46c9, pinned shared packages)`
- `lake env lean Scratch/Stmts.lean and Scratch/FinalChallenge.lean (6 child statements as _root_ comparator targets in the contract scope; 0 errors)`
- `lake env lean Scratch/Assembly.lean (SlicingTheorem from slicing_exists, slicing_support_subset, slicing_mass_bound, slicing_integer_multiplicity_ae; #print axioms)`
- `lake env lean Scratch/Glue.lean (slicing_exists from slicing_mass_representation; slicing_support_subset from slicing_representation_unique; restriction-mass identification from both; #print axioms)`
- `python3 listing of dag.json lean_name values (20 nodes) and grep of the run's nodes/ for the six proposed names (no matches)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Representation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonOuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1/parent-child-handoff.json`
- `/tmp/slicing_split_check_r1/Scratch/Stmts.lean`
- `/tmp/slicing_split_check_r1/Scratch/FinalChallenge.lean`
- `/tmp/slicing_split_check_r1/Scratch/Assembly.lean`
- `/tmp/slicing_split_check_r1/Scratch/Glue.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 Contract; Submission is byte-identical, so child statements may use only contract, SimonGMT and Mathlib names. SimonGMT provides currents with sequential continuity, boundary, massOn (Euclidean coefficient norm), support/zeroRegion and the vector Riesz theorem `simon_theorem_4_14` on any locally compact Hausdorff space (Radon outer measure, unit field a.e.). It has only linear co-area and no co-area for rectifiable sets, and Mathlib has neither (nor Lusin's continuity theorem), so these are cited from Simon Ch. 3 §2 and Ch. 1, 1.17. Mathlib provides McShane (`LipschitzOnWith.extend_real`), Rademacher (`LipschitzOnWith.ae_differentiableWithinAt_of_mem`), Lebesgue's theorem for monotone functions (`Monotone.ae_differentiableAt`, `MonotoneOn.intervalIntegral_deriv_mem_uIcc`) and π-system uniqueness of finite measures (`ext_of_generate_finite`). In a scratch build of the frozen project, all six child statements elaborate in the comparator's child scope. `SlicingTheorem` follows from the four property children by `choose` plus assembly. `slicing_exists` follows from `slicing_mass_representation`, `slicing_support_subset` from `slicing_representation_unique`, and the restriction-mass identification used by `slicing_mass_bound` from both. All of these are kernel-checked with axioms [propext, Classical.choice, Quot.sound]. The DAG (20 nodes) reserves none of the six proposed names; the concurrently added polyhedral children have different names and types. These checks do not certify the analytic proofs.
