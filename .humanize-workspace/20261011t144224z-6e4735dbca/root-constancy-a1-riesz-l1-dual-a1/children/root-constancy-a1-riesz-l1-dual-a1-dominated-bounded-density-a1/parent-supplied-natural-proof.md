# Parent-supplied natural-language proof

- Parent DAG node: `root.constancy-a1.riesz_l1_dual-a1`
- Child DAG node: `root.constancy-a1.riesz_l1_dual-a1.dominated_bounded_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and role. Simon, Ch. 6, proof of Theorem 2.34 (p. 142), invokes the Riesz representation theorem (L¹)* = L^∞ without proof. This lemma is Steps 3–5 of the parent-supplied standard Radon–Nikodym proof of that theorem (cf. Folland, Real Analysis, Thm 6.15), stated for a set function ν. The parent applies it to ν(A) := F(1_A) with the constant max(C, 0). Throughout, μ(A) denotes the real number μ.real A = (μ A).toReal, which is finite and ≥ 0 because μ is finite.

Hypotheses:
- μ is finite and C ≥ 0.
- (Add) ν(A ∪ B) = ν(A) + ν(B) for disjoint measurable A, B.
- (Dom) |ν(A)| ≤ C μ(A) for measurable A.

1. (ν(∅) = 0.) ∅ is measurable and μ(∅) = 0, so (Dom) gives |ν(∅)| ≤ C·0 = 0.

2. (Finite unions.) Let (s_i)_{i∈ℕ} be pairwise disjoint measurable sets and S_N := ⋃_{i<N} s_i. Each S_N is a finite union of measurable sets, hence measurable. We show ν(S_N) = Σ_{i<N} ν(s_i) by induction on N.
   - N = 0: S_0 = ∅, and both sides vanish by Step 1.
   - N → N+1: S_{N+1} = S_N ∪ s_N, and S_N ∩ s_N = ∅ because s_i ∩ s_N = ∅ for every i < N (as i ≠ N). So (Add) gives ν(S_{N+1}) = ν(S_N) + ν(s_N) = Σ_{i<N+1} ν(s_i).

3. (Countable additivity.) With s_i and S_N as in Step 2, let A := ⋃_i s_i (measurable).
   (a) For each N, S_N ⊆ A, so A is the disjoint union of the measurable sets S_N and A \ S_N. (Add) and Step 2 give ν(A) − Σ_{i<N} ν(s_i) = ν(A \ S_N).
   (b) By (Dom) and finiteness of μ, |ν(A \ S_N)| ≤ C μ(A \ S_N) = C (μ(A) − μ(S_N)). The sets S_N increase and ⋃_N S_N = A (a point of s_i lies in S_{i+1}). By continuity of measure from below, μ(S_N) → μ(A); the real values converge because μ(A) < ∞. Hence ν(A \ S_N) → 0, i.e. Σ_{i<N} ν(s_i) → ν(A) as N → ∞.
   (c) By σ-additivity of μ on the disjoint measurable s_i, Σ_i μ(s_i) = μ(A) < ∞, so the real series Σ_i μ(s_i) is summable. Since |ν(s_i)| ≤ C μ(s_i), the series Σ_i |ν(s_i)| is summable by comparison.
   (d) A real series whose absolute values are summable is unconditionally summable, and its sum is the limit of its partial sums over {0, …, N−1} (Mathlib hasSum_iff_tendsto_nat_of_summable_norm). By (b) and (c), HasSum (i ↦ ν(s_i)) (ν(A)).

4. (The signed measure.) Define s(B) := ν(B) if B is measurable and s(B) := 0 otherwise.
   - By Step 1, s(∅) = 0.
   - s vanishes on non-measurable sets.
   - For every pairwise disjoint sequence of measurable sets, Step 3 gives HasSum (i ↦ s(s_i)) (s(⋃_i s_i)), since all sets involved are measurable.
   Hence s is a finite signed measure on α (Mathlib SignedMeasure α = VectorMeasure α ℝ), and s(B) = ν(B) for every measurable B.
   Lean: Steps 2–4 are packaged in Mathlib as MeasureTheory.VectorMeasure.of_additive_of_le_measure (Mathlib/MeasureTheory/VectorMeasure/AddContent.lean). Apply it to m(B) := if MeasurableSet B then ν B else 0 and the finite measure C.toNNReal • μ, checking its hypotheses as follows.
   - For measurable B: ‖m B‖ₑ = ENNReal.ofReal |ν B| ≤ ENNReal.ofReal (C · μ.real B) = ENNReal.ofReal C · μ B = (C.toNNReal • μ) B. This uses ENNReal.ofReal_mul with C ≥ 0 and ofReal_measureReal with μ B ≠ ∞.
   - For non-measurable B: ‖m B‖ₑ = 0.
   - m is additive on disjoint measurable pairs by (Add) and vanishes on non-measurable sets.

5. (Absolute continuity.) If B is measurable and μ(B) = 0, then |s(B)| = |ν(B)| ≤ C·0 = 0. If B is not measurable, then s(B) = 0. Hence s ≪ μ, in Lean s ≪ᵥ μ.toENNRealVectorMeasure; for measurable B, μ.toENNRealVectorMeasure B = μ B by Measure.toENNRealVectorMeasure_apply_measurable.

6. (Radon–Nikodym.) μ is finite, hence σ-finite. By the Radon–Nikodym theorem for signed measures, θ₀ := s.rnDeriv μ is measurable and μ-integrable, and μ.withDensityᵥ θ₀ = s (Mathlib SignedMeasure.measurable_rnDeriv, SignedMeasure.integrable_rnDeriv, SignedMeasure.withDensityᵥ_rnDeriv_eq). Evaluating at a measurable B with withDensityᵥ_apply gives ν(B) = s(B) = ∫_B θ₀ dμ.

7. (A.e. bound.) For every measurable B, ∫_B θ₀ dμ = ν(B) ≤ |ν(B)| ≤ C μ(B) = ∫_B C dμ. Since θ₀ and the constant C are μ-integrable (μ finite), θ₀ ≤ C μ-a.e. by Mathlib ae_le_of_forall_setIntegral_le. Directly: E := {θ₀ > C} is measurable, and if μ(E) > 0 then ∫_E (θ₀ − C) dμ > 0 because the integrand is strictly positive on E, contradicting ∫_E θ₀ dμ ≤ C μ(E). Likewise ∫_B (−θ₀) dμ = −ν(B) ≤ |ν(B)| ≤ C μ(B) = ∫_B C dμ for every measurable B, so −θ₀ ≤ C μ-a.e. Therefore |θ₀| ≤ C μ-a.e.

8. (Truncation.) Define θ(x) := θ₀(x) if |θ₀(x)| ≤ C and θ(x) := 0 otherwise.
   - The set {x : |θ₀(x)| ≤ C} is measurable because θ₀ is measurable and |·| is continuous. So θ is measurable as a piecewise combination of the measurable functions θ₀ and 0.
   - For every x ∈ α, |θ(x)| ≤ C: in the first case by definition, in the second because |0| = 0 ≤ C.
   - By Step 7, θ(x) = θ₀(x) for μ-a.e. x, so for every measurable B, ∫_B θ dμ = ∫_B θ₀ dμ = ν(B) (Mathlib setIntegral_congr_ae).
   Thus θ is measurable, |θ(x)| ≤ C for all x, and ν(B) = ∫_B θ dμ for all measurable B. ∎

Implementation note (not a proof step): the frozen Submission imports do not include the vector-measure library. The child's Submission.lean must add import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym and import Mathlib.MeasureTheory.VectorMeasure.AddContent.

## Key steps

1. ν(∅) = 0, and ν(⋃_{i<N} s_i) = Σ_{i<N} ν(s_i) for pairwise disjoint measurable s_i (induction using additivity).
2. Countable additivity: ν(⋃ s_i) − Σ_{i<N} ν(s_i) = ν(A∖S_N), with |ν(A∖S_N)| ≤ C μ(A∖S_N) → 0, and Σ|ν(s_i)| ≤ C μ(⋃ s_i) < ∞, so HasSum holds. In Lean this is VectorMeasure.of_additive_of_le_measure with the finite measure C.toNNReal • μ.
3. s := ν on measurable sets (0 elsewhere) is a signed measure, and s ≪ μ because μ(A) = 0 implies |ν(A)| ≤ 0.
4. Signed Radon–Nikodym: θ₀ := s.rnDeriv μ is measurable and integrable, with ν(A) = ∫_A θ₀ dμ (withDensityᵥ_rnDeriv_eq, withDensityᵥ_apply).
5. ±∫_A θ₀ = ±ν(A) ≤ C μ(A) = ∫_A C for every measurable A, so |θ₀| ≤ C μ-a.e. (ae_le_of_forall_setIntegral_le).
6. Truncate: θ := θ₀ on {|θ₀| ≤ C} and 0 elsewhere. θ is measurable, |θ| ≤ C everywhere and θ = θ₀ a.e., so ν(A) = ∫_A θ dμ.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n -i 'dual.*L1|L1.*dual|LpDual|Lp\.dual|lpDual|toDual' mathlib/Mathlib/MeasureTheory -l`
- `rg -n 'StrongDual|Dual' mathlib/Mathlib/MeasureTheory/Function/Holder.lean`
- `rg -n "def ofAdditive|ofAddContent|def of_additive|m_iUnion'" mathlib/Mathlib/MeasureTheory/VectorMeasure`
- `sed -n 1,120p mathlib/Mathlib/MeasureTheory/VectorMeasure/AddContent.lean (VectorMeasure.of_additive_of_le_measure)`
- `rg -n 'theorem Integrable.induction|theorem withDensityᵥ_rnDeriv_eq|theorem ae_le_of_forall_setIntegral_le|theorem hasSum_iff_tendsto_nat_of_summable_norm|theorem tendsto_measure_iUnion_atTop|theorem integral_indicator_one|theorem Integrable.mul_bdd|theorem summable_toReal|theorem toENNRealVectorMeasure_apply_measurable' mathlib/Mathlib`
- `rg -n 'theorem measurable_rnDeriv|theorem integrable_rnDeriv|theorem withDensityᵥ_apply|theorem setIntegral_congr_ae|theorem setIntegral_const|theorem coeFn_sub|theorem integrable_coeFn|theorem measureReal_nonneg' mathlib/Mathlib/MeasureTheory`
- `rg -n -i 'riesz|L1Dual|rnDeriv|SignedMeasure' project/GMT/Ch06`
- `lake env lean Probe.lean after `import GMT.Ch06.Submission`: #check Integrable.induction, SignedMeasure.withDensityᵥ_rnDeriv_eq, ae_le_of_forall_setIntegral_le, integral_indicator_one, Measure.real, finiteL1DualField, hasSum_iff_tendsto_nat_of_summable_norm, VectorMeasure`
- `cat lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/FiniteL1Dual.lean (alternative L2 route of the parent's remark)`
- `python3 -I: lean_contract.validate_lean_statement + gmt-compare.child_modules(mode='contract') on both child statements against the frozen Contract.lean`
- `lake env lean /tmp/riesz_l1_decomp/{ChildB,ChildA,ChildAMerged,Assembly,AssemblyNodes,Assembly2,ChildBFrozenOnly}.lean with #print axioms`
- `dag.json lean_name scan (259 nodes) and git grep of the proposed names over all branch heads under GMT/`
- `git show <candidate_commit>:GMT/Ch06/Submission.lean import scan over DAG nodes (extra imports present in accepted children)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/VectorMeasure/AddContent.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/VectorMeasure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/VectorMeasure/Decomposition/Lebesgue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/VectorMeasure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/VectorMeasure/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/VectorMeasure/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Holder.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/InfiniteSum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/FiniteL1Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-riesz-l1-dual-a1/parent-child-handoff.json`
- `/tmp/riesz_l1_decomp/Probe.lean`
- `/tmp/riesz_l1_decomp/Stmts.lean`
- `/tmp/riesz_l1_decomp/ChildA.lean`
- `/tmp/riesz_l1_decomp/ChildB.lean`
- `/tmp/riesz_l1_decomp/ChildAMerged.lean`
- `/tmp/riesz_l1_decomp/Assembly.lean`
- `/tmp/riesz_l1_decomp/AssemblyNodes.lean`
- `/tmp/riesz_l1_decomp/Assembly2.lean`
- `/tmp/riesz_l1_decomp/ChildBFrozenOnly.lean`

Snapshot: project d8d46c95 with Mathlib 25730c7c.

No-match results: the snapshot Mathlib has no (L1)* = L∞ theorem. The dual-pattern search matched only unrelated files (Measure/CharacteristicFunction/Basic.lean, Constructions/BorelSpace/Order.lean), and Function/Holder.lean only defines the pairing map Lp → StrongDual(Lq). The project snapshot has no Riesz, rnDeriv or SignedMeasure declaration, only docstring mentions in Contract.lean, Submission.lean and README.md.

Found and used:
- MeasureTheory.VectorMeasure.of_additive_of_le_measure (VectorMeasure/AddContent.lean:34): a finitely additive set function dominated by a finite measure is countably additive. This makes a separate countable-additivity child redundant.
- SignedMeasure.measurable_rnDeriv and integrable_rnDeriv (Decomposition/Lebesgue.lean:169,173).
- SignedMeasure.withDensityᵥ_rnDeriv_eq (Decomposition/RadonNikodym.lean:29) and withDensityᵥ_apply (WithDensity.lean:60).
- Measure.toENNRealVectorMeasure_apply_measurable (Operations.lean:114).
- ae_le_of_forall_setIntegral_le (AEEqOfIntegral.lean:151).
- Integrable.induction (SimpleFuncDenseLp.lean:943) and Integrable.mul_bdd (L1Space/Integrable.lean:1072).
- integral_indicator_one (Bochner/Set.lean:533), hasSum_iff_tendsto_nat_of_summable_norm and tendsto_measure_iUnion_atTop.

Import scope: after the frozen `import GMT.Ch06.Submission`, Integrable.induction, ae_le_of_forall_setIntegral_le, integral_indicator_one and Measure.real resolve. VectorMeasure, SignedMeasure.withDensityᵥ_rnDeriv_eq and SimonGMT finiteL1DualField are unknown identifiers. The frozen child statements therefore use only Measure, Integrable, indicators and set integrals. gmt-compare.py byte-checks only the Contract and build inputs, and accepted children (restriction_theory, mass_measure_representation, orientation, weighted_tangent_ae) added imports, so child 1 may import the vector-measure modules. SimonGMT FiniteL1Dual, the L2 route of the parent's remark, is not needed.

Verification: both statements pass the validator and contract-mode child_modules generation. Full proofs of both children, the parent assembled from them, and the simulated NodeSolution targets compile with only propext, Classical.choice and Quot.sound. Child 2 also compiles with the frozen imports alone. Neither name collides with the 259 DAG nodes or any branch head.
