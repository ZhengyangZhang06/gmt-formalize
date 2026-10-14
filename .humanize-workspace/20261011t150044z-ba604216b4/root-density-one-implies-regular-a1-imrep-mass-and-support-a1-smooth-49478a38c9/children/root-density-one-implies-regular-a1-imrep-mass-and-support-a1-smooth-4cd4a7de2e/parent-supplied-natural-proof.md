# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.smooth_unit_approximation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.smooth_unit_approximation-a1.covector_finite_dimensional-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 (Tietze) of the parent proof uses the fact 'Λ is a finite-dimensional real vector space' without proof. Mathlib has no such instance for continuous alternating maps, so the fact is proved here.
1. Let e = (e_j)_{j ∈ Fin P} be the standard basis of ℝ^P (EuclideanSpace.basisFun (Fin P) ℝ, regarded as a basis of the module Euclid P).
2. Define Φ : Λ → ((Fin n → Fin P) → ℝ) by Φ(α)(v) := α(e_{v(0)}, …, e_{v(n−1)}). Addition and scalar multiplication in Λ are pointwise, so Φ(α + α') = Φ(α) + Φ(α') and Φ(cα) = cΦ(α). Hence Φ is ℝ-linear.
3. Φ is injective. Suppose Φ(α) = Φ(α').
   - The underlying alternating maps of α and α' (ContinuousAlternatingMap.toAlternatingMap) are n-linear. They take the same value on every n-tuple of basis vectors (e_{v(0)}, …, e_{v(n−1)}).
   - An n-linear map is determined by these values. Write each argument as w_k = ∑_j w_k^j e_j and expand by multilinearity: α(w_0, …, w_{n−1}) = ∑_{σ : Fin n → Fin P} (∏_k w_k^{σ(k)}) α(e_{σ(0)}, …, e_{σ(n−1)}), and likewise for α'.
   - So the two alternating maps are equal (Mathlib Module.Basis.ext_alternating, which only needs agreement on injective σ).
   - A continuous alternating map is determined by its underlying alternating map (ContinuousAlternatingMap.toAlternatingMap_injective). Hence α = α'.
4. The codomain (Fin n → Fin P) → ℝ is finite-dimensional: its index set is finite, and its dimension is Pⁿ. A vector space with an injective linear map into a finite-dimensional space is finite-dimensional (FiniteDimensional.of_injective). Therefore Λ is finite-dimensional.

## Key steps

1. Evaluation on all n-tuples of standard basis vectors is a linear map Φ from Λ into the finite-dimensional space (Fin n → Fin P) → ℝ.
2. Φ is injective: multilinear maps that agree on basis tuples are equal (Module.Basis.ext_alternating), and a continuous alternating map is determined by its underlying alternating map.
3. An injective linear map into a finite-dimensional space forces finite dimension (FiniteDimensional.of_injective).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-smooth-49478a38c9/{parent-child-handoff.json,parent-supplied-natural-proof.md,parent-supplied-plan.md}`
- `python3 scan of dag.json nodes for lean_name/lean_statement containing smooth|testForm_approx|covectorEuclideanNorm|finiteDimensional (statuses and reserved names)`
- `grep -n covectorEuclideanNorm lake-packages-25730c7c/simongmt/Poincare/SimonGMT (Chapter06/Mass.lean, FormSupNorm.lean); grep -n 'Covector|DifferentialForm|IsTestForm' Chapter06/Forms.lean`
- `grep -n '^namespace|^open|^end|^noncomputable section|^variable|^theorem' GMT/Ch07/Contract.lean; sed -n 545,612p verifier/gmt-compare.py (contract_scope, child_modules)`
- `lake env lean /tmp/sua-decomp/Probe1.lean: FiniteDimensional ℝ (Covector (Euclid P) n) fails to synthesize; TietzeExtension, ContinuousMap.exists_restrict_eq and ContDiffBump.dist_normed_convolution_le are not imported by the contract`
- `rg -n 'dist_normed_convolution_le|normed_convolution_eq_right|nonneg_normed|contDiff_normed|integral_normed|support_normed_eq|hasCompactSupport_normed' mathlib/Mathlib/Analysis/Calculus/BumpFunction/*.lean; cat BumpFunction/SmoothApprox.lean`
- `rg -n 'ContinuousMap.exists_restrict_eq|instTietzeExtensionTVS|TietzeExtension.of_tvs|instance.*TietzeExtension' Topology/TietzeExtension.lean Analysis/Complex/Tietze.lean`
- `rg -n 'ext_multilinear|ext_alternating' LinearAlgebra/; grep 'theorem of_injective' LinearAlgebra/FiniteDimensional/Defs.lean; grep 'instance' LinearAlgebra/Multilinear/FiniteDimensional.lean; grep 'toAlternatingMap_injective|def apply' Topology/Algebra/Module/Alternating/{Basic,Topology}.lean`
- `grep -n 'dist_convolution_le|convolutionExists|convolution_def' Analysis/Convolution.lean; grep -n 'uniformContinuous_of_continuous' Topology/UniformSpace/HeineCantor.lean; grep -n 'mem_thickening_iff|mem_thickening_iff_infDist_lt|closure_thickening_subset_cthickening|cthickening_mono' Topology/MetricSpace/Thickening.lean; grep EuclideanSpace.equiv|EuclideanSpace.norm_eq Analysis/InnerProductSpace/PiL2.lean`
- `grep -rl dor_ims_sua over the run directory and GMT/; git grep for dor_ims_sua and the four proposed names over all 541 refs (no match)`
- `lake env lean /tmp/sua-decomp/Children.lean; /tmp/sua-decomp/final/Challenges.lean; /tmp/sua-decomp/final/FinalProofs.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-smooth-49478a38c9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-smooth-49478a38c9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/TietzeExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Tietze.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Multilinear/Basis.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Multilinear/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/tmp/sua-decomp/Probe1.lean`
- `/tmp/sua-decomp/Children.lean`
- `/tmp/sua-decomp/final/statements.json`
- `/tmp/sua-decomp/final/Challenges.lean`
- `/tmp/sua-decomp/final/FinalProofs.lean`

Snapshot: project b4d606d, mathlib 25730c7c. SimonGMT Chapter06 provides covectorEuclideanNorm, defined as √(∑_I [StrictMono I] α(e_I)²), together with covectorEuclideanNorm_zero, _nonneg and _neg. Chapter06/Forms.lean provides Covector, DifferentialForm and IsTestForm (= ContDiff ℝ ∞ ∧ HasCompactSupport).

Missing locally:
- No FiniteDimensional instance for Covector (Euclid P) n (synthesis fails).
- No continuity, homogeneity or integral lemmas for covectorEuclideanNorm.
- No smooth unit approximation lemma.
Therefore finite-dimensionality and the coefficient-map representation become children.

Available in Mathlib and used by the child proofs:
- Tietze: ContinuousMap.exists_restrict_eq with RCLike.instTietzeExtensionTVS (Analysis/Complex/Tietze.lean, needs FiniteDimensional).
- Linear algebra: Module.Basis.ext_alternating, ContinuousAlternatingMap.toAlternatingMap_injective, FiniteDimensional.of_injective, ContinuousAlternatingMap.apply, ContinuousLinearMap.pi, EuclideanSpace.equiv and EuclideanSpace.norm_eq.
- Thickenings: IsCompact.exists_cthickening_subset_open, mem_thickening_iff(_infDist_lt), closure_thickening_subset_cthickening, cthickening_mono and IsCompact.cthickening.
- Bump functions: ContDiffBump.normed with nonneg_normed, integral_normed, support_normed_eq, hasCompactSupport_normed, contDiff_normed, continuous_normed, integrable_normed and dist_normed_convolution_le.
- Convolution and integration: HasCompactSupport.contDiff_convolution_left, HasCompactSupport.convolution, support_convolution_subset, HasCompactSupport.convolutionExists_left, convolution_def, ContinuousLinearMap.integral_comp_comm and HasCompactSupport.uniformContinuous_of_continuous.
These live in modules that the contract does not import, so child proofs must import them in Submission.lean. The statements need only the contract imports.

Names: no dor_ims_sua* name occurs in dag.json, the run directory, GMT/ or any of the 541 git refs. No accepted declaration has an identical type, so nothing is reused.

Lean checks:
- The four exact child types elaborate after `import GMT.Ch07.Submission` in the replayed contract scope.
- Full proofs of all four children, and of the frozen parent from children 3 and 4, compile.
- #print axioms shows only propext, Classical.choice and Quot.sound.
