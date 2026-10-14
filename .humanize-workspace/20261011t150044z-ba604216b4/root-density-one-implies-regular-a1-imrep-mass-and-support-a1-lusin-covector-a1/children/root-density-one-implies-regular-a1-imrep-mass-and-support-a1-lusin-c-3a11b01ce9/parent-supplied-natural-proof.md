# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.lusin_covector-a1`
- Child DAG node: `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.lusin_covector-a1.lusin_measurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–5 of the parent proof, which is the standard proof of Lusin's theorem (Simon Ch. 1, 1.17) in the compact form used by the parent. Here they are applied directly to a measurable map g, so the parent's measurable-modification step 1 is not needed (take A₀ = A). The target Λ is replaced by an arbitrary second-countable space Y, because steps 2–5 use only a countable basis of the target and the measurability of preimages of open sets. The error budget ε·2^{−k−2} is replaced by summable positive weights η_k, which also covers ε = ∞.
Hypotheses: P ∈ ℕ. Y is a second-countable topological space with a σ-algebra in which every open set is measurable. μ is any measure on ℝ^P (Borel σ-algebra). A ⊆ ℝ^P is measurable with μ(A) < ∞. g : ℝ^P → Y is measurable. ε ∈ [0, ∞] with ε ≠ 0.
1. (Inner regularity inside A.) Let ν := μ.restrict A, so ν(B) = μ(B ∩ A) for measurable B.
 ν is a finite Borel measure on ℝ^P, since ν(ℝ^P) = μ(A) < ∞. A finite measure is locally finite, and ℝ^P is a σ-compact (indeed proper) metric space, so ν is regular (Mathlib instance Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure). Hence ν is inner regular by compact sets on measurable sets of finite measure (InnerRegularCompactLTTop). (Alternatively, Ulam's theorem: finite Borel measures on the Polish space ℝ^P are tight.)
 Consequently (MeasurableSet.exists_isCompact_sdiff_lt), for every measurable B ⊆ A and every η ∈ (0, ∞] there is a compact C ⊆ B with ν(B ∖ C) < η. C is compact in a Hausdorff space, hence closed and measurable. So B ∖ C is measurable and contained in A, and ν(B ∖ C) = μ((B ∖ C) ∩ A) = μ(B ∖ C). Thus μ(B ∖ C) < η.
2. (Countable basis.) Since Y is second countable, fix a countable basis 𝓑 of its topology. Y is nonempty (it contains g(0)) and ⋃𝓑 = Y, so 𝓑 is nonempty. Enumerate it as 𝓑 = {O_k : k ∈ ℕ}, with repetitions allowed. Each O_k is open, hence measurable in Y. Since g is measurable, S_k := g^{−1}(O_k) is a measurable subset of ℝ^P.
3. (Weights.) Choose η_k ∈ (0, ∞) for k ∈ ℕ with Σ_k η_k < ε. For example, put δ := min(ε, 1) ∈ (0, 1] and η_k := δ·2^{−k−2}; then Σ_k η_k = δ/2 < δ ≤ ε. (In Mathlib: ENNReal.exists_pos_sum_of_countable'.)
4. (Compact pieces.) Fix k. The sets A ∩ S_k and A ∖ S_k are measurable subsets of A. By step 1 with η = η_k/2 > 0, choose compact sets C_k ⊆ A ∩ S_k and D_k ⊆ A ∖ S_k with
 μ((A ∩ S_k) ∖ C_k) < η_k/2 and μ((A ∖ S_k) ∖ D_k) < η_k/2.
 Put E_k := C_k ∪ D_k, a compact subset of A. Let x ∈ A ∖ E_k. If g(x) ∈ O_k, then x ∈ (A ∩ S_k) ∖ C_k; otherwise x ∈ (A ∖ S_k) ∖ D_k. Hence A ∖ E_k ⊆ ((A ∩ S_k) ∖ C_k) ∪ ((A ∖ S_k) ∖ D_k), and subadditivity gives μ(A ∖ E_k) < η_k/2 + η_k/2 = η_k.
5. (The compact set.) Let K := ⋂_k E_k.
 Each E_k is compact in the Hausdorff space ℝ^P, hence closed, so K is closed. K lies in the compact set E_0, so K is compact, being a closed subset of a compact set. Also K ⊆ E_0 ⊆ A.
 Since A ∖ K = ⋃_k (A ∖ E_k), countable subadditivity and steps 3–4 give μ(A ∖ K) ≤ Σ_k μ(A ∖ E_k) ≤ Σ_k η_k < ε.
6. (Continuity.) Fix k and x ∈ K, so x ∈ E_k = C_k ∪ D_k.
 - If x ∉ D_k, then x ∈ C_k ⊆ A ∩ S_k, so g(x) ∈ O_k.
 - If g(x) ∈ O_k, then x ∈ S_k, so x ∉ D_k because D_k ⊆ A ∖ S_k.
 Hence K ∩ g^{−1}(O_k) = K ∩ (ℝ^P ∖ D_k). D_k is compact, hence closed, so ℝ^P ∖ D_k is open. Therefore the preimage of O_k under the restriction g|_K : K → Y is open in the subspace topology of K.
 Every open subset of Y is a union of sets O_k, so its preimage under g|_K is a union of open subsets of K, hence open (IsTopologicalBasis.continuous_iff). Therefore g|_K is continuous, i.e. ContinuousOn g K (continuousOn_iff_continuous_restrict).
 Together with step 5, K is a compact subset of A with μ(A ∖ K) < ε on which g is continuous. ∎

## Key steps

1. ν = μ.restrict A is finite, so it is regular on ℝ^P (a σ-compact metric space) and hence InnerRegularCompactLTTop. So each measurable B ⊆ A contains a compact C with μ(B ∖ C) = ν(B ∖ C) < η.
2. Enumerate a countable basis (O_k)_{k∈ℕ} of Y; it is nonempty because g(0) ∈ Y. Each S_k = g⁻¹(O_k) is measurable.
3. Choose positive weights η_k with Σ η_k < ε, e.g. min(ε,1)·2^{−k−2}.
4. Choose compact C_k ⊆ A ∩ S_k and D_k ⊆ A ∖ S_k with defects < η_k/2. Then E_k = C_k ∪ D_k ⊆ A has μ(A ∖ E_k) < η_k.
5. K = ⋂_k E_k is closed inside the compact E_0, hence compact. K ⊆ A and μ(A ∖ K) ≤ Σ_k μ(A ∖ E_k) < ε.
6. For x ∈ K, g(x) ∈ O_k ⇔ x ∉ D_k. So (g|_K)⁻¹(O_k) = K ∩ D_kᶜ is open in K, and by the basis criterion g is continuous on K.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; cmp snapshot project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD`
- `grep -rn -i lusin <snapshot>/mathlib/Mathlib/{MeasureTheory,Topology,Analysis}`
- `grep -n 'theorem|lemma|instance' MeasureTheory/Measure/RegularityCompacts.lean; grep -n 'exists_isCompact_sdiff_lt|exists_isCompact_lt_add|exists_isCompact_isClosed_sdiff_lt|InnerRegularCompactLTTop' MeasureTheory/Measure/Regular.lean`
- `grep -rln 'ContinuousAlternatingMap|ContinuousMultilinearMap' <snapshot>/mathlib/Mathlib | xargs grep -ln 'FiniteDimensional|Module.Finite|SecondCountableTopology|SeparableSpace'`
- `grep -n of_injective LinearAlgebra/FiniteDimensional/Defs.lean; grep -n 'secondCountable_of_proper|proper_real' Topology/MetricSpace/ProperSpace.lean Analysis/Normed/Module/FiniteDimension.lean`
- `grep -rn 'SecondCountableTopology|FiniteDimensional|SeparableSpace' simongmt/Poincare/SimonGMT/Chapter06/; grep -n 'abbrev Covector' Chapter06/Forms.lean`
- `python3 -I scan of dag.json nodes: lean_name set, 'lusin', 'SecondCountableTopology', 'FiniteDimensional ℝ (Covector', status of dor_ims_sua_covector_finiteDimensional / imsupp_covector_finiteDimensional`
- `verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') and child_modules shape`
- `grep -n -i lusin book/chapter-01.txt; sed -n 300,400p book/chapter-01.txt (Simon 1.17)`
- `lake env lean /tmp/lusin-decomp/{Probe,Probe2,Assembly,C1,C2}.lean and /tmp/lusin-decomp/final/Final.lean (#synth probes, #print axioms)`
- `web (standard): Lusin's theorem second-countable topological space measurable function compact set continuous restriction proof countable basis`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-lusin-covector-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-support-eq-measure-sup-8f5d9ea2e2/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/lusin-decomp/final/Final.lean`

Snapshot: project b4d606d, mathlib 25730c7c. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical.

Not available in the Submission scope (#synth / fail_if_success):
- Lusin's continuity theorem. Mathlib has only Lusin–Souslin and Lusin separation (Constructions/Polish/Basic.lean), which justifies child lusin_measurable.
- FiniteDimensional, SecondCountableTopology, ProperSpace and MeasurableSpace instances on Covector (Euclid P) n = E [⋀^Fin n]→L[ℝ] ℝ. No Mathlib file links continuous alternating or multilinear maps to finite-dimensionality, which justifies child covector_finite_dimensional.
- RegularityCompacts.lean is not imported, so an arbitrary μ is not InnerRegularCompactLTTop.

Available:
- μ.restrict A with μ A ≠ ∞ is IsFiniteMeasure, hence Regular (Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure), hence InnerRegularCompactLTTop. MeasurableSet.exists_isCompact_sdiff_lt then gives the compact approximations.
- ENNReal.exists_pos_sum_of_countable', TopologicalSpace.exists_countable_basis, IsTopologicalBasis.continuous_iff, continuousOn_iff_continuous_domRestrict.
- FiniteDimensional.of_injective, Module.Basis.ext_alternating, ContinuousAlternatingMap.toAlternatingMap_injective; FiniteDimensional.proper_real then secondCountable_of_proper.

DAG and naming:
- The same FiniteDimensional type is reserved as dor_ims_sua_covector_finiteDimensional (decomposing) and imsupp_covector_finiteDimensional (comparing). Neither is accepted, so the unique name dor_ims_lusin_covector_finiteDimensional is used.
- Neither proposed name occurs in dag.json, GMT/, simongmt or the run directory.
- The comparator child scope is the 7 replayed commands (open…, namespace GMT.Ch07, opens, noncomputable section, end).

Lean checks (/tmp/lusin-decomp/final/Final.lean):
- Both children are fully proved.
- The parent is assembled only from the two children.
- Comparator-shaped targets close by `exact Submission.X`.
- All axioms are [propext, Classical.choice, Quot.sound].
- An independent reviewer reproduced these results.

Sources: Simon 1.17 (book/chapter-01.txt lines 344–380) prints a level-set proof for a real-valued target and a closed C. The parent's countable-basis proof matches the second-countable form in https://math.univ-lyon1.fr/~santambrogio/Lusin.pdf and https://arxiv.org/pdf/math/0406370.
