# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1`
- Child DAG node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1.cylinder_grouping-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 6–8 of the parent proof: (b) disjointness, (c) inclusion into the enlarged cylinders about cluster representatives, and (d) grouping and rescaling. Here d/2 plays the role of τ̃, ρ and S are as in the parent, and u replaces aδ².
Notation. p := Grassmannian.project P and q(v) := v − p(v). For w ∈ ℝ^N, A(w) := U^{d/2}_ρ(w) = closedBall w ρ ∩ {z : ‖q(z − w)‖ < d/2} and B(w) := U^{d/2+S}_{ρ+S}(w) = closedBall w (ρ + S) ∩ {z : ‖q(z − w)‖ < d/2 + S}. Inequalities between measures are in [0,∞], real coefficients enter through ENNReal.ofReal, and r^n means ofReal(r)^n.

0. Facts on p.
 – By definition, Grassmannian.project P v = (Grassmannian.projectionLinearMap P) v, so p is linear. Hence p(a − b) = p(a) − p(b), and q(a − b) = (a − p a) − (b − p b) = q(a) − q(b).
 – p is a linear map on the finite-dimensional space ℝ^N, so it is continuous (LinearMap.continuous_of_finiteDimensional).
 – (F4) For y, y' ∈ s: p(y − y') = p(y) − p(y') = x − x = 0, so q(y − y') = y − y'.
 – u ≥ 0. Otherwise uρ < 0 ≤ S ≤ uρ, since ρ > 0.

1. Representatives. For each y ∈ s choose r(y) ∈ Z with ‖y − r(y)‖ ≤ S, and extend r arbitrarily outside s. Then r maps s into Z, and r(y) ∈ s because Z ⊆ s.

2. Measurability. A(y) is the intersection of the closed set closedBall y ρ with {z : ‖(z − y) − p(z − y)‖ < d/2}. The latter set is open, because z ↦ ‖(z − y) − p(z − y)‖ is continuous. So every A(y) is Borel.

3. Disjointness. For distinct y, y' ∈ s, A(y) ∩ A(y') = ∅. Suppose z lies in both. By (F4) and linearity of q,
 y − y' = q(y − y') = q((z − y') − (z − y)) = q(z − y') − q(z − y).
 Hence ‖y − y'‖ ≤ ‖q(z − y')‖ + ‖q(z − y)‖ < d/2 + d/2 = d ≤ ‖y − y'‖, a contradiction.

4. Inclusion. For y ∈ s, A(y) ⊆ B(r(y)). Let z ∈ A(y).
 – Ball: ‖z − r(y)‖ ≤ ‖z − y‖ + ‖y − r(y)‖ ≤ ρ + S.
 – Cylinder: y and r(y) both lie in s. So (F4) and linearity give q(z − r(y)) = q(z − y) + q(y − r(y)) = q(z − y) + (y − r(y)). Hence ‖q(z − r(y))‖ ≤ ‖q(z − y)‖ + ‖y − r(y)‖ < d/2 + S.

5. Grouping. For w ∈ Z let s_w := {y ∈ s : r(y) = w}. By steps 2 and 3, the sets A(y), y ∈ s_w, are pairwise disjoint Borel sets. So Σ_{y∈s_w} μ(A(y)) = μ(⋃_{y∈s_w} A(y)) (measure_biUnion_finset). By step 4 this union lies in B(w), so Σ_{y∈s_w} μ(A(y)) ≤ μ(B(w)).
 Since r maps s into Z, Σ_{y∈s} g(y) = Σ_{w∈Z} Σ_{y∈s_w} g(y) for every g (Finset.sum_fiberwise_of_maps_to). In [0,∞], (Σ_i f_i)/c = Σ_i f_i/c (ENNReal.sum_div), and division by a fixed c is monotone. Therefore
 Σ_{y∈s} μ(A(y))/ρ^n = Σ_{w∈Z} (Σ_{y∈s_w} μ(A(y)))/ρ^n ≤ Σ_{w∈Z} μ(B(w))/ρ^n.

6. (F1) For k ∈ ℕ, (1 + u)^k ≤ 1 + (2^k − 1)u, using 0 ≤ u ≤ 1. Induct on k. For k = 0 both sides equal 1. If it holds for k, then (1 + u)^{k+1} ≤ (1 + (2^k − 1)u)(1 + u) = 1 + 2^k·u + (2^k − 1)u² ≤ 1 + (2^{k+1} − 1)u. This uses 1 + u ≥ 0, u² ≤ u and 2^k ≥ 1.

7. Rescaling. Put k := 1 + (2^n − 1)u. Then k ≥ 1, since 2^n ≥ 1 and u ≥ 0. As 0 < ρ ≤ ρ + S ≤ ρ + uρ = (1 + u)ρ,
 (ρ + S)^n ≤ ((1 + u)ρ)^n = (1 + u)^n·ρ^n ≤ k·ρ^n,
 by monotonicity of t ↦ t^n on [0,∞) and (F1).
 In [0,∞] put a := ofReal(ρ)^n = ofReal(ρ^n), b := ofReal(ρ + S)^n = ofReal((ρ + S)^n) and κ := ofReal(k). Then κ ≠ 0 and κ ≠ ∞. The real inequality gives b ≤ ofReal(k·ρ^n) = κ·a (ENNReal.ofReal_pow, ENNReal.ofReal_mul with k ≥ 0, ENNReal.ofReal_le_ofReal). Hence for every X ∈ [0,∞], including X = ∞:
 X/a = (κ·X)/(κ·a) ≤ (κ·X)/b = κ·(X/b).
 The equality is ENNReal.mul_div_mul_left, the inequality ENNReal.div_le_div_left, and the last step mul_div_assoc.

8. Conclusion. By steps 5 and 7 and Finset.mul_sum:
 Σ_{y∈s} μ(A(y))/ρ^n ≤ Σ_{w∈Z} μ(B(w))/ρ^n ≤ Σ_{w∈Z} κ·(μ(B(w))/(ρ + S)^n) = κ·Σ_{w∈Z} μ(B(w))/(ρ + S)^n.
 This is the claim, because κ = ofReal(1 + (2^n − 1)u). ∎

## Key steps

1. p = Grassmannian.project P is linear and continuous; for y, y' ∈ s, (y − y') − p(y − y') = y − y'; u ≥ 0 from 0 ≤ S ≤ uρ, ρ > 0
2. choose representatives r(y) ∈ Z ⊆ s with ‖y − r(y)‖ ≤ S
3. A(y) := U^{d/2}_ρ(y) is Borel, and A(y) ∩ A(y') = ∅ for distinct y, y' ∈ s since ‖y − y'‖ ≤ ‖q(z − y')‖ + ‖q(z − y)‖ < d
4. A(y) ⊆ U^{d/2+S}_{ρ+S}(r(y)) by the triangle inequality and q(z − r(y)) = q(z − y) + (y − r(y))
5. fibrewise grouping (Finset.sum_fiberwise_of_maps_to, measure_biUnion_finset, ENNReal.sum_div): Σ_{y∈s} μ(A(y))/ρ^n ≤ Σ_{z∈Z} μ(U^{d/2+S}_{ρ+S}(z))/ρ^n
6. (1 + u)^k ≤ 1 + (2^k − 1)u, so (ρ + S)^n ≤ (1 + (2^n − 1)u)ρ^n and X/ρ^n ≤ ofReal(1 + (2^n − 1)u)·X/(ρ + S)^n for all X ∈ [0,∞]

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum of snapshot project/GMT/Ch08/Contract.lean, workspace GMT/Ch08/Contract.lean and GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'theorem (one_add_pow_le|pow_le_one_add|one_add_mul_le_pow|add_pow_le_pow_mul_pow_of_sq_le_sq|one_add_pow_le_pow_one_add|pow_le_pow_of_le_one|sub_one_le_pow)' mathlib/Mathlib ; rg -n '\(1 \+ [a-z]\) \^ [a-z] ≤ 1 \+' mathlib/Mathlib`
- `rg -n 'theorem exp_bound_div_one_sub_of_interval|theorem add_one_le_exp|theorem exp_le_one_add|theorem one_sub_le_exp_neg|theorem exp_bound' mathlib/Mathlib`
- `rg -n 'offDiag.*Nonempty|Nonempty.*offDiag|offDiag_nonempty' mathlib/Mathlib ; rg -n 'theorem one_lt_card' mathlib/Mathlib/Data/Finset/Card.lean ; rg -n 'theorem mem_offDiag' mathlib/Mathlib/Data/Finset/Prod.lean`
- `rg/grep for prod_fiberwise_of_maps_to, measure_biUnion_finset, ENNReal sum_div / mul_div_mul_left / div_le_div_left / mul_div_right_comm / ofReal_div_of_pos, LinearMap.continuous_of_finiteDimensional, one_le_pow₀ / pow_le_pow_left₀ / pow_le_pow_right₀ in mathlib/Mathlib`
- `#check from import GMT.Ch08.Submission (/tmp/ccb-decomp-v1/Probe.lean, Probe2.lean): Grassmannian.project, Finset.sum_fiberwise_of_maps_to, measure_biUnion_finset, Finset.exists_min_image, one_add_mul_le_pow, ENNReal.sum_div, ENNReal.mul_div_mul_left, ENNReal.div_le_div_left, ENNReal.mul_div_right_comm, ENNReal.ofReal_div_of_pos, Real.exp_bound_div_one_sub_of_interval, LinearMap.continuous_of_finiteDimensional, Finset.one_lt_card_iff_nontrivial (Finset.offDiag_nonempty: unknown constant); example proofs of linearity (simp [Grassmannian.project, map_sub]) and continuity (projectionLinearMap.continuous_of_finiteDimensional) of Grassmannian.project`
- `grep -n 'theorem|def|abbrev' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean (Euclidean, Grassmannian, projectionLinearMap, project, project_project; no norm-contraction lemma for v − project v)`
- `python3 -I /tmp/ccb-decomp-v1/scripts/gen.py (verifier lean_contract.validate_lean_statement + gmt-compare.py layout/child_modules in contract mode on the four lean_statements)`
- `lake env lean /tmp/ccb-decomp-v1/compform/C{1,2,3,4}_Challenge.lean, /tmp/ccb-decomp-v1/assembly/Assembly.lean, Full.lean, FullAxiomComp.lean (with #print axioms)`
- `grep -c of intcpt_allard_ccb_* names in dag.json, grep -rl in the run directory, git grep over all 314 refs (0 hits)`
- `read nodes/root-integral-compactness-a1-allard-lemma-a1-weighted-radial-monotonicity-a1/decomposition-v1.json and decomposition-audit-v1.json (precedent: an uncle dependency is passed to a child as an explicit hypothesis)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Data/Set/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Data/Finset/Card.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Data/Finset/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/BigOperators.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-cylinder-cluster-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-weighted-radial-monotonicity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-weighted-radial-monotonicity-a1/decomposition-audit-v1.json`
- `/tmp/ccb-decomp-v1/compform/C1_Challenge.lean`
- `/tmp/ccb-decomp-v1/assembly/Assembly.lean`
- `/tmp/ccb-decomp-v1/assembly/Full.lean`
- `/tmp/ccb-decomp-v1/assembly/FullAxiomComp.lean`

Snapshot provenance:
- The snapshot is project 63436ae6 with Mathlib 25730c7c. Its Contract is byte-identical to the workspace Contract and Submission.

Projection facts:
- Grassmannian.project P is defined as the linear map Grassmannian.projectionLinearMap P (SimonGMT Chapter08/Varifold.lean:82,105). So q = id − p is linear, and p is continuous by LinearMap.continuous_of_finiteDimensional.
- No contraction lemma ‖v − p v‖ ≤ ‖v‖ exists, and none is needed: the fibre identity q(y − y') = y − y' for p(y) = p(y') = x suffices.

Lemmas absent from Mathlib, and what replaces them:
- There is no lemma (1+u)^n ≤ 1 + (2^n − 1)u. The only nearby result is the rpow Bernoulli bound at Analysis/Convex/SpecificFunctions/Basic.lean:166. (F1) is therefore proved inline by induction in the two children that use it.
- Finset.offDiag_nonempty does not exist; only Set.offDiag_nonempty exists (Data/Set/Prod.lean:559). Finset.one_lt_card (Data/Finset/Card.lean:747), Finset.mem_offDiag (Data/Finset/Prod.lean:266) and Finset.exists_min_image give the minimal distance instead.

Lemmas used:
- e^ε ≤ 1/(1 − ε) is Real.exp_bound_div_one_sub_of_interval (Analysis/Complex/Exponential.lean:617).
- Grouping: Finset.sum_fiberwise_of_maps_to (the additive form of prod_fiberwise_of_maps_to, Algebra/BigOperators/Group/Finset/Basic.lean:264) and measure_biUnion_finset (MeasureTheory/Measure/Basic.lean:150).
- Division in [0,∞]: ENNReal.sum_div (Basic/ENNReal/BigOperators.lean:143), and ENNReal.mul_div_mul_left, div_le_div_left, mul_div_right_comm and ofReal_div_of_pos (Basic/ENNReal/Inv.lean:264, 471, 194, 960).
- Powers: one_le_pow₀, pow_le_pow_right₀ and pow_le_pow_left₀ (Algebra/Order/GroupWithZero/Basic.lean:483, 500, 513).
- All of these were #checked from import GMT.Ch08.Submission.

Lean checks:
- All four child statements pass validate_lean_statement and elaborate in comparator form.
- The parent's frozen type is proved from sorried children with a sorry-free assembly.
- All four children are fully proved with axioms propext, Classical.choice, Quot.sound; the comparator-form exact targets are accepted.

Names:
- The four lean_names are unused in dag.json, in the run directory and in the git refs.
