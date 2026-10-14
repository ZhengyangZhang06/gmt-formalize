# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1`
- Child DAG node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 5, proof of Corollary 7.3 (chapter-05.txt lines 1388–1395: Ṽ = v(M, N^{−1}θ)⌞B_ρ(ξ) has density ≥ 1, with density 1 at x₀). This is in the form of steps 4–5 of the parent proof: minimality of the reduced current via the competitor T + N₀(S₀ − T₀), and the transfer T = N₀m[[M']].

Notation:
- B := B_r(z₀), which is open with B ⊆ U; μ := R.measure = θH^n⌞M.
- For ω ∈ 𝒟^n(B), ι(ω) ∈ 𝒟^n(U) is the same form regarded in U (spt ω ⊆ B ⊆ U). Every ω ∈ 𝒟^n(U) with spt ω ⊆ B is ι of a unique form in 𝒟^n(B).
- Since θ ≥ 1 on M, μ-null and H^n⌞M-null sets coincide, so the hypothesis gives θ = N₀ H^n-a.e. on M ∩ B.

1. Definition. Put T₀(ω) := N₀^{−1}T(ι(ω)) for ω ∈ 𝒟^n(B). T₀ is linear. It is sequentially continuous, because ω_j → 0 in 𝒟^n(B) implies ι(ω_j) → 0 in 𝒟^n(U) (same compact support set ⊆ B ⊆ U, same derivatives). So T₀ ∈ 𝒟_n(B), and T(ι(ω)) = N₀T₀(ω).

2. Integer multiplicity. R₀ := (M ∩ B, 1, ξ) is an IMRep in B:
- M ∩ B is Borel, ⊆ B, and countably n-rectifiable (a subset of M).
- The multiplicity 1 is Borel and positive.
- For compact K ⊆ B, ∫_{M∩B∩K} 1 dH^n ≤ ∫_{M∩K} θ dH^n < ∞.
- ξ is H^n⌞(M ∩ B)-measurable.
- For H^n-a.e. x ∈ M ∩ B, T_xM =: Q exists with ξ(x) orienting Q, and T_x(M ∩ B) = Q because B is open: if spt f ⊆ B̄_R(0) and ρR < dist(x, ℝ^P ∖ B), then η_{x,ρ}(M ∩ B) and η_{x,ρ}(M) coincide on B̄_R(0), so the integrals in Definition 1.4 agree for small ρ.
For ω ∈ 𝒟^n(B) we have ω = 0 off B, so T₀(ω) = N₀^{−1}∫_M θ⟨ω, ξ⟩ dH^n = N₀^{−1}∫_{M∩B} N₀⟨ω, ξ⟩ dH^n = ∫_{M∩B} 1·⟨ω, ξ⟩ dH^n. Thus R₀ represents T₀.

3. Boundary. If n = 0, BoundaryVanishes T₀ holds by definition. If n ≥ 1 and ω ∈ 𝒟^{n−1}(B), then ∂T₀(ω) = T₀(dω) = N₀^{−1}T(d ι(ω)) = N₀^{−1}∂T(ι(ω)) = 0.

4. Supports.
(a) spt T₀ ⊆ spt T. Let y ∈ B ∖ spt T. Then y ∈ W for an open W with W̄ compact ⊆ U on which T vanishes. Choose s > 0 with B̄_s(y) ⊆ B and put W' := W ∩ B_s(y). W' is open, W̄' ⊆ B̄_s(y) ⊆ B is compact, and T₀(ω) = N₀^{−1}T(ι(ω)) = 0 whenever spt ω ⊆ W'. So y ∉ spt T₀. Hence spt T₀ ⊆ spt T ⊆ N.
(b) z₀ ∈ spt T₀. Otherwise z₀ ∈ W' for an open W' with W̄' compact ⊆ B on which T₀ vanishes. Then W̄' ⊆ U, and every ω ∈ 𝒟^n(U) with spt ω ⊆ W' is ι(ω'), so T(ω) = N₀T₀(ω') = 0. Thus z₀ ∉ spt T, contrary to hypothesis.

5. Masses. For W ⊆ B, ι is a bijection from the forms admissible for M_W(T₀) (in 𝒟^n(B), spt ⊆ W, |ω| ≤ 1) onto those admissible for M_W(T), and T(ι(ω)) = N₀T₀(ω). Hence M_W(T) = N₀M_W(T₀).
(a) Local mass bound. If W is open with W̄ compact ⊆ B, the sibling mass_eq_weight (Submission.rsd_massOn_eq_measure, W open ⊆ U) gives M_W(T₀) = N₀^{−1}μ(W) ≤ N₀^{−1}∫_{M∩W̄} θ dH^n < ∞.
(b) Density. For 0 < ρ ≤ r, B_ρ(z₀) ⊆ B, so M_{B_ρ(z₀)}(T₀)/(ω_nρ^n) = N₀^{−1}·M_{B_ρ(z₀)}(T)/(ω_nρ^n) → N₀^{−1}·N₀ = 1 by HasMassDensity T z₀ N₀. Hence HasMassDensity T₀ z₀ 1.

6. Minimality. T₀ is integer multiplicity (step 2). Let W be open with W̄ compact ⊆ B. Let S₀ ∈ 𝒟_n(B) be integer multiplicity with ∂S₀ = ∂T₀ (if n ≥ 1), such that K := spt(S₀ − T₀) is compact and K ⊆ (B ∩ N) ∩ W. Put X := S₀ − T₀.
(a) X is integer multiplicity in B by the sibling integer_combination (Submission.rsd_isIntegerMultiplicity_int_combination, with p₁ = 1, p₂ = −1). Let R_X = (M_X, θ_X, ξ_X) represent X, and μ_X := R_X.measure.
(b) The carrier of X lies in K up to a null set. Each y ∈ B ∖ K lies in B ∖ spt X, so the sibling support_iff_weight_pos (Submission.rsd_mem_support_iff_measure_ball_pos, applied to X and R_X in B) gives r_y > 0 with μ_X(B_{r_y}(y)) = 0. These balls cover B ∖ K, hence countably many of them do (ℝ^P is second countable), so μ_X(B ∖ K) = 0. As θ_X ≥ 1 on M_X, H^n(M_X ∖ K) = 0.
(c) Extension by zero. R'_X := (M_X ∩ K, θ_X, ξ_X) is an IMRep in U:
- M_X ∩ K is Borel (K is compact), ⊆ K ⊆ U, and countably n-rectifiable.
- ∫_{M_X∩K∩K''} θ_X dH^n ≤ ∫_{M_X∩K} θ_X dH^n < ∞, since K is a compact subset of B.
- ξ_X is measurable.
- H^n(M_X ∖ (M_X ∩ K)) = 0 and H^n(η_{x,ρ}(Z)) = ρ^{−n}H^n(Z), so the integrals in Definition 1.4 for M_X ∩ K and M_X coincide. Hence T_x(M_X ∩ K) = T_xM_X wherever the latter exists.
Define E(ω) := ∫_{M_X∩K} θ_X⟨ω, ξ_X⟩ dH^n for ω ∈ 𝒟^n(U). E is linear, and |E(ω)| ≤ sup_x ‖ω(x)‖·∫_{M_X∩K} θ_X dH^n, because |⟨α, ξ_X⟩| ≤ ‖α‖ H^n-a.e. (ξ_X is a unit simple n-vector a.e.). So E is sequentially continuous, E ∈ 𝒟_n(U), and E is integer multiplicity, represented by R'_X. Moreover:
(i) E(ι(ω)) = ∫_{M_X} θ_X⟨ω, ξ_X⟩ dH^n = X(ω) for ω ∈ 𝒟^n(B), by (b);
(ii) E(ω) = 0 whenever ω = 0 on K, in particular whenever spt ω ∩ K = ∅.
(d) The competitor. S(ω) := T(ω) + N₀E(ω) defines S ∈ 𝒟_n(U). S is integer multiplicity by integer_combination (p₁ = 1, p₂ = N₀), and (S − T)(ω) = N₀E(ω).
(e) ∂S = ∂T (if n ≥ 1). Let ω ∈ 𝒟^{n−1}(U), and choose φ ∈ C_c^∞(ℝ^P) with spt φ ⊆ B and φ = 1 on an open V ⊇ K. Then φω ∈ 𝒟^{n−1}(B), and dω − d(φω) = d((1 − φ)ω) vanishes on V ⊇ K. By (c)(ii) and then (c)(i), E(dω) = E(d(φω)) = X(d(φω)) = ∂S₀(φω) − ∂T₀(φω) = 0. Hence ∂S(ω) = ∂T(ω) + N₀E(dω) = ∂T(ω).
(f) Support of S − T. For y ∈ U ∖ K choose s > 0 with B̄_s(y) ⊆ U ∖ K (K is closed, U is open). By (c)(ii), S − T vanishes on all forms supported in B_{s/2}(y), whose closure is compact and contained in U, so y ∉ spt(S − T). Thus spt(S − T) ⊆ K. Being relatively closed in U and contained in the compact K ⊆ U, spt(S − T) is compact. Also spt(S − T) ⊆ K ⊆ (B ∩ N) ∩ W ⊆ (U ∩ N) ∩ W.
(g) Comparison. W is open and W̄ is a compact subset of B ⊆ U. By (d)–(f), S is an admissible competitor in the definition of 'T minimizing in U ∩ N', so M_W(T) ≤ M_W(S). For ω admissible for M_W(S) (spt ω ⊆ W ⊆ B), write ω = ι(ω'); then S(ω) = T(ι(ω')) + N₀E(ι(ω')) = N₀T₀(ω') + N₀X(ω') = N₀S₀(ω'). With the bijection of step 5, M_W(S) = N₀M_W(S₀) and M_W(T) = N₀M_W(T₀). Dividing by N₀ ∈ (0, ∞) gives M_W(T₀) ≤ M_W(S₀). Hence T₀ is minimizing in B ∩ N.

7. Regularity transfer. Suppose z₀ ∈ reg T₀. Then there are ρ' > 0 with B_{ρ'}(z₀) ⊆ B, m ∈ ℤ ∖ {0}, and an embedded C¹ n-submanifold M' ∋ z₀ with continuous orientation ξ' and H^n(M' ∩ K) < ∞ for compact K ⊆ B_{ρ'}(z₀), such that T₀(ω) = m∫_{M'}⟨ω, ξ'⟩ dH^n whenever spt ω ⊆ B_{ρ'}(z₀). Then B_{ρ'}(z₀) ⊆ U and N₀m ∈ ℤ ∖ {0}. Every ω ∈ 𝒟^n(U) with spt ω ⊆ B_{ρ'}(z₀) is ι(ω'), with T(ω) = N₀T₀(ω') = N₀m∫_{M'}⟨ω, ξ'⟩ dH^n. Since z₀ ∈ spt T, the same ρ', M', ξ' and the multiplicity N₀m witness z₀ ∈ reg T.

8. Conclusion. By steps 2–7, T₀ has every asserted property.

## Key steps

1. T₀ := N₀⁻¹·T on B_r(z₀) is represented by (M ∩ B, 1, ξ), and ∂T₀ = 0.
2. spt T₀ ⊆ spt T and z₀ ∈ spt T₀; M_W(T) = N₀M_W(T₀), giving the local mass bound (mass_eq_weight) and density 1 at z₀.
3. Competitor T + N₀E, where E is the zero extension of S₀ − T₀ (carrier in K by support_iff_weight_pos): integer multiplicity (integer_combination), same boundary, compact difference support in (U ∩ N) ∩ W, hence M_W(T₀) ≤ M_W(S₀).
4. T₀ = m[[M']] near z₀ gives T = N₀m[[M']], so z₀ ∈ reg T.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'IMRep|IsIntegerMultiplicity|regularSet|HasMassDensity' local-references/123e8435b4a2469b/project -t lean -c`
- `rg -n 'IMRep|IsIntegerMultiplicity|^def |^theorem |^structure ' local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `grep -n '^def \|^theorem \|^structure ' simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,Representation}.lean simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n '^theorem [a-zA-Z_.]*(density|Density|ball|Ball)' simongmt/Poincare/SimonGMT/Chapter01 Chapter03 Chapter04`
- `grep -n 'ae_tendsto_rnDeriv\|ae_tendsto_measure_inter_div\|ae_tendsto_average' -r local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/`
- `grep -n 'μHE\[' local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -rl 'rsd_' runs/20261011T150044Z-ba604216b4; grep -rn 'rsd_massOn_eq_measure|...|rsd_constant_multiplicity_reduction' GMT .humanize`
- `lake env lean /tmp/rsd-a1-check/Test/Children.lean (five child types in the comparator's replayed Contract scope)`
- `lake env lean /tmp/rsd-a1-check/Test/Assembly.lean (RegularSetDense from children 1,2,3,5 + DensityAndTangentCones + DensityOneImpliesRegular; #print axioms)`
- `lake env lean /tmp/rsd-a1-check/Test/Axioms.lean; lake env lean /tmp/rsd-a1-review/Child5Literal.lean; lake env lean /tmp/rsd-a1-review/CompetitorSupport.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Representation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/rsd-a1-check/Test/Children.lean`
- `/tmp/rsd-a1-check/Test/Assembly.lean`
- `/tmp/rsd-a1-check/Test/Axioms.lean`
- `/tmp/rsd-a1-review/Child5Literal.lean`
- `/tmp/rsd-a1-review/CompetitorSupport.lean`

The snapshot's Ch07 contract (project b4d606d, Mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean.

No match for the structural facts the parent proof cites:
- GMT/Ch06/Contract.lean has its own unproved integer-multiplicity notions; they have different types and live in a separate module that Ch07 does not import.
- The simongmt Chapter06 files provide massOn, support/zeroRegion and restrictDomain, but no mass = weight, density = multiplicity, spt T = spt mu_T, or integer-combination lemma for IMRep.
- Representation.lean leaves the mass-representation bridge pending.

Reusable tools, each checked to depend only on propext, Classical.choice and Quot.sound:
- Chapter06: GeometricCurrentOn.le_massOn, massOn_mono, support_subset_domain.
- Chapter03: HasApproximateTangentSpaceAt.unique, CountablyRectifiable.mono, countablyRectifiable_iUnion.
- Chapter01: ae_dimensionalUpperDensity_eq_zero_outside (Simon 1.3.6, stated for simonHausdorffMeasureReal).
- Mathlib: Besicovitch.ae_tendsto_rnDeriv and ae_tendsto_measure_inter_div_of_measurableSet.
- Mathlib muHE scaling and isometry lemmas (euclideanHausdorffMeasure_homothety_image, Isometry.euclideanHausdorffMeasure_image); these two were located by grep but their axioms were not printed.

The five child types elaborate in the comparator's replayed scope. The conditional assembly of RegularSetDense from children 1, 2, 3 and 5 plus DensityAndTangentCones and DensityOneImpliesRegular depends only on propext, Classical.choice and Quot.sound. No rsd_ name occurs in the run directory or workspace, so the proposed names do not collide.
