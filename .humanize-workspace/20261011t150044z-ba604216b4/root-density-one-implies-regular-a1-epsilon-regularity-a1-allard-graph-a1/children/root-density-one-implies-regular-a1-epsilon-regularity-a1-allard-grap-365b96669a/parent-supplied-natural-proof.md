# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Part 6 (Simon Ch. 5, Lemma 3.1 and its proof; estimates 3.2–3.4) and the use made of them in Part 7, Steps 7–8 ((17'), (18'), (19')). Conventions: Lⁿ := volume on ℝⁿ (Lean Euclid n); B̆_ρ, B_ρ open/closed balls of ℝⁿ centred at 0 unless indicated; ω_n := Lⁿ(B̆₁) ∈ (0, ∞); for a Lipschitz function w, ∇w := the a.e. derivative (Lean fderiv ℝ w, a linear functional whose operator norm |∇w| is the Euclidean norm of the gradient), ∇w·∇ζ := Σ_i ∂_iw ∂_iζ (the Lean sum over EuclideanSpace.single i 1). A Lipschitz function on B̆_ρ belongs to W^{1,2}(B̆_ρ) and its weak gradient equals its a.e. gradient. "Harmonic on B̆_ρ" means C² (hence C^∞) with Δh = 0 there.

Part A (Harmonic approximation, Simon 3.1, normalized). Claim: for every ε' > 0 there is δ_A(n, ε') > 0 such that if B := B̆₁ and w ∈ W^{1,2}(B) satisfies ∫_B|∇w|² ≤ 1 and |∫_B ∇w·∇ζ| ≤ δ_A sup|∇ζ| for every ζ ∈ C¹_c(B), then there is a harmonic h on B with ∫_B|∇h|² ≤ 1 and ∫_B(h − w)² ≤ ε'.
A1. Suppose not. Then there are ε' > 0 and w_j ∈ W^{1,2}(B) (j = 1, 2, …) with ∫_B|∇w_j|² ≤ 1, |∫_B ∇w_j·∇ζ| ≤ j^{−1}sup|∇ζ| for all ζ ∈ C¹_c(B), and ∫_B(w_j − h)² > ε' for every harmonic h on B with ∫_B|∇h|² ≤ 1.
A2. Let λ_j := ω_n^{−1}∫_B w_j. By the Poincaré inequality on the ball (e.g. [GT01, (7.45)]), ∫_B|w_j − λ_j|² ≤ C(n)∫_B|∇w_j|² ≤ C(n). Thus (w_j − λ_j) is bounded in W^{1,2}(B), and by Rellich's compactness theorem and weak compactness of bounded sets in L²(B) a subsequence (not relabelled) satisfies w_j − λ_j → w in L²(B) and ∇w_j ⇀ ∇w weakly in L²(B; ℝⁿ), with w ∈ W^{1,2}(B) and ∫_B|∇w|² ≤ liminf ∫_B|∇w_j|² ≤ 1 (weak lower semicontinuity of the norm).
A3. For ζ ∈ C¹_c(B), ∇ζ ∈ L²(B), so ∫_B ∇w·∇ζ = lim_j ∫_B ∇w_j·∇ζ = 0 by A1. By Weyl's lemma, w (after modification on a null set) is harmonic on B.
A4. h_j := w + λ_j is harmonic with ∫_B|∇h_j|² = ∫_B|∇w|² ≤ 1, and ∫_B(w_j − h_j)² = ∫_B(w_j − λ_j − w)² → 0 < ε', contradicting A1 for large j.
Part B (Scaling). Let R₀ > 0 and w ∈ W^{1,2}(B̆_{R₀}) with R₀^{−n}∫_{B̆_{R₀}}|∇w|² ≤ 1 and |∫_{B̆_{R₀}}∇w·∇ζ| ≤ δ_A R₀ⁿ sup|∇ζ| for all ζ ∈ C¹_c(B̆_{R₀}). Put w₁(y) := R₀^{−1}w(R₀y). Then ∇w₁(y) = ∇w(R₀y), ∫_B|∇w₁|² = R₀^{−n}∫_{B̆_{R₀}}|∇w|² ≤ 1; for ζ₁ ∈ C¹_c(B) let ζ(x) := R₀ζ₁(x/R₀) ∈ C¹_c(B̆_{R₀}), so ∇ζ(x) = ∇ζ₁(x/R₀), sup|∇ζ| = sup|∇ζ₁| and ∫_{B̆_{R₀}}∇w·∇ζ = R₀ⁿ∫_B∇w₁·∇ζ₁; hence |∫_B∇w₁·∇ζ₁| ≤ δ_A sup|∇ζ₁|. Part A gives a harmonic h₁ on B; then h(x) := R₀h₁(x/R₀) is harmonic on B̆_{R₀} with R₀^{−n}∫_{B̆_{R₀}}|∇h|² ≤ 1 and ∫_{B̆_{R₀}}(h − w)² = R₀^{n+2}∫_B(h₁ − w₁)² ≤ ε'R₀^{n+2}.
Part C (Estimates for harmonic functions, Simon 3.2–3.4). Let h be harmonic on B̆_{R₀} with ∫_{B̆_{R₀}}|∇h|² ≤ R₀ⁿ and h ∈ L²(B̆_{R₀}).
C1. Mean value property: h(0) = (ω_nρⁿ)^{−1}∫_{B̆_ρ}h for 0 < ρ < R₀; letting ρ ↑ R₀ (h ∈ L¹(B̆_{R₀})), h(0) = (ω_nR₀ⁿ)^{−1}∫_{B̆_{R₀}}h, so by Cauchy–Schwarz |h(0)| ≤ ω_n^{−1/2}R₀^{−n/2}‖h‖_{L²(B̆_{R₀})}.
C2. Each ∂_ih is harmonic, so likewise ∇h(0) = (ω_nR₀ⁿ)^{−1}∫_{B̆_{R₀}}∇h and |∇h(0)| ≤ ω_n^{−1/2}R₀^{−n/2}‖∇h‖_{L²(B̆_{R₀})} ≤ ω_n^{−1/2}.
C3. For |y| ≤ 3R₀/4, B̆_{R₀/4}(y) ⊆ B̆_{R₀}, so by the mean value property |∂_ih(y)| ≤ (ω_n(R₀/4)ⁿ)^{−1/2}‖∇h‖_{L²(B̆_{R₀})} ≤ 2ⁿω_n^{−1/2}. For a harmonic u on B̆_ρ(x), |∇u(x)| ≤ (n/ρ)sup_{B̆_ρ(x)}|u| (apply the mean value property to ∂_ju and the divergence theorem). With u = ∂_ih, ρ = R₀/4 and |x| ≤ R₀/2: |D²h(x)| ≤ C₁/R₀ for |x| ≤ R₀/2, C₁ := n^{3/2}·4·2ⁿω_n^{−1/2} (|D²h| the Hilbert–Schmidt norm).
C4. Let ℓ(v) := h(0) + ∇h(0)·v and θ' ∈ (0, 1/4]. For |v| ≤ θ'R₀ ≤ R₀/4, Taylor's formula with the segment [0, v] ⊆ B_{R₀/2} gives |h(v) − ℓ(v)| ≤ ½|v|² sup_{B_{R₀/2}}|D²h| ≤ ½C₁θ'²R₀.
Part D (Conclusion; Simon 3.4 and the computation (17')–(19') of the parent proof). Put C := max{ω_n^{−1/2}, 2, ½ω_nC₁²} (depends only on n) and, given ε' > 0, δ_h := δ_A(n, ε'). Let R₀ > 0 and w : ℝⁿ → ℝ be Lipschitz with ∫_{B̆_{R₀}}|∇w|² ≤ R₀ⁿ and |∫_{B̆_{R₀}}∇w·∇ζ| ≤ δ_h R₀ⁿ G whenever ζ is C¹ with compact support, tsupport ζ ⊆ B̆_{R₀}, and |∇ζ| ≤ G everywhere (in particular with G = sup|∇ζ|). (Integrability: fderiv ℝ w is Borel measurable (Mathlib measurable_fderiv, valid for every function), and since w is Lipschitz with constant Lw, ‖fderiv ℝ w v‖ ≤ Lw for every v (norm_fderiv_le_of_lipschitz; fderiv is 0 where w is not differentiable); by Rademacher's theorem w is differentiable a.e., and, as recalled in the conventions, its a.e. derivative fderiv ℝ w is the weak gradient ∇w. For ζ as above, fderiv ℝ ζ is continuous with compact support, hence bounded. So the integrands ‖fderiv ℝ w v‖² and Σ_i ∂_iw(v)∂_iζ(v) of the two Lean hypotheses are bounded Borel functions on the ball B̆_{R₀}, which has finite measure, and their Bochner integrals are the Lebesgue integrals written here; likewise w² and (w − a − b)² are continuous, hence bounded on bounded balls, so the Bochner integrals in the conclusions are genuine Lebesgue integrals.) Then w|_{B̆_{R₀}} ∈ W^{1,2}(B̆_{R₀}) and Part B provides a harmonic h on B̆_{R₀} with ∫_{B̆_{R₀}}|∇h|² ≤ R₀ⁿ and ∫_{B̆_{R₀}}(h − w)² ≤ ε'R₀^{n+2}; in particular h ∈ L²(B̆_{R₀}) (w is bounded on B̆_{R₀}). Let a := h(0) and b := Dh(0) (the linear functional v ↦ ∇h(0)·v; ‖b‖ = |∇h(0)|).
D1. ‖b‖ ≤ ω_n^{−1/2} ≤ C by C2.
D2. By C1 and Minkowski, |a| ≤ ω_n^{−1/2}R₀^{−n/2}(‖w‖_{L²(B̆_{R₀})} + ‖h − w‖_{L²(B̆_{R₀})}) ≤ ω_n^{−1/2}(R₀^{−n}∫_{B̆_{R₀}}w²)^{1/2} + ω_n^{−1/2}R₀^{−n/2}(ε'R₀^{n+2})^{1/2} ≤ C·√(∫_{B̆_{R₀}}w²/R₀ⁿ) + C√ε' R₀.
D3. For θ' ∈ (0, 1/4], by (u + u')² ≤ 2u² + 2u'², Part B and C4: ∫_{B̆_{θ'R₀}}(w − a − b(v))²dv ≤ 2∫_{B̆_{R₀}}(w − h)² + 2∫_{B̆_{θ'R₀}}(h − ℓ)² ≤ 2ε'R₀^{n+2} + 2ω_n(θ'R₀)ⁿ(½C₁θ'²R₀)² = (θ'R₀)^{n+2}(2ε'/θ'^{n+2} + ½ω_nC₁²θ'²) ≤ C(ε'/θ'^{n+2} + θ'²)(θ'R₀)^{n+2}.
D1–D3 are the three asserted conclusions; C does not depend on ε', and δ_h depends only on n and ε'. ∎

## Key steps

1. Harmonic approximation (Simon 3.1) by contradiction, using the Poincaré inequality, Rellich compactness, weak limits and Weyl's lemma.
2. Scale to radius R₀.
3. Mean-value and derivative estimates for harmonic h (Simon 3.2–3.4), and Taylor expansion on B_{θ'R₀}.
4. Set a := h(0) and b := Dh(0), and derive the bounds on ‖b‖, |a| and ∫(w − a − b)².

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical)`
- `rg -n -i 'allard|tilt.?excess|harmonic.?approx|lipschitz.?approx' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `rg -n 'sorry' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean; rg -n '^theorem|^lemma' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `rg -l -i "rellich|kondrachov|weyl's lemma|weakly harmonic" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory  (no match, exit 1)`
- `rg -n 'theorem ae_differentiableAt|theorem norm_fderiv_le_of_lipschitz' Analysis/Calculus/Rademacher.lean Analysis/Calculus/FDeriv/Basic.lean; grep -n ae_differentiableAt Analysis/Calculus/Rademacher.lean  (in the snapshot Mathlib)`
- `rg -n 'theorem exists_disjoint_subfamily_covering_enlargement_closedBall' MeasureTheory/Covering/Vitali.lean; rg -n 'theorem ae_tendsto_average_norm_sub' MeasureTheory/Covering/Differentiation.lean; rg -n 'theorem measurable_fderiv' Analysis/Calculus/FDeriv/Measurable.lean  (in the snapshot Mathlib)`
- `sed -n 10,30p lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean (simongmt rev 2b3663083f3fe399b6296fb8eaee52169170e197 from the snapshot's lake-manifest.json)`
- `python3: lean_name collision scan of the 12 dorag_* names over dag.json (200 nodes), nodes/*/*.json and other workspaces' dag.json; exact-statement comparison against .humanize/math-wiki/*.md (43 pages)`
- `python3 -I lean_contract.validate_lean_statement on all 12 lean_statements; lean (lean-4.35.0-rc3, LEAN_PATH of the built workspace) on 13 comparator-format modules Challenge_<key>.lean`
- `lean Check.lean (#check of the Mathlib API used by the assembly); lean Assembly.lean with #print axioms GMT.Ch07.AllardAsmV3.assembly`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/math-wiki`
- `/tmp/allard-v3-work/v3/Challenge_PARENT.lean`
- `/tmp/allard-v3-work/asm3/Assembly.lean`
- `/tmp/allard-v3-work/asm3/Assembly.log`

The snapshot pins project b4d606d and Mathlib 25730c7c. Its GMT/Ch07/Contract.lean is byte-identical to the workspace contract and to GMT/Ch07/Submission.lean, which is the compiler context of every child type.

Nothing in the snapshot proves Allard regularity or any child:
- The only Allard-related declarations are in GMT/Ch05/Submission.lean: Prop definitions (TiltExcessHeightEstimate, AffineApproximationLemma, LipschitzApproximationLemma, HarmonicApproximationLemma, TiltExcessDecayTheorem, AllardRegularityTheorem, …) for a different varifold type. They are used only in main_theorem := by sorry (line 461), so nothing is proved there.
- SimonGMT Chapter05/Basic.lean says compactness, Lipschitz approximation, excess decay and Allard regularity are not formalized.
- The Rellich/Kondrachov/Weyl/weakly-harmonic search found no match in the snapshot's Mathlib Analysis and MeasureTheory.
The split into 12 children therefore stands, and no identical comparator-approved declaration exists to reuse.

The Mathlib tools the children cite exist at the pinned revision:
- LipschitzWith.ae_differentiableAt (Rademacher.lean:385);
- norm_fderiv_le_of_lipschitz (FDeriv/Basic.lean:947);
- measurable_fderiv (FDeriv/Measurable.lean:378);
- Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall (Vitali.lean:158);
- VitaliFamily.ae_tendsto_average_norm_sub (Differentiation.lean:837).

Lean checks:
- All 12 child types and the frozen parent type elaborate in comparator scope; the only diagnostic is the expected sorry warning.
- The assembly proves the exact parent type from the five top-level child types, with axioms propext, Classical.choice and Quot.sound only.
- No dorag_* name collides with any DAG reservation.
