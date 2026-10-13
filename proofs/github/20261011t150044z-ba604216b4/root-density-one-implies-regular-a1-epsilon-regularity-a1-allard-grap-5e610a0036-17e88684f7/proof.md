# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Sibling map (dependency key — frozen Lean declaration — labels used below): tangent_projection_measurable — Submission.dorag_approxTangent_starProjection_aesm (x ↦ p_x is AE-strongly measurable for μ = R.measure).
Source: parent proof Part 1.1–1.3 (Simon Ch. 4, 3.2–3.6, 3.16–3.17 with bounded H, and 4.10(1); Ch. 3, 1.5(3)). Conventions: E := ℝ^{n+k}; B_t(y) closed ball, B̆_t(y) open ball; M := R.carrier, θ := R.mult, μ := R.measure = θHⁿ⌞M, Hⁿ := μHE[n], ω_n := unitBallVolume n ∈ (0, ∞); p_x := projection onto T_xM := approxTangentPlane n M x, p_x^⊥ := I − p_x. Write F_y(x) := |p_x^⊥(x − y)|²/|x − y|^{n+2} (the integrand; F_y(y) = 0 by the convention 0/0 = 0). All integrals of nonnegative functions are in [0, ∞].
Preliminaries. (P1) κ ≥ 0 since κ ≥ ‖H(x)‖. (P2) For compact K ⊆ W, μ(K) = ∫_{M∩K}θ dHⁿ < ∞ by IMRep.locallyIntegrable_mult (K ⊆ W ⊆ U); if B_t(y) ⊆ W then, W being open and B_t(y) compact, B_{R'}(y) ⊆ W for some R' > t. (P3) For μ-a.e. x: x ∈ M, T_xM is an n-dimensional approximate tangent plane of M at x (IMRep.orients, definition of approxTangentPlane, uniqueness HasApproximateTangentSpaceAt.unique), so trace p_x = n; x ↦ p_x is μ-measurable (sibling tangent_projection_measurable), hence F_y is μ-measurable. (P4) For C¹ compactly supported X with tsupport X ⊆ W, div_M X(x) = trace(p_x∘DX(x)) is bounded, measurable and compactly supported in W, so R.firstVariation X = ∫ div_M X dμ, and (MC) reads ∫ div_M X dμ = −∫⟨X, H⟩ dμ. (P5) μ({y}) = θ(y)Hⁿ({y}) = 0 for every y, since n ≥ 1.

(Remark: the library's Chapter04/MeanCurvature.lean proves the analogous cutoff identity HasGeneralizedMeanCurvatureIn.cutoffMass_deriv_identity and monotonicity HasGeneralizedMeanCurvatureIn.exp_normalizedBallMass_monotoneOn for its own varifold structure; they can serve as templates, but they do not contain the annular term ∫F_y dμ, so (M1), (M2) are proved here.)
Step 1 (the identity). Fix y and 0 < s < t with B_t(y) ⊆ W, and R' > t with B_{R'}(y) ⊆ W (P2). Let r(x) := |x − y|, and for x ≠ y let ∇r := (x − y)/r and D^⊥r(x) := p_x^⊥(∇r), so |D^⊥r|² ≤ 1 and r^{−n}|D^⊥r|² = F_y. Fix ε' ∈ (0, 1) with (1 + ε')t < R', and φ ∈ C¹(ℝ) with 0 ≤ φ ≤ 1, φ' ≤ 0, φ ≡ 1 on (−∞, 1], φ ≡ 0 on [1 + ε', ∞). For τ ∈ (0, R'/(1+ε')) let X_τ(x) := φ(r/τ)(x − y). X_τ is C¹ (it equals x − y on B̆_τ(y), and away from y it is a composition of C¹ maps), compactly supported, with tsupport X_τ ⊆ B_{(1+ε')τ}(y) ⊆ W. At x ≠ y, DX_τ(x) = φ(r/τ)I + τ^{−1}φ'(r/τ)(x − y)⊗∇r (i.e. h ↦ φ(r/τ)h + τ^{−1}φ'(r/τ)⟨∇r, h⟩(x − y)); hence at μ-a.e. x (P3, P5), div_M X_τ(x) = nφ(r/τ) + τ^{−1}φ'(r/τ)⟨p_x(x − y), ∇r⟩ = nφ(r/τ) + (r/τ)φ'(r/τ)(1 − |D^⊥r|²), because ⟨p_x∇r, ∇r⟩ = |p_x∇r|² = 1 − |D^⊥r|².
 Put I(τ) := ∫φ(r/τ)dμ, J(τ) := ∫φ(r/τ)|D^⊥r|²dμ and h(τ) := ∫φ(r/τ)⟨x − y, H(x)⟩dμ. All integrands vanish outside B_{R'}(y), which has finite μ-measure (P2); ∂_τ[φ(r/τ)] = −(r/τ²)φ'(r/τ) ≥ 0 is bounded by sup|φ'|(1+ε')/τ, uniformly for τ in compact subintervals; so by differentiation under the integral sign I and J are C¹ with I'(τ) = ∫∂_τ[φ(r/τ)]dμ and J'(τ) = ∫∂_τ[φ(r/τ)]|D^⊥r|²dμ ≥ 0. Since (r/τ)φ'(r/τ) = −τ∂_τ[φ(r/τ)], (MC) applied to X_τ (P4) gives nI(τ) − τI'(τ) + τJ'(τ) = −h(τ). As φ(r/τ) ≠ 0 only where r ≤ (1+ε')τ, |h(τ)| ≤ (1+ε')κτ I(τ).
Step 2 (integration). Let g(τ) := τ^{−n}I(τ) and c := (1+ε')κ ≥ 0. From Step 1, g' = τ^{−n−1}(τI' − nI) = τ^{−n}J' + e with e := τ^{−n−1}h, |e| ≤ cg. Hence (e^{cτ}g)' = e^{cτ}(τ^{−n}J' + e + cg) ≥ e^{cτ}τ^{−n}J' ≥ τ^{−n}J' and (e^{−cτ}g)' = e^{−cτ}(τ^{−n}J' + e − cg) ≤ e^{−cτ}τ^{−n}J' ≤ τ^{−n}J' (J' ≥ 0, c ≥ 0). Integrating over [s, t]:
 (i) ∫_s^t τ^{−n}J'(τ)dτ ≤ e^{ct}g(t) − e^{cs}g(s);  (ii) e^{−ct}g(t) − e^{−cs}g(s) ≤ ∫_s^t τ^{−n}J'(τ)dτ.
 By Tonelli (nonnegative integrand), ∫_s^t τ^{−n}J'(τ)dτ = ∫|D^⊥r|²Λ dμ with Λ(x) := ∫_s^t τ^{−n}∂_τ[φ(r/τ)]dτ. Since ∂_τ[φ(r/τ)] ≥ 0 vanishes unless r/(1+ε') ≤ τ ≤ r, where r^{−n} ≤ τ^{−n} ≤ (1+ε')ⁿr^{−n}, and ∫_s^t∂_τ[φ(r/τ)]dτ = φ(r/t) − φ(r/s), we have r^{−n}(φ(r/t) − φ(r/s)) ≤ Λ ≤ (1+ε')ⁿr^{−n}(φ(r/t) − φ(r/s)). Moreover 1_{B_t(y)∖B_{(1+ε')s}(y)} ≤ φ(r/t) − φ(r/s) ≤ 1_{B_{(1+ε')t}(y)∖B_s(y)} and μ(B_τ(y)) ≤ I(τ) ≤ μ(B_{(1+ε')τ}(y)). Therefore (i) gives
 (i') ∫_{B_t(y)∖B_{(1+ε')s}(y)} F_y dμ + e^{cs}s^{−n}μ(B_s(y)) ≤ e^{ct}t^{−n}μ(B_{(1+ε')t}(y)),
 and (ii) gives
 (ii') e^{−ct}t^{−n}μ(B_t(y)) ≤ e^{−cs}s^{−n}μ(B_{(1+ε')s}(y)) + (1+ε')ⁿ∫_{B_{(1+ε')t}(y)∖B_s(y)} F_y dμ.
Step 3 (limit ε' ↓ 0; (M1), (M2)). Let ε' ↓ 0 along a sequence. Then c → κ; μ(B_{(1+ε')τ}(y)) ↓ μ(B_τ(y)) for τ ∈ {s, t} (closed balls decreasing to the closed ball, finite measure); the sets B_t(y)∖B_{(1+ε')s}(y) increase to B_t(y)∖B_s(y), so the first integral in (i') increases to ∫_{B_t(y)∖B_s(y)}F_y dμ (monotone convergence); and the sets B_{(1+ε')t}(y)∖B_s(y) decrease to B_t(y)∖B_s(y) with F_y ≤ s^{−n} on them and finite measure, so the integral in (ii') converges to ∫_{B_t(y)∖B_s(y)}F_y dμ. All quantities are finite, so in [0, ∞]: (M1) ∫_{B_t(y)∖B_s(y)}F_y dμ + e^{κs}s^{−n}μ(B_s(y)) ≤ e^{κt}t^{−n}μ(B_t(y)); (M2) e^{−κt}t^{−n}μ(B_t(y)) ≤ e^{−κs}s^{−n}μ(B_s(y)) + ∫_{B_t(y)∖B_s(y)}F_y dμ. This is the first conclusion (in Lean: ENNReal.ofReal (Real.exp (κ s)/sⁿ) * μ(B_s(y)) etc.).
Step 4 (monotonicity and density). By (M1) (its integral term is ≥ 0), for y with B_{t₀}(y) ⊆ W the function τ ↦ e^{κτ}τ^{−n}μ(B_τ(y)) is nondecreasing on (0, t₀]. Hence for y ∈ W the limit Θ(μ, y) := lim_{τ↓0} μ(B_τ(y))/(ω_nτⁿ) exists in [0, ∞) (e^{κτ} → 1).
Step 5 (Θ ≥ 1 on spt μ ∩ W; Simon Ch. 4, 4.10(1)). (i) Let x ∈ M ∩ W be a point where M has an approximate tangent plane Q (HasApproximateTangentSpaceAt n M x Q, dim Q = n). For ε'' ∈ (0, 1) choose continuous compactly supported ψ₋ ≤ ψ₊ with 1_{B_{1−ε''}(0)} ≤ ψ₋ ≤ 1_{B_1(0)} ≤ ψ₊ ≤ 1_{B_{1+ε''}(0)}. With η_{x,λ}(y') := λ^{−1}(y' − x) one has Hⁿ(η_{x,λ}(M) ∩ B_ρ'(0)) = λ^{−n}Hⁿ(M ∩ B_{λρ'}(x)) (scaling of Hⁿ), so λ^{−n}Hⁿ(M ∩ B_{λ(1−ε'')}(x)) ≤ ∫_{η_{x,λ}(M)}ψ₋dHⁿ and ∫_{η_{x,λ}(M)}ψ₊dHⁿ ≤ λ^{−n}Hⁿ(M ∩ B_{λ(1+ε'')}(x)) (for λ so small that B_{2λ}(x) ⊆ W, Hⁿ(M ∩ B_{2λ}(x)) ≤ μ(B_{2λ}(x)) < ∞ by (P2) and θ ≥ 1 on M, so ψ_± are integrable for Hⁿ⌞η_{x,λ}(M) and these Bochner integrals, which are the ones in the library definition of HasApproximateTangentSpaceAt, are genuine integrals); by the definition of approximate tangent plane these integrals converge to ∫_Qψ_± dHⁿ ∈ [ω_n(1−ε'')ⁿ, ω_n(1+ε'')ⁿ] (Hⁿ⌞Q is Lebesgue measure on the n-plane Q). Letting ε'' ↓ 0: Hⁿ(M ∩ B_λ(x))/(ω_nλⁿ) → 1 as λ ↓ 0 (Simon Ch. 3, 1.5(3)). Since μ ≥ Hⁿ⌞M (θ ≥ 1 on M), Θ(μ, x) ≥ 1. By (P3) this holds for μ-a.e. x ∈ W.
 (ii) Θ(μ, ·) is upper semicontinuous on W: let y_j → y ∈ W, and τ, ε'' > 0 with B_{τ+ε''}(y) ⊆ W. For large j, |y_j − y| ≤ ε'', so B_τ(y_j) ⊆ B_{τ+ε''}(y) ⊆ W and by Step 4 at y_j, Θ(μ, y_j) ≤ ω_n^{−1}e^{κτ}τ^{−n}μ(B_τ(y_j)) ≤ ω_n^{−1}e^{κτ}τ^{−n}μ(B_{τ+ε''}(y)). Let j → ∞, then ε'' ↓ 0 (μ(B_{τ+ε''}(y)) ↓ μ(B_τ(y))), then τ ↓ 0: limsup_j Θ(μ, y_j) ≤ Θ(μ, y).
 (iii) Let y ∈ spt μ ∩ W. For large j the open ball B̆_{1/j}(y) lies in W and has positive μ-measure (definition of support), so by (i) it contains a point x_j with Θ(μ, x_j) ≥ 1. As x_j → y, (ii) gives Θ(μ, y) ≥ 1.
Step 6 ((D)). Let y ∈ spt μ and t > 0 with B_t(y) ⊆ W (so y ∈ W). For 0 < s < t, (M1) gives ∫_{B_t(y)∖B_s(y)}F_y dμ + e^{κs}s^{−n}μ(B_s(y)) ≤ e^{κt}t^{−n}μ(B_t(y)). Let s ↓ 0 along a sequence: the sets B_t(y)∖B_s(y) increase to B_t(y)∖{y}, and μ({y}) = 0 (P5), so the integrals increase to ∫_{B_t(y)}F_y dμ (monotone convergence); and e^{κs}s^{−n}μ(B_s(y)) → ω_nΘ(μ, y) ≥ ω_n by Steps 4–5. Hence for every c < ω_n, ∫_{B_t(y)∖B_s(y)}F_y dμ + c ≤ e^{κt}t^{−n}μ(B_t(y)) for all small s, and letting s ↓ 0 and then c ↑ ω_n: ∫_{B_t(y)}F_y dμ + ω_n ≤ e^{κt}t^{−n}μ(B_t(y)). This is the second conclusion. ∎

## Key steps

1. Radial test fields X_τ = φ(r/τ)(x − y) give div_M X_τ = nφ(r/τ) + (r/τ)φ'(r/τ)(1 − |D^⊥r|²) μ-a.e.
2. The first variation identity yields nI − τI' + τJ' = −h with |h| ≤ (1+ε')κτI, hence (e^{cτ}g)' ≥ τ^{−n}J' and (e^{−cτ}g)' ≤ τ^{−n}J' for g = τ^{−n}I.
3. Integrate over [s, t], use Tonelli and the cutoff bounds, then let ε' ↓ 0 to obtain (M1) and (M2) with closed balls.
4. (M1) gives monotonicity of e^{κτ}τ^{−n}μ(B_τ(y)), so Θ(μ, y) exists.
5. Θ ≥ 1 μ-a.e. via the density of M at approximate tangent points, upper semicontinuity of Θ, hence Θ ≥ 1 on spt μ ∩ W.
6. Let s ↓ 0 in (M1) to obtain (D).

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
