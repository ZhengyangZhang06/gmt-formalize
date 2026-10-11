# Parent-supplied natural-language proof

- Parent DAG node: `root.sobolev_inequality-a1`
- Child DAG node: `root.sobolev_inequality-a1.truncation_layer_cake-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. E = Ambient n ℓ = ℝ^{n+ℓ} with its Borel σ-algebra; B_ρ(ξ) = closedBall ξ ρ (closed ball); ω_n = omega n ∈ (0, ∞) for n ≥ 1 (Lebesgue measure of the open unit ball of ℝⁿ, which is open, nonempty and bounded); μ = μ_V = V.weight; p_x = (V.tangentSpace x).starProjection, the orthogonal projection onto T_xV, a continuous linear map with |p_x v| ≤ |v| (Mathlib Submodule.norm_starProjection_apply_le); ∇g(x) = gradient g x (0 where g is not differentiable); ∇^M g(x) = V.tangentialGradient g x = p_x(∇g(x)). All integrals ∫ are Bochner integrals (value 0 for non-integrable integrands), so integrability is checked wherever integrals are compared or split; ∫_{(a,b]} denotes the Lebesgue integral over the interval Ioc a b. Source: Steps 5 (truncation and layer cake) and 6 (ε ↓ 0) of the parent proof (end of the proof of Simon 5.7, with 4.11). Put p := n/(n − 1) (so p > 1, p − 1 = 1/(n − 1), 1/p = (n − 1)/n), K := tsupport h, M_s := {x : h(x) > s} for s ∈ ℝ, J := ∫(|∇^M h| + h|H|) dμ, Q := ∫ h^p dμ.

1. (Setup.) By the sibling sobolev_energy_integrable applied to h: h ∈ C¹(E), ∇^M h = 0 off K, and |∇^M h|, h|H| are μ-integrable; in particular J ≥ 0 is finite. K is compact with μ(K) < ∞; h is continuous, so every M_s is open (Borel), and for s ≥ 0, M_s ⊆ support h ⊆ K, so μ(M_s) < ∞. |H| is μ-integrable on K (local integrability on U, K ⊆ U compact). h^p is continuous, vanishes off K and is bounded, so Q < ∞.
2. (Cut-off.) Fix ε ∈ (0, 1] and let ψ(s) := smoothTransition(s/ε) (Mathlib Real.smoothTransition): ψ ∈ C^∞(ℝ), ψ is nondecreasing, 0 ≤ ψ ≤ 1, ψ = 0 on (−∞, 0] and ψ = 1 on [ε, ∞). Hence ψ' ≥ 0 is continuous and bounded, and ψ' = 0 on (−∞, 0). (This ψ is the axiom-clean SimonGMT Chapter04.exists_smooth_superlevel_cutoff.)
3. (Truncations.) For t ≥ 0 let h_t := ψ ∘ (h − t). Then h_t ∈ C¹(E), so h_t is C¹ on U; 0 ≤ h_t ≤ 1; if h_t(x) ≠ 0 then h(x) − t > 0, so h(x) > t ≥ 0 and x ∈ support h; hence tsupport h_t ⊆ K ⊆ U and h_t has compact support. Moreover h_t ≤ 1_{M_t}, and h_t = 1 on M_{t+ε} (there h − t > ε), so M_{t+ε} ⊆ {h_t ≥ 1}. By the chain rule ∇h_t(x) = ψ'(h(x) − t)∇h(x), and p_x is linear, so ∇^M h_t(x) = ψ'(h(x) − t)∇^M h(x) and |∇^M h_t| = ψ'(h − t)|∇^M h| for every x.
4. (Truncated inequality.) Apply the hypothesis (4.1) to g := h_t (admissible by step 3). Left side: h_t ≥ 0 is integrable, M_{t+ε} ⊆ {h_t ≥ 1} and h_t = 1 on M_{t+ε}, so ∫_{{h_t ≥ 1}} h_t dμ ≥ ∫_{M_{t+ε}} h_t dμ = μ(M_{t+ε}). Right side: 0 ≤ ∫ h_t dμ ≤ μ(M_t), so (∫h_t dμ)^{1/n} ≤ μ(M_t)^{1/n}; and, the integrands being integrable (sibling sobolev_energy_integrable for h_t, or the bounds ψ'(h − t)|∇^M h| ≤ (sup ψ')|∇^M h| and h_t|H| ≤ 1_K|H|), ∫(|∇^M h_t| + h_t|H|) dμ = P(t) + ∫ h_t|H| dμ ≤ P(t) + R(t), where P(t) := ∫ ψ'(h − t)|∇^M h| dμ ≥ 0 and R(t) := ∫_{M_t} |H| dμ ≥ 0 (h_t|H| ≤ 1_{M_t}|H|). Since C ≥ 0:
 (4.a) μ(M_{t+ε}) ≤ C μ(M_t)^{1/n}(P(t) + R(t)) for every t ≥ 0.
5. (Moment factor.) Q_ε := ∫_{M_0}(h + ε)^p dμ < ∞ (bounded integrand, M_0 ⊆ K). For t ≥ 0, on M_t we have h + ε > t + ε ≥ 0, and M_t ⊆ M_0, so (t + ε)^p μ(M_t) ≤ ∫_{M_t}(h + ε)^p dμ ≤ Q_ε. Taking 1/n-th powers ((t + ε)^{p/n} = (t + ε)^{1/(n−1)}): (t + ε)^{1/(n−1)}μ(M_t)^{1/n} ≤ Q_ε^{1/n}. Multiplying (4.a) by (t + ε)^{1/(n−1)} ≥ 0:
 (5.a) (t + ε)^{1/(n−1)} μ(M_{t+ε}) ≤ C Q_ε^{1/n}(P(t) + R(t)) for every t ≥ 0.
6. (Integration in t, Tonelli; Simon 4.11.) All quantities are nonnegative; (x, t) ↦ ψ'(h(x) − t)|∇^M h(x)| and (x, t) ↦ 1_{h(x)>t}|H(x)| are (a.e.) measurable for μ ⊗ dt (continuous functions of (x, t) times a.e.-measurable functions of x), μ is σ-finite (finite on compacts in the σ-compact E), and t ↦ μ(M_{t+ε}) is nonincreasing, hence measurable. Integrate (5.a) over t ∈ (0, ∞) (as lower Lebesgue integrals of nonnegative functions):
 Left side: by the translation u = t + ε and Tonelli, ∫_0^∞ (t + ε)^{1/(n−1)}μ(M_{t+ε}) dt = ∫_ε^∞ u^{1/(n−1)}μ(M_u) du = ∫ (∫_ε^∞ u^{1/(n−1)}1_{h(x)>u} du) dμ(x) = ((n − 1)/n)∫_{M_ε}(h^p − ε^p) dμ, since for h(x) > ε the inner integral is ∫_ε^{h(x)} u^{1/(n−1)} du = ((n − 1)/n)(h(x)^p − ε^p), and it is 0 otherwise.
 Right side: by Tonelli, ∫_0^∞ P(t) dt = ∫ |∇^M h(x)| (∫_0^∞ ψ'(h(x) − t) dt) dμ(x), and for a := h(x) ≥ 0, ψ'(a − t) = 0 for t > a, so ∫_0^∞ ψ'(a − t) dt = ∫_0^a ψ'(a − t) dt = ψ(a) − ψ(0) = ψ(a) ≤ 1 (fundamental theorem of calculus); hence ∫_0^∞ P(t) dt ≤ ∫|∇^M h| dμ. Likewise ∫_0^∞ R(t) dt = ∫ |H(x)|(∫_0^∞ 1_{h(x)>t} dt) dμ(x) = ∫ h|H| dμ.
 Hence (6.a) ((n − 1)/n)∫_{M_ε}(h^p − ε^p) dμ ≤ C Q_ε^{1/n} J for every ε ∈ (0, 1]. (Library pointers, all axiom-clean: the Tonelli bound for ∫_0^∞(P + R) is SimonGMT Chapter04.lintegral_smooth_truncation_energy_le applied to μ⌞K; the layer-cake identities are Mathlib lintegral_comp_eq_lintegral_meas_lt_mul / lintegral_rpow_eq_lintegral_meas_lt_mul.)
7. (ε ↓ 0.) Take ε = 1/k, k → ∞. Pointwise, 1_{M_ε}(h^p − ε^p) → h^p (if h(x) > 0 then eventually h(x) > ε and ε^p → 0; if h(x) = 0 both sides vanish), and 0 ≤ 1_{M_ε}(h^p − ε^p) ≤ h^p ≤ (max h)^p 1_K ∈ L¹(μ); by dominated convergence ∫_{M_ε}(h^p − ε^p) dμ → Q. Similarly 1_{M_0}(h + ε)^p → 1_{M_0}h^p with domination by (max h + 1)^p 1_K, so Q_ε → ∫_{M_0}h^p dμ = Q (h^p = 0 off M_0). As y ↦ y^{1/n} is continuous on [0, ∞), Q_ε^{1/n} → Q^{1/n}. Letting k → ∞ in (6.a): ((n − 1)/n)Q ≤ C Q^{1/n} J.
8. (Conclusion.) If Q = 0, the left side of the claim is 0^{(n−1)/n} = 0 ≤ (n/(n − 1))·C·J because C ≥ 0 and J ≥ 0. If Q > 0, divide step 7 by ((n − 1)/n)Q^{1/n} > 0: Q^{(n−1)/n} = Q^{1−1/n} = Q/Q^{1/n} ≤ (n/(n − 1))·C·J. This is (∫h^{n/(n−1)} dμ)^{(n−1)/n} ≤ (n/(n − 1))·C·∫(|∇^M h| + h|H|) dμ. ∎

## Key steps

1. Truncations h_t = ψ(h − t) with a C¹ cut-off ψ (0 on (−∞,0], 1 on [ε,∞)) are admissible, h_t = 1 on {h > t+ε}, h_t ≤ 1_{h>t}, |∇^M h_t| = ψ'(h − t)|∇^M h|
2. The hypothesis for h_t gives μ(M_{t+ε}) ≤ Cμ(M_t)^{1/n}[∫ψ'(h−t)|∇^M h| + ∫_{M_t}|H|]
3. Multiply by (t+ε)^{1/(n−1)} and use (t+ε)^{1/(n−1)}μ(M_t)^{1/n} ≤ Q_ε^{1/n}
4. Integrate in t (Tonelli, layer cake): ((n−1)/n)∫_{M_ε}(h^p − ε^p) ≤ CQ_ε^{1/n}∫(|∇^M h| + h|H|)
5. Let ε ↓ 0 by dominated convergence and divide by Q^{1/n} (Q = 0 trivial)

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `rg -n 'theorem exists_disjoint_subfamily_covering_enlargement_closedBall' -A 12 <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `rg -n 'theorem lintegral_comp_eq_lintegral_meas_lt_mul|theorem lintegral_eq_lintegral_meas_lt|theorem lintegral_comp_eq_lintegral_meas_le_mul|theorem lintegral_rpow_eq_lintegral_meas_lt_mul' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `rg -n 'countable_of_nonempty_interior|countable_of_isOpen' <snapshot>/mathlib/Mathlib`
- `rg -n '^theorem|^lemma|^def|^protected theorem' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `sed -n 586,880p book/chapter-04.txt (Simon 5.1-5.9 printed text)`
- `grep -rn 'theorem contDiff_of_tsupport_subset|theorem exists_fiveTimesCovering|theorem integrableOn_norm_tangentialGradient' lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `cat simongmt/Poincare/SimonGMT/Chapter04/{SobolevCovering,GoodRadius,SobolevGoodRadius,SobolevTruncation,SobolevLayerCake,Sobolev,CompactWeighted}.lean Chapter01/DensityCovering.lean`
- `git -C lake-packages-25730c7c/simongmt rev-parse HEAD`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/sobolev-a1-audit/olean/GMT/Ch04/Submission.olean`
- `python3 -I gen_challenges.py: verifier/lean_contract.validate_lean_statement + gmt-compare.child_modules(mode=contract) for each child; LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/sobolev-a1-audit/olean lean Challenge_<name>.lean`
- `LEAN_PATH=... lean /tmp/sobolev-a1-audit/lean/Assembly.lean (parent frozen type proved from the uncle and six sorry'd children; #print axioms)`
- `LEAN_PATH=... lean /tmp/sobolev-a1-audit/lean/Inspect.lean (Iff.rfl against explicit @HPow.hPow ℝ ℕ ℝ / Real.rpow / Measure toReal forms)`
- `lake env lean /tmp/sobolev-a1-audit/lean/Axioms.lean (#print axioms of cited SimonGMT and Mathlib lemmas)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-sobolev-inequality-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/SobolevCovering.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/GoodRadius.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/SobolevGoodRadius.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/SobolevTruncation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/SobolevLayerCake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Sobolev.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/CompactWeighted.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityCovering.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/sobolev-a1-audit/children.json`
- `/tmp/sobolev-a1-audit/lean/Assembly.lean`
- `/tmp/sobolev-a1-audit/lean/Inspect.lean`
- `/tmp/sobolev-a1-audit/lean/Axioms.lean`

Contract provenance. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 6e58e5dd…0f4770b). The manifest pins project ff75f52 and Mathlib 25730c7c. The SimonGMT package is at the pinned revision 2b3663083f3fe399b6296fb8eaee52169170e197.

Mathlib lemmas available in the snapshot, each depending only on propext, Classical.choice and Quot.sound:
- Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall (requires τ > 3; used with τ = 5)
- Set.PairwiseDisjoint.countable_of_nonempty_interior
- the Layercake lemmas lintegral_comp_eq_lintegral_meas_lt_mul and lintegral_rpow_eq_lintegral_meas_lt_mul
- Real.smoothTransition (smooth, monotone, values in [0,1], 0 on (−∞,0], 1 on [1,∞))
- withDensity_absolutelyContinuous, exists_measurable_superset_of_null, Tendsto.limUnder_eq
- LocallyIntegrableOn.integrableOn_compact_subset, Continuous.integrable_of_hasCompactSupport
- intervalIntegral.integral_comp_mul_left, MonotoneOn.intervalIntegrable, Real.rpow_inv_natCast_pow
- Submodule.norm_starProjection_apply_le

Pinned SimonGMT. It contains a kernel-checked Sobolev proof for its own Chapter04.RectifiableVarifold. That structure differs from the contract's, so its varifold-specific lemmas cannot be applied. Its general lemmas are reusable as tools, each with the same three axioms only:
- Chapter04.lintegral_le_of_ae_exists_good_radius (5-times covering plus summation)
- exists_smooth_superlevel_cutoff
- lintegral_smooth_truncation_energy_le
- lintegral_superlevel_le_of_positive_shifts
- rpow_one_sub_le_of_le_rpow_mul
- intervalIntegrable_radiusQuotient_of_monotoneOn
- RectifiableVarifold.contDiff_of_tsupport_subset (fully general despite the namespace)
- Chapter01.exists_fiveTimesCovering
Its calculus lemma exists_goodRadius_of_local_radius_inequality has a weaker constant (4·5ⁿM^{1/n}, r ≤ R). The corrected Lemma 5.8 child therefore keeps the parent's sharp constant and is proved directly.

Child type checks. With GMT.Ch04.Submission compiled to an olean:
- All six child types pass validate_lean_statement and elaborate in comparator-generated NodeChallenge files (contract scope: the opens, namespace GMT.Ch04, noncomputable section, open RectifiableVarifold); the only diagnostics are the expected sorry warnings.
- Iff.rfl confirms ℕ-powers and Real.rpow where intended.
- The parent's frozen type is proved, with no sorry in its body, from the uncle weighted_monotonicity_identity (frozen type copied byte-identically) and the six children. #print axioms shows sorryAx only through the stubs.
