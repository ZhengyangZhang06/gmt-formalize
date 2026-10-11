# Parent-supplied natural-language proof

- Parent DAG node: `root.sobolev_inequality-a1`
- Child DAG node: `root.sobolev_inequality-a1.energy_integrable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. E = Ambient n ℓ = ℝ^{n+ℓ} with its Borel σ-algebra; B_ρ(ξ) = closedBall ξ ρ (closed ball); ω_n = omega n ∈ (0, ∞) for n ≥ 1 (Lebesgue measure of the open unit ball of ℝⁿ, which is open, nonempty and bounded); μ = μ_V = V.weight; p_x = (V.tangentSpace x).starProjection, the orthogonal projection onto T_xV, a continuous linear map with |p_x v| ≤ |v| (Mathlib Submodule.norm_starProjection_apply_le); ∇g(x) = gradient g x (0 where g is not differentiable); ∇^M g(x) = V.tangentialGradient g x = p_x(∇g(x)). All integrals ∫ are Bochner integrals (value 0 for non-integrable integrands), so integrability is checked wherever integrals are compared or split; ∫_{(a,b]} denotes the Lebesgue integral over the interval Ioc a b. Source: Step 1 (Preliminaries) of the parent proof of SobolevInequality (Simon Ch. 4, §5). Let K := tsupport g.

1. (g is C¹ on E.) Let x ∈ E. If x ∈ U, then U is a neighbourhood of x (U is open) and g is C¹ on U, so g is C¹ at x. If x ∉ U, then x ∉ K because K ⊆ U; K is closed, so g vanishes identically on the open neighbourhood E ∖ K of x, hence g agrees near x with the constant 0 and is C¹ at x. Being C¹ at every point, g is C¹ on E (Mathlib contDiff_iff_contDiffAt; the same statement is SimonGMT Chapter04.RectifiableVarifold.contDiff_of_tsupport_subset). In particular g and x ↦ ∇g(x) are continuous on E.
2. (∇^M g vanishes off K.) If x ∉ K, then g = 0 on a neighbourhood of x, so Dg(x) = 0, ∇g(x) = 0, and ∇^M g(x) = p_x(0) = 0. In particular ∇g also vanishes off K.
3. (Finiteness.) K is compact because g has compact support, so μ(K) < ∞ since μ is finite on compact sets. The continuous functions |g| and |∇g| vanish off the compact set K, so M_0 := sup_E |g| < ∞ and M_1 := sup_E |∇g| < ∞ (each is a maximum over K, or 0 if K = ∅).
4. (|∇^M g| ∈ L¹(μ).) The map x ↦ p_x is μ-a.e. strongly measurable by hypothesis, x ↦ ∇g(x) is continuous, and evaluation (P, v) ↦ P v, L(E, E) × E → E, is continuous; therefore x ↦ ∇^M g(x) = p_x(∇g(x)) is μ-a.e. strongly measurable, and so is x ↦ |∇^M g(x)|. By step 2 and |p_x v| ≤ |v|, |∇^M g(x)| ≤ M_1·1_K(x) for every x ∈ E. The function M_1·1_K is μ-integrable because μ(K) < ∞, so |∇^M g| is μ-integrable.
5. (g|H| ∈ L¹(μ).) H is locally μ-integrable on U and K is a compact subset of U, so H is μ-integrable on K (Mathlib LocallyIntegrableOn.integrableOn_compact_subset); hence |H| is μ-integrable on K. On K the function x ↦ g(x)|H(x)| is a.e. strongly measurable (continuous factor times a.e. strongly measurable factor) and bounded in absolute value by M_0|H|, hence μ-integrable on K. Off K, g = 0 and therefore g|H| = 0. A function that is integrable on K and vanishes off K is integrable on E, so g|H| ∈ L¹(μ).
6. Steps 1, 2, 4 and 5 are the four asserted conclusions: g ∈ C¹(E); ∇^M g(x) = 0 for x ∉ tsupport g; |∇^M g| ∈ L¹(μ); g|H| ∈ L¹(μ). ∎

## Key steps

1. g is C¹ at points of U (U open) and near points off tsupport g (g ≡ 0 there), hence C¹ on E
2. ∇g and ∇^M g = p_x(∇g) vanish off the compact K = tsupport g, and μ(K) < ∞
3. ∇^M g is μ-a.e. strongly measurable from (FV3) and continuity of ∇g, and |∇^M g| ≤ (sup|∇g|)·1_K, so it is integrable
4. H is integrable on the compact K ⊆ U; g|H| ≤ (sup|g|)|H| on K and vanishes off K, so it is integrable

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
