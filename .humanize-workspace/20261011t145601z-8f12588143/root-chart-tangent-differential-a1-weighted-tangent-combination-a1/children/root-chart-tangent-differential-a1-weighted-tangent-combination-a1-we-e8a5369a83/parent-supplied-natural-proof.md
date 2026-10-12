# Parent-supplied natural-language proof

- Parent DAG node: `root.chart_tangent_differential-a1.weighted_tangent_combination-a1`
- Child DAG node: `root.chart_tangent_differential-a1.weighted_tangent_combination-a1.weighted_blowup_split-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 3-4 of the parent proof. This is the decomposition in Simon's proof of Theorem 1.6 '⇒' (chapter-03.txt lines 116-120: ∫_{η_{x,λ}(M)} f dHⁿ = ∫_{η_{x,λ}(N_j)} f dHⁿ − ∫_{η_{x,λ}(N_j∖M_j)} f dHⁿ + ∫_{η_{x,λ}(M∖M_j)} f dHⁿ), in the weighted form of Definition 1.7 and Remark 1.8(1) (lines 284-306). It is written on the unscaled side, before the change of variables, and on M ∩ Γ the weight is split as θ = θ(x) + (θ − θ(x)). Conventions: η_{x,r}(z) = r⁻¹(z − x) (SimonGMT blowUpMap x r); Hⁿ = μHE[n]; ∫_T h dHⁿ is the Bochner integral against Hⁿ⌞T; g(z) := f(η_{x,r}(z)).

1. Properties of g. Since f ∈ C_c(ℝ^N, ℝ), there is C with |f(y)| ≤ C for all y, so C ≥ 0 (Continuous.bounded_above_of_compact_support). There is also R₀ with tsupport f ⊆ B_{R₀}(0) (compact, hence bounded: Bornology.IsBounded.subset_ball), so f(y) ≠ 0 ⇒ ‖y‖ < R₀. The map η_{x,r} is affine, hence continuous, so g is continuous and |g| ≤ C. If g(z) ≠ 0, then r⁻¹‖z − x‖ = ‖η_{x,r}(z)‖ < R₀. Since r > 0, ‖z − x‖ < R₀r, so z ∈ K := B̄_{R₀r}(x).

2. gθ is Hⁿ-integrable on M. K is a closed ball in ℝ^N, hence compact and Borel. So θ is Hⁿ-integrable on M ∩ K by the third clause of IsPositiveLocallyIntegrableWeight n M θ.
 Measurability: g is continuous, hence strongly measurable, and θ is Hⁿ⌞M-a.e. measurable by the second clause. So gθ is Hⁿ⌞M-a.e. strongly measurable.
 Domination: |g(z)θ(z)| ≤ 1_K(z)·C|θ(z)| for every z. If g(z) = 0 the left side is 0; otherwise z ∈ K by step 1 and |g(z)| ≤ C.
 The majorant 1_K·C|θ| is Hⁿ⌞M-integrable, because K is Borel and C|θ| is integrable on M ∩ K (integrable_indicator_iff, Measure.restrict_restrict). By domination (Integrable.mono'), gθ is integrable on M.

3. g is Hⁿ-integrable on Γ. Hⁿ⌞Γ is a finite measure because Hⁿ(Γ) < ∞. The function g is continuous, hence strongly measurable, and bounded by C. A bounded, strongly measurable function is integrable for a finite measure (Integrable.of_bound).

4. Integrability on M ∩ Γ. By restriction (IntegrableOn.mono_set), gθ is integrable on M ∩ Γ ⊆ M (step 2), and g is integrable on M ∩ Γ ⊆ Γ (step 3). Hence g·(θ − θ(x)), which equals gθ − θ(x)·g pointwise, is integrable on M ∩ Γ.

5. Three exact identities. If t is Hⁿ-null-measurable and F is Hⁿ-integrable on s, then ∫_{s∩t} F + ∫_{s∖t} F = ∫_s F (integral_inter_add_sdiff₀).
 (a) Take s = M, t = Γ (null-measurable by hypothesis) and F = gθ (step 2): ∫_M gθ = ∫_{M∩Γ} gθ + ∫_{M∖Γ} gθ.
 (b) Take s = Γ, t = M (null-measurable by hypothesis) and F = g (step 3): ∫_Γ g = ∫_{Γ∩M} g + ∫_{Γ∖M} g, and Γ ∩ M = M ∩ Γ.
 (c) On M ∩ Γ, gθ = θ(x)·g + g·(θ − θ(x)) pointwise, and both terms are integrable there (step 4). By additivity and homogeneity of the integral (integral_add, integral_const_mul), ∫_{M∩Γ} gθ = θ(x)·∫_{M∩Γ} g + ∫_{M∩Γ} g·(θ − θ(x)).

6. Conclusion. From (a) and (c),
 ∫_M gθ = θ(x)·∫_{M∩Γ} g + ∫_{M∩Γ} g·(θ − θ(x)) + ∫_{M∖Γ} gθ.
 By (b), ∫_{M∩Γ} g = ∫_Γ g − ∫_{Γ∖M} g. Substituting and rearranging (commutative ring arithmetic) gives
 ∫_M gθ dHⁿ = ∫_{M∖Γ} gθ dHⁿ + θ(x)·(∫_Γ g dHⁿ − ∫_{Γ∖M} g dHⁿ) + ∫_{M∩Γ} g·(θ − θ(x)) dHⁿ,
 which is the claim. The positivity of θ is not used, and r > 0 is used only in step 1, to localize g to the compact ball K. ∎

## Key steps

1. g = f∘η_{x,r} is continuous, |g| ≤ C, and g(z) ≠ 0 ⇒ z ∈ K = B̄_{R₀r}(x) (compact).
2. gθ is Hⁿ⌞M-integrable: dominated by 1_K·C|θ|, integrable since θ ∈ L¹(Hⁿ⌞(M∩K)); gθ a.e.-strongly measurable.
3. g is Hⁿ⌞Γ-integrable (bounded, continuous, Hⁿ(Γ) < ∞); hence gθ, g, g(θ − θ(x)) are integrable on M∩Γ.
4. integral_inter_add_sdiff₀ splits ∫_M gθ along Γ and ∫_Γ g along M; linearity splits ∫_{M∩Γ} gθ = θ(x)∫_{M∩Γ} g + ∫_{M∩Γ} g(θ − θ(x)).
5. Substitute and rearrange to obtain the stated identity.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `rg -n "blowUpMap" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project`
- `rg -n "blowUpMap" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `rg -n "blowUpMap.*\* .*h |integral_tendsto_zero|tendsto_zero_of_density|upperDensity.*blowUp|negligible" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `grep -n "def \|theorem \|lemma " /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n "theorem|lemma" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `rg -n -F -e "theorem <name>" -e "lemma <name>" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/{MeasureTheory,Topology,Analysis/Normed,Order} for <name> in Continuous.bounded_above_of_compact_support, norm_integral_le_of_norm_le, setIntegral_indicator, integrable_indicator_iff, integral_inter_add_sdiff₀, Integrable.of_bound, integrableOn_const, squeeze_zero_norm' (squeeze_one_norm'), tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within, Integrable.mono', setIntegral_const, isFiniteMeasure_restrict, Bornology.IsBounded.subset_ball, integral_const_mul`
- `lake env lean GMT/Scratch/WTC_Check0.lean, WTC_Check1.lean (#check of every cited lemma after `import GMT.Ch03.Submission`)`
- `lake env lean GMT/Scratch/WTC_Final.lean (children, uncle and parent glue fully proved in the replayed contract scope; #print axioms)`
- `python3 verifier/gmt-compare.py contract_scope + verifier/lean_contract.py validate_lean_statement on both child statements`
- `dag.json lean_name scan and grep -rl <name> over the run directory (collision check)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Group/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/NhdsWithin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/ClassicalTangent.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`

Snapshot manifest: project d09bc8a (mode local-project), Mathlib 25730c7c, plus the pinned simongmt package. No match for a ready-made lemma for either child. The snapshot project has no blowUpMap lemmas beyond the frozen contract. SimonGMT Chapter03/Rectifiable.lean only defines blowUpMap (l.96), HasApproximateTangentSpaceAt (l.102) and HasWeightedApproximateTangentSpaceAt (l.330). SimonGMT Chapter04 (WeightedBlowUp.lean, TangentDensity.lean, ClassicalTangent.lean) has blow-up change-of-variables and density lemmas for varifolds, but they are not imported by the contract, and none states the vanishing-density estimate or the Γ-splitting identity. The no-match search for 'integral_tendsto_zero|tendsto_zero_of_density|negligible' returned nothing. Both children are therefore supplied here. Every Mathlib lemma their proofs use is in the snapshot: Continuous.bounded_above_of_compact_support (Analysis/Normed/Group/Bounded.lean:153), norm_integral_le_of_norm_le (Bochner/Basic.lean:985), integral_const_mul (Bochner/Basic.lean:290), integral_inter_add_sdiff₀ (Bochner/Set.lean:106), setIntegral_indicator (Bochner/Set.lean:194), setIntegral_const (Bochner/Set.lean:524), integrableOn_const (IntegrableOn.lean:119), Integrable.of_bound (IntegrableOn.lean:171), integrable_indicator_iff (IntegrableOn.lean:340), Integrable.mono' (L1Space/Integrable.lean:104), isFiniteMeasure_restrict (Typeclasses/Finite.lean:40), tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (Topology/NhdsWithin.lean:470), squeeze_zero_norm' via to_additive of squeeze_one_norm' (Analysis/Normed/Group/Continuity.lean:94), Bornology.IsBounded.subset_ball (Topology/MetricSpace/Bounded.lean:111). All are visible after `import GMT.Ch03.Submission`, confirmed by #check and by full compilation of both children and the parent glue, with axioms propext/Classical.choice/Quot.sound. The resolved uncle Submission.chartTD_setIntegral_blowUpMap_image is used only by the parent glue.
