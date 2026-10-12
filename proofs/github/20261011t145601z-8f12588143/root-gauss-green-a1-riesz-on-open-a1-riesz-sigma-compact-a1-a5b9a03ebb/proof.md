# Parent-supplied natural-language proof

- Parent DAG node: `root.gauss_green-a1.riesz_on_open-a1`
- Child DAG node: `root.gauss_green-a1.riesz_on_open-a1.riesz_sigma_compact-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 1, Theorem 4.14 (Riesz Representation Theorem, chapter-01.txt lines 1654-1663) with H = ℝ^N, as used in Steps 5 and 6(f)-(g) of the supplied proof of gaussGreenRep_riesz_on_open. Here X is an arbitrary Hausdorff, locally compact, σ-compact space in place of U. Step 6(a)-(e) is the sibling theorem gaussGreenRep_riesz_caratheodory_borel_version (child caratheodory_borel_version).

1. The hypothesis of Theorem 4.14. For each compact K ⊆ X, the set {L(f) : f ∈ C_c(X; ℝ^N), |f(x)| ≤ 1 for all x, tsupport f ⊆ K} is bounded above by the C of the hypothesis. This is SimonGMT Chapter01.IsLocallyBoundedCcFunctional L, whose definition is: for every compact K, BddAbove (L '' {ω | (∀ x, ‖ω x‖ ≤ 1) ∧ tsupport ω ⊆ K}).

2. Riesz representation (Simon 4.14; Step 5). X is locally compact Hausdorff with its Borel σ-algebra. H := ℝ^N is a finite-dimensional, hence complete and second-countable, real inner product space. SimonGMT Chapter01.simon_theorem_4_14_caratheodory provides:
- μ₀ := vectorFunctionalEnvelopeMeasure L, a regular Borel measure on X (instance vectorFunctionalEnvelopeMeasure_regular);
- μ̄₀ := radonCaratheodoryMeasure μ₀, the outer measure μ₀* of μ₀ restricted to its Carathéodory σ-algebra;
- ν₁ : X → ℝ^N, strongly measurable for the Carathéodory σ-algebra of μ₀*, with |ν₁| = 1 μ̄₀-a.e. and L(f) = ∫_X ⟨f, ν₁⟩ dμ̄₀ for every f ∈ C_c(X; ℝ^N).
No case distinction on N is needed: the theorem covers every finite-dimensional target, including ℝ^0.

3. Finiteness on compacts. μ₀ is regular, in particular finite on compact sets: μ₀(K) < ∞ for every compact K ⊆ X (IsCompact.measure_lt_top).

4. Borel version (Step 6(a)-(e)). A map into the metrizable Borel space ℝ^N that is strongly measurable for some σ-algebra is measurable for it (StronglyMeasurable.measurable). So ν₁ is measurable from the Carathéodory σ-algebra of μ₀* to the Borel sets of ℝ^N. With step 3, gaussGreenRep_riesz_caratheodory_borel_version applied to (X, μ₀, N, ν₁) gives a strongly measurable (Borel) ν₂ : X → ℝ^N with ν₁ = ν₂ μ₀-a.e.

5. μ̄₀ and μ₀ have the same null sets (Step 6(f)). For every A ⊆ X, μ̄₀(A) = μ₀*(A) = μ₀(A) (SimonGMT radonCaratheodoryMeasure_apply). Hence, for every property P, P holds μ̄₀-a.e. iff P holds μ₀-a.e.: both statements say that {x : ¬P(x)} has outer measure 0 (SimonGMT ae_radonCaratheodoryMeasure_iff). Consequently |ν₁| = 1 μ₀-a.e., and since ν₁ = ν₂ μ₀-a.e., also |ν₂| = 1 μ₀-a.e. Moreover ν₁ = ν₂ μ̄₀-a.e.

6. The representation (Step 6(g)). Let f ∈ C_c(X; ℝ^N).
- By step 5, ⟨f, ν₁⟩ = ⟨f, ν₂⟩ μ̄₀-a.e., so L(f) = ∫⟨f, ν₁⟩ dμ̄₀ = ∫⟨f, ν₂⟩ dμ̄₀ (integral_congr_ae).
- x ↦ ⟨f(x), ν₂(x)⟩ is strongly measurable for the Borel σ-algebra of X: f is continuous with compact support (Continuous.stronglyMeasurable_of_hasCompactSupport), ν₂ is strongly measurable, and inner products of strongly measurable maps are strongly measurable (StronglyMeasurable.inner).
- The trim of μ̄₀ to the Borel σ-algebra is μ₀, because μ̄₀(B) = μ₀(B) for Borel B. So μ̄₀- and μ₀-integrals of Borel strongly measurable integrands agree (SimonGMT integral_radonCaratheodoryMeasure, proved via integral_trim and radonCaratheodoryMeasure_trim).
Hence L(f) = ∫_X ⟨f, ν₂⟩ dμ₀.

7. Conclusion. μ := μ₀ and ν := ν₂ satisfy every claim:
- μ is a Borel measure, finite on compact sets (step 3);
- ν is strongly measurable (step 4);
- |ν| = 1 μ-a.e. (step 5);
- L(f) = ∫⟨f, ν⟩ dμ for every f ∈ C_c(X; ℝ^N) (step 6).

Formalization note: the SimonGMT declarations used above are in Poincare.SimonGMT.Chapter01.{VectorFunctionalEnvelope, RadonCaratheodoryIntegral, RadonPolarRepresentation}, built in the pinned package. Adding `import Poincare.SimonGMT.Chapter01.RadonPolarRepresentation` makes all of them available.

## Key steps

1. The local bound on L is SimonGMT IsLocallyBoundedCcFunctional L, the hypothesis of Simon 4.14.
2. simon_theorem_4_14_caratheodory gives the regular Borel measure μ₀ = vectorFunctionalEnvelopeMeasure L and a Carathéodory-measurable ν₁. It has |ν₁| = 1 μ̄₀-a.e. and L(f) = ∫⟨f, ν₁⟩dμ̄₀ with μ̄₀ = radonCaratheodoryMeasure μ₀.
3. μ₀ is finite on compacts. The sibling theorem gaussGreenRep_riesz_caratheodory_borel_version gives a Borel strongly measurable ν₂ with ν₁ = ν₂ μ₀-a.e.
4. μ̄₀ and μ₀ agree on all sets, so they have the same a.e. statements: |ν₂| = 1 μ₀-a.e. and ν₁ = ν₂ μ̄₀-a.e.
5. For f ∈ C_c(X; ℝ^N), ∫⟨f, ν₁⟩dμ̄₀ = ∫⟨f, ν₂⟩dμ̄₀ = ∫⟨f, ν₂⟩dμ₀ because the last integrand is Borel strongly measurable. Take μ := μ₀, ν := ν₂.

## Reference use

### local-project

Queries:
- `diff local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean workspaces/gmt-ch03/GMT/Ch03/Contract.lean (identical); grep -n -i 'unfaithful|Riesz|4.14|### 11' project/GMT/Ch03/README.md`
- `python3 transitive import scan of Poincare.SimonGMT.Chapter02.BV + Chapter03.Rectifiable (Submission imports): only Chapter01.{Basic,Hausdorff,MetricCriterion}; ls simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter01 (RadonPolarRepresentation.olean present)`
- `grep -n 'theorem simon_theorem_4_14' -A 60 Poincare/SimonGMT/Chapter01/*.lean`
- `sed -n 1,135p RadonPolarRepresentation.lean; sed -n 1,120p,200,280p VectorFunctionalEnvelope.lean; cat RadonCaratheodoryIntegral.lean`
- `grep -rn 'exists_borel_subset_mod_null|isOpenSigmaFinite_of_finite_compacts|measure_toOuterMeasure_isBorelRegular|def IsOpenSigmaFinite|def IsBorelRegularOuterMeasure|structure IsRadonOuterMeasure|toCaratheodoryMeasure_apply_all' Poincare/SimonGMT; grep -n 'IsCaratheodoryMeasurable' Chapter01/Basic.lean`
- `rg -n 'NullMeasurable.aemeasurable|theorem integral_map|aestronglyMeasurable_map_iff|ae_map_iff|subtype_coe|measurable_extend|map_apply' mathlib/Mathlib/MeasureTheory/{Measure/AEMeasurable,Integral/Bochner/Basic,Function/StronglyMeasurable/AEStronglyMeasurable,MeasurableSpace/Embedding,Measure/Map}.lean`
- `rg -n 'continuous_extend_one|continuous_extend_zero|extend_zero|extendByZero|continuous_of_mulTSupport' mathlib/Mathlib/Topology; sed -n 280,365p Mathlib/Topology/Algebra/Support.lean`
- `rg -n 'theorem IsOpen.locallyCompactSpace|sigmaCompactSpace_of_locallyCompact_secondCountable|instance Subtype.borelSpace|theorem Subtype.isCompact_iff' mathlib/Mathlib`
- `sed -n 1640,1760p book/chapter-01.txt (Thm 4.14 at line 1654); sed -n 480,500p book/chapter-02.txt`
- `sed -n 1,80p,520,570p verifier/gmt-compare.py; cat verifier/lean_contract.py (child_modules, contract_scope, validate_lean_statement)`
- `python3: lean_contract.validate_lean_statement on the 4 statements; grep -rl candidate lean_names over the run directory; dag.json lean_name scan`
- `lake env lean /tmp/riesz_decomp/gen/ChallengeCheck.lean (exact NodeChallenge forms, pp.explicit #check, assembly from A2,B,C, #print axioms)`
- `lake env lean /tmp/riesz_decomp/gen/ProofCheck.lean (Submission-style proofs of the 4 children and the parent, exact Submission.X checks, #print axioms)`
- `WebSearch: Evans Gariepy vector-valued Riesz representation §1.8; Folland Proposition 2.12 completion-measurable functions a.e. equal measurable`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/AEMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonCaratheodoryIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonOuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RegularityCompletion.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-gauss-green-a1-riesz-on-open-a1/parent-child-handoff.json`

Snapshot state: project d09bc8a with Contract.lean identical to the workspace contract, Mathlib 25730c7c, pinned simongmt. No declaration proves the selected statement or any of the four child statements.

SimonGMT supplies the following:
- Simon 4.14 only in Carathéodory form: simon_theorem_4_14_caratheodory, with vectorFunctionalEnvelopeMeasure (Regular), IsLocallyBoundedCcFunctional, radonCaratheodoryMeasure_apply, ae_radonCaratheodoryMeasure_iff and integral_radonCaratheodoryMeasure (used by child riesz_sigma_compact).
- The Borel-regularity tools measure_toOuterMeasure_isBorelRegular, isOpenSigmaFinite_of_finite_compacts and IsBorelRegularOuterMeasure.exists_borel_subset_mod_null (child caratheodory_borel_version). IsCaratheodoryMeasurable is an abbrev for Mathlib's OuterMeasure.IsCaratheodory.
- These modules are not imported by GMT.Ch03.Submission, but their oleans are built. A child proof may add `import Poincare.SimonGMT.Chapter01.RadonPolarRepresentation`, as earlier proved nodes added SimonGMT imports. The frozen statements use only Mathlib notions, so they elaborate with or without that import.
- README section 11 flags only Chapter03.FinitePerimeterRepresentation (not used). No SimonGMT Chapter01 Riesz definition is marked unfaithful.

Mathlib supplies the following:
- Zero extension from an open set: HasCompactSupport.continuous_extend_zero, tsupport_extend_zero_subset, extend_zero and HasCompactSupport.intro (child zero_extension_functional).
- Push-forward: MeasurableEmbedding.subtype_coe, map_apply (valid on all sets), ae_map_iff, aestronglyMeasurable_map_iff and integral_map (child pushforward_from_subset).
- NullMeasurable.aemeasurable (child caratheodory_borel_version).
- For the parent assembly: IsOpen.locallyCompactSpace, the instance sigmaCompactSpace_of_locallyCompact_secondCountable, and Subtype.borelSpace.

No match: Mathlib and SimonGMT have no Riesz theorem with a Borel unit field on σ-compact spaces and no ambient push-forward of a Riesz pair from an open subset. These are therefore supplied as children.

Checks run:
- All four frozen statements pass validate_lean_statement and elaborate in the exact NodeChallenge form.
- The assembly A2 + B + C ⇒ parent compiles.
- Complete Submission-style proofs of all four children and the parent compile with only propext, Classical.choice and Quot.sound.
- Public references: Simon Ch. 1 Thm 4.14 (chapter-01.txt 1654-1663) and Ch. 2 (2.1)-(2.2) (chapter-02.txt 485-496); Evans–Gariepy §1.8; Folland Prop. 2.12.
