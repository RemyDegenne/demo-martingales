/-
 - Created in 2025 by Rémy Degenne
-/

import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option pp.rawOnError true

set_option verso.exampleProject "src/"

set_option verso.exampleModule "Martingales.Martingales"

#doc (Manual) "Martingales" =>
%%%
htmlSplit := .never
%%%

# Stochastic processes, filtrations, and martingales

We define a measure space {anchorTerm Variables}`Ω`, with a probability mesure {anchorTerm Variables}`P : Measure Ω`.

```anchor Variables
variable {Ω : Type} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]
```

Let then `X` be a stochastic process indexed by `ℕ`: a function `ℕ → Ω → E`.
Here `E` is a Banach space, a complete normed space (that's what the martingale property needs).
We will often need a measurability condition on `X` in lemmas, but we don't add it yet.

```anchor Variables2
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mE : MeasurableSpace E} {X : ℕ → Ω → E}
```

A filtration is a monotone family of sub-σ-algebras indexed by `ℕ`.
Remember that you can learn about a definition by hovering over it, or by using ctrl-click to go to
its declaration.
```anchor Filtration
variable {𝓕 : Filtration ℕ mΩ}

example : ∀ n, 𝓕 n ≤ mΩ := Filtration.le 𝓕

example {i j : ℕ} (hij : i ≤ j) : 𝓕 i ≤ 𝓕 j := Filtration.mono 𝓕 hij
```

If `X` is a martingale, then it is adapted to the filtration, which means that for all `n`,
`X n` is (strongly) measurable with respect to {anchorTerm Filtration}`𝓕 n`.
```anchor Martingale
example (hX : Martingale X 𝓕 P) : Adapted 𝓕 X := hX.adapted

example (hX : Martingale X 𝓕 P) (n : ℕ) : StronglyMeasurable[𝓕 n] (X n) := hX.adapted n

example [BorelSpace E] (hX : Martingale X 𝓕 P) (n : ℕ) : Measurable[𝓕 n] (X n) :=
  (hX.adapted n).measurable

/-- A martingale satisfies the following equality: for all `i ≤ j`, the conditional expectation of
`X j` with respect to `𝓕 i` is equal to `X i`. -/
example (hX : Martingale X 𝓕 P) {i j : ℕ} (hij : i ≤ j) : P[X j | 𝓕 i] =ᵐ[P] X i :=
  hX.condExp_ae_eq hij

/-- For a submartingale, the conditional expectation of `Y j` with respect to `𝓕 i` is greater than
or equal to `Y i`. -/
example {Y : ℕ → Ω → ℝ} (hX : Submartingale Y 𝓕 P) {i j : ℕ} (hij : i ≤ j) :
    Y i ≤ᵐ[P] P[Y j | 𝓕 i] :=
  hX.ae_le_condExp hij
```

*Almost everywhere martingale convergence theorem*: An L¹-bounded submartingale converges
almost everywhere to a `⨆ n, ℱ n`-measurable function.

```anchor AeTendstoLimitProcess
theorem ae_tendsto_limitProcess {Y : ℕ → Ω → ℝ} (hY : Submartingale Y 𝓕 P)
    {R : ℝ≥0} (hbdd : ∀ n, eLpNorm (Y n) 1 P ≤ R) :
    ∀ᵐ ω ∂P, Tendsto (Y · ω) atTop (𝓝 (𝓕.limitProcess Y P ω)) := by
  classical
  suffices ∃ g, StronglyMeasurable[⨆ n, 𝓕 n] g ∧ ∀ᵐ ω ∂P, Tendsto (Y · ω) atTop (𝓝 (g ω)) by
    rw [Filtration.limitProcess, dif_pos this]
    exact (Classical.choose_spec this).2
  set g' : Ω → ℝ := fun ω ↦ if h : ∃ c, Tendsto (Y · ω) atTop (𝓝 c) then h.choose else 0
  have hle : ⨆ n, 𝓕 n ≤ mΩ := sSup_le fun m ⟨n, hn⟩ ↦ hn ▸ 𝓕.le _
  have hg' : ∀ᵐ ω ∂P.trim hle, Tendsto (Y · ω) atTop (𝓝 (g' ω)) := by
    filter_upwards [hY.exists_ae_trim_tendsto_of_bdd hbdd] with ω hω
    simp_rw [g', dif_pos hω]
    exact hω.choose_spec
  have hg'm : AEStronglyMeasurable[⨆ n, 𝓕 n] g' (P.trim hle) :=
    (@aemeasurable_of_tendsto_metrizable_ae' _ _ (⨆ n, 𝓕 n) _ _ _ _ _ _ _
      (fun n ↦ ((hY.stronglyMeasurable n).measurable.mono (le_sSup ⟨n, rfl⟩ : 𝓕 n ≤ ⨆ n, 𝓕 n)
        le_rfl).aemeasurable) hg').aestronglyMeasurable
  obtain ⟨g, hgm, hae⟩ := hg'm
  have hg : ∀ᵐ ω ∂P.trim hle, Tendsto (Y · ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hae, hg'] with ω hω hg'ω using hω ▸ hg'ω
  exact ⟨g, hgm, measure_eq_zero_of_trim_eq_zero hle hg⟩
```

# Stopping times

A stopping time with respect to a filtration indexed by `ℕ` is a random time {anchorTerm Variables3}`τ : Ω → ℕ∞` such that
for all `n`, the set `{ω | τ ω ≤ n}` is measurable with respect to {anchorTerm Filtration}`𝓕 n`.

```anchor Variables3
variable {τ : Ω → ℕ∞} (hτ : IsStoppingTime 𝓕 τ)

example (i : ℕ) : MeasurableSet[𝓕 i] {ω | τ ω ≤ i} := hτ.measurableSet_le i
```

*The optional stopping theorem* (fair game theorem): an adapted integrable process `Y`
is a submartingale if and only if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `Y` at `τ` has expectation smaller than its stopped value at `π`.
```anchor submartingale_iff_expected_stoppedValue_mono
theorem submartingale_iff_expected_stoppedValue_mono' {Y : ℕ → Ω → ℝ} (hadp : Adapted 𝓕 Y)
    (hint : ∀ i, Integrable (Y i) P) :
    Submartingale Y 𝓕 P ↔ ∀ τ π : Ω → ℕ∞, IsStoppingTime 𝓕 τ → IsStoppingTime 𝓕 π →
      τ ≤ π → (∃ N : ℕ, ∀ x, π x ≤ N) → P[stoppedValue Y τ] ≤ P[stoppedValue Y π] :=
  ⟨fun hf _ _ hτ hπ hle ⟨_, hN⟩ => hf.expected_stoppedValue_mono hτ hπ hle hN,
    submartingale_of_expected_stoppedValue_mono hadp hint⟩
```

The stopped process of a submartingale with respect to a stopping time is a submartingale.
```anchor Submartingale.stoppedProcess
protected theorem Submartingale.stoppedProcess {Y : ℕ → Ω → ℝ} (h : Submartingale Y 𝓕 P)
    (hτ : IsStoppingTime 𝓕 τ) :
    Submartingale (stoppedProcess Y τ) 𝓕 P := by
  rw [submartingale_iff_expected_stoppedValue_mono]
  · intro σ π hσ hπ hσ_le_π hπ_bdd
    simp_rw [stoppedValue_stoppedProcess]
    obtain ⟨n, hπ_le_n⟩ := hπ_bdd
    have hπ_top ω : π ω ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hπ_le_n ω)
    have hσ_top ω : σ ω ≠ ⊤ := ne_top_of_le_ne_top (hπ_top ω) (hσ_le_π ω)
    simp only [ne_eq, hσ_top, not_false_eq_true, ↓reduceIte, hπ_top, ge_iff_le]
    exact h.expected_stoppedValue_mono (hσ.min hτ) (hπ.min hτ)
      (fun ω => min_le_min (hσ_le_π ω) le_rfl) fun ω => (min_le_left _ _).trans (hπ_le_n ω)
  · exact Adapted.stoppedProcess_of_discrete h.adapted hτ
  · exact fun i =>
      h.integrable_stoppedValue ((isStoppingTime_const _ i).min hτ) fun ω => min_le_left _ _
```
