/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Algebraic.AnalyticFactor
public import DiskRigidity.Algebraic.RealComponent

/-!
# Absolute irreducibility from a regular real-analytic arc

A real irreducible equation containing a real-analytic arc is absolutely
irreducible as soon as one point of that arc is regular.  Analytic factor
selection chooses a complex component containing the whole arc.  At the
regular real point this component must agree with its conjugate, so it
descends to a real divisor of the original real irreducible equation.
-/

@[expose] public section

namespace DiskRigidity.Algebraic

namespace RealAnalyticIrreducibility

open MvPolynomial Set

/-- A real irreducible hypersurface with a regular real-analytic arc remains
irreducible after extension of scalars to `ℂ`. -/
theorem irreducible_map_real_of_regular_analytic_arc
    {N : ℕ} {Q : MvPolynomial (Fin N) ℝ}
    (hQirr : Irreducible Q)
    (U : Set ℝ) (γ : ℝ → Fin N → ℝ)
    (hU : U.Nonempty) (hpre : IsPreconnected U)
    (hγ : ∀ i, AnalyticOnNhd ℝ (fun t ↦ γ t i) U)
    (hzero : ∀ t ∈ U, MvPolynomial.eval (γ t) Q = 0)
    (t₀ : ℝ) (ht₀ : t₀ ∈ U)
    (hregular : ProjectiveDual.RegularAt Q (γ t₀)) :
    Irreducible (MvPolynomial.map (algebraMap ℝ ℂ) Q) := by
  let Qc := MvPolynomial.map (algebraMap ℝ ℂ) Q
  let γc : ℝ → Fin N → ℂ := fun t i ↦ γ t i
  have hQc0 : Qc ≠ 0 := by
    intro hmap
    apply hQirr.ne_zero
    apply MvPolynomial.map_injective (algebraMap ℝ ℂ)
      Complex.ofReal_injective
    simpa only [map_zero] using hmap
  have hγc : ∀ i, AnalyticOnNhd ℝ (fun t ↦ γc t i) U := by
    intro i
    change AnalyticOnNhd ℝ
      (Complex.ofRealCLM ∘ fun t ↦ γ t i) U
    exact Complex.ofRealCLM.comp_analyticOnNhd (hγ i)
  have hzeroC : ∀ t ∈ U, MvPolynomial.eval (γc t) Qc = 0 := by
    intro t ht
    change MvPolynomial.eval (fun i ↦ (γ t i : ℂ))
      (MvPolynomial.map (algebraMap ℝ ℂ) Q) = 0
    rw [RealComponent.eval_map_real]
    simpa using congrArg Complex.ofReal (hzero t ht)
  obtain ⟨P, hPirr, hPdiv, hPzero⟩ :=
    AnalyticFactor.exists_irreducible_factor_zero_on_analytic_arc
      hQc0 γc hU hpre hγc hzeroC
  have hassociated :
      Associated P (RealComponent.conjugatePolynomial P) := by
    apply RealComponent.associated_conjugatePolynomial_of_common_regular_real_point
      (P := Qc) (F := P) (x := γc t₀)
    · exact RealComponent.conjugatePolynomial_map_real Q
    · exact hPirr
    · exact hPdiv
    · intro i
      exact Complex.conj_ofReal _
    · exact hPzero t₀ ht₀
    · exact RealComponent.regularAt_map_real hregular
  obtain ⟨F, hFirr, hmapFirr, hmapFassociated⟩ :=
    RealComponent.exists_real_irreducible_associate_of_associated_conjugate
      hPirr hassociated
  have hmapFdiv : MvPolynomial.map (algebraMap ℝ ℂ) F ∣ Qc :=
    hmapFassociated.dvd.trans hPdiv
  have hFdiv : F ∣ Q := by
    exact RealComponent.dvd_of_map_dvd_map_real_complex hmapFdiv
  have hFQassociated : Associated F Q :=
    ((hQirr.dvd_iff.mp hFdiv).resolve_left hFirr.not_isUnit).symm
  have hmapFQassociated : Associated
      (MvPolynomial.map (algebraMap ℝ ℂ) F) Qc :=
    hFQassociated.map (MvPolynomial.map (algebraMap ℝ ℂ))
  exact hmapFQassociated.irreducible hmapFirr

end RealAnalyticIrreducibility

end DiskRigidity.Algebraic
