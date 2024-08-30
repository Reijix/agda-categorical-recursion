open import Categories.Category.Core
open import Categories.Functor using (Endofunctor; Functor)
open import Categories.Object.Terminal using (Terminal)
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Functor.Coalgebra using (F-Coalgebra; F-Coalgebra-Morphism)
open import Categories.Category.Cocartesian using (Cocartesian)

import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

module Functor.Algebra.Recursion.Primitive {o ℓ e} {C : Category o ℓ e} (cocartesian : Cocartesian C) {F : Endofunctor C} (terminal : Terminal (F-Coalgebras F)) where
  open Category C
  open Cocartesian cocartesian
  open Terminal terminal
  open F-Coalgebra ⊤ using () renaming (A to νF; α to outF)
  private
    module F = Functor F
  open HomReasoning
  open Equiv
  open M C
  open MR C
  open F using (F₀; F₁)

  open import Functor.Coalgebra.Corecursion terminal

  abstract
    -- sadly no fitting unicode symbol
    [⟨_⟩] : ∀ {X} → (X ⇒ F₀ (X + νF)) → (X ⇒ νF)
    [⟨_⟩] {X} φ = ⟦ [ φ , F₁ i₂ ∘ outF ] ⟧ ∘ i₁

    apo-cancel : ∀ {X} {φ : X ⇒ F₀ (X + νF)} → outF ∘ [⟨ φ ⟩] ≈ F₁ [ [⟨ φ ⟩] , id ] ∘ φ
    apo-cancel {X} {φ} = begin 
      outF ∘ ⟦ [ φ , F₁ i₂ ∘ outF ] ⟧ ∘ i₁                    ≈⟨ extendʳ ana-cancel ⟩ 
      F₁ ⟦ [ φ , F₁ i₂ ∘ outF ] ⟧ ∘ [ φ , F₁ i₂ ∘ outF ] ∘ i₁ ≈⟨ refl⟩∘⟨ inject₁ ⟩ 
      F₁ ⟦ [ φ , F₁ i₂ ∘ outF ] ⟧ ∘ φ                         ≈˘⟨ (F.F-resp-≈ +-g-η) ⟩∘⟨refl ⟩ 
      F₁ [ [⟨ φ ⟩] , ⟦ [ φ , F₁ i₂ ∘ outF ] ⟧ ∘ i₂ ] ∘ φ      ≈˘⟨ (F.F-resp-≈ ([]-cong₂ refl (ana-fusion inject₂))) ⟩∘⟨refl ⟩ 
      F₁ [ [⟨ φ ⟩] , ⟦ outF ⟧ ] ∘ φ                           ≈⟨ F.F-resp-≈ ([]-cong₂ refl ana-refl) ⟩∘⟨refl ⟩ 
      F₁ [ [⟨ φ ⟩] , id ] ∘ φ                                 ∎

    apo-unique : ∀ {X} {φ : X ⇒ F₀ (X + νF)} {f : X ⇒ νF} → outF ∘ f ≈ F₁ [ f , id ] ∘ φ → [⟨ φ ⟩] ≈ f
    apo-unique {X} {φ} {f} f-cancel = begin 
      ⟦ [ φ , F₁ i₂ ∘ outF ] ⟧ ∘ i₁ ≈⟨ (ana-unique helper) ⟩∘⟨refl ⟩ 
      [ f , id ] ∘ i₁               ≈⟨ inject₁ ⟩ 
      f                             ∎
      where
      helper : outF ∘ [ f , id ] ≈ F₁ [ f , id ] ∘ [ φ , F₁ i₂ ∘ outF ]
      helper = begin 
        outF ∘ [ f , id ]                    ≈⟨ ∘[] ○ []-cong₂ f-cancel identityʳ ⟩ 
        [ (F₁ [ f , id ] ∘ φ) , outF ]       ≈˘⟨ ∘[] ○ []-cong₂ refl (cancelˡ (sym F.homomorphism ○ F.F-resp-≈ inject₂ ○ F.identity)) ⟩ 
        F₁ [ f , id ] ∘ [ φ , F₁ i₂ ∘ outF ] ∎

    apo-refl : [⟨ F₁ i₁ ∘ outF ⟩] ≈ id
    apo-refl = apo-unique (id-comm ○ sym (pullˡ (sym F.homomorphism ○ F.F-resp-≈ inject₁ ○ F.identity)))

    apo-fusion : ∀ {X Y} {φ : X ⇒ F₀ (X + νF)} {ψ : Y ⇒ F₀ (Y + νF)} {f : X ⇒ Y} → ψ ∘ f ≈ F₁ (f +₁ id) ∘ φ → [⟨ φ ⟩] ≈ [⟨ ψ ⟩] ∘ f
    apo-fusion {X} {Y} {φ} {ψ} {f} eq = apo-unique (begin 
      outF ∘ [⟨ ψ ⟩] ∘ f                     ≈⟨ extendʳ apo-cancel ⟩ 
      F₁ [ [⟨ ψ ⟩] , id ] ∘ ψ ∘ f            ≈⟨ refl⟩∘⟨ eq ⟩ 
      F₁ [ [⟨ ψ ⟩] , id ] ∘ F₁ (f +₁ id) ∘ φ ≈⟨ pullˡ (sym F.homomorphism ○ F.F-resp-≈ ([]∘+₁ ○ []-cong₂ refl identity²)) ⟩ 
      F₁ [ [⟨ ψ ⟩] ∘ f , id ] ∘ φ            ∎)

    apo-ana : ∀ {X} (φ : X ⇒ F₀ X) → [⟨ F₁ i₁ ∘ φ ⟩] ≈ ⟦ φ ⟧
    apo-ana {X} φ  = apo-unique (begin 
      outF ∘ ⟦ φ ⟧                  ≈⟨ ana-cancel ⟩ 
      F₁ ⟦ φ ⟧ ∘ φ                  ≈˘⟨ pullˡ (sym F.homomorphism ○ F.F-resp-≈ inject₁) ⟩ 
      F₁ [ ⟦ φ ⟧ , id ] ∘ F₁ i₁ ∘ φ ∎)

    apo-any : ∀ {X} (f : X ⇒ νF) → [⟨ F₁ i₂ ∘ outF ∘ f ⟩] ≈ f
    apo-any {X} f = apo-unique (begin 
      outF ∘ f                         ≈˘⟨ cancelˡ (sym F.homomorphism ○ F.F-resp-≈ inject₂ ○ F.identity) ⟩ 
      F₁ [ f , id ] ∘ F₁ i₂ ∘ outF ∘ f ∎)

    -- Lambek's Lemma:
    inF : F₀ νF ⇒ νF
    inF = [⟨ F₁ i₂ ⟩]

    lambek : F₀ νF ≅ νF
    lambek = record 
      { from = inF 
      ; to = outF 
      ; iso = record 
        { isoˡ = apo-cancel ○ sym F.homomorphism ○ F.F-resp-≈ inject₂ ○ F.identity 
        ; isoʳ = begin 
          inF ∘ outF ≈˘⟨ apo-fusion (sym (pullˡ (sym F.homomorphism ○ F.F-resp-≈ (inject₂ ○ identityʳ)))) ⟩ 
          [⟨ F₁ i₂ ∘ outF ⟩] ≈⟨ apo-unique helper ⟩ 
          [⟨ F₁ i₁ ∘ outF ⟩] ≈⟨ apo-refl ⟩ 
          id ∎
        } 
      }
      where
      helper : outF ∘ [⟨ F₁ i₁ ∘ outF ⟩] ≈ F₁ [ [⟨ F₁ i₁ ∘ outF ⟩] , id ] ∘ F₁ i₂ ∘ outF
      helper = elimʳ apo-refl ○ sym (cancelˡ (sym F.homomorphism ○ F.F-resp-≈ inject₂ ○ F.identity))

