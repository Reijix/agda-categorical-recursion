open import Categories.Category.Core
open import Categories.Functor using (Endofunctor; Functor)
open import Categories.Object.Initial using (Initial)
open import Categories.Category.Construction.F-Algebras
open import Categories.Functor.Algebra using (F-Algebra; F-Algebra-Morphism)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.BinaryProducts using (BinaryProducts)

import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

module Functor.Coalgebra.Corecursion.Primitive {o ℓ e} {C : Category o ℓ e} (cartesian : Cartesian C) {F : Endofunctor C} (initial : Initial (F-Algebras F)) where
  open Category C
  open Cartesian cartesian
  open BinaryProducts products
  open Initial initial
  open F-Algebra ⊥ using () renaming (A to μF; α to inF)
  private
    module F = Functor F
  open HomReasoning
  open Equiv
  open M C
  open MR C
  open F using (F₀; F₁)

  open import Functor.Algebra.Recursion initial

  abstract
    ⦉_⦊ : ∀ {X} → (F₀ (X × μF) ⇒ X) → (μF ⇒ X)
    ⦉_⦊ {X} φ = π₁ ∘ ⦅ ⟨ φ , inF ∘ F₁ π₂ ⟩ ⦆

    para-cancel : ∀ {X} {φ : F₀ (X × μF) ⇒ X} → ⦉ φ ⦊ ∘ inF ≈ φ ∘ F₁ ⟨ ⦉ φ ⦊ , id ⟩
    para-cancel {X} {φ} = begin 
      (π₁ ∘ ⦅ ⟨ φ , inF ∘ F₁ π₂ ⟩ ⦆) ∘ inF                  ≈⟨ pullʳ cata-cancel ⟩ 
      π₁ ∘ ⟨ φ , inF ∘ F₁ π₂ ⟩ ∘ F₁ ⦅ ⟨ φ , inF ∘ F₁ π₂ ⟩ ⦆ ≈⟨ pullˡ project₁ ⟩ 
      φ ∘ F₁ ⦅ ⟨ φ , inF ∘ F₁ π₂ ⟩ ⦆                        ≈˘⟨ refl⟩∘⟨ F.F-resp-≈ g-η ⟩ 
      φ ∘ F₁ ⟨ ⦉ φ ⦊ , π₂ ∘ ⦅ ⟨ φ , inF ∘ F₁ π₂ ⟩ ⦆ ⟩       ≈˘⟨ refl⟩∘⟨ (F.F-resp-≈ (⟨⟩-cong₂ refl (cata-fusion project₂))) ⟩ 
      φ ∘ F₁ ⟨ ⦉ φ ⦊ , ⦅ inF ⦆ ⟩                            ≈⟨ refl⟩∘⟨ F.F-resp-≈ (⟨⟩-cong₂ refl cata-refl) ⟩
      φ ∘ F₁ ⟨ ⦉ φ ⦊ , id ⟩                                 ∎

    para-unique : ∀ {X} {φ : F₀ (X × μF) ⇒ X} {f : μF ⇒ X} → f ∘ inF ≈ φ ∘ F₁ ⟨ f , id ⟩ → ⦉ φ ⦊ ≈ f
    para-unique {X} {φ} {f} f-cancel = begin 
      π₁ ∘ ⦅ ⟨ φ , inF ∘ F₁ π₂ ⟩ ⦆ ≈⟨ refl⟩∘⟨ cata-unique helper ⟩ 
      π₁ ∘ ⟨ f , id ⟩              ≈⟨ project₁ ⟩ 
      f                            ∎
      where
      helper : ⟨ f , id ⟩ ∘ inF ≈ ⟨ φ , inF ∘ F₁ π₂ ⟩ ∘ F₁ ⟨ f , id ⟩
      helper = begin 
        ⟨ f , id ⟩ ∘ inF                    ≈⟨ ⟨⟩∘ ○ ⟨⟩-cong₂ f-cancel identityˡ ⟩ 
        ⟨ φ ∘ F₁ ⟨ f , id ⟩ , inF ⟩         ≈˘⟨ ⟨⟩∘ ○ ⟨⟩-cong₂ refl (cancelʳ (sym F.homomorphism ○ F.F-resp-≈ project₂ ○ F.identity)) ⟩ 
        ⟨ φ , inF ∘ F₁ π₂ ⟩ ∘ F₁ ⟨ f , id ⟩ ∎

    para-refl : ⦉ inF ∘ F₁ π₁ ⦊ ≈ id
    para-refl = para-unique (id-comm-sym ○ sym (pullʳ (sym F.homomorphism ○ F.F-resp-≈ project₁ ○ F.identity)))

    para-fusion : ∀ {X Y} {φ : F₀ (X × μF) ⇒ X} {ψ : F₀ (Y × μF) ⇒ Y} {f : X ⇒ Y} → f ∘ φ ≈ ψ ∘ F₁ (f ⁂ id) → ⦉ ψ ⦊ ≈ f ∘ ⦉ φ ⦊
    para-fusion {X} {Y} {φ} {ψ} {f} eq = para-unique (begin 
      (f ∘ ⦉ φ ⦊) ∘ inF                   ≈⟨ pullʳ para-cancel ⟩ 
      f ∘ φ ∘ F₁ ⟨ ⦉ φ ⦊ , id ⟩           ≈⟨ extendʳ eq ⟩ 
      ψ ∘ F₁ (f ⁂ id) ∘ F₁ ⟨ ⦉ φ ⦊ , id ⟩ ≈⟨ refl⟩∘⟨ (sym F.homomorphism ○ F.F-resp-≈ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ refl identity²)) ⟩ 
      ψ ∘ F₁ ⟨ f ∘ ⦉ φ ⦊ , id ⟩           ∎)

    para-cata : ∀ {X} (φ : F₀ X ⇒ X) → ⦉ φ ∘ F₁ π₁ ⦊ ≈ ⦅ φ ⦆
    para-cata {X} φ = para-unique (begin 
      ⦅ φ ⦆ ∘ inF                     ≈⟨ cata-cancel ⟩ 
      φ ∘ F₁ ⦅ φ ⦆                    ≈˘⟨ pullʳ (sym F.homomorphism ○ F.F-resp-≈ project₁) ⟩ 
      (φ ∘ F₁ π₁) ∘ F₁ ⟨ ⦅ φ ⦆ , id ⟩ ∎)

    para-any : ∀ {X} (f : μF ⇒ X) → ⦉ f ∘ inF ∘ F₁ π₂ ⦊ ≈ f
    para-any {X} f = para-unique (begin 
      f ∘ inF                           ≈˘⟨ pullʳ (cancelʳ (sym F.homomorphism ○ F.F-resp-≈ project₂ ○ F.identity)) ⟩ 
      (f ∘ inF ∘ F₁ π₂) ∘ F₁ ⟨ f , id ⟩ ∎)

    -- Lambek's Lemma:

    outF : μF ⇒ F₀ μF
    outF = ⦉ F₁ π₂ ⦊

    lambek : F₀ μF ≅ μF
    lambek = record 
      { from = inF 
      ; to = outF 
      ; iso = record 
        { isoˡ = para-cancel ○ sym F.homomorphism ○ F.F-resp-≈ project₂ ○ F.identity 
        ; isoʳ = begin 
          inF ∘ outF      ≈˘⟨ para-fusion (sym (pullʳ (sym F.homomorphism ○ F.F-resp-≈ (project₂ ○ identityˡ)))) ⟩
          ⦉ inF ∘ F₁ π₂ ⦊ ≈⟨ para-unique helper ⟩ 
          ⦉ inF ∘ F₁ π₁ ⦊ ≈⟨ para-refl ⟩ 
          id              ∎
        } 
      }
      where
      helper : ⦉ inF ∘ F₁ π₁ ⦊ ∘ inF ≈ (inF ∘ F₁ π₂) ∘ F₁ ⟨ ⦉ inF ∘ F₁ π₁ ⦊ , id ⟩
      helper = elimˡ para-refl ○ sym (cancelʳ (sym F.homomorphism ○ F.F-resp-≈ project₂ ○ F.identity))
