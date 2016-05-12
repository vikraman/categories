{-# OPTIONS --universe-polymorphism #-}
module Categories.Groupoid where

open import Level
open import Data.Product

open import Categories.Category
open import Categories.Product renaming (Product to ℙroduct)
import Categories.Morphisms as M

record Groupoid {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  private module C = Category C
  open C using (_⇒_) 

  open M C

  field
    _⁻¹  : ∀ {A B} → (A ⇒ B) → (B ⇒ A)
    .iso : ∀ {A B} {f : A ⇒ B} → Iso f (f ⁻¹)

Product : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂} {ℂ₁ : Category o₁ ℓ₁ e₁} {ℂ₂ : Category o₂ ℓ₂ e₂}
        → Groupoid ℂ₁ → Groupoid ℂ₂ → Groupoid (ℙroduct ℂ₁ ℂ₂)
Product c₁ c₂ = record
         { _⁻¹ = λ {(x₁ , x₂) → Groupoid._⁻¹ c₁ x₁
                              , Groupoid._⁻¹ c₂ x₂}
         ; iso = record { isoˡ = M.Iso.isoˡ (Groupoid.iso c₁)
                               , M.Iso.isoˡ (Groupoid.iso c₂)
                        ; isoʳ = M.Iso.isoʳ (Groupoid.iso c₁)
                               , M.Iso.isoʳ (Groupoid.iso c₂) } }
