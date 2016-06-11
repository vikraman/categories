{-# OPTIONS --universe-polymorphism #-}

module Categories.Groupoid.Product where

open import Data.Product

open import Categories.Category
open import Categories.Groupoid
open import Categories.Morphisms
import Categories.Product as ProductC

Product : ∀ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂} {ℂ₁ : Category o₁ ℓ₁ e₁} {ℂ₂ : Category o₂ ℓ₂ e₂}
        → Groupoid ℂ₁ → Groupoid ℂ₂ → Groupoid (ProductC.Product ℂ₁ ℂ₂)
Product c₁ c₂ = record
         { _⁻¹ = λ {(x₁ , x₂) → Groupoid._⁻¹ c₁ x₁
                              , Groupoid._⁻¹ c₂ x₂}
         ; iso = record { isoˡ = Iso.isoˡ (Groupoid.iso c₁)
                               , Iso.isoˡ (Groupoid.iso c₂)
                        ; isoʳ = Iso.isoʳ (Groupoid.iso c₁)
                               , Iso.isoʳ (Groupoid.iso c₂) } }
