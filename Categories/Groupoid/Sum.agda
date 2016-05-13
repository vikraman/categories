{-# OPTIONS --universe-polymorphism #-}

module Categories.Groupoid.Sum where

open import Level
open import Data.Sum

open import Categories.Category
open import Categories.Groupoid
open import Categories.Morphisms
import Categories.Sum as SumC

Sum : ∀ {o ℓ e} {C D : Category o ℓ e} → Groupoid C → Groupoid D → Groupoid (SumC.Sum C D)
Sum C D = record
  { _⁻¹ = λ { {inj₁ _} {inj₁ _} → C._⁻¹
            ; {inj₁ x} {inj₂ y} (lift ())
            ; {inj₂ y} {inj₁ x} (lift ())
            ; {inj₂ y} {inj₂ y₁} → D._⁻¹
            }
  ; iso = λ { {inj₁ _} {inj₁ _} → record { isoˡ = Iso.isoˡ C.iso ; isoʳ = Iso.isoʳ C.iso }
            ; {inj₁ x} {inj₂ y} {lift ()}
            ; {inj₂ y} {inj₁ x} {lift ()}
            ; {inj₂ y} {inj₂ y₁} → record { isoˡ = Iso.isoˡ D.iso ; isoʳ = Iso.isoʳ D.iso }
            }
  }
  where
  module C = Groupoid C
  module D = Groupoid D
