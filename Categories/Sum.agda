module Categories.Sum where

open import Level
open import Data.Empty
open import Data.Sum

open import Categories.Category

Sum : ∀ {o ℓ e} (C D : Category o ℓ e) → Category o ℓ e
Sum C D = record
  { Obj = C.Obj ⊎ D.Obj
  ; _⇒_ = λ { (inj₁ c₁) (inj₁ c₂) → C._⇒_ c₁ c₂
            ; (inj₁ c) (inj₂ d) → Lift ⊥
            ; (inj₂ d) (inj₁ c) → Lift ⊥
            ; (inj₂ d₁) (inj₂ d₂) → D._⇒_ d₁ d₂
            }
  ; _≡_ = λ { {inj₁ _} {inj₁ _} → C._≡_
            ; {inj₁ x} {inj₂ y} (lift ()) (lift ())
            ; {inj₂ _} {inj₁ _} (lift ()) (lift ())
            ; {inj₂ _} {inj₂ _} → D._≡_
            }
  ; _∘_ = λ { {inj₁ _} {inj₁ _} {inj₁ _} → C._∘_
            ; {inj₁ _} {inj₁ _} {inj₂ _} (lift ()) _
            ; {inj₁ _} {inj₂ _} {inj₁ _} _ (lift ())
            ; {inj₁ _} {inj₂ _} {inj₂ _} _ (lift ())
            ; {inj₂ _} {inj₁ _} {inj₁ _} _ (lift ())
            ; {inj₂ _} {inj₁ _} {inj₂ _} (lift ()) _
            ; {inj₂ _} {inj₂ _} {inj₁ _} (lift ()) _
            ; {inj₂ _} {inj₂ _} {inj₂ _} → D._∘_
            }
  ; id = λ { {inj₁ _} → C.id ; {inj₂ _} → D.id }
  ; assoc = λ { {inj₁ _} {inj₁ _} {inj₁ _} {inj₁ _} → C.assoc
              ; {inj₁ _} {inj₁ _} {inj₁ _} {inj₂ _} {_} {_} {lift ()}
              ; {inj₁ _} {inj₁ _} {inj₂ _} {inj₁ _} {_} {lift ()} {_}
              ; {inj₁ _} {inj₁ _} {inj₂ _} {inj₂ _} {_} {lift ()} {_}
              ; {inj₁ _} {inj₂ _} {inj₁ _} {inj₁ _} {lift ()} {_} {_}
              ; {inj₁ _} {inj₂ _} {inj₁ _} {inj₂ _} {lift ()} {_} {_}
              ; {inj₁ _} {inj₂ _} {inj₂ _} {inj₁ _} {lift ()} {_} {_}
              ; {inj₁ _} {inj₂ _} {inj₂ _} {inj₂ _} {lift ()} {_} {_}
              ; {inj₂ _} {inj₁ _} {inj₁ _} {inj₁ _} {lift ()} {_} {_}
              ; {inj₂ _} {inj₁ _} {inj₁ _} {inj₂ _} {lift ()} {_} {_}
              ; {inj₂ _} {inj₁ _} {inj₂ _} {inj₁ _} {lift ()} {_} {_}
              ; {inj₂ _} {inj₁ _} {inj₂ _} {inj₂ _} {lift ()} {_} {_}
              ; {inj₂ _} {inj₂ _} {inj₁ _} {inj₁ _} {_} {lift ()} {_}
              ; {inj₂ _} {inj₂ _} {inj₁ _} {inj₂ _} {_} {lift ()} {_}
              ; {inj₂ _} {inj₂ _} {inj₂ _} {inj₁ _} {_} {_} {lift ()}
              ; {inj₂ _} {inj₂ _} {inj₂ _} {inj₂ _} → D.assoc
              }
  ; identityˡ = λ { {inj₁ _} {inj₁ _} → C.identityˡ
                  ; {inj₁ _} {inj₂ _} {lift ()}
                  ; {inj₂ _} {inj₁ _} {lift ()}
                  ; {inj₂ _} {inj₂ _} → D.identityˡ
                  }
  ; identityʳ = λ { {inj₁ _} {inj₁ _} → C.identityʳ
                  ; {inj₁ _} {inj₂ _} {lift ()}
                  ; {inj₂ _} {inj₁ _} {lift ()}
                  ; {inj₂ _} {inj₂ _} → D.identityʳ
                  }
  ; equiv = λ { {inj₁ _} {inj₁ _} → C.equiv
              ; {inj₁ _} {inj₂ _} → record { refl = λ { {lift ()} }
                                           ; sym = λ { {lift ()} }
                                           ; trans = λ { {lift ()} }
                                           }
              ; {inj₂ _} {inj₁ _} → record { refl = λ { {lift ()} }
                                           ; sym = λ { {lift ()} }
                                           ; trans = λ { {lift ()} }
                                           }
              ; {inj₂ _} {inj₂ _} → D.equiv
              }
  ; ∘-resp-≡ = λ { {inj₁ _} {inj₁ _} {inj₁ _} → C.∘-resp-≡
                 ; {inj₁ _} {inj₁ _} {inj₂ _} {lift ()} {_} {_}
                 ; {inj₁ _} {inj₂ _} {inj₁ _} {lift ()} {_} {_}
                 ; {inj₁ _} {inj₂ _} {inj₂ _} {_} {_} {lift ()}
                 ; {inj₂ _} {inj₁ _} {inj₁ _} {_} {_} {lift ()}
                 ; {inj₂ _} {inj₁ _} {inj₂ _} {lift ()} {_} {_}
                 ; {inj₂ _} {inj₂ _} {inj₁ _} {lift ()} {_} {_}
                 ; {inj₂ _} {inj₂ _} {inj₂ _} → D.∘-resp-≡
                 }
  }
  where
  module C = Category C
  module D = Category D
