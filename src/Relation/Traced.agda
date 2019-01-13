open import Polynomial.Simple.AlmostCommutativeRing

module Relation.Traced {c ℓ} (base : AlmostCommutativeRing c ℓ) where

open import Data.Sum
open import Relation.Binary.Construct.Closure.Equivalence
open import Relation.Binary.Construct.Closure.Symmetric
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Data.String
open import Relation.Nullary
open import Function
open import Level using (_⊔_)
open import Algebra.FunctionProperties

open AlmostCommutativeRing

data BinOp : Set where
  [+] : BinOp
  [*] : BinOp
  [^] : BinOp

data Step : Set c where
  [sym]  : Step → Step
  [cong] : Step → BinOp → Step → Step
  [-cong] : Step → Step
  [refl] : Carrier base → Step
  [assoc] : BinOp → Carrier base → Carrier base → Carrier base → Step
  [ident] : BinOp → Carrier base → Step
  [comm]  : BinOp → Carrier base → Carrier base → Step
  [zero] : Carrier base → Step
  [distrib] : Carrier base → Carrier base → Carrier base → Step
  [-distrib] : Carrier base → Carrier base → Step
  [-+comm] : Carrier base → Carrier base → Step

record _≈ⁱ_ (x y : base .Carrier) : Set (c ⊔ ℓ) where
   constructor _~?_
   field
     proof : base ._≈_ x y
     why : Step

open _≈ⁱ_

decTrace : ∀ x y → Dec (EqClosure _≈ⁱ_ x y)
decTrace x y with base ._≟_ x y
decTrace x y | yes p = yes (return (inj₁ (p ~? [refl] x)))
decTrace x y | no ¬p = no (¬p ∘ gfold id (base ._≈_) (trans base ∘ [ id , sym base ] ∘ Data.Sum.map proof proof) (refl base))

neg-cong : ∀ {x y} → x ≈ⁱ y → -_ base x ≈ⁱ -_ base y
neg-cong (prf ~? reason) = -‿cong base prf ~? ( [-cong] reason)

zip-cong : BinOp
         → ∀ {f : Carrier base → Carrier base → Carrier base}
         → Congruent₂ (_≈_ base) f
         → Congruent₂ (EqClosure _≈ⁱ_) f
zip-cong op f-cong {x₁} {x₂} {y₁} {y₂} ε ε = ε
zip-cong op f-cong {x₁} {x₂} {y₁} {y₂} ε (inj₁ (y ~? yr) ◅ ys) = inj₁ (f-cong (refl base) y ~? ([cong] ([refl] x₁) op yr)) ◅ zip-cong op f-cong ε ys
zip-cong op f-cong {x₁} {x₂} {y₁} {y₂} ε (inj₂ (y ~? yr) ◅ ys) = inj₂ (f-cong (refl base) y ~? ([cong] ([refl] x₁) op yr)) ◅ zip-cong op f-cong ε ys
zip-cong op f-cong {x₁} {x₂} {y₁} {y₂} (inj₁ (x ~? xr) ◅ xs) ε = inj₁ (f-cong x (refl base) ~? ([cong] xr op ([refl] y₁))) ◅ zip-cong op f-cong xs ε
zip-cong op f-cong {x₁} {x₂} {y₁} {y₂} (inj₂ (x ~? xr) ◅ xs) ε = inj₂ (f-cong x (refl base) ~? ([cong] xr op ([refl] y₁))) ◅ zip-cong op f-cong xs ε
zip-cong op f-cong {x₁} {x₂} {y₁} {y₂} (inj₁ (x ~? xr) ◅ xs) (inj₁ (y ~? yr) ◅ ys) = inj₁ (f-cong x y ~? ([cong] xr op yr)) ◅ zip-cong op f-cong xs ys
zip-cong op f-cong {x₁} {x₂} {y₁} {y₂} (inj₁ (x ~? xr) ◅ xs) (inj₂ (y ~? yr) ◅ ys) = inj₁ (f-cong x (sym base y) ~? ([cong] xr op ([sym] yr))) ◅ zip-cong op f-cong xs ys
zip-cong op f-cong {x₁} {x₂} {y₁} {y₂} (inj₂ (x ~? xr) ◅ xs) (inj₁ (y ~? yr) ◅ ys) = inj₂ (f-cong x (sym base y) ~? ([cong] xr op ([sym] yr))) ◅ zip-cong op f-cong xs ys
zip-cong op f-cong {x₁} {x₂} {y₁} {y₂} (inj₂ (x ~? xr) ◅ xs) (inj₂ (y ~? yr) ◅ ys) = inj₂ (f-cong x y ~? ([cong] xr op yr)) ◅ zip-cong op f-cong xs ys

tracedRing : AlmostCommutativeRing c (c ⊔ ℓ)
tracedRing = record
  { Carrier                 = base .Carrier
  ; _≈_                     = EqClosure _≈ⁱ_
  ; _≟_                     = decTrace
  ; _+_                     = _+_ base
  ; _*_                     = _*_ base
  ; -_                      = -_ base
  ; 0#                      = 0# base
  ; 1#                      = 1# base
  ; isAlmostCommutativeRing = record
    {  -‿cong      = Relation.Binary.Construct.Closure.ReflexiveTransitive.gmap (-_ base) (Data.Sum.map neg-cong neg-cong)
    ; -‿*-distribˡ = λ x y → return (inj₁ (-‿*-distribˡ base x y ~? [-distrib] x y))
    ; -‿+-comm     = λ x y → return (inj₁ (-‿+-comm     base x y ~? [-+comm] x y))
    ; isCommutativeSemiring = record
      { distribʳ = λ x y z → return (inj₁ (distribʳ base x y z ~? [distrib] x y z))
      ; zeroˡ = λ x → return (inj₁ (zeroˡ base x ~? ([zero] x)))
      ; *-isCommutativeMonoid = record
        { identityˡ = λ x → return (inj₁ (*-identityˡ base x ~? [ident] [*] x))
        ; comm = λ x y → return (inj₁ (*-comm base x y ~? [comm] [*] x y))
        ; isSemigroup = record
          { assoc = λ x y z → return (inj₁ (*-assoc base x y z ~? [assoc] [*] x y z))
          ; isMagma = record
            { isEquivalence = Relation.Binary.Construct.Closure.Equivalence.isEquivalence _≈ⁱ_
            ; ∙-cong = zip-cong [*] (*-cong base)
            }
          }
        }
      ; +-isCommutativeMonoid = record
        { identityˡ = λ x → return (inj₁ (+-identityˡ base x ~? ([ident] [+] x)))
        ; comm = λ x y → return (inj₁ (+-comm base x y ~? ([comm] [+] x y)))
        ; isSemigroup = record
          { assoc = λ x y z → return (inj₁ (+-assoc base x y z ~? ([assoc] [+] x y z)))
          ; isMagma = record
            { isEquivalence = Relation.Binary.Construct.Closure.Equivalence.isEquivalence _≈ⁱ_
            ; ∙-cong = zip-cong [+] (+-cong base)
            }
          }
        }
      }
    }
  }

open import Data.List

showProof : ∀ {x y} → EqClosure _≈ⁱ_ x y → List Step
showProof ε = []
showProof (inj₁ x ◅ xs) = why x ∷ showProof xs
showProof (inj₂ y ◅ xs) = why y ∷ showProof xs
