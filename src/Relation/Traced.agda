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

open import Data.Bool using (Bool; false; true ; _∧_; _∨_)
decBinOp : BinOp → BinOp → Bool
decBinOp [+] [+] = true
decBinOp [*] [*] = true
decBinOp [^] [^] = true
decBinOp _ _ = false

decStep : (x y : Step) → Bool
decStep ([sym] x) ([sym] y) = decStep x y
decStep ([cong] x x₁ x₂) ([cong] y y₁ y₂) = decStep x y ∧ decBinOp x₁ y₁ ∧ decStep x₂ y₂
decStep ([-cong] x) ([-cong] y) = decStep x y
decStep ([assoc] x x₁ x₂ x₃) ([assoc] y y₁ y₂ y₃) with decBinOp x y | base ._≟_ x₁ y₁ | base ._≟_ x₂ y₂ | base ._≟_ x₃ y₃
decStep ([assoc] x x₁ x₂ x₃) ([assoc] y y₁ y₂ y₃) | true | yes _ | yes _ | yes _ = true
decStep ([assoc] x x₁ x₂ x₃) ([assoc] y y₁ y₂ y₃) | res | a | b | c = false
decStep ([ident] x x₁) ([ident] y y₁) with decBinOp x y | base ._≟_ x₁ y₁
decStep ([ident] x x₁) ([ident] y y₁) | true | yes _ = true
decStep ([ident] x x₁) ([ident] y y₁) | res | a = false
decStep ([comm] x x₁ x₂) ([comm] y y₁ y₂) with decBinOp x y | base ._≟_ x₁ y₁ | base ._≟_ x₂ y₂
decStep ([comm] x x₁ x₂) ([comm] y y₁ y₂) | true | yes _ | yes _ = true
decStep ([comm] x x₁ x₂) ([comm] y y₁ y₂) | res | a | b = false
decStep ([zero] x) ([zero] y) with base ._≟_ x y
decStep ([zero] x) ([zero] y) | yes p = true
decStep ([zero] x) ([zero] y) | no ¬p = false
decStep ([distrib] x x₁ x₂) ([distrib] y y₁ y₂) with base ._≟_ x y | base ._≟_ x₁ y₁ | base ._≟_ x₂ y₂
decStep ([distrib] x x₁ x₂) ([distrib] y y₁ y₂) | yes _ | yes _ | yes _ = true
decStep ([distrib] x x₁ x₂) ([distrib] y y₁ y₂) | a | b | c = false
decStep ([-distrib] x x₁) ([-distrib] y y₁) with base ._≟_ x y | base ._≟_ x₁ y₁
decStep ([-distrib] x x₁) ([-distrib] y y₁) | yes a | yes b = true
decStep ([-distrib] x x₁) ([-distrib] y y₁) | a | b = false
decStep ([-+comm] x x₁) ([-+comm] y y₁) with base ._≟_ x y | base ._≟_ x₁ y₁
decStep ([-+comm] x x₁) ([-+comm] y y₁) | yes p | yes _ = true
decStep ([-+comm] x x₁) ([-+comm] y y₁) | _ | _ = false
decStep ([refl] x) ([refl] y) with base ._≟_ x y
decStep ([refl] x) ([refl] y) | yes p = true
decStep ([refl] x) ([refl] y) | no ¬p = false
decStep _ _ = false

interesting : Step → Bool
interesting ([sym] x) = interesting x
interesting ([cong] x x₁ x₂) = interesting x ∨ interesting x₂
interesting ([-cong] x) = interesting x
interesting ([refl] x) = false
interesting ([assoc] x x₁ x₂ x₃) = false
interesting ([ident] x x₁) = false
interesting ([zero] x) = false
interesting ([distrib] x x₁ x₂) = true
interesting ([-distrib] x x₁) = false
interesting ([-+comm] x x₁) = false
interesting ([comm] [+] x₁ x₂) with base ._≟_ x₁ (base .0#) | base ._≟_ x₂ (base .0#)
interesting ([comm] [+] x₁ x₂) | no _ | no _ = true
interesting ([comm] [+] x₁ x₂) | a | b = false
interesting ([comm] [*] x₁ x₂) with base ._≟_ x₁ (base .1#) | base ._≟_ x₂ (base .1#)
interesting ([comm] [*] x₁ x₂) | no _ | no _ = true
interesting ([comm] [*] x₁ x₂) | a | b = false
interesting ([comm] [^] x₁ x₂) = true

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

open import Data.List as List

showProof′ : ∀ {x y} → EqClosure _≈ⁱ_ x y → List Step
showProof′ ε = []
showProof′ (inj₁ x ◅ xs) = why x ∷ showProof′ xs
showProof′ (inj₂ y ◅ xs) = why y ∷ showProof′ xs


compressProof : List Step → List Step
compressProof [] = []
compressProof (x ∷ xs) = go [] x xs
  where
  go : List Step → Step → List Step → List Step
  go ys y [] = List.reverse (y ∷ ys)
  go ys y (x ∷ xs) with decStep y x
  go ys y (x ∷ xs) | false = go (y ∷ ys) x xs
  go [] y (x ∷ []) | true = []
  go [] y (x ∷ x₁ ∷ xs) | true = go [] x₁ xs
  go (x₁ ∷ ys) y (x ∷ xs) | true = go ys x₁ xs

showProof : ∀ {x y} → EqClosure _≈ⁱ_ x y → List Step
showProof = List.boolFilter interesting ∘ compressProof ∘ showProof′
