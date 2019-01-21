open import Polynomial.Simple.AlmostCommutativeRing
open import Relation.Binary
open import Data.Bool using (Bool; false; true ; _∧_; _∨_; not; if_then_else_)
open import Data.String using (String)

module Relation.Traced
  {c ℓ}
  (base : AlmostCommutativeRing c ℓ)
  (eqBase : AlmostCommutativeRing.Carrier base → AlmostCommutativeRing.Carrier base → Bool)
  (showBase : AlmostCommutativeRing.Carrier base → String)
  where

open import Data.Sum
open import Relation.Binary.Construct.Closure.Equivalence
open import Relation.Binary.Construct.Closure.Symmetric
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Data.String
open import Relation.Nullary
open import Function
open import Level using (_⊔_)
open import Algebra.FunctionProperties
open import Data.String using (String)
open import Data.String.Unsafe renaming (_==_ to eqBoolString)
open import Data.Maybe
open import Data.Nat using (ℕ)

open AlmostCommutativeRing base

record EqBool {a} (A : Set a) : Set a where
  field _==_ : A → A → Bool

open EqBool {{...}}

instance
  eqNat : EqBool ℕ
  _==_ {{eqNat}} = ℕ==
    where open import Agda.Builtin.Nat renaming (_==_ to ℕ==)

instance
  eqCarrier : EqBool Carrier
  _==_ {{eqCarrier}} = eqBase

instance
  eqString : EqBool String
  _==_ {{eqString}} = eqBoolString

infixl 6 _⊕_
infixl 7 _⊗_
data Open : Set c where
  V   : (v : String) → Open
  K   : (k : Carrier) → Open
  _⊕_ : (x : Open) → (y : Open) → Open
  _⊗_ : (x : Open) → (y : Open) → Open
  ⊝_  : (x : Open) → Open
{-# DISPLAY V v = v #-}
{-# DISPLAY K x = x #-}


instance
  eqOpen : EqBool Open
  _==_ ⦃ eqOpen ⦄ (V v) (V y) = v == y
  _==_ ⦃ eqOpen ⦄ (K k) (K y) = k == y
  _==_ ⦃ eqOpen ⦄ (x₁ ⊕ y₁) (x₂ ⊕ y₂) = x₁ == x₂ ∧ y₁ == y₂
  _==_ ⦃ eqOpen ⦄ (x₁ ⊗ y₁) (x₂ ⊗ y₂) = x₁ == x₂ ∧ y₁ == y₂
  _==_ ⦃ eqOpen ⦄ (⊝ x) (⊝ y) = x == y
  _==_ ⦃ eqOpen ⦄ _ _ = false

data Expr : Set c where
  C : Carrier → Expr
  O : Open → Expr
{-# DISPLAY C x = x #-}
{-# DISPLAY O x = x #-}

module Display where
  open import PrettyPrinting.Unparser
  toStruct : Expr → ShowExpr
  toStruct (C x) = lit (showBase x)
  toStruct (O x) = go x
    where
    go : Open → ShowExpr
    go (V v) = lit v
    go (K k) = lit (showBase k)
    go (x ⊕ y) = bin " + " (op 6 left) (go x) (go y)
    go (x ⊗ y) = bin " * " (op 6 left) (go x) (go y)
    go (⊝ x) = pre "- " (op 1 left) (go x)

  prettyExpr : Expr → String
  prettyExpr = showExpr ∘ toStruct

normalise′ : Open → Expr
normalise′ (V v) = O (V v)
normalise′ (K k) = C k
normalise′ (x ⊕ y) with normalise′ x | normalise′ y
normalise′ (x ⊕ y) | C x₁ | C x₂ = C (x₁ + x₂)
normalise′ (x ⊕ y) | C x₁ | O x₂ = if x₁ == 0# then O x₂ else O (K x₁ ⊕ x₂)
normalise′ (x ⊕ y) | O x₁ | C x₂ = if x₂ == 0# then O x₁ else O (x₁ ⊕ K x₂)
normalise′ (x ⊕ y) | O x₁ | O x₂ = O (x₁ ⊕ x₂)
normalise′ (x ⊗ y) with normalise′ x | normalise′ y
normalise′ (x ⊗ y) | C x₁ | C x₂ = C (x₁ + x₂)
normalise′ (x ⊗ y) | C x₁ | O x₂ = if x₁ == 0# then C 0# else if x₁ == 1# then O x₂ else O (K x₁ ⊗ x₂)
normalise′ (x ⊗ y) | O x₁ | C x₂ = if x₂ == 0# then C 0# else if x₂ == 1# then O x₁ else O (x₁ ⊗ K x₂)
normalise′ (x ⊗ y) | O x₁ | O x₂ = O (x₁ ⊗ x₂)
normalise′ (⊝ x) with normalise′ x
normalise′ (⊝ x) | C x₁ = C (- x₁)
normalise′ (⊝ x) | O x₁ = O (⊝ x₁)

normalise : Expr → Expr
normalise (C x) = C x
normalise (O x) = normalise′ x

instance
  eqExpr : EqBool Expr
  _==_ ⦃ eqExpr ⦄ (C x) (C x₁) = x == x₁
  _==_ ⦃ eqExpr ⦄ (C x) (O x₁) = false
  _==_ ⦃ eqExpr ⦄ (O x) (C x₁) = false
  _==_ ⦃ eqExpr ⦄ (O x) (O x₁) = x == x₁

-- open import Agda.Builtin.FromNat using (Number; fromNat) public

-- -- instance
-- --   numberNat : Number ℕ
-- --   numberNat = Data.Nat.Literals.number
-- --     where import Data.Nat.Literals

-- instance
--   numberVar : {{nc : Number Carrier}} → Number Expr
--   numberVar {{nc}} = record
--     { Constraint = Number.Constraint nc
--     ; fromNat = λ n → C ( (Number.fromNat nc n)) }

data BinOp : Set where
  [+] : BinOp
  [*] : BinOp

instance
  eqBinOp : EqBool BinOp
  _==_ ⦃ eqBinOp ⦄ [+] [+] = true
  _==_ ⦃ eqBinOp ⦄ [+] [*] = false
  _==_ ⦃ eqBinOp ⦄ [*] [+] = false
  _==_ ⦃ eqBinOp ⦄ [*] [*] = true

liftBinOp : BinOp → Expr → Expr → Expr
liftBinOp [+] (C x) (C y) = normalise (C (x + y))
liftBinOp [+] (C x) (O y) = normalise (O (K x ⊕ y))
liftBinOp [+] (O x) (C y) = normalise (O (x ⊕ K y))
liftBinOp [+] (O x) (O y) = normalise (O (x ⊕ y))
liftBinOp [*] (C x) (C y) = normalise (C (x * y))
liftBinOp [*] (C x) (O y) = normalise (O (K x ⊗ y))
liftBinOp [*] (O x) (C y) = normalise (O (x ⊗ K y))
liftBinOp [*] (O x) (O y) = normalise (O (x ⊗ y))

⊟_ : Expr → Expr
⊟ C x = C (- x)
⊟ O x = normalise (O (⊝ x))

data Step : Set c where
  [sym]      : Step → Step
  [cong]     : Step → BinOp → Step → Step
  [-cong]    : Step → Step
  [refl]     : Expr  → Step
  [assoc]    : BinOp → Expr → Expr → Expr → Step
  [ident]    : BinOp → Expr → Step
  [comm]     : BinOp → Expr → Expr → Step
  [zero]     : Expr → Step
  [distrib]  : Expr → Expr → Expr → Step
  [-distrib] : Expr → Expr → Step
  [-+comm]   : Expr → Expr → Step

instance
  eqStep : EqBool Step
  _==_ {{eqStep}} ([sym] x) ([sym] y) = x == y
  _==_ {{eqStep}} ([cong] x x₁ x₂) ([cong] y y₁ y₂) = x == y ∧ x₁ == y₁ ∧ x₂ == y₂
  _==_ {{eqStep}} ([-cong] x) ([-cong] y) = x == y
  _==_ {{eqStep}} ([assoc] x x₁ x₂ x₃) ([assoc] y y₁ y₂ y₃) = x == y ∧ x₁ == y₁ ∧ x₂ == y₂ ∧ x₃ == y₃
  _==_ {{eqStep}} ([ident] x x₁) ([ident] y y₁) = x == y ∧ x₁ == y₁
  _==_ {{eqStep}} ([comm] x x₁ x₂) ([comm] y y₁ y₂) = x == y ∧ x₁ == y₁ ∧ x₂ == y₂
  _==_ {{eqStep}} ([zero] x) ([zero] y) = x == y
  _==_ {{eqStep}} ([distrib] x x₁ x₂) ([distrib] y y₁ y₂) = x == y ∧ x₁ == y₁ ∧ x₂ == y₂
  _==_ {{eqStep}} ([-distrib] x x₁) ([-distrib] y y₁) = x == y ∧ x₁ == y₁
  _==_ {{eqStep}} ([-+comm] x x₁) ([-+comm] y y₁) = x == y ∧ x₁ == y₁
  _==_ {{eqStep}} ([refl] x) ([refl] y) = x == y
  _==_ {{eqStep}} _ _ = false

record _≈ⁱ_ (x y : Expr) : Set c where
   constructor ~?_
   field
     why : Step
open _≈ⁱ_


interesting : Step → Maybe Step
interesting ([sym] x) = interesting x
interesting ([-cong] x) = interesting x
interesting ([refl] x) = nothing
interesting ([assoc] x x₁ x₂ x₃) = nothing
interesting ([ident] x x₁) = nothing
interesting ([zero] x) = nothing
interesting ([cong] x x₁ x₂) with interesting x | interesting x₂
interesting ([cong] x x₁ x₂) | just res₁ | just res₂ = just ([cong] res₁ x₁ res₂)
interesting ([cong] x x₁ x₂) | just res₁ | nothing  = just res₁
interesting ([cong] x x₁ x₂) | nothing | just res₂ = just res₂
interesting ([cong] x x₁ x₂) | nothing | nothing  = nothing
interesting s@([comm] _ x y) with x == y
interesting s@([comm] _ x y) | true = nothing
interesting s@([comm] o (C x) (C y))    | false = nothing
interesting s@([comm] [+] (C x) x₂)     | false = if x == 0# then nothing else just s
interesting s@([comm] [+] (O x) (C x₁)) | false = if x₁ == 0# then nothing else just s
interesting s@([comm] [+] (O x) (O x₁)) | false = just s
interesting s@([comm] [*] (C x) x₂)     | false = if (x == 0# ∨ x == 1#) then nothing else just s
interesting s@([comm] [*] (O x) (C x₁)) | false = if (x₁ == 0# ∨ x₁ == 1#) then nothing else just s
interesting s@([comm] [*] (O x) (O x₁)) | false = just s
interesting s@([distrib] (C _) (C _) (C _)) = nothing
interesting s@([distrib] (C x) x₁ x₂) = if (x == 0# ∨ x == 1#) then nothing else just s
interesting s@([distrib] x x₁ x₂) = just s
interesting s@([-distrib] x x₁) = nothing
interesting s@([-+comm] x x₁) = nothing

neg-cong : ∀ {x y} → x ≈ⁱ y → ⊟_  x ≈ⁱ ⊟_  y
neg-cong (~? reason) = ~? ( [-cong] reason)

zip-cong : BinOp
         → (f : Expr → Expr → Expr)
         → Congruent₂ (EqClosure _≈ⁱ_) f
zip-cong op f {x₁} {x₂} {y₁} {y₂} ε ε = ε
zip-cong op f {x₁} {x₂} {y₁} {y₂} ε (inj₁ (~? yr) ◅ ys) = inj₁ (~? ([cong] ([refl] x₁) op yr)) ◅ zip-cong op f ε ys
zip-cong op f {x₁} {x₂} {y₁} {y₂} ε (inj₂ (~? yr) ◅ ys) = inj₂ (~? ([cong] ([refl] x₁) op yr)) ◅ zip-cong op f ε ys
zip-cong op f {x₁} {x₂} {y₁} {y₂} (inj₁ (~? xr) ◅ xs) ε = inj₁ (~? ([cong] xr op ([refl] y₁))) ◅ zip-cong op f xs ε
zip-cong op f {x₁} {x₂} {y₁} {y₂} (inj₂ (~? xr) ◅ xs) ε = inj₂ (~? ([cong] xr op ([refl] y₁))) ◅ zip-cong op f xs ε
zip-cong op f {x₁} {x₂} {y₁} {y₂} (inj₁ (~? xr) ◅ xs) (inj₁ (~? yr) ◅ ys) = inj₁ (~? ([cong] xr op yr)) ◅ zip-cong op f xs ys
zip-cong op f {x₁} {x₂} {y₁} {y₂} (inj₁ (~? xr) ◅ xs) (inj₂ (~? yr) ◅ ys) = inj₁ (~? ([cong] xr op ([sym] yr))) ◅ zip-cong op f xs ys
zip-cong op f {x₁} {x₂} {y₁} {y₂} (inj₂ (~? xr) ◅ xs) (inj₁ (~? yr) ◅ ys) = inj₂ (~? ([cong] xr op ([sym] yr))) ◅ zip-cong op f xs ys
zip-cong op f {x₁} {x₂} {y₁} {y₂} (inj₂ (~? xr) ◅ xs) (inj₂ (~? yr) ◅ ys) = inj₂ (~? ([cong] xr op yr)) ◅ zip-cong op f xs ys

isZero : (x : Expr) → Maybe (EqClosure _≈ⁱ_ (C 0#) x)
isZero (C x) = if 0# == x then just (inj₁ (~? [refl] (C x)) ◅ ε) else nothing
isZero _ = nothing

tracedRing : AlmostCommutativeRing c c
tracedRing = record
  { Carrier                 = Expr
  ; _≈_                     = EqClosure _≈ⁱ_
  ; _+_                     = liftBinOp [+]
  ; _*_                     = liftBinOp [*]
  ; -_                      = ⊟_
  ; 0#                      = C 0#
  ; 1#                      = C 1#
  ; 0≟_                     = isZero
  ; isAlmostCommutativeRing = record
    {  -‿cong      = Relation.Binary.Construct.Closure.ReflexiveTransitive.gmap ⊟_ (Data.Sum.map neg-cong neg-cong)
    ; -‿*-distribˡ = λ x y → return (inj₁ (~? [-distrib] x y))
    ; -‿+-comm     = λ x y → return (inj₁ (~? [-+comm] x y))
    ; isCommutativeSemiring = record
      { distribʳ = λ x y z → return (inj₁ (~? [distrib] x y z))
      ; zeroˡ = λ x → return (inj₁ (~? ([zero] x)))
      ; *-isCommutativeMonoid = record
        { identityˡ = λ x → return (inj₁ (~? [ident] [*] x))
        ; comm = λ x y → return (inj₁ (~? [comm] [*] x y))
        ; isSemigroup = record
          { assoc = λ x y z → return (inj₁ (~? [assoc] [*] x y z))
          ; isMagma = record
            { isEquivalence = Relation.Binary.Construct.Closure.Equivalence.isEquivalence _≈ⁱ_
            ; ∙-cong = zip-cong [*] (liftBinOp [*])
            }
          }
        }
      ; +-isCommutativeMonoid = record
        { identityˡ = λ x → return (inj₁ (~? ([ident] [+] x)))
        ; comm = λ x y → return (inj₁ (~? ([comm] [+] x y)))
        ; isSemigroup = record
          { assoc = λ x y z → return (inj₁ (~? ([assoc] [+] x y z)))
          ; isMagma = record
            { isEquivalence = Relation.Binary.Construct.Closure.Equivalence.isEquivalence _≈ⁱ_
            ; ∙-cong = zip-cong [+] (liftBinOp [+])
            }
          }
        }
      }
    }
  }

open import Data.List as List using (List; _∷_; [])

record Explanation {a} (A : Set a) : Set (a ⊔ c) where
  constructor _≈⟨_⟩≈_
  field
    lhs : A
    step : Step
    rhs : A
open Explanation

toExplanation : ∀ {x y} → x ≈ⁱ y → Explanation Expr
toExplanation {x} {y} x≈y = x ≈⟨ why x≈y ⟩≈ y

showProof′ : ∀ {x y} → EqClosure _≈ⁱ_ x y → List (Explanation Expr)
showProof′ ε = []
showProof′ (inj₁ x ◅ xs) = toExplanation x ∷ showProof′ xs
showProof′ (inj₂ y ◅ xs) = toExplanation y ∷ showProof′ xs


isReversal : Explanation Expr → Explanation Expr → Bool
isReversal (lhs₁ ≈⟨ step₁ ⟩≈ rhs₁) (lhs₂ ≈⟨ step₂ ⟩≈ rhs₂) = lhs₁ == rhs₂ ∨ step₁ == step₂ ∨ go step₁ step₂
  where
  go : Step → Step → Bool
  go ([comm] op₁ x₁ y₁) ([comm] op₂ x₂ y₂) = op₁ == op₂ ∧ x₁ == y₂ ∧ y₁ == x₂
  go ([sym] x) ([sym] y) = go x y
  go ([sym] x) y = x == y
  -- go ([cong] x x₁ x₂) y = {!!}
  -- go ([-cong] x) y = {!!}
  -- go ([refl] x) y = {!!}
  -- go ([assoc] x x₁ x₂ x₃) y = {!!}
  -- go ([ident] x x₁) y = {!!}
  -- go ([zero] x) y = {!!}
  -- go ([distrib] x x₁ x₂) y = {!!}
  -- go ([-distrib] x x₁) y = {!!}
  -- go ([-+comm] x x₁) y = {!!}
  go x ([sym] y) = x == y
  go _ _ = false


prettyStep : Step → String
prettyStep ([sym] x) = "sym (" ++ prettyStep x ++ ")"
prettyStep ([cong] x [+] x₂) = "(" ++ prettyStep x ++ ") + (" ++ prettyStep x₂ ++ ")"
prettyStep ([cong] x [*] x₂) = "(" ++ prettyStep x ++ ") * (" ++ prettyStep x₂ ++ ")"
prettyStep ([-cong] x) = "- (" ++ prettyStep x ++ ")"
prettyStep ([refl] x) = "eval"
prettyStep ([assoc] [+] x₁ x₂ x₃) = "+-assoc(" ++ Display.prettyExpr x₁ ++ ", " ++ Display.prettyExpr x₂ ++ ", " ++ Display.prettyExpr x₂ ++ ")"
prettyStep ([assoc] [*] x₁ x₂ x₃) = "*-assoc(" ++ Display.prettyExpr x₁ ++ ", " ++ Display.prettyExpr x₂ ++ ", " ++ Display.prettyExpr x₂ ++ ")"
prettyStep ([ident] [+] x₁) = "+-ident(" ++ Display.prettyExpr x₁ ++ ")"
prettyStep ([ident] [*] x₁) = "*-ident(" ++ Display.prettyExpr x₁ ++ ")"
prettyStep ([comm] [+] x₁ x₂) = "+-comm(" ++ Display.prettyExpr x₁ ++ ", " ++ Display.prettyExpr x₂ ++ ")"
prettyStep ([comm] [*] x₁ x₂) = "+-comm(" ++ Display.prettyExpr x₁ ++ ", " ++ Display.prettyExpr x₂ ++ ")"
prettyStep ([zero] x) = "*-zero(" ++ Display.prettyExpr x ++ ")"
prettyStep ([distrib] x x₁ x₂) = "*-distrib(" ++ Display.prettyExpr x ++ ", " ++ Display.prettyExpr x₁ ++ ", " ++ Display.prettyExpr x₂ ++ ")"
prettyStep ([-distrib] x x₁) = "-distrib(" ++ Display.prettyExpr x ++ ", " ++ Display.prettyExpr x₁ ++ ")"
prettyStep ([-+comm] x x₁) = "-+-comm(" ++ Display.prettyExpr x ++ ", " ++ Display.prettyExpr x₁ ++ ")"

showProof : ∀ {x y} → EqClosure _≈ⁱ_ x y → List String
showProof = List.foldr unparse [] ∘ List.foldr spotReverse [] ∘ List.mapMaybe interesting′ ∘ showProof′
  where
  unparse : Explanation Expr → List String → List String
  unparse (lhs₁ ≈⟨ step₁ ⟩≈ rhs₁) [] = Display.prettyExpr lhs₁ ∷ ("    ={ " ++ prettyStep step₁ ++ " }") ∷ Display.prettyExpr rhs₁ ∷ []
  unparse (lhs₁ ≈⟨ step₁ ⟩≈ rhs₁) (y ∷ ys) = if r == y then l ∷ m ∷ y ∷ ys else l ∷ m ∷ r ∷ "    ={ eval }" ∷ y ∷ ys
    where
    l = Display.prettyExpr lhs₁
    m = "    ={ " ++ prettyStep step₁ ++ " }"
    r = Display.prettyExpr rhs₁

  spotReverse : Explanation Expr → List (Explanation Expr) → List (Explanation Expr)
  spotReverse x [] = x ∷ []

  spotReverse x (y ∷ xs) = if isReversal x y then xs else x ∷ y ∷ xs
  interesting′ : Explanation Expr → Maybe (Explanation Expr)
  interesting′ (lhs ≈⟨ stp ⟩≈ rhs) with interesting stp
  interesting′ (lhs ≈⟨ stp ⟩≈ rhs) | just x = just (lhs ≈⟨ x ⟩≈ rhs)
  interesting′ (lhs ≈⟨ stp ⟩≈ rhs) | nothing = nothing

