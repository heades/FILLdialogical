module dep-rel where

open import Data.Nat hiding (_*_)
open import Data.Bool
open import Data.Empty renaming (⊥ to False)
open import Data.List
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

-------------------------------------------------------------------------
-- Lists a treated as sets.  Here we give all the necessary tools need --
-- to define relation composition and its generalization.  All         --
-- relations a endorelations, because we really only need relations on --
-- formulas to track dependencies.                                     --
-------------------------------------------------------------------------

-- Cartesian product:
_cp_ : {A : Set} → List A → List A → List (A × A)
[] cp l₂ = []
l₁ cp [] = []
(x ∷ xs) cp l₂ = (helper x l₂) ++ (xs cp l₂)    
 where
   helper : {A : Set} → A → List A → List (A × A)
   helper x [] = []
   helper x (y ∷ ys) = (x , y) ∷ helper x ys

l₁ = (1 ∷ 2 ∷ 3 ∷ 5 ∷ [])
l₂ = (3 ∷ 4 ∷ 5 ∷ 6 ∷ 2 ∷ [])
test1 = l₁ cp l₂

Eq : ∀{a} → (A : Set a) → Set a
Eq A = A → A → Bool

elem : {A : Set} → Eq A → A → List A → Bool
elem _ x [] = false
elem _≡_ x (y ∷ ys) with (x ≡ y)
... | true = true
... | false = elem _≡_ x ys

diff : {A : Set} → Eq A → List A → List A → List A
diff _≡_ l₁ l₂ = filter (λ x → not (elem _≡_ x l₂)) l₁

_≡ℕ_ : ℕ → ℕ → Bool
0 ≡ℕ 0 = true
(suc n) ≡ℕ (suc m) = n ≡ℕ m
_ ≡ℕ _ = false

test2 = diff _≡ℕ_ l₁ l₂

intersect : {A : Set} → Eq A → List A → List A → List A
intersect _≡_ l₁ l₂ = filter (λ x → (elem _≡_ x l₂)) l₁

test5 = intersect _≡ℕ_ l₁ l₂

EndoRel : (A : Set) → Set
EndoRel A = List (A × A)

relComp : {A : Set} → Eq A → EndoRel A → EndoRel A → EndoRel A
relComp {A} _≡_ ((x , y) ∷ ps) r₂ = (helper r₂) ++ (relComp _≡_ ps r₂)
  where
    helper : EndoRel A → EndoRel A
    helper [] = []
    helper ((y' , z) ∷ ps) with y ≡ y' 
    ... | true = (x , z) ∷ helper ps
    ... | false = helper ps
relComp _≡_ r₁ r₂ = []

testRelComp : EndoRel ℕ
testRelComp = relComp _≡ℕ_ (( 1 , 2 ) ∷ ( 3 , 4 ) ∷ ( 5 , 6 ) ∷ (2 , 9) ∷ []) (( 4 , 8) ∷ (2 , 7) ∷ (9 , 10) ∷ (6 , 6) ∷ [])

nub : {A : Set} → Eq A → List A → List A
nub _≡_ l = nub' _≡_ l []
  where
    nub' : {A : Set} → Eq A → List A → List A → List A
    nub' _≡_ [] acc = reverse acc
    nub' _≡_ (x ∷ xs) acc with elem _≡_ x acc
    ... | true = nub' _≡_ xs acc
    ... | false = nub' _≡_ xs (x ∷ acc)

test3 = nub _≡ℕ_ (1 ∷ 1 ∷ 5 ∷ 7 ∷ 7 ∷ 8 ∷ 7 ∷ 1 ∷ 8 ∷ [])
test4 = nub _≡ℕ_ (1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ [])

-- This defines the generalization of relation composition given in
-- the paper.
relStarComp : {A : Set} → Eq A → EndoRel A → EndoRel A → EndoRel A
relStarComp {A} _≡_ r₁ r₂ = 
  let a₁ = nubb (map proj₁ r₁)  -- We are removing duplicates because 
      a₂ = nubb (map proj₁ r₂)  -- we are treating lists as sets.
      b₁ = nubb (map proj₂ r₁) 
      b₂ = nubb (map proj₂ r₂) 
      c₁ = r₁ ∩ᵣ (a₁ cp (b₁ ∩ a₂))
      c₂ = r₂ ∩ᵣ ((a₂ ∩ b₁) cp b₂)
      c₃ = r₁ ∩ᵣ (a₁ cp (b₁ - a₂))
      c₄ = r₂ ∩ᵣ ((a₂ - b₁) cp b₂)
   in ((c₁ * c₂) ∪ c₃) ∪ c₄
  where
    _≡P_ : (A × A) → (A × A) → Bool
    _≡P_ (x₁ , y₁) (x₂ , y₂) = (x₁ ≡ x₂) ∧ (y₁ ≡ y₂)

    nubb : List A → List A
    nubb = nub _≡_

    -- Intersection for relations.
    _∩ᵣ_ : List (A × A) → List (A × A) → List (A × A)
    _∩ᵣ_ = intersect _≡P_

    _∩_ : List A → List A → List A
    _∩_ = intersect _≡_

    _-_ : List A → List A → List A
    _-_ = diff _≡_

    _*_ : EndoRel A → EndoRel A → EndoRel A
    _*_ = relComp _≡_

    _∪_ : List (A × A) → List (A × A) → List (A × A)
    _∪_ = _++_

testRelStarComp : EndoRel ℕ
testRelStarComp = relStarComp _≡ℕ_ (( 1 , 2 ) ∷ ( 3 , 4 ) ∷ (11 , 12 ) ∷ ( 5 , 6 ) ∷ (2 , 9) ∷ []) (( 4 , 8) ∷ (2 , 7) ∷ (9 , 10) ∷ (6 , 6) ∷ (10 , 10) ∷ (3 , 4 ) ∷ [])

data Form : Set where
  At : ℕ → Form
  I : Form
  ⊥ : Form
  _⊗_ : Form → Form → Form
  _⊕_ : Form → Form → Form
  _⊸_ : Form → Form → Form
  pr  : Form → Form

_≡F_ : Form → Form → Bool
(At n) ≡F (At m) = n ≡ℕ m
I ≡F I = true
⊥ ≡F ⊥ = true
(pr A) ≡F (pr B) = A ≡F B
(A ⊗ B) ≡F (A' ⊗ B') = (A ≡F A') ∧ (B ≡F B')
(A ⊕ B) ≡F (A' ⊕ B') = (A ≡F A') ∧ (B ≡F B')
(A ⊸ B) ≡F (A' ⊸ B') = (A ≡F A') ∧ (B ≡F B')
_ ≡F _ = false

_⋆_ : EndoRel Form → EndoRel Form → EndoRel Form
_⋆_ = relStarComp _≡F_

_●_ : List Form → List Form → EndoRel Form
_●_ = _cp_

Ctx : Set
Ctx = List Form

data Derivation : Ctx → Ctx → Set where
  Ax : ∀{a : Form} 
    → Derivation [ a ] [ a ]
  Cut : ∀{Γ₁ Γ₂ Δ₁ Δ₂ : Ctx}{a : Form} 
    → Derivation Γ₁ (a ∷ Δ₁) 
    → Derivation (a ∷ Γ₂) Δ₂ 
    → Derivation (Γ₁ ++ Γ₂) (Δ₁ ++ Δ₂)
  TL : ∀{Γ₁ Γ₂ Δ : Ctx}{a b : Form} 
    → Derivation (Γ₁ ++ (a ∷ b ∷ Γ₂)) Δ
    → Derivation (Γ₁ ++ ((a ⊗ b) ∷ Γ₂)) Δ
  TR : ∀{Γ₁ Γ₂ Δ₁ Δ₂ : Ctx}{a b : Form}
    → Derivation Γ₁ (a ∷ Δ₁)
    → Derivation Γ₂ (b ∷ Δ₂)
    → Derivation (Γ₁ ++ Γ₂) ((a ⊗ b) ∷ (Δ₁ ++ Δ₂))
  IL : ∀{Γ₁ Γ₂ Δ : Ctx}
    → Derivation (Γ₁ ++ Γ₂) Δ
    → Derivation (Γ₁ ++ (I ∷ Γ₂)) Δ
  IR : Derivation [] [ I ]
  ParL : ∀{Γ₁ Δ₁ Γ₂ Δ₂ : Ctx}{a b : Form} 
    → Derivation (a ∷ Γ₁) Δ₁
    → Derivation (b ∷ Γ₂) Δ₂
    → Derivation (a ⊕ b ∷ (Γ₁ ++ Γ₂)) (Δ₁ ++ Δ₂)
  ParR : ∀{Γ Δ₁ Δ₂ : Ctx}{a b : Form} 
    → Derivation Γ (Δ₁ ++ (a ∷ b ∷ Δ₂))
    → Derivation Γ (Δ₁ ++ (a ⊕ b ∷ Δ₂))
  PL : Derivation [ ⊥ ] []
  PR : ∀{Γ Δ₁ Δ₂ : Ctx} 
    → Derivation Γ (Δ₁ ++ Δ₂) 
    → Derivation Γ (Δ₁ ++ (⊥ ∷ Δ₂))
  ImpL : ∀{Γ₁ Γ₂ Δ₁ Δ₂ : Ctx}{a b : Form}
    → Derivation (Γ₁ ++ (b ∷ [])) Δ₁
    → Derivation Γ₂ (a ∷ Δ₂)
    → Derivation ((a ⊸ b) ∷ (Γ₁ ++ Γ₂)) (Δ₁ ++ Δ₂)
  ImpR : ∀{Γ Δ₁ Δ₂ : Ctx}{a b : Form}
    → Derivation (Γ ++ (a ∷ [])) (Δ₁ ++ (b ∷ Δ₂))
    → Derivation Γ (Δ₁ ++ (a ⊸ b ∷ Δ₂))

dep : {Γ Δ : Ctx} → Derivation Γ Δ → EndoRel Form
dep (Ax {a}) = [ ((pr a) , (pr (pr a))) ]
dep (Cut {a = a} σ₁ σ₂) = ((dep σ₁) ⋆ [ (pr a , pr (pr a)) ]) ⋆ (dep σ₂)
dep (TL {a = a}{b = b} σ) = ((a ⊗ b , a )∷ (a ⊗ b , b) ∷ []) ⋆ (dep σ)
dep (TR {a = a}{b = b} σ₁ σ₂) = ((dep σ₁) ++ (dep σ₂)) ⋆ ((a , a ⊗ b) ∷ (b , a ⊗ b) ∷ [])
dep (IL σ) = dep σ
dep IR = []
dep (ParL {a = a}{b = b} σ₁ σ₂) = ((a ⊕ b , a) ∷ (a ⊕ b , b) ∷ []) ⋆ ((dep σ₁) ++ (dep σ₂))
dep (ParR {a = a}{b = b} σ) = (dep σ) ⋆ ((a , a ⊕ b) ∷ (b , a ⊕ b) ∷ [])
dep PL = []
dep (PR σ) = dep σ
dep (ImpL {a = a}{b = b} σ₁ σ₂) = (dep σ₂) ⋆ (((a , b) ∷ ((a ⊸ b) , b) ∷ []) ⋆ (dep σ₁))
dep (ImpR {a = a}{b = b} σ) = ((dep σ) ⋆ [ (b , a ⊸ b) ])


test-derv1 : ∀{A B C D : Form} → Derivation ((A ⊗ B) ⊸ (C ⊕ D) ∷ A ∷ []) (C ∷ B ⊸ D ∷ [])
test-derv1 {A}{B}{C}{D} = ImpR {(A ⊗ B) ⊸ (C ⊕ D) ∷ A ∷ []}{[ C ]}{[]} (ImpL {[]} {A ∷ B ∷ []} {C ∷ D ∷ []} {[]} {A ⊗ B} {C ⊕ D} 
                          (ParL {[]} {[ C ]} {[]} {[ D ]} {C} {D} (Ax {C}) (Ax {D})) 
                          (TR {[ A ]} {[ B ]} {[]} {[]} {A} {B} (Ax {A}) (Ax {B})))

-- The result:
-- A = At 1
-- B = At 2
-- C = At 3
-- D = At 4
-- (A , B ⊸ D) ∷
-- (B , B ⊸ D) ∷
-- ((A ⊗ B) ⊸ (C ⊕ D) , B ⊸ D) ∷
-- (A , C) ∷
-- (B , C) ∷
-- (pr A , pr (pr A)) ∷
-- (pr B , pr (pr B)) ∷
-- ((A ⊗ B) ⊸ (C ⊕ D) , C) ∷
-- (pr C , pr (pr C)) ∷ (pr D , pr (pr D)) ∷ []
dep-test-derv1 : EndoRel Form
dep-test-derv1 = dep (test-derv1 {At 1}{At 2}{At 3}{At 4})

test-derv2 : ∀{A B C D : Form} → Derivation ((A ⊗ B) ⊸ (C ⊕ D) ∷ A ∷ B ∷ []) (C ∷ D ∷ [])
test-derv2 {A}{B}{C}{D} = ImpL {[]} {A ∷ B ∷ []} {C ∷ D ∷ []} {[]} {A ⊗ B} {C ⊕ D} 
                          (ParL {[]} {[ C ]} {[]} {[ D ]} {C} {D} (Ax {C}) (Ax {D})) 
                          (TR {[ A ]} {[ B ]} {[]} {[]} {A} {B} (Ax {A}) (Ax {B}))
-- The result:
-- A = At 1
-- B = At 2
-- C = At 3
-- D = At 4
-- (A , C) ∷
-- (A , D) ∷
-- (B , C) ∷
-- (B , D) ∷
-- (pr A , pr (pr A)) ∷
-- (pr B , pr (pr B)) ∷
-- ((A ⊗ B) ⊸ (C ⊕ D) , C) ∷
-- ((A ⊗ B) ⊸ (C ⊕ D) , D) ∷
-- (pr C , pr (pr C)) ∷ (pr D , pr (pr D)) ∷ []
dep-test-derv2 : EndoRel Form
dep-test-derv2 = dep (test-derv2 {At 1}{At 2}{At 3}{At 4})
