-----------------------------------------------------------------------
-- This file defines Dial₂(Sets) and its SMC structure.              --
-----------------------------------------------------------------------
module Dial2Sets where

open import level
open import product public
open import empty
open import unit
open import functions renaming (id to id-set)
open import eq

-- Extensionality will be used when proving equivalences of morphisms.
postulate ext-set : ∀{l1 l2 : level} → extensionality {l1} {l2}
-- These are isomorphisms, but Agda has no way to prove these as
-- equivalences.  They are consistent to adopt as equivalences by
-- univalence:
postulate ∧-unit : ∀{ℓ}{A : Set ℓ} → A ≡ (⊤ ∧ A)
postulate ∧-assoc : ∀{ℓ}{A B C : Set ℓ} →  (A ∧ (B ∧ C)) ≡ ((A ∧ B) ∧ C)

-- The objects:
Obj : Set₁
Obj = Σ[ U ∈ Set ] (Σ[ X ∈ Set ] (U → X → Set))

-- The morphisms:
Hom : Obj → Obj → Set
Hom (U , X , α) (V , Y , β) =
  Σ[ f ∈ (U → V) ]
    (Σ[ F ∈ (Y → X) ] (∀{u : U}{y : Y} → α u (F y) → β (f u) y))

-- Composition:
comp : {A B C : Obj} → Hom A B → Hom B C → Hom A C
comp {(U , X , α)} {(V , Y , β)} {(W , Z , γ)} (f , F , p₁) (g , G , p₂) =
  (g ∘ f , F ∘ G , (λ {u z} p-α → p₂ (p₁ p-α)))

infixl 5 _○_

_○_ = comp

-- The contravariant hom-functor:
Homₐ :  {A' A B B' : Obj} → Hom A' A → Hom B B' → Hom A B → Hom A' B'
Homₐ f h g = comp f (comp g h)

-- The identity function:
id : {A : Obj} → Hom A A 
id {(U , V , α)} = (id-set , id-set , id-set)

-- In this formalization we will only worry about proving that the
-- data of morphisms are equivalent, and not worry about the morphism
-- conditions.  This will make proofs shorter and faster.
--
-- If we have parallel morphisms (f,F) and (g,G) in which we know that
-- f = g and F = G, then the condition for (f,F) will imply the
-- condition of (g,G) and vice versa.  Thus, we can safly ignore it.
infix 4 _≡h_

_≡h_ : {A B : Obj} → (f g : Hom A B) → Set
_≡h_ {(U , X , α)}{(V , Y , β)} (f , F , p₁) (g , G , p₂) = f ≡ g × F ≡ G

-----------------------------------------------------------------------
-- Dial₂(Sets) is a SMC                                              --
-----------------------------------------------------------------------

-- The tensor functor: ⊗
_⊗ᵣ_ : ∀{U X V Y : Set} → (U → X → Set) → (V → Y → Set) → ((U × V) → ((V → X) × (U → Y)) → Set)
_⊗ᵣ_ α β (u , v) (f , g) = (α u (f v)) × (β v (g u))

_⊗ₒ_ : (A B : Obj) → Obj
(U , X , α) ⊗ₒ (V , Y , β) = ((U × V) , ((V → X) × (U → Y)) , α ⊗ᵣ β)

F⊗ : ∀{S Z W T V X U Y : Set}{f : U → W}{F : Z → X}{g : V → S}{G : T → Y} → (S → Z) × (W → T) → (V → X) × (U → Y)
F⊗ {f = f}{F}{g}{G} (h₁ , h₂) = (λ v → F(h₁ (g v))) , (λ u → G(h₂ (f u)))
  
_⊗ₐ_ : {A B C D : Obj} → Hom A C → Hom B D → Hom (A ⊗ₒ B) (C ⊗ₒ D)
_⊗ₐ_ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)}{(S , T , δ)} (f , F , p₁) (g , G , p₂) = ⟨ f , g ⟩ , F⊗ {f = f}{F}{g}{G} , p
 where
  p : {u : U × V} {y : (S → Z) × (W → T)} → (α ⊗ᵣ β) u ((F⊗ {f = f}{F}{g}{G}) y) → (γ ⊗ᵣ δ) (⟨ f , g ⟩ u) y
  p {(u , v)} {(h₁ , h₂)} (p-α , p-β) = p₁ p-α , p₂ p-β

-- The unit for tensor:
ι : ⊤ → ⊤ → Set
ι triv triv = ⊤

I : Obj
I = (⊤ , ⊤ , ι)

-- The left-unitor:
λ⊗-p : ∀{U X α}{u : ⊤ × U} {x : X} → (ι ⊗ᵣ α) u ((λ _ → triv) , (λ _ → x)) → α (snd u) x
λ⊗-p {U}{X}{α}{(triv , u)}{x} (triv , p-α) = p-α
   
λ⊗ : ∀{A : Obj} → Hom (I ⊗ₒ A) A
λ⊗ {(U , X , α)} = snd , (λ x → (λ _ → triv) , (λ _ → x)) , λ⊗-p

λ⁻¹⊗ : ∀{A : Obj} → Hom A (I ⊗ₒ A)
λ⁻¹⊗ {(U , X , α)} = (λ u → triv , u) , ((λ x → snd x triv) , λ⁻¹⊗-p)  
 where
  λ⁻¹⊗-p : ∀{U X α} → {u : U} {y : (U → ⊤) × (⊤ → X)} → α u (snd y triv) → (ι ⊗ᵣ α) (triv , u) y
  λ⁻¹⊗-p {U}{X}{α}{u}{(h₁ , h₂)} p-α with h₁ u
  ... | triv = triv , p-α

-- The right-unitor:
ρ⊗ : ∀{A : Obj} → Hom (A ⊗ₒ I) A
ρ⊗ {(U , X , α)} = fst , (λ x → (λ x₁ → x) , (λ x₁ → triv)) , ρ⊗-p
 where
  ρ⊗-p : ∀{U X α}{u : U × ⊤}{x : X} → (α ⊗ᵣ ι) u ((λ _ → x) , (λ _ → triv)) → α (fst u) x
  ρ⊗-p {U}{X}{α}{(u , triv)}{x} (p-α , triv) = p-α

ρ⊗-inv : ∀{A : Obj} → Hom A (A ⊗ₒ I)
ρ⊗-inv {(U , X , α)} = (λ x → x , triv) , (λ x → fst x triv) , ρ⊗-p-inv
 where
  ρ⊗-p-inv : ∀{U X α}{u : U} {y : Σ (⊤ → X) (λ x → U → ⊤)} → α u (fst y triv) → (α ⊗ᵣ ι) (u , triv) y
  ρ⊗-p-inv {U}{X}{α}{u}{(f , g)} p-α rewrite single-range {g = g}{u} = p-α , triv

-- Symmetry:
β⊗ : ∀{A B : Obj} → Hom (A ⊗ₒ B) (B ⊗ₒ A)
β⊗ {(U , X , α)}{(V , Y , β)} = twist-× , twist-× , β⊗-p
 where
   β⊗-p : ∀{U V Y X α β} → {u : U × V} {y : (U → Y) × (V → X)} →
       (α ⊗ᵣ β) u (twist-× y) → (β ⊗ᵣ α) (twist-× u) y
   β⊗-p {U}{V}{Y}{X}{α}{β}{(u , v)}{(h₁ , h₂)} p-α = twist-× p-α

-- The associator:
α⊗-inv : ∀{A B C : Obj} → Hom (A ⊗ₒ (B ⊗ₒ C)) ((A ⊗ₒ B) ⊗ₒ C)
α⊗-inv {(U , X , α)}{(V , Y , β)}{(W , Z , γ)} = rl-assoc-× , Fα-inv , α-inv-cond
 where
   Fα-inv : (W → (V → X) × (U → Y)) × (U × V → Z) → (V × W → X) × (U → (W → Y) × (V → Z))
   Fα-inv = (λ p → (λ p' → fst ((fst p) (snd p')) (fst p')) , (λ u → (λ w → snd (fst p w) u) , (λ v → (snd p) (u , v))))
   α-inv-cond : ∀{u : U × V × W} {y : (W → (V → X) × (U → Y)) × (U × V → Z)} → (α ⊗ᵣ (β ⊗ᵣ γ)) u (Fα-inv y) → ((α ⊗ᵣ β) ⊗ᵣ γ) (rl-assoc-× u) y
   α-inv-cond {(u , v , w)} {(h₁ , h₂)} (p₁ , p₂ , p₃) with h₁ w
   ... | (a , b) = (p₁ , p₂) , p₃

Fα : ∀{V W X Y U V Z : Set} → Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z))
       → Σ (W → Σ (V → X) (λ x → U → Y)) (λ x → Σ U (λ x₁ → V) → Z)
Fα (f ,  g) = (λ x → (λ x₁ → f ((x₁ , x))) , (λ x₁ → fst (g x₁) x)) , (λ x → snd (g (fst x)) (snd x))

α⊗ : ∀{A B C : Obj} → Hom ((A ⊗ₒ B) ⊗ₒ C) (A ⊗ₒ (B ⊗ₒ C)) 
α⊗ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)} = (lr-assoc-× , Fα {V} , α-cond)
 where
  α-cond : {u : Σ (Σ U (λ x → V)) (λ x → W)}{y : Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z))} →
      ((α ⊗ᵣ β) ⊗ᵣ γ) u (Fα {V} y) → (α ⊗ᵣ (β ⊗ᵣ γ)) (lr-assoc-× u) y
  α-cond {(u , v) , w}{(f , g)} ((p₁ , p₂) , p₃) with g u
  ... | (h₁ , h₂) = p₁ , p₂ , p₃

-- Internal hom:
⊸-cond : ∀{U V X Y : Set} → (U → X → Set) → (V → Y → Set) → (U → V) × (Y → X) → U × Y → Set
⊸-cond α β (f , g) (u , y) = α u (g y) → β (f u) y

_⊸ₒ_ : Obj → Obj → Obj
(U , X , α) ⊸ₒ (V , Y , β) = ((U → V) × (Y → X)) , (U × Y) , ⊸-cond α β

_⊸ₐ_ : {A B C D : Obj} → Hom C A → Hom B D → Hom (A ⊸ₒ B) (C ⊸ₒ D)
_⊸ₐ_ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)}{(S , T , δ)} (f , F , p₁) (g , G , p₂) =
  h , H , p₃
  where
   h : Σ (U → V) (λ x → Y → X) → Σ (W → S) (λ x → T → Z)
   h (h₁ , h₂) = (λ w → g (h₁ (f w))) , (λ t → F (h₂ (G t)))
   H : Σ W (λ x → T) → Σ U (λ x → Y)
   H (w , t) = f w , G t
   p₃ : {u : Σ (U → V) (λ x → Y → X)} {y : Σ W (λ x → T)} → ⊸-cond α β u (H y) → ⊸-cond γ δ (h u) y
   p₃ {h₁ , h₂}{w , t} c c' = p₂ (c (p₁ c'))
