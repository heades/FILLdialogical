-----------------------------------------------------------------------
-- This file formalizes the proof that Dial₂(Sets) is indeed a model --
-- of Full Tensorial Logic.  See Lemma ?? on page ?? of the paper.   --
-----------------------------------------------------------------------
module Tensorial where

open import prelude
open import product
open import product-thms

open import Dial2Sets

-----------------------------------------------------------------------
-- We first must prove that Dial₂(Sets) is a dialogue category.      --
-- See Definition ?? on page ?? of the paper.                        --
-----------------------------------------------------------------------

-- This defines the negation functor: ¬ : Dial₂(Sets) → Dial₂ᵒᵖ(Sets)
¬ₒ : Obj → Obj
¬ₒ (U , X , α) = (X , U , (λ x u → (α u x) → ⊥))

¬ₐ : {A B : Obj} → Hom A B → Hom (¬ₒ B) (¬ₒ A)
¬ₐ {(U , X , α)}{(V , Y , β)} (f , F , p) = (F , f , (λ x x₁ → x (p x₁)))

-- Next we must define a family of bijections.
φ : {A B C : Obj} → Hom (A ⊗ₒ B) (¬ₒ C) → Hom A (¬ₒ (B ⊗ₒ C))
φ {(U , X , α)} {(V , Y , β)} {(W , Z , γ)} (f , F , p₁) = (λ u → (λ w → (snd (F w)) u) , (λ v → f (u , v))) , (λ c → fst (F (snd c)) (fst c)) , c
 where
   G : V × W → X
   G = λ c → fst (F (snd c)) (fst c)
   c : ∀{u : U} {y : V × W} → α u (G y) → (β ⊗ᵣ γ) y ((λ w → snd (F w) u) , (λ v → f (u , v))) → ⊥
   c {u}{(v , w)} p' (p'' , p''') with F w | p₁ {u , v}{w}
   ... | (h1 , h2) | p₂ = p₂ (p' , p'') p'''

φ-inv : {A B C : Obj} → Hom A (¬ₒ (B ⊗ₒ C)) → Hom (A ⊗ₒ B) (¬ₒ C)
φ-inv {(U , X , α)} {(V , Y , β)} {(W , Z , γ)} (h , H , p₁) = (λ c → (snd (h (fst c))) (snd c)) , (λ w → (λ v → H (v , w)) , (λ u → (fst (h u)) w)) , p₂
 where
  j : U × V → Z
  j = λ c → (snd (h (fst c))) (snd c)
  J : W → (V → X) × (U → Y)
  J = λ w → (λ v → H (v , w)) , (λ u → (fst (h u)) w)
  p₂ : ∀{i : U × V} {w : W} → (α ⊗ᵣ β) i (J w) → γ w (j i) → ⊥
  p₂ {(u , v)} {w} (p₃ , p₄) p₅ with h u | p₁ {u}{(v , w)}
  ... | (h₁ , h₂) | p₆ = p₆ p₃ (p₄ , p₅)

-- The following proves that φ and φ-inv are mutual inverse, and thus
-- define a bijection.
φ-bij-1 : ∀{A B C}{m : Hom (A ⊗ₒ B) (¬ₒ C)} → φ-inv (φ m) ≡h id-set m
φ-bij-1 {(U , X , α)} {(V , Y , β)} {(W , Z , γ)}{(h , H , p₁)} = eta-× ext-set , ext-set aux
 where
   aux : {a : W} → ((λ v → fst (H a) v) , (λ u → snd (H a) u)) ≡ H a
   aux {w} with H w
   ... | (h₁ , h₂) = refl

φ-bij-2 : ∀{A B C}{m : Hom A (¬ₒ (B ⊗ₒ C))} → φ (φ-inv m) ≡h id-set m
φ-bij-2 {(U , X , α)} {(V , Y , β)} {(W , Z , γ)}{(h , H , p₁)} = ext-set aux , eta-× ext-set
 where
   aux : {a : U} → ((λ w → fst (h a) w) , (λ v → snd (h a) v)) ≡ h a
   aux {u} with h u
   ... | (h₁ , h₂)= refl

-- The following shows that φ {A}{B}{C} is natural in A, B, and C.
φ-nat-1 : ∀{A A' B C}{n : Hom A' A}{m : Hom (A ⊗ₒ B) (¬ₒ C)}
        → Homₐ n (id {¬ₒ (B ⊗ₒ C)}) (φ {A}{B}{C} m) ≡h φ {A'} {B} {C} (Homₐ (n ⊗ₐ (id {B})) (id {¬ₒ C}) m)
φ-nat-1 {(U , X , α)} {(V , Y , β)} {(V' , Y' , β')} {(W , Z , γ)} {(n , N , pn)} {(m , M , pm)} =
 ext-set (λ {v} → eq-× (ext-set (λ {w} → aux {w})) (ext-set refl)) , ext-set (λ {a} → aux' {a})
 where
   aux : ∀{w v} → snd (M w) (n v) ≡ snd (F⊗ {f = n}{N}{id-set}{id-set} (M w)) v
   aux {w} with M w
   ... | (h₁ , h₂) = refl

   aux' : ∀{a} → N (fst (M (snd a)) (fst a)) ≡ fst (F⊗ {f = n}{N}{id-set}{id-set} (M (snd a))) (fst a)
   aux' {(v' , w)} with M w
   ... | (h₁ , h₂) = refl
   
φ-nat-2 : ∀{A B B' C}{n : Hom B' B}{m : Hom (A ⊗ₒ B) (¬ₒ C)}
  → Homₐ (id {A}) (¬ₐ (n ⊗ₐ id {C})) (φ {A} {B} {C} m) ≡h φ {A} {B'} {C} (Homₐ ((id {A} ⊗ₐ n)) (id {¬ₒ C}) m)
φ-nat-2 {(U , X , α)} {(V , Y , β)} {(V' , Y' , β')} {(W , Z , γ)} {(n , N , pn)} {(m , M , pm)} =
  let f = λ x → fst (M (snd (⟨ n , (λ x₁ → x₁) ⟩ x))) (fst (⟨ n , (λ x₁ → x₁) ⟩ x))
      g = λ c → fst (F⊗ (M (snd c))) (fst c)
   in ext-set (λ {u} → eq-× (ext-set aux) refl) , ext-set {f = f}{g} (λ {a} → aux' {a})
 where
  aux : {u : U}{a : W} → N (snd (M a) u) ≡ snd (F⊗ {f = id-set}{id-set}{n}{N} (M a)) u
  aux {u}{a} with M a
  ... | (h₁ , h₂) = refl

  aux' : {a : Σ V' (λ x → W)}
       →   fst (M (snd (⟨ n , (λ x → x) ⟩ a))) (fst (⟨ n , (λ x → x) ⟩ a))
         ≡ fst (F⊗ {f = id-set}{id-set}{n}{N} (M (snd a))) (fst a)
  aux' {v' , w} with M w
  ... | (h₁ , h₂) = refl

φ-nat-3 : ∀{A B C C'}{n : Hom C' C}{m : Hom (A ⊗ₒ B) (¬ₒ C)}
        → Homₐ (id {A}) (¬ₐ ((id {B}) ⊗ₐ n)) (φ {A}{B}{C} m) ≡h φ {A} {B} {C'} (Homₐ (id {A ⊗ₒ B}) (¬ₐ n) m)
φ-nat-3 {(U , X , α)} {(V , Y , β)} {(V' , Y' , β')} {(W , Z , γ)} {(n , N , pn)} {(m , M , pm)}
 = refl , ext-set (λ {a} → aux {a}) 
 where
   aux : ∀{a} → fst (M (snd (⟨ (λ x → x) , n ⟩ a))) (fst (⟨ (λ x → x) , n ⟩ a)) ≡ fst (M (n (snd a))) (fst a)
   aux {(v , w)} = refl

-- Finally, φ must adhere to a coherence diagrams.  See Definition ??
-- on page ?? of the paper for the diagram.
φ-coh : ∀{A B C D}{m : Hom (A ⊗ₒ (B ⊗ₒ C)) (¬ₒ D)}
  →    φ (φ (Homₐ (α⊗ {A} {B} {C}) (id {¬ₒ D}) m))
    ≡h Homₐ (id {A}) (¬ₐ (α⊗-inv {B} {C} {D})) (φ m)
φ-coh {(U , X , α)} {(V , Y , β)} {(W , Z , γ)} {(S , T , δ)} {(m , M , pm)}
  = ext-set (λ {u} → eq-× aux (ext-set (λ {v} → eq-× aux'' refl))) , ext-set (λ {a} → aux'''' {a})
 where
   aux : ∀{u} → (λ w → snd (fst (Fα {V} (M (snd w))) (fst w)) u) ≡
      (λ p' → fst (snd (M (snd p')) u) (fst p'))
   aux {u} = ext-set (λ {a} → aux' {a})
    where
     aux' : {a : Σ W (λ x → S)} → snd (fst (Fα {V} (M (snd a))) (fst a)) u ≡ fst (snd (M (snd a)) u) (fst a)
     aux' {w , s} with M s
     ... | (h₁ , h₂) = refl

   aux'' : ∀{u v} → (λ w → snd (Fα {V} (M w)) (u , v)) ≡ (λ w → snd (snd (M w) u) v)
   aux'' {u}{v} = ext-set aux'''
    where
      aux''' : {a : S} → snd (Fα {V} (M a)) (u , v) ≡ snd (snd (M a) u) v
      aux''' {s} with M s
      ... | (h₁ , h₂) = refl

   aux'''' : ∀{a}
     →   fst (fst (Fα {V} (M (snd (snd a)))) (fst (snd a))) (fst a)
       ≡ fst (M (snd (rl-assoc-× a))) (fst (rl-assoc-× a))
   aux'''' {v , w , s} with M s
   ... | (h₁ , h₂) = refl

-----------------------------------------------------------------------
-- A dialouge category is a model of multiplicative tensor logic.    --
-- Now Dial₂(Sets) is a model of multiplicative additive tensor      --
-- logic, because we know Dial₂(Sets) has coproducts that distribute --
-- over tensor; Proposition 28 on page 52 of Valeria's thesis.       --
--                                                                   --
-- The battle still left to be faught is showing that Dial₂(Sets) is --
-- a model of full tensor logic.  Thus, we must show that there is   --
-- an exponential resource modality.                                 --
-----------------------------------------------------------------------

-- The following shows that Dial₂(Sets)! is cartesian.

-- First, we define the cartesian product in Dial₂(Sets), and then use
-- !ₒ to put us inside of Dial₂(Sets)!.
_&ᵣ_ : {U X V Y : Set}
  → (α : U → X → Set)
  → (β : V → Y → Set)
  → Σ U (λ x → V)
  → X ⊎ Y
  → Set
_&ᵣ_ α β (u , v) (inj₁ x) = α u x
_&ᵣ_ α β (u , v) (inj₂ y) = β v y

_&ₒ_ : (A B : Obj) → Obj
(U , X , α) &ₒ (V , Y , β) = (U × V) , (X ⊎ Y) , α &ᵣ β

-- The remainder of this file will work under the !ₒ functor which
-- will put us inside of Dial₂(Sets)!.

-- This defines the projection morphism: π₁ : A & B → A.
π₁ : {U X V Y : Set}
  → {α : U → X → Set}
  → {β : V → Y → Set}
  → Hom (!ₒ ((U , X , α) &ₒ (V , Y , β))) (!ₒ (U , X , α))
π₁ {U}{X}{V}{Y}{α}{β} =
  fst ,
  (λ (f : U → (X *)) (p : U × V) → map inj₁ (f (fst p))) ,
  λ {u}{y} p → π₁-cond {u}{y} p
 where
  π₁-cond : {u : Σ U (λ x → V)} {y : U → 𝕃 X} →
      all-pred ((α &ᵣ β) u) (map inj₁ (y (fst u))) →
      all-pred (α (fst u)) (y (fst u))
  π₁-cond {u , v} y = aux y
   where
     aux : {l : X *}
       → all-pred ((α &ᵣ β) (u , v)) (map inj₁ l) → all-pred (α u) l
     aux {[]} triv = triv
     aux {x :: l} (j₁ , j₂) = j₁ , aux j₂

-- This defines the projection morphism: π₂ : A & B → B.
π₂ : {U X V Y : Set}
  → {α : U → X → Set}
  → {β : V → Y → Set}
  → Hom (!ₒ ((U , X , α) &ₒ (V , Y , β))) (!ₒ (V , Y , β))
π₂ {U}{X}{V}{Y}{α}{β} =
  snd , (λ f p → map inj₂ (f (snd p))) , λ {u}{y} p → π₂-cond {u}{y} p
 where
  π₂-cond : {u : Σ U (λ x → V)} {y : V → 𝕃 Y} →
      all-pred ((α &ᵣ β) u) (map inj₂ (y (snd u))) →
      all-pred (β (snd u)) (y (snd u))
  π₂-cond {u , v} y = aux y
   where
     aux : {l : Y *}
       → all-pred ((α &ᵣ β) (u , v)) (map inj₂ l) → all-pred (β v) l
     aux {[]} triv = triv
     aux {x :: l} (j₁ , j₂) = j₁ , aux j₂

cart-ar-crt : {U X V Y W Z : Set}
  → {α : U → X → Set}
  → {β : V → Y → Set}
  → {γ : W → Z → Set}
  → Hom (!ₒ (W , Z , γ)) (!ₒ (U , X , α))
  → Hom (!ₒ (W , Z , γ)) (!ₒ (V , Y , β))
  → (Σ U (λ x → V) → 𝕃 (X ⊎ Y)) → W → 𝕃 Z
cart-ar-crt  (f , F , p₁) (g , G , p₂) j w
  with (λ u → (proj-⊎₁ (j (u , g w)))) | (λ v → (proj-⊎₂ (j (f w , v))))
... | j₁ | j₂ = F j₁ w ++ G j₂ w 

-- This takes two morphisms f : C → A and g : C → B, and constructs
-- a morphism (f,g) : C → A & B.
cart-ar : {U X V Y W Z : Set}
  → {α : U → X → Set}
  → {β : V → Y → Set}
  → {γ : W → Z → Set}
  → Hom (!ₒ (W , Z , γ)) (!ₒ (U , X , α))
  → Hom (!ₒ (W , Z , γ)) (!ₒ (V , Y , β))
  → Hom (!ₒ (W , Z , γ)) (!ₒ ((U , X , α) &ₒ (V , Y , β)))
cart-ar {U}{X}{V}{Y}{W}{Z}{α}{β}{γ} (f , F , p₁) (g , G , p₂)
  = (λ w → (f w , g w)) ,
    cart-ar-crt {α = α}{β}{γ} (f , F , p₁) (g , G , p₂) ,
    (λ {u}{y} p → cart-ar-cond {u}{y} p)
  where
    cart-ar-cond : {u : W} {y : Σ U (λ x → V) → 𝕃 (X ⊎ Y)} →
      all-pred (γ u)
      (F (λ u₁ → proj-⊎₁ (y (u₁ , g u))) u ++
       G (λ v → proj-⊎₂ (y (f u , v))) u) →
      all-pred ((α &ᵣ β) (f u , g u)) (y (f u , g u))
    cart-ar-cond {u}{j} p
      rewrite
        all-pred-append
          {f = γ u}
          {F (λ u₁ → (proj-⊎₁ (j (u₁ , g u)))) u}
          {G (λ v → (proj-⊎₂ (j (f u , v)))) u}
          ∧-unit ∧-assoc
     with p
    ... | (r₁ , r₂) = aux (p₁ r₁) (p₂ r₂)
     where
       aux : ∀{l}
         → all-pred (α (f u)) ((proj-⊎₁ l))
         → all-pred (β (g u)) ((proj-⊎₂ l))
         → all-pred ((α &ᵣ β) (f u , g u)) l
       aux {[]} _ _ = triv
       aux {inj₁ x :: l} (s₁ , s₂) x₂ = s₁ , aux {l} s₂ x₂
       aux {inj₂ y :: l} x₁ (s₁ , s₂) = s₁ , aux {l} x₁ s₂

-- This shows that f ≡ (f,g);π₁.
cart-diag₁ : {U X V Y W Z : Set}
  → {α : U → X → Set}
  → {β : V → Y → Set}
  → {γ : W → Z → Set}
  → {f : Hom (W , Z , γ) (U , X , α)}
  → {g : Hom (W , Z , γ) (V , Y , β)}
  → _≡h_ { !ₒ (W , Z , γ)}{ !ₒ (U , X , α)}
    (!ₐ {W , Z , γ}{U , X , α} f)
    (comp { !ₒ (W , Z , γ)}
          {(!ₒ ((U , X , α) &ₒ (V , Y , β)))}
          { !ₒ (U , X , α)}
          (cart-ar {α = α}{β}
            (!ₐ {W , Z , γ}{U , X , α} f) (!ₐ {W , Z , γ}{V , Y , β} g))
          π₁)
cart-diag₁ {X = X}{Y = Y}{f = f , F , p₁}{g , G , p₂}
  = refl , ext-set (λ {j₁} → ext-set (λ {w} → aux))
  where
    aux : ∀{l : X *} →
      map F l ≡
      map F (proj-⊎₁ {_}{_}{X}{Y} (map inj₁ l)) ++
      map G (proj-⊎₂ (map inj₁ l))
    aux {l} rewrite
      map-proj-⊎₁ {_}{_}{X}{Y} l |
      map-proj-⊎₂-[] {_}{_}{X}{Y} l = sym (++[] (map F l))

-- This shows that g ≡ (f,g);π₂.
cart-diag₂ : {U X V Y W Z : Set}
  → {α : U → X → Set}
  → {β : V → Y → Set}
  → {γ : W → Z → Set}
  → {f : Hom (W , Z , γ) (U , X , α)}
  → {g : Hom (W , Z , γ) (V , Y , β)}
  → _≡h_ { !ₒ (W , Z , γ)}{ !ₒ (V , Y , β)}
    (!ₐ {W , Z , γ}{V , Y , β} g)
    (comp { !ₒ (W , Z , γ)}
          {(!ₒ ((U , X , α) &ₒ (V , Y , β)))}
          { !ₒ (V , Y , β)}
          (cart-ar {α = α}{β}
            (!ₐ {W , Z , γ}{U , X , α} f) (!ₐ {W , Z , γ}{V , Y , β} g))
          π₂)
cart-diag₂ {X = X}{Y = Y}{f = f , F , p₁}{g , G , p₂}
  = refl , ext-set (λ {j₁} → ext-set (λ {w} → aux))
  where
    aux : ∀{l : Y *} →
      map G l ≡
      map F (proj-⊎₁ {_}{_}{X}{Y} (map inj₂ l)) ++
      map G (proj-⊎₂ {_}{_}{X}{Y} (map inj₂ l))
    aux {l} rewrite map-proj-⊎₂ {_}{_}{X}{Y} l |
                    map-proj-⊎₁-[] {_}{_}{X}{Y} l = refl
