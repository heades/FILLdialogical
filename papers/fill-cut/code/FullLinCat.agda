module FullLinCat where

open import unit
open import list
open import list-thms
open import functions renaming (id to id-set)
open import eq

open import Dial2Sets

_* = 𝕃

-- The of-course exponential:
!ₒ-cond : ∀{U X : Set}
  → (U → X → Set)
  → U
  → (U → X *)
  → Set
!ₒ-cond α u f = all-pred (α u) (f u)
   
!ₒ : Obj → Obj
!ₒ (U , X , α) = U , (U → X *) , !ₒ-cond α

!-cta : {V Y U X : Set}
  → (Y → X)
  → (U → V)
  → (V → Y *)
  → (U → X *)
!-cta F f g = λ u → list-funct F (g (f u))

!ₐ-cond : ∀{U V Y X : Set}{F : Y → X}{f : U → V}
  → (α : U → X → Set)
  → (β : V → Y → Set)
  → (p : {u : U} {y : Y} → α u (F y) → β (f u) y)
    {u : U}{l : Y *}
  → all-pred (α u) (list-funct F l)
  → all-pred (β (f u)) l
!ₐ-cond _ _ _ {l = []} _ = triv
!ₐ-cond α β p {u}{x :: xs} (p' , p'') = p p' , !ₐ-cond α β p p''     
      
!ₐ : {A B : Obj} → Hom A B → Hom (!ₒ A) (!ₒ B)
!ₐ {U , X , α}{V , Y , β} (f , F , p) = f , !-cta F f , !ₐ-cond α β p

-- Of-course is a comonad:
ε : ∀{A} → Hom (!ₒ A) A
ε {U , X , α} = id-set , (λ x y → [ x ]) , fst

δ-cta : {U X : Set} → (U → 𝕃 (U → 𝕃 X)) → U → 𝕃 X
δ-cta g u = foldr (λ f rest → (f u) ++ rest) [] (g u)
  
δ : ∀{A} → Hom (!ₒ A) (!ₒ (!ₒ A))
δ {U , X , α} = id-set , δ-cta , δ-cond
  where
   δ-cond : {u : U} {l : 𝕃 (U → 𝕃 X)}
     → all-pred (α u) (foldr (λ f → _++_ (f u)) [] l)
     → all-pred (λ f
     → all-pred (α u) (f u)) l
   δ-cond {l = []} _ = triv
   δ-cond {u}{l = x :: l'} p with
     all-pred-append {X}{α u}{x u}{foldr (λ f → _++_ (f u)) [] l'} ∧-unit ∧-assoc
   ... | p' rewrite p' = fst p , δ-cond {u} {l'} (snd p)
 
comonand-diag₁ : ∀{A} → (δ {A}) ○ (!ₐ (δ {A})) ≡h (δ {A}) ○ (δ { !ₒ A})
comonand-diag₁ {U , X , α} = refl , ext-set (λ {a} → ext-set (λ {a₁} → aux {a₁}{a a₁}))
 where
   aux : ∀{a₁ : U}{l : 𝕃 (U → 𝕃 (U → 𝕃 X))} →
      foldr (λ f → _++_ (f a₁)) []
      (map (λ g u → foldr (λ f → _++_ (f u)) [] (g u)) l)
      ≡
      foldr (λ f → _++_ (f a₁)) [] (foldr (λ f → _++_ (f a₁)) [] l)
   aux {a}{[]} = refl  
   aux {a}{x :: l} rewrite
     sym (foldr-append {l₁ = x a}{foldr (λ f → _++_ (f a)) [] l}{a})
     = cong2 {a = foldr (λ f → _++_ (f a)) [] (x a)}
             _++_
             refl
             (aux {a}{l})

comonand-diag₂ : ∀{A} → (δ {A}) ○ (ε { !ₒ A}) ≡h (δ {A}) ○ (!ₐ (ε {A}))
comonand-diag₂ {U , X , α} = refl , ext-set (λ {f} → ext-set (λ {a} → aux {a}{f a}))
 where
  aux : ∀{a : U}{l : X *} → l ++ [] ≡ foldr (λ f₁ → _++_ (f₁ a)) [] (map (λ x y → x :: []) l)
  aux {a}{[]} = refl
  aux {a}{x :: l} with aux {a}{l}
  ... | IH rewrite ++[] l = cong2 {a = x} {x} {l}
                      {foldr (λ f₁ → _++_ (f₁ a)) [] (map (λ x₁ y → x₁ :: []) l)} _::_ refl
                      IH

-- Monoidal nat. trans. m⊤ : ⊤ → !⊤:
m⊤ : Hom I (!ₒ I)
m⊤ = id-set , (λ f → triv) , m⊤-cond
 where
  m⊤-cond : {u : ⊤} {l : 𝕃 ⊤} → ι u triv → all-pred (ι u) l
  m⊤-cond {triv}{[]} triv = triv
  m⊤-cond {triv}{triv :: l} triv = triv , m⊤-cond {triv}{l} triv
  
m⊤-diag₁ : _≡h_ {I}{ !ₒ (!ₒ I)}
  (comp {I} { !ₒ I} { !ₒ (!ₒ I)} m⊤ (!ₐ {I}{ !ₒ I} m⊤))
  (comp {I} { !ₒ I} { !ₒ (!ₒ I)} m⊤ (δ {I}))
m⊤-diag₁ = refl , refl

m⊤-diag₂ : _≡h_ {I}{I} (comp {I}{ !ₒ I}{I} m⊤ (ε {I})) (id {I})
m⊤-diag₂ = refl , ext-set aux
 where
  aux : {a : ⊤} → triv ≡ a
  aux {triv} = refl

-- The monoidal nat. trans. m : !A ⊗ !B → !(A ⊗ B):
h'₁ : {U V X Y : Set} → (((V → X) × (U → Y)) *) → (V → U → (X *))
h'₁ [] v u = []
h'₁ ((j₁ , j₂) :: js) v u = (j₁ v) :: h'₁ js v u

h₁ : {U V X Y : Set} → ((U × V) → (((V → X) × (U → Y)) *)) → (V → U → (X *))
h₁ g v u = h'₁ (g (u , v)) v u

h'₂ : {U V X Y : Set} → (((V → X) × (U → Y)) *) → (U → V → (Y *))
h'₂ [] u v = []
h'₂ ((j₁ , j₂) :: js) u v = (j₂ u) :: h'₂ js u v

h₂ : {U V X Y : Set} → ((U × V) → (((V → X) × (U → Y)) *)) → (U → V → (Y *))
h₂ g u v = h'₂ (g (u , v)) u v

m⊗ : {A B : Obj} → Hom ((!ₒ A) ⊗ₒ (!ₒ B)) (!ₒ (A ⊗ₒ B))
m⊗ {U , X , α} {V , Y , β} = id-set , (λ g → h₁ g , h₂ g) , (λ {u}{y} x → m⊗-cond {u}{y} x)
 where
  m⊗-cond : {u : Σ U (λ x → V)}
      {y : Σ U (λ x → V) → 𝕃 (Σ (V → X) (λ x → U → Y))} →
      ((λ u₁ f → all-pred (α u₁) (f u₁)) ⊗ᵣ
       (λ u₁ f → all-pred (β u₁) (f u₁)))
      u
      ((λ v u₁ → h'₁ (y (u₁ , v)) v u₁) ,
       (λ u₁ v → h'₂ (y (u₁ , v)) u₁ v)) →
      all-pred ((α ⊗ᵣ β) u) (y u)
  m⊗-cond {(u , v)}{g} (p₁ , p₂) = aux p₁ p₂
   where
    aux : ∀{l}
        → all-pred (α u) (h'₁ l v u)
        → all-pred (β v) (h'₂ l u v)
        → all-pred ((α ⊗ᵣ β) (u , v)) l
    aux {[]} p₁ p₂ = triv
    aux {(j₁ , j₂) :: js} (p₁ , p₂) (p₃ , p₄) = (p₁ , p₃) , aux {js} p₂ p₄

-- The following diagrams can be found on page 24 of the report.
m⊗-diag-A : ∀{A} → (m⊤ ⊗ₐ (id { !ₒ A})) ○ (m⊗ {I} {A} ○ !ₐ (λ⊗ {A})) ≡h λ⊗ { !ₒ A}
m⊗-diag-A {U , X , α} = ext-set (λ {a} → aux {a}) ,
                        ext-set (λ {g} → cong2 _,_ refl (ext-set (aux' {g})))
 where
  aux : {a : Σ ⊤ (λ x → U)} → snd (⟨ (λ x → x) , (λ x → x) ⟩ a) ≡ snd a
  aux {triv , u} = refl
  aux' : {g : U → X *} → {a : ⊤} → (λ v → h'₂ (map (λ x → (λ _ → triv) , (λ _ → x)) (g v)) a v) ≡ g
  aux' {g}{triv} = ext-set (λ {a} → aux'' {a}{g a})
   where
    aux'' : {a : U}{l : X *} → h'₂ (map (λ x → (λ _ → triv) , (λ _ → x)) l) triv a ≡ l
    aux'' {u}{[]} = refl
    aux'' {u}{x :: xs} rewrite aux'' {u}{xs} = refl

m⊗-diag-B : ∀{A} → ((id { !ₒ A}) ⊗ₐ m⊤) ○ (m⊗ {A} {I} ○ !ₐ (ρ⊗ {A})) ≡h ρ⊗ { !ₒ A}
m⊗-diag-B {U , X , α} = (ext-set (λ {a} → aux {a})) , ext-set (λ {g} → cong2 _,_ (ext-set aux') refl)
 where
   aux : {a : Σ U (λ x → ⊤)} → fst (⟨ (λ x → x) , (λ x → x) ⟩ a) ≡ fst a
   aux {u , triv} = refl
   aux' : {g : U → X *} → {a : ⊤} → (λ u → h'₁ (map (λ x → (λ x₁ → x) , (λ x₁ → triv)) (g u)) a u) ≡ g
   aux' {g}{triv} = ext-set (λ {u} →  aux'' {g u}{u})
    where
      aux'' : ∀{l : X *}{u : U} → h'₁ (map (λ x → (λ x₁ → x) , (λ x₁ → triv)) l) triv u ≡ l
      aux'' {[]}{u}  = refl
      aux'' {x :: xs}{u} rewrite aux'' {xs}{u} = refl

m⊗-diag-C : ∀{A B} → β⊗ { !ₒ A} { !ₒ B} ○ m⊗ {B} {A} ≡h (m⊗ {A}{B}) ○ (!ₐ (β⊗ {A}{B}))
m⊗-diag-C {U , X , α}{V , Y , β} =
          refl ,
          ext-set (λ {g} → cong2 _,_ (ext-set (λ {v} → ext-set (λ {u} → aux {g (v , u)}{u}{v})))
                                     (ext-set (λ {u} → ext-set (λ {v} → aux' {g (v , u)}{u}{v}))))
 where
   aux : ∀{l : 𝕃 (Σ (U → Y) (λ x → V → X))}{u v} → h'₂ l v u ≡  h'₁ (map twist-× l) v u
   aux {[]} = refl
   aux {(j₁ , j₂) :: js} {u}{v} rewrite aux {js}{u}{v} = refl
   aux' : ∀{l : 𝕃 (Σ (U → Y) (λ x → V → X))}{u v} → h'₁ l u v ≡  h'₂ (map twist-× l) u v
   aux' {[]} = refl
   aux' {(j₁ , j₂) :: js} {u}{v} rewrite aux' {js}{u}{v} = refl

m⊗-diag-D : ∀{A B C : Obj}
  →  α⊗ { !ₒ A} { !ₒ B} { !ₒ C} ○ id { !ₒ A} ⊗ₐ m⊗ {B} {C} ○ m⊗ {A} {B ⊗ₒ C}
  ≡h ((m⊗ {A}{B}) ⊗ₐ (id { !ₒ C})) ○ (m⊗ {A ⊗ₒ B}{C}) ○ (!ₐ (α⊗ {A}{B}{C})) 
m⊗-diag-D {U , X , α}{V , Y , β}{W , Z , γ} =
  ext-set aux  ,
  ext-set (λ {g} → cong2 _,_
                         (ext-set
                           (λ {w} → cong2 _,_
                                          (ext-set
                                            (λ {v} → ext-set
                                                      (λ {u} → aux' {g (u , v , w)}{u}{v}{w})))
                                          (ext-set (λ {u} → ext-set (λ {v} → aux'' {g (u , v , w)}{u}{v}{w})))))
                         (ext-set (λ {a} → aux''' {a}{g})))
 where
  aux : {a : Σ (Σ U (λ x → V)) (λ x → W)}
    → ⟨ (λ x → x) , (λ x → x) ⟩ (lr-assoc-× a) ≡ lr-assoc-× (⟨ (λ x → x) , (λ x → x) ⟩ a)
  aux {((u , v) , w)} = refl
  aux' : ∀{l : 𝕃 (Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z)))}{u v w}
    → h'₁ l (v , w) u ≡ h'₁ (h'₁ (map (Fα {V}{W}{X}{Y}{U}{V}{Z}) l) w (u , v)) v u
  aux' {[]} = refl
  aux' {(j₁ , j₂) :: js}{u}{v}{w} rewrite aux' {js}{u}{v}{w} = refl
  aux'' : ∀{l : 𝕃 (Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z)))}{u v w}
    → h'₁ (h'₂ l u (v , w)) w v ≡ h'₂ (h'₁ (map (Fα {V}{W}{X}{Y}{U}{V}{Z}) l) w (u , v)) u v
  aux'' {[]} = refl
  aux'' {(j₁ , j₂) :: js}{u}{v}{w} with j₂ u
  ... | (j₃ , j₄) rewrite aux'' {js}{u}{v}{w} = refl
  aux''' : ∀{a : Σ U (λ x → V)}{g : Σ U (λ x → Σ V (λ x₁ → W)) →
    𝕃 (Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z)))} →
       (λ v →
          h'₂ (h'₂ (g (fst a , snd a , v)) (fst a) (snd a , v)) (snd a) v)
       ≡ (λ v → h'₂ (map (Fα {V}{W}{X}{Y}{U}{V}{Z}) (g (lr-assoc-× (a , v)))) a v)
  aux''' {u , v}{g} = ext-set (λ {w} → aux'''' {g (u , v , w)}{w})
   where
     aux'''' : ∀{l : 𝕃 (Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z)))}{w : W}
       → h'₂ (h'₂ l u (v , w)) v w ≡ h'₂ (map (Fα {V}{W}{X}{Y}{U}{V}{Z}) l) (u , v) w
     aux'''' {[]} = refl
     aux'''' {(j₁ , j₂) :: js}{w} with j₂ u
     ... | (j₃ , j₄) rewrite aux'''' {js}{w} = refl
