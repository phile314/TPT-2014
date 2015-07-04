{-#  OPTIONS --no-termination-check  #-}
{-#  OPTIONS --no-positivity-check  #-}

--  Only needed for Indexed2IG, should be removed...
{-#  OPTIONS --type-in-type  #-}

module fcadgp where

open import Relation.Binary.PropositionalEquality public
open import Coinduction public
open import Data.Empty public
open import Data.Unit public hiding (setoid ; decSetoid ; preorder)
open import Data.Sum public hiding (map)
open import Data.Product public hiding (map)
open import Function public
open import Level public

module Regular where

  data Code : Set where
    U    :                 Code
    I'   :                 Code
    _⊕_  : (F G : Code) →  Code
    _⊗_  : (F G : Code) →  Code

  ⟦_⟧ : Code → (Set → Set)
  ⟦ U      ⟧  A = ⊤
  ⟦ I'     ⟧  A = A
  ⟦ F ⊕ G  ⟧  A = ⟦ F ⟧ A  ⊎  ⟦ G ⟧ A
  ⟦ F ⊗ G  ⟧  A = ⟦ F ⟧ A  ×  ⟦ G ⟧ A

  data μ (F : Code) : Set where 
    ⟨_⟩ : ⟦ F ⟧ (μ F) → μ F

  map  :  (F : Code) → {A B : Set} → (A → B) → ⟦ F ⟧ A → ⟦ F ⟧ B
  map U        f _            = tt
  map I'       f x            = f x
  map (F ⊕ G)  f (inj₁  x)    = inj₁  (map F  f x)
  map (F ⊕ G)  f (inj₂  x)    = inj₂  (map G  f x)
  map (F ⊗ G)  f (x , y)  = map F f x , map G f y

  cata : {A : Set} -> (F : Code) -> (⟦ F ⟧ A -> A) -> μ F -> A
  cata C f ⟨ x ⟩ = f (map C (cata C f) x)

  NatC : Code
  NatC = U ⊕ I'

  aNat : μ NatC
  aNat = ⟨ inj₂ ⟨ inj₂ ⟨ inj₁ tt ⟩ ⟩ ⟩

  map∀ : (C : Code) {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → (∀ x → map C f x ≡ map C g x)
  map∀ U p x = refl
  map∀ I' p x = p x
  map∀ (F ⊕ G) p (inj₁ x) = cong inj₁ (map∀ F p x)
  map∀ (F ⊕ G) p (inj₂ x) = cong inj₂ (map∀ G p x)
  map∀ (F ⊗ G) p (x , y)  = cong₂ _,_ (map∀ F p x) (map∀ G p y)

  map∘ : {A B C : Set} (D : Code) {f : B → C} {g : A → B} {x : ⟦ D ⟧ A}
            → map D f (map D g x) ≡ map D (f ∘ g) x
  map∘ U = refl
  map∘ I' {_} = refl
  map∘ (F ⊕ G) {x = inj₁ _} = cong inj₁ (map∘ F)
  map∘ (F ⊕ G) {x = inj₂ _} = cong inj₂ (map∘ G)
  map∘ (F ⊗ G) {x = _ , _}  = cong₂ _,_ (map∘ F) (map∘ G)

  mapId : ∀ {A} (C : Code) {x : ⟦ C ⟧ A} → map C id x ≡ x
  mapId U {tt} = refl
  mapId I' = refl
  mapId (F ⊕ G) {inj₁ _} = cong inj₁ (mapId F)
  mapId (F ⊕ G) {inj₂ _} = cong inj₂ (mapId G)
  mapId (F ⊗ G) {_ , _}  = cong₂ _,_ (mapId F) (mapId G)

module PolyP where
 mutual
  data Code : Set where
    U    :                 Code
    P'   :                 Code
    I'   :                 Code
    _⊕_  : (F G : Code) →  Code
    _⊗_  : (F G : Code) →  Code
    _⊚_  : (F G : Code) →  Code


  ⟦_⟧ : Code → (Set → Set → Set)
  ⟦ U      ⟧  A R = ⊤
  ⟦ P'     ⟧  A R = A
  ⟦ I'     ⟧  A R = R
  ⟦ F ⊕ G  ⟧  A R = ⟦ F ⟧ A R ⊎  ⟦ G ⟧ A R
  ⟦ F ⊗ G  ⟧  A R = ⟦ F ⟧ A R ×  ⟦ G ⟧ A R
  ⟦ F ⊚ G  ⟧  A R = μ F (⟦ G ⟧ A R)


  data μ (F : Code) (A : Set) : Set where 
    ⟨_⟩ : ⟦ F ⟧ A (μ F A) → μ F A


  map  :  {A B R S : Set} (F : Code) → (A → B) → (R → S) → ⟦ F ⟧ A R → ⟦ F ⟧ B S
  map U        f g _            = tt
  map P'       f g x            = f  x
  map I'       f g x            = g  x
  map (F ⊕ G)  f g (inj₁  x)    = inj₁  (map F  f g x)
  map (F ⊕ G)  f g (inj₂  x)    = inj₂  (map G  f g x)
  map (F ⊗ G)  f g (x , y)  = map F f g x , map G f g y
  map (F ⊚ G)  f g ⟨ x ⟩        =  ⟨ map F (map G f g) (map (F ⊚ G) f g) x ⟩

  pmap  :  {A B : Set} (F : Code) →  (A → B) → μ F A → μ F B
  pmap F f ⟨ x ⟩ = ⟨ map F f (pmap F f) x ⟩

 ListC : Code
 ListC = U ⊕ (P' ⊗ I')

 RoseC : Code
 RoseC = P' ⊗ (ListC ⊚ I')

 sRose : μ RoseC ⊤
 sRose = ⟨ tt , ⟨ inj₁ tt ⟩ ⟩ 

 lRose : μ RoseC ⊤
 lRose = ⟨ tt , ⟨ inj₂ (sRose , ⟨ inj₂ (sRose , ⟨ inj₁ tt ⟩)⟩)⟩ ⟩

module Multirec where

  Indexed : Set → Set₁
  Indexed I = I → Set

  data Code (I : Set) : Set where
    U    :                    Code I
    I'   : I               →  Code I
    !    : I               →  Code I
    _⊕_  : (F G : Code I)  →  Code I
    _⊗_  : (F G : Code I)  →  Code I

  ⟦_⟧ : {I : Set} → Code I → Indexed I → Indexed I
  ⟦ U      ⟧  r i = ⊤
  ⟦ I' j   ⟧  r i = r j
  ⟦ ! j    ⟧  r i = i ≡ j
  ⟦ F ⊕ G  ⟧  r i = ⟦ F ⟧ r i  ⊎  ⟦ G ⟧ r i
  ⟦ F ⊗ G  ⟧  r i = ⟦ F ⟧ r i  ×  ⟦ G ⟧ r i

  data μ {I : Set} (F : Code I) (i : I) : Set where 
    ⟨_⟩ : ⟦ F ⟧ (μ F) i → μ F i

  map  :  {I : Set} {R S : Indexed I} (F : Code I)
       →  (∀ i → R i → S i) → (∀ i → ⟦ F ⟧ R i → ⟦ F ⟧ S i)
  map U        f i _            = tt
  map (I' j)   f i x            = f j x
  map (! j)    f i x            = x
  map (F ⊕ G)  f i (inj₁  x)    = inj₁  (map F  f i x)
  map (F ⊕ G)  f i (inj₂  x)    = inj₂  (map G  f i x)
  map (F ⊗ G)  f i (x , y)  = map F f i x , map G f i y

  mutual
    data Zig :  Set where
      zig  : Zag -> Zig
      end  : Zig
    
    data Zag :  Set where
      zag : Zig -> Zag

  ZigC  : Code (⊤ ⊎ ⊤)
  ZigC    = I' (inj₂ tt) ⊕ U

  ZagC  : Code (⊤ ⊎ ⊤)
  ZagC    = I' (inj₁ tt)

  ZigZagC : Code (⊤ ⊎ ⊤)
  ZigZagC = (! (inj₁ tt) ⊗ ZigC) ⊕ (! (inj₂ tt) ⊗ ZagC)
  
  zigZagEnd : μ ZigZagC (inj₁ tt)
  zigZagEnd = ⟨ inj₁ (refl , inj₁ ⟨ inj₂ (refl , ⟨ inj₁ (refl , inj₂ tt) ⟩) ⟩) ⟩

module Indexed where  
 mutual
  Indexed : Set → Set₁
  Indexed I = I → Set

  _∣_  :  ∀ {I J} → Indexed I → Indexed J
       →  Indexed (I ⊎ J)
  (r ∣ s) (inj₁  i) = r  i
  (r ∣ s) (inj₂  i) = s  i

  data Code (I O : Set) : Set₁ where
    U     :        Code I O
    I'    :  I  →  Code I O
    !     :  O  →  Code I O
    _⊕_   :  (F G : Code I O)  → Code I O
    _⊗_   :  (F G : Code I O)  → Code I O
    _⊚_   :  {M : Set} → (F : Code M O)
          →  (G : Code I M) → Code I O
    Fix   :  (F : Code (I ⊎ O) O) → Code I O

  ⟦_⟧  :  {I O : Set} → Code I O
       →  Indexed I → Indexed O
  ⟦ U      ⟧  r i =  ⊤
  ⟦ I' j   ⟧  r i =  r j
  ⟦ ! j    ⟧  r i =  i ≡ j
  ⟦ F ⊕ G  ⟧  r i =  ⟦ F ⟧ r i  ⊎  ⟦ G ⟧ r i
  ⟦ F ⊗ G  ⟧  r i =  ⟦ F ⟧ r i  ×  ⟦ G ⟧ r i
  ⟦ F ⊚ G  ⟧  r i =  ⟦ F ⟧ (⟦ G ⟧ r) i
  ⟦ Fix F  ⟧  r i =  μ F r i

  data μ {I O : Set} (F : Code (I ⊎ O) O) (r : Indexed I) (o : O) : Set where
    ⟨_⟩ : ⟦ F ⟧ (r ∣ μ F r) o → μ F r o

  _⇉_ : ∀ {I} → (R S : Indexed I) → Set
  r ⇉ s = (i : _) → r i → s i

  _∥_ : ∀ {I J} {A C : Indexed I} {B D : Indexed J} → A ⇉ C → B ⇉ D → (A ∣ B) ⇉ (C ∣ D)
  (f ∥ g) (inj₁  x) z = f  x z
  (f ∥ g) (inj₂  x) z = g  x z
   
  map : {I O : Set} {r s : Indexed I} (F : Code I O) → (r ⇉ s) → ⟦ F ⟧ r ⇉ ⟦ F ⟧ s
  map U        f i _            = tt
  map (I' j)   f i x            = f j x
  map (! j)    f i x            = x
  map (F ⊕ G)  f i (inj₁  x)    = inj₁  (map F  f i x)
  map (F ⊕ G)  f i (inj₂  x)    = inj₂  (map G  f i x)
  map (F ⊗ G)  f i (x , y)  = map F f i x , map G f i y
  map (F ⊚ G)  f i x            = map F (map G f) i x
  map (Fix F)  f i ⟨ x ⟩        = ⟨ map F (f ∥ map (Fix F) f) i x ⟩

 infix 4 _≅_
 _≅_ : ∀ {I : Set}{r s : Indexed I} (f g : r ⇉ s) → Set
 f ≅ g = ∀ i x → f i x ≡ g i x

 _⇉∘_ : {Ix : Set} {R S T : Indexed Ix} → S ⇉ T → R ⇉ S → R ⇉ T
 (f ⇉∘ g) ix i = f ix (g ix i)

 id⇉ : {Ix : Set} {R : Indexed Ix} → R ⇉ R
 id⇉ i x = x

 ∥∘ : {I J : Set}{r₁ s₁ t₁ : Indexed I}{r₂ s₂ t₂ : Indexed J} → 
      {f₁ : s₁ ⇉ t₁}{g₁ : r₁ ⇉ s₁}{f₂ : s₂ ⇉ t₂}{g₂ : r₂ ⇉ s₂} →
      ((f₁ ⇉∘ g₁) ∥ (f₂ ⇉∘ g₂)) ≅ ((f₁ ∥ f₂) ⇉∘ (g₁ ∥ g₂))
 ∥∘ (inj₁ i) x = refl
 ∥∘ (inj₂ j) x = refl

 ∥cong : {I J : Set}{r u : Indexed I}{s v : Indexed J}{f₁ f₂ : r ⇉ u}{g₁ g₂ : s ⇉ v} →
         f₁ ≅ f₂ → g₁ ≅ g₂ → (f₁ ∥ g₁) ≅ (f₂ ∥ g₂)
 ∥cong if ig (inj₁ i) x = if i x
 ∥cong if ig (inj₂ j) x = ig j x

 ∥id : {I J : Set} {r : Indexed I} {s : Indexed J}{f : r ⇉ r}{g : s ⇉ s} →
       f ≅ id⇉ → g ≅ id⇉ → (f ∥ g) ≅ id⇉
 ∥id if ig (inj₁ i) x = if i x
 ∥id if ig (inj₂ j) x = ig j x

 map-cong : {I O : Set}{r s : Indexed I}{f g : r ⇉ s}→
            (C : Code I O) → f ≅ g →
            map C f ≅ map C g
 map-cong U           ip i x        = refl
 map-cong (I' i′)     ip i x        = ip i′ x
 map-cong (F ⊕ G)     ip i (inj₁ x) = cong inj₁ (map-cong F ip i x)
 map-cong (F ⊕ G)     ip i (inj₂ x) = cong inj₂ (map-cong G ip i x)
 map-cong (F ⊗ G)     ip i (x , y)  = cong₂ _,_ (map-cong F ip i x) (map-cong G ip i y)
 map-cong (F ⊚ G)     ip i x        = map-cong F (map-cong G ip) i x
 map-cong (! o′)      ip i x        = refl
 map-cong (Fix F)     ip i ⟨ x ⟩    = cong ⟨_⟩ (map-cong F (∥cong ip (map-cong (Fix F) ip)) i x)

 map-id : {I O : Set}{r : Indexed I}(C : Code I O) →
          map {r = r} C id⇉ ≅ id⇉
 map-id U          i x        = refl
 map-id (I' i′)    i x        = refl
 map-id (F ⊕ G)    i (inj₁ x) = cong inj₁ (map-id F i x)
 map-id (F ⊕ G)    i (inj₂ x) = cong inj₂ (map-id G i x)
 map-id (F ⊗ G)    i (x , y)  = cong₂ _,_ (map-id F i x) (map-id G i y)
 map-id (F ⊚ G)    i x        = trans (map-cong F (map-id G) i x) (map-id F i x)
 map-id (! o′)     i x        = refl
 map-id (Fix F)    i ⟨ x ⟩    = cong ⟨_⟩ (trans (map-cong F (∥id (λ _ _ → refl)
                                                            (map-id (Fix F))) i x)
                                                (map-id F i x))

 map-∘ : {I O : Set} {r s t : Indexed I}
         (C : Code I O) (f : s ⇉ t) (g : r ⇉ s)
       → map C (f ⇉∘ g) ≅ map C f ⇉∘ map C g
 map-∘ U           f g i x        = refl
 map-∘ (I' i′)     f g i x        = refl
 map-∘ (F ⊕ G)     f g i (inj₁ x) = cong inj₁ (map-∘ F f g i x)
 map-∘ (F ⊕ G)     f g i (inj₂ x) = cong inj₂ (map-∘ G f g i x)
 map-∘ (F ⊗ G)     f g i (x , y)  = cong₂ _,_ (map-∘ F f g i x) (map-∘ G f g i y)
 map-∘ (F ⊚ G)     f g i x        = trans (map-cong F (map-∘ G f g) i x)
                                          (map-∘ F (map G f) (map G g) i x)
 map-∘ (! o′)      f g i x        = refl
 map-∘ (Fix F)     f g i ⟨ x ⟩    = cong ⟨_⟩ (trans (map-cong F (∥cong (λ _ _ → refl)
                                                                       (map-∘ (Fix F) f g))
                                                              i x)
                                             (trans (map-cong F ∥∘ i x)
                                                    (map-∘ F (f ∥ map (Fix F) f)
                                                             (g ∥ map (Fix F) g) i x)))
module IG where

  open import Data.Nat

  data Code : Set₁ where
    U     :                  Code
    K     : Set           →  Code
    R'    : (C : ∞ Code)  →  Code
    _⊕_   : (C D : Code)  →  Code
    _⊗_   : (C D : Code)  →  Code

  data ⟦_⟧ : Code → Set₁ where
    tt       :                                   ⟦ U      ⟧
    k        : {A : Set}     → A              →  ⟦ K A    ⟧
    rec      : {C : ∞ Code}  → ⟦ ♭ C ⟧        →  ⟦ R' C   ⟧
    inj₁     : {C D : Code}  → ⟦ C ⟧          →  ⟦ C ⊕ D  ⟧
    inj₂     : {C D : Code}  → ⟦ D ⟧          →  ⟦ C ⊕ D  ⟧
    _,_  : {C D : Code}  → ⟦ C ⟧ → ⟦ D ⟧  →  ⟦ C ⊗ D  ⟧

  ListC : Set → Code
  ListC A = U ⊕ (K A ⊗ R' (♯ ListC A))

  crush : {R : Set} (A : Code) → (R → R → R) → (R → R) → R → ⟦ A ⟧ → R
  crush U        _comb_ frec zero' _            = zero'
  crush (K y)    _comb_ frec zero' _            = zero'
  crush (R' C)   _comb_ frec zero' (rec x)      = frec (crush (♭ C) _comb_ frec zero' x)
  crush (C ⊕ D)  _comb_ frec zero' (inj₁ x)     = crush C      _comb_ frec zero' x
  crush (C ⊕ D)  _comb_ frec zero' (inj₂ x)     = crush D      _comb_ frec zero' x
  crush (C ⊗ D)  _comb_ frec zero' (x , y)  = (crush C _comb_ frec zero' x) comb (crush D _comb_ frec zero' y)

  size : (A : Code) → ⟦ A ⟧ → ℕ
  size C = crush C _+_ Data.Nat.suc 0

  aList : ⟦ ListC ⊤ ⟧
  aList = inj₂ (k tt , rec (inj₂ (k tt , rec (inj₁ tt))))

  testSize : size _ aList  ≡ 2
  testSize = refl

module Regular2PolyP where
  r2pC : Regular.Code → PolyP.Code
  r2pC Regular.U          = PolyP.U
  r2pC Regular.I'         = PolyP.I'
  r2pC (Regular._⊕_ F G)  = (PolyP._⊕_ (r2pC F) (r2pC G))
  r2pC (Regular._⊗_ F G)  = (PolyP._⊗_ (r2pC F) (r2pC G))

  fromRegular : {R : Set} (C : Regular.Code) → (Regular.⟦_⟧ C R) → (PolyP.⟦_⟧ (r2pC C) ⊥ R)
  fromRegular Regular.U           tt           = tt
  fromRegular Regular.I'          x            = x
  fromRegular (Regular._⊕_ F G)   (inj₁  x)    = inj₁  (fromRegular F  x)
  fromRegular (Regular._⊕_ F G)   (inj₂  x)    = inj₂  (fromRegular G  x)
  fromRegular (Regular._⊗_ F G)   (x , y)  = fromRegular F x , fromRegular G y

  fromμRegular : (C : Regular.Code) → Regular.μ C → PolyP.μ (r2pC C) ⊥
  fromμRegular C (Regular.⟨_⟩ x) 
    = (PolyP.⟨_⟩ (fromRegular C (Regular.map C (fromμRegular C) x)))

  toRegular : {R : Set} (C : Regular.Code) → PolyP.⟦_⟧ (r2pC C) ⊥ R → Regular.⟦_⟧ C R
  toRegular  Regular.U        = id
  toRegular  Regular.I'       = id
  toRegular (Regular._⊕_ F G) = [_,_] (inj₁ ∘ toRegular F) (inj₂ ∘ toRegular G)
  toRegular (Regular._⊗_ F G) = <_,_> (toRegular F ∘ proj₁) (toRegular G ∘ proj₂)

  toμRegular : (C : Regular.Code) → PolyP.μ (r2pC C) ⊥ → Regular.μ C
  toμRegular C (PolyP.⟨_⟩ x) = Regular.⟨_⟩ (toRegular C (PolyP.map (r2pC C) id (toμRegular C) x))

  iso₁ : {R : Set} → (C : Regular.Code) → (x : (Regular.⟦_⟧ C) R) → toRegular C (fromRegular C x) ≡ x
  iso₁ Regular.U          _            = refl
  iso₁ Regular.I'         _            = refl
  iso₁ (Regular._⊕_ F G)  (inj₁  x)    = cong inj₁  (iso₁ F  x)
  iso₁ (Regular._⊕_ F G)  (inj₂  x)    = cong inj₂  (iso₁ G  x)
  iso₁ (Regular._⊗_ F G)  (x , y)  = cong₂ _,_ (iso₁ F x) (iso₁ G y)

  lemma₁ : {R₁ R₂ : Set} (C : Regular.Code)
           {f : R₁ → R₂} (x : PolyP.⟦_⟧ (r2pC C) ⊥ R₁)
         → toRegular C (PolyP.map (r2pC C) id f x)
         ≡ Regular.map C f (toRegular C x)
  lemma₁ Regular.U     _ = refl
  lemma₁ Regular.I'    _ = refl
  lemma₁ (Regular._⊕_ F G) (inj₁ x) = cong inj₁ (lemma₁ F x)
  lemma₁ (Regular._⊕_ F G) (inj₂ x) = cong inj₂ (lemma₁ G x)
  lemma₁ (Regular._⊗_ F G) (x , y)  = cong₂ _,_ (lemma₁ F x) (lemma₁ G y)

  open ≡-Reasoning

  isoμ₁ : (C : Regular.Code) (x : Regular.μ C) → toμRegular C (fromμRegular C x) ≡ x
  isoμ₁ C (Regular.⟨_⟩ x) = cong Regular.⟨_⟩ $

      begin

        toRegular C (PolyP.map (r2pC C) id (toμRegular C) (fromRegular C (Regular.map C (fromμRegular C) x)))

      ≡⟨ lemma₁ C _ ⟩ 

        Regular.map C (toμRegular C) (toRegular C (fromRegular C (Regular.map C (fromμRegular C) x)))
 
      ≡⟨ cong (Regular.map C (toμRegular C)) (iso₁ C _) ⟩

        Regular.map C (toμRegular C) (Regular.map C (fromμRegular C) x)

      ≡⟨ Regular.map∘ C ⟩

        Regular.map C (toμRegular C ∘ fromμRegular C) x

      ≡⟨ Regular.map∀ C (isoμ₁ C) x ⟩

        Regular.map C id x

      ≡⟨ Regular.mapId C ⟩

        x ∎

module PolyP2Indexed where
  p2iC : PolyP.Code → Indexed.Code (⊤ ⊎ ⊤) ⊤

  p2iC ((PolyP._⊚_  F G))  = (Indexed._⊚_ (Indexed.Fix (p2iC F)) (p2iC G))
  p2iC PolyP.U             = Indexed.U
  p2iC PolyP.P'            = Indexed.I' (inj₁ tt)
  p2iC PolyP.I'            = Indexed.I' (inj₂ tt)
  p2iC ((PolyP._⊕_  F G))  = (Indexed._⊕_ (p2iC F) (p2iC G))
  p2iC ((PolyP._⊗_  F G))  = (Indexed._⊗_ (p2iC F) (p2iC G))

  fromP : {A R : Set} (C : PolyP.Code) → (PolyP.⟦_⟧ C A R) → (Indexed.⟦_⟧ (p2iC C) ((Indexed._∣_ (const A) (const R))) tt)
  fromP ((PolyP._⊚_ F G))  (PolyP.⟨_⟩ x)  =  (Indexed.⟨_⟩ (Indexed.map (p2iC F) ((Indexed._∥_ (λ _ → fromP G) (λ _ → fromP ((PolyP._⊚_ F G))))) tt (fromP F x)))
  fromP PolyP.U            tt             =  tt
  fromP PolyP.I'           y              =  y
  fromP PolyP.P'           y              =  y
  fromP ((PolyP._⊕_ F G))  (inj₁  x)      =  inj₁ (fromP F x)
  fromP ((PolyP._⊕_ F G))  (inj₂  y)      =  inj₂ (fromP G y)
  fromP ((PolyP._⊗_ F G))  (x , y)        =  fromP F x , fromP G y

  toP : {A R : Set} (C : PolyP.Code) → (Indexed.⟦_⟧ (p2iC C) ((Indexed._∣_ (const A) (const R))) tt) → (PolyP.⟦_⟧ C A R)
  toP ((PolyP._⊚_ F G))  (Indexed.⟨_⟩ x)  = (PolyP.⟨_⟩ (toP F (Indexed.map (p2iC F) ((Indexed._∥_ (λ _ → toP G) (λ _ → toP ((PolyP._⊚_ F G))))) tt x)))
  toP PolyP.U            tt               = tt
  toP PolyP.I'           x                = x
  toP PolyP.P'           x                = x
  toP ((PolyP._⊕_ F G))  (inj₁  x)        = inj₁ (toP F x)
  toP ((PolyP._⊕_ F G))  (inj₂  y)        = inj₂ (toP G y)
  toP ((PolyP._⊗_ F G))  (x , y)          = toP F x , toP G y

  toμP : {A : Set} (C : PolyP.Code) → (Indexed.⟦_⟧ (p2iC C) ((Indexed._∣_ (const A) (Indexed.μ (p2iC C) (const A)))) tt) → PolyP.μ C A
  toμP {A} C x = (PolyP.⟨_⟩ (toP C (Indexed.map (p2iC C) ((Indexed._∥_ (const id) g)) tt x))) where
    g : (i : ⊤) → Indexed.μ (p2iC C) (const A) i → _
    g _ (Indexed.⟨_⟩ x) = toμP C x --  unfortunately we cannot inline g above

  fromμP : {A : Set} (C : PolyP.Code) → PolyP.μ C A → (Indexed.⟦_⟧ (Indexed.Fix (p2iC C)) (const A) tt)
  fromμP C (PolyP.⟨_⟩ x) = (Indexed.⟨_⟩ (Indexed.map (p2iC C) ((Indexed._∥_ (const id) (λ _ → fromμP C))) tt (fromP C x)))

  open ≡-Reasoning

  isoP₁ : {A R : Set} (C : PolyP.Code) → (x : (PolyP.⟦_⟧ C A R)) → toP {A} {R} C (fromP C x) ≡ x
  isoP₁ ((PolyP._⊚_ F G))  (PolyP.⟨_⟩ x)  = cong PolyP.⟨_⟩ $

    begin
  
      (toP F  (Indexed.map (p2iC F) ((Indexed._∥_ (λ _ → toP     G) (λ _ → toP    ((PolyP._⊚_ F G))))) tt
              (Indexed.map (p2iC F) ((Indexed._∥_ (λ _ → fromP   G) (λ _ → fromP  ((PolyP._⊚_ F G))))) tt (fromP F x))))

    ≡⟨ cong (toP F) (sym (Indexed.map-∘ (p2iC F) _ _ tt (fromP F x))) ⟩

      (toP F (Indexed.map (p2iC F) ((Indexed._⇉∘_  ((Indexed._∥_   (λ _ → toP    G) (λ _ → toP    ((PolyP._⊚_ F G)))))
                                                   ((Indexed._∥_   (λ _ → fromP  G) (λ _ → fromP  ((PolyP._⊚_ F G))))))) tt (fromP F x)))

    ≡⟨ cong (toP F) (Indexed.map-cong (p2iC F) (λ i x → sym (Indexed.∥∘ i x)) tt (fromP F x)) ⟩

      (toP F (Indexed.map (p2iC F) ((Indexed._∥_   ((Indexed._⇉∘_  ((λ _ → toP G))                 ((λ _ → fromP G))))
                                                   ((Indexed._⇉∘_  ((λ _ → toP (PolyP._⊚_ F G)))   ((λ _ → fromP (PolyP._⊚_ F G))))))) tt (fromP F x)))

    ≡⟨ cong (toP F) (Indexed.map-cong (p2iC F) (Indexed.∥cong (λ _ → isoP₁ G) (λ _ _ → refl)) tt (fromP F x)) ⟩

      (toP F (Indexed.map (p2iC F) ((Indexed._∥_ Indexed.id⇉ ((Indexed._⇉∘_ (λ _ → toP ((PolyP._⊚_ F G)))) (λ _ → fromP ((PolyP._⊚_ F G)))))) tt (fromP F x)))

    ≡⟨ cong (toP F) (Indexed.map-cong (p2iC F) (Indexed.∥cong (λ _ _ → refl) (λ _ → isoP₁ (PolyP._⊚_ F G))) tt (fromP F x)) ⟩

      (toP F (Indexed.map (p2iC F) ((Indexed._∥_ Indexed.id⇉ Indexed.id⇉)) tt (fromP F x)))

    ≡⟨ cong (toP F) (Indexed.map-cong (p2iC F) (Indexed.∥id (λ _ _ → refl) (λ _ _ → refl)) tt (fromP F x)) ⟩

      (toP F (Indexed.map (p2iC F) Indexed.id⇉ tt (fromP F x)))
  
    ≡⟨ cong (toP F) (Indexed.map-id (p2iC F) tt (fromP F x)) ⟩

      (toP F (fromP F x))

    ≡⟨ isoP₁ F x ⟩

      x ∎

  isoP₁ PolyP.U            tt             = refl
  isoP₁ PolyP.I'           _              = refl
  isoP₁ PolyP.P'           _              = refl
  isoP₁ ((PolyP._⊕_ F G))  (inj₁  x)      = cong inj₁ (isoP₁ F x)
  isoP₁ ((PolyP._⊕_ F G))  (inj₂  x)      = cong inj₂ (isoP₁ G x)
  isoP₁ ((PolyP._⊗_ F G))  (x , y)        = cong₂ _,_ (isoP₁ F x) (isoP₁ G y)

module Indexed2IG where

  i2cC : {I O : Set} → Indexed.Code I O → (I → Set) → (O → IG.Code)
  i2cC Indexed.U            r o = IG.U
  i2cC (Indexed.I' i)       r o = IG.K (r i)
  i2cC (Indexed.! i)        r o = IG.K (o ≡ i)

  i2cC ((Indexed._⊕_ F G))  r o = (IG._⊕_ (i2cC F r o) (i2cC G r o))
  i2cC ((Indexed._⊗_ F G))  r o = (IG._⊗_ (i2cC F r o) (i2cC G r o))
  i2cC ((Indexed._⊚_ F G))  r o = IG.R' (♯ i2cC F (λ i → (IG.⟦_⟧ (i2cC G r i))) o)
  i2cC (Indexed.Fix F)      r o = IG.R' (♯ i2cC F ((Indexed._∣_ r (λ i → (IG.⟦_⟧ (i2cC (Indexed.Fix F) r i))))) o)

  from : {I O : Set} {r : I → Set} (C : Indexed.Code I O) (o : O) → (Indexed.⟦_⟧ C r o) → (IG.⟦_⟧ (i2cC C r o))
  from Indexed.U            o tt               = IG.tt
  from (Indexed.I' i)       o x                = IG.k x
  from (Indexed.! i)        o x                = IG.k x

  from ((Indexed._⊕_ F G))  o (inj₁  x)        = IG.inj₁  (from F  o x)
  from ((Indexed._⊕_ F G))  o (inj₂  x)        = IG.inj₂  (from G  o x)
  from ((Indexed._⊗_ F G))  o (x , y )     = (IG._,_ (from F o x) (from G o y))
  from ((Indexed._⊚_ F G))  o x                = IG.rec (from F o (Indexed.map F (from G) o x))
  from (Indexed.Fix F)      o (Indexed.⟨_⟩ x)  = IG.rec (from F o (Indexed.map F ((Indexed._∥_ (λ _ → id) (from (Indexed.Fix F)))) o x))

  to : {I O : Set} {r : I → Set} (C : Indexed.Code I O) (o : O) → IG.⟦_⟧ (i2cC C r o) → Indexed.⟦_⟧ C r o
  to Indexed.U     _ _ = tt
  to (Indexed.I' _) _ (IG.k x) = x
  to (Indexed.! _) _ (IG.k x) = x
  to (Indexed._⊕_ F G) o (IG.inj₁ x) = inj₁ (to F o x)
  to (Indexed._⊕_ F G) o (IG.inj₂ x) = inj₂ (to G o x)
  to (Indexed._⊗_ F G) o (IG._,_ x y) = to F o x , to G o y
  to (Indexed._⊚_ F G) o (IG.rec x) =
    Indexed.map F (to G) o (to F o x)
  to (Indexed.Fix F) o (IG.rec x) =  
    Indexed.⟨_⟩ (Indexed.map F (Indexed._∥_ (λ _ → id) (to (Indexed.Fix F))) o
      (to F o x))

  open ≡-Reasoning

  iso₁ : {I O : Set} (C : Indexed.Code I O) (r : I → Set) → (Indexed._≅_ ((Indexed._⇉∘_ (to {r = r} C) (from C))) (Indexed.id⇉))
  iso₁ ((Indexed._⊚_ F G))  r o x         =

    begin
    
      Indexed.map F (to G) o (to F o (from F o (Indexed.map F (from G) o x)))
  
    ≡⟨ cong (Indexed.map F (to G) o) (iso₁ F _ o _) ⟩

       Indexed.map F (to G) o (Indexed.map F (from G) o x)

    ≡⟨ sym (Indexed.map-∘ F (to G) (from G) o x) ⟩

      Indexed.map F ((Indexed._⇉∘_ (to G) (from G))) o x

    ≡⟨ Indexed.map-cong F (iso₁ G r) o x ⟩

      Indexed.map F Indexed.id⇉ o x

    ≡⟨ Indexed.map-id F o x ⟩

      x ∎
  iso₁ (Indexed.Fix F) r o (Indexed.⟨_⟩ x) = cong Indexed.⟨_⟩ $
    begin

      Indexed.map F ((Indexed._∥_ Indexed.id⇉ (to (Indexed.Fix F)))) o (to F o (from F o (Indexed.map F ((Indexed._∥_ Indexed.id⇉ (from (Indexed.Fix F)))) o x)))

    ≡⟨ cong (Indexed.map F ((Indexed._∥_ Indexed.id⇉ (to (Indexed.Fix F)))) o) (iso₁ F _ o _) ⟩

      Indexed.map F ((Indexed._∥_ Indexed.id⇉ (to (Indexed.Fix F)))) o (Indexed.map F ((Indexed._∥_ Indexed.id⇉ (from (Indexed.Fix F)))) o x)

    ≡⟨ sym (Indexed.map-∘ F ((Indexed._∥_ Indexed.id⇉ (to   (Indexed.Fix F)))) ((Indexed._∥_ Indexed.id⇉ (from (Indexed.Fix F)))) o x) ⟩

      Indexed.map F (Indexed._⇉∘_ ((Indexed._∥_ Indexed.id⇉ (to (Indexed.Fix F)))) ((Indexed._∥_ Indexed.id⇉ (from (Indexed.Fix F))))) o x

    ≡⟨ sym (Indexed.map-cong F Indexed.∥∘ o x) ⟩

      Indexed.map F ((Indexed._∥_ ((Indexed._⇉∘_ Indexed.id⇉ Indexed.id⇉)) ((Indexed._⇉∘_ (to (Indexed.Fix F)) (from (Indexed.Fix F)))))) o x

    ≡⟨ Indexed.map-cong F (Indexed.∥cong (λ _ _ → refl) (iso₁ (Indexed.Fix F) r)) o x ⟩

      Indexed.map F ((Indexed._∥_ Indexed.id⇉ Indexed.id⇉)) o x

    ≡⟨ Indexed.map-cong F (Indexed.∥id (λ _ _ → refl) (λ _ _ → refl)) o x ⟩

      Indexed.map F Indexed.id⇉ o x
 
    ≡⟨ Indexed.map-id F o x ⟩

      x ∎

  iso₁  Indexed.U           r o _         = refl
  iso₁ (Indexed.I' i)       r o _         = refl
  iso₁ (Indexed.!  i)       r o _         = refl
  iso₁ ((Indexed._⊕_ F G))  r o (inj₁ x)  = cong inj₁ (iso₁ F r o x)
  iso₁ ((Indexed._⊕_ F G))  r o (inj₂ x)  = cong inj₂ (iso₁ G r o x)
  iso₁ ((Indexed._⊗_ F G))  r o (x , y)   = cong₂ _,_ (iso₁ F r o x) (iso₁ G r o y)
