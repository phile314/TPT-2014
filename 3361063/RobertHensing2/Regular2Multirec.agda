{-#  OPTIONS --no-termination-check  #-}

open import fcadgp
open import Data.Unit
open ≡-Reasoning
module Regular2Multirec where

  -- First, we define a mapping function from Regular codes to Multirec codes

  ᵣ⇑ᵐ : Regular.Code -> Multirec.Code ⊤
  ᵣ⇑ᵐ Regular.U = Multirec.U
  ᵣ⇑ᵐ Regular.I' = Multirec.I' tt
  ᵣ⇑ᵐ (f Regular.⊕ g) = ᵣ⇑ᵐ f Multirec.⊕ ᵣ⇑ᵐ g
  ᵣ⇑ᵐ (f Regular.⊗ g) = ᵣ⇑ᵐ f Multirec.⊗ ᵣ⇑ᵐ g

  -- Then we show that we can map Multirec codes to Regular codes

  toᵣ : {R : Set}(C : Regular.Code) -> (Multirec.⟦ ᵣ⇑ᵐ C ⟧ (λ x → R) tt) -> Regular.⟦ C ⟧ R
  toᵣ Regular.U x = tt
  toᵣ Regular.I' x = x
  toᵣ (f Regular.⊕ g) (inj₁ x₂) = inj₁ (toᵣ f x₂)
  toᵣ (f Regular.⊕ g) (inj₂ y) = inj₂ (toᵣ g y)
  toᵣ (f Regular.⊗ g) (proj₁ , proj₂) = toᵣ f proj₁ , toᵣ g proj₂

  -- And the other way around

  fromᵣ : {R : Set}(C : Regular.Code) -> (x : Regular.⟦ C ⟧ R) -> Multirec.⟦ ᵣ⇑ᵐ C ⟧ (\x -> R) tt
  fromᵣ Regular.U x = tt
  fromᵣ Regular.I' x = x
  fromᵣ (f Regular.⊕ g) (inj₁ x) = inj₁ (fromᵣ f x)
  fromᵣ (f Regular.⊕ g) (inj₂ y) = inj₂ (fromᵣ g y)
  fromᵣ (f Regular.⊗ g) (proj₁ , proj₂) = fromᵣ f proj₁ , fromᵣ g proj₂

  fromμᵣ : (C : Regular.Code) -> Regular.μ C -> Multirec.μ (ᵣ⇑ᵐ C) tt
  fromμᵣ C Regular.⟨ x ⟩ = Multirec.⟨ fromᵣ C (Regular.map C (fromμᵣ C) x) ⟩

  toμᵣ : (C : Regular.Code) -> Multirec.μ (ᵣ⇑ᵐ C) tt -> Regular.μ C
  toμᵣ C Multirec.⟨ x ⟩ = Regular.⟨ (toᵣ C (Multirec.map (ᵣ⇑ᵐ C) (f) tt x)) ⟩
                    where
                      f : ⊤ -> Multirec.μ (ᵣ⇑ᵐ C) tt -> Regular.μ C
                      f i x₁ = toμᵣ C x₁

  -- Which is necessary to prove isomorphism

  iso₁ : {R : Set}(C : Regular.Code)(x : Regular.⟦ C ⟧ R) -> toᵣ C (fromᵣ C x) ≡ x
  iso₁ Regular.U tt = refl
  iso₁ Regular.I' x = refl
  iso₁ (f Regular.⊕ g) (inj₁ x) = cong inj₁ (iso₁ f x)
  iso₁ (f Regular.⊕ g) (inj₂ y) = cong inj₂ (iso₁ g y)
  iso₁ (f Regular.⊗ g) (proj₁ , proj₂) = cong₂ _,_ (iso₁ f proj₁) (iso₁ g proj₂)

  mapCommuteᵣᵐ : {R₁ R₂ : Set}{f : R₁ -> R₂}(C : Regular.Code)(x : Multirec.⟦ ᵣ⇑ᵐ C ⟧ (λ _ → R₁) tt) -> toᵣ C (Multirec.map (ᵣ⇑ᵐ C) (λ i → f) tt x) ≡ Regular.map C f (toᵣ C x)
  mapCommuteᵣᵐ Regular.U tt = refl
  mapCommuteᵣᵐ Regular.I' x = refl
  mapCommuteᵣᵐ (c Regular.⊕ c₁) (inj₁ x) = cong inj₁ (mapCommuteᵣᵐ c x)
  mapCommuteᵣᵐ (c Regular.⊕ c₁) (inj₂ y) = cong inj₂ (mapCommuteᵣᵐ c₁ y)
  mapCommuteᵣᵐ (c Regular.⊗ c₁) (proj₁ , proj₂) = cong₂ _,_ (mapCommuteᵣᵐ c proj₁) (mapCommuteᵣᵐ c₁ proj₂)

  isoμ₁ : (C : Regular.Code)(x : Regular.μ C) -> toμᵣ C (fromμᵣ C x) ≡ x
  isoμ₁ C Regular.⟨ x ⟩ = let C' = ᵣ⇑ᵐ C
      in cong Regular.⟨_⟩ $
        begin
          toᵣ C (Multirec.map C' (λ i → toμᵣ C) tt (fromᵣ C (Regular.map C (fromμᵣ C) x))) ≡⟨ mapCommuteᵣᵐ C _ ⟩
            Regular.map C (toμᵣ C) (toᵣ C (fromᵣ C (Regular.map C (fromμᵣ C) x))) ≡⟨ cong (Regular.map C (toμᵣ C)) (iso₁ C (Regular.map C (fromμᵣ C) x)) ⟩
            Regular.map C (toμᵣ C) (Regular.map C (fromμᵣ C) x) ≡⟨ Regular.map∘ C ⟩
            Regular.map C (toμᵣ C ∘ fromμᵣ C) x ≡⟨ Regular.map∀ C (isoμ₁ C) x ⟩
            Regular.map C id x ≡⟨ Regular.mapId C ⟩
            x ∎

  mapCommuteₘr : {R₁ R₂ : Multirec.Indexed ⊤}{f :  R₁ tt -> R₂ tt }(C : Regular.Code)(x : Regular.⟦ C ⟧ (R₂ tt)) ->
                       fromᵣ C (Regular.map C (\i -> f) x) ≡ Multirec.map (ᵣ⇑ᵐ C) (λ i z → f) tt (fromᵣ C x)
  mapCommuteₘr Regular.U tt = refl
  mapCommuteₘr Regular.I' x = refl
  mapCommuteₘr (C Regular.⊕ C₁) (inj₁ x) = cong inj₁ (mapCommuteₘr C x)
  mapCommuteₘr (C Regular.⊕ C₁) (inj₂ y) = cong inj₂ (mapCommuteₘr C₁ y)
  mapCommuteₘr (C Regular.⊗ C₁) (proj₁ , proj₂) = cong₂ _,_ (mapCommuteₘr C proj₁) (mapCommuteₘr C₁ proj₂)


  map∀ₘ : (C : Multirec.Code ⊤){R S : Multirec.Indexed ⊤}{f g : R tt → S tt} → (∀ x → f x ≡ g x) →
                             ∀ x -> Multirec.map C (λ i z → f z) tt x ≡ Multirec.map C (λ i z → g z) tt x
  map∀ₘ Multirec.U x x₁ = refl
  map∀ₘ (Multirec.I' _) p x = p x
  map∀ₘ (Multirec.! _) p x = refl
  map∀ₘ (c Multirec.⊕ c₁) p (inj₁ x) = cong inj₁ (map∀ₘ c p x)
  map∀ₘ (c Multirec.⊕ c₁) p (inj₂ y) = cong inj₂ (map∀ₘ c₁ p y)
  map∀ₘ (c Multirec.⊗ c₁) p (proj₁ , proj₂) = cong₂ _,_ (map∀ₘ c p proj₁) (map∀ₘ c₁ p proj₂)

  mapIdₘ : ∀ {A} (C : Multirec.Code ⊤) {x : Multirec.⟦ C ⟧ A tt} → Multirec.map C (λ i z → z) tt x ≡ x
  mapIdₘ Multirec.U {tt} = refl
  mapIdₘ (Multirec.I' tt) {x} = refl
  mapIdₘ (Multirec.! tt) {x} = refl
  mapIdₘ (C Multirec.⊕ C₁) {inj₁ x} = cong inj₁ (mapIdₘ C)
  mapIdₘ (C Multirec.⊕ C₁) {inj₂ y} = cong inj₂ (mapIdₘ C₁)
  mapIdₘ (C Multirec.⊗ C₁) {proj₁ , proj₂} = cong₂ _,_ (mapIdₘ C) (mapIdₘ C₁)

  map∘ₘ' : {A B C : Multirec.Indexed ⊤} (D : Regular.Code) {f : B tt → C tt} {g : A tt → B tt} {x : Multirec.⟦ ᵣ⇑ᵐ D ⟧ (λ _ → A tt) tt}
           → Multirec.map (ᵣ⇑ᵐ D) (λ i₁ → f) tt (Multirec.map (ᵣ⇑ᵐ D) (λ i₁ → g) tt x) ≡ Multirec.map (ᵣ⇑ᵐ D) (λ i → f ∘ g) tt x
  map∘ₘ' Regular.U {f} {g} {x} = refl 
  map∘ₘ' Regular.I' {f} {g} {x} = refl
  map∘ₘ' (C₁ Regular.⊕ C₂) {x = inj₁ y} = cong inj₁ (map∘ₘ' C₁)
  map∘ₘ' (C₁ Regular.⊕ C₂) {x = inj₂ y} = cong inj₂ (map∘ₘ' C₂)
  map∘ₘ' (C₁ Regular.⊗ C₂) = cong₂ _,_ (map∘ₘ' C₁) (map∘ₘ' C₂)

  map∘ₘ : {A B C : Multirec.Indexed ⊤} (D : Multirec.Code ⊤) {f : B tt → C tt} {g : A tt → B tt} {x : Multirec.⟦ D ⟧ (λ _ → A tt) tt}
           → Multirec.map D (λ i₁ → f) tt (Multirec.map D (λ i₁ → g) tt x) ≡ Multirec.map D (λ i → f ∘ g) tt x
  map∘ₘ Multirec.U = refl
  map∘ₘ (Multirec.I' x) = refl
  map∘ₘ (Multirec.! x)  = refl
  map∘ₘ (C₁ Multirec.⊕ C₂) {x = inj₁ x} = cong inj₁ (map∘ₘ C₁)
  map∘ₘ (C₁ Multirec.⊕ C₂) {x = inj₂ y} = cong inj₂ (map∘ₘ C₂)
  map∘ₘ (C₁ Multirec.⊗ C₂) = cong₂ _,_ (map∘ₘ C₁) (map∘ₘ C₂)

  iso₂ : {R : Multirec.Indexed ⊤}(C : Regular.Code)(x : Multirec.⟦ ᵣ⇑ᵐ C ⟧ (λ _ → R tt) tt) -> fromᵣ C (toᵣ C x) ≡ x
  iso₂ Regular.U tt = refl
  iso₂ Regular.I' x = refl
  iso₂ (c Regular.⊕ c₁) (inj₁ x) = cong inj₁ (iso₂ c x)
  iso₂ (c Regular.⊕ c₁) (inj₂ y) = cong inj₂ (iso₂ c₁ y)
  iso₂ (c Regular.⊗ c₁) (proj₁ , proj₂) = cong₂ _,_ (iso₂ c proj₁) (iso₂ c₁ proj₂)

  ᵣ⇑ᵐ-distributes-⊕ : ∀ c1 c2 -> ᵣ⇑ᵐ (c1 Regular.⊕ c2) ≡ (ᵣ⇑ᵐ c1) Multirec.⊕ (ᵣ⇑ᵐ c2)
  ᵣ⇑ᵐ-distributes-⊕ c1 c2 = refl
  
  ᵣ⇑ᵐ-distributes-⊗ : ∀ c1 c2 -> ᵣ⇑ᵐ (c1 Regular.⊗ c2) ≡ (ᵣ⇑ᵐ c1) Multirec.⊗ (ᵣ⇑ᵐ c2)
  ᵣ⇑ᵐ-distributes-⊗ c1 c2 = refl

  mapCommutemr : (C : Regular.Code)(x : Multirec.⟦ ᵣ⇑ᵐ C ⟧ (λ _ → Multirec.μ (ᵣ⇑ᵐ C) tt) tt) ->
       fromᵣ C (Regular.map C (fromμᵣ C) (toᵣ C (Multirec.map (ᵣ⇑ᵐ C) (λ i → toμᵣ C) tt x))) ≡
       (Multirec.map (ᵣ⇑ᵐ C) (λ i → fromμᵣ C) tt (fromᵣ C (toᵣ C (Multirec.map (ᵣ⇑ᵐ C) (λ i → toμᵣ C) tt x))))
  mapCommutemr Regular.U tt = refl
  mapCommutemr Regular.I' Multirec.⟨ x ⟩ = refl
  mapCommutemr (c Regular.⊕ c₁) (inj₁ x) = {!!} -- cong inj₁ (mapCommutemr {!c!} x)
  mapCommutemr (c Regular.⊕ c₁) (inj₂ y) = {!!} -- cong inj₂ (mapCommutemr {!c₁!} y)
  mapCommutemr (c Regular.⊗ c₁) (proj₁ , proj₂) = {!!} -- cong₂ _,_ (mapCommutemr {!c!} proj₁) (mapCommutemr {!c₁!} proj₂)

  isoμ₂ : (C : Regular.Code)(x : Multirec.μ (ᵣ⇑ᵐ C) (tt)) -> fromμᵣ C (toμᵣ C x) ≡ x
  isoμ₂ C Multirec.⟨ x ⟩ = let C' = ᵣ⇑ᵐ C
      in cong Multirec.⟨_⟩ $
        begin
              fromᵣ C (Regular.map C (fromμᵣ C) (toᵣ C (Multirec.map C' (λ i → toμᵣ C) tt x)))
          ≡⟨ mapCommutemr C x ⟩
              Multirec.map C' (λ i → fromμᵣ C) tt (fromᵣ C (toᵣ C (Multirec.map C' (λ i → toμᵣ C) tt x)))
          ≡⟨ cong (Multirec.map C' (λ i → fromμᵣ C) tt) (iso₂ C (Multirec.map C' (λ i → toμᵣ C) tt x)) ⟩
              Multirec.map C' (λ i → fromμᵣ C) tt (Multirec.map C' (λ i x₁ → toμᵣ C x₁) tt x)
          ≡⟨ map∘ₘ' C {fromμᵣ C} {toμᵣ C} {x} ⟩
              Multirec.map C' (λ i → fromμᵣ C ∘ toμᵣ C) tt x
          ≡⟨ map∀ₘ C' (isoμ₂ C) x ⟩
              Multirec.map C' (λ i z → z) tt x ≡⟨ mapIdₘ C' ⟩
          x ∎
