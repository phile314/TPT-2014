{-#  OPTIONS --no-termination-check  #-}
{-#  OPTIONS --no-positivity-check  #-}
open import fcadgp

module Regular2Multirec where

  -- Since the Regular approach cannot really handle mutually
  -- recursive constructors (or, n-ary recursion, for that matter)
  -- the trick is to translate it to the simplest possible multirec
  -- encoding. And that will be by indexing by Unit, or no
  -- indexing at all.
  r2m : Regular.Code → Multirec.Code Unit
  r2m Regular.U        = Multirec.U
  r2m Regular.I'       = Multirec.I' unit
  r2m (r Regular.⊕ r₁) = r2m r Multirec.⊕ r2m r₁
  r2m (r Regular.⊗ r₁) = r2m r Multirec.⊗ r2m r₁

  fromRegular : {R : Set}(C : Regular.Code)
              → (Regular.⟦_⟧ C R)
              → (Multirec.⟦ r2m C ⟧ (λ _ → R) unit)
  fromRegular Regular.U x = tt
  fromRegular Regular.I' x = x
  fromRegular (c Regular.⊕ c₁) (inj₁ x) = inj₁ (fromRegular c x)
  fromRegular (c Regular.⊕ c₁) (inj₂ y) = inj₂ (fromRegular c₁ y)
  fromRegular (c Regular.⊗ c₁) (x , y) 
    = fromRegular c x , fromRegular c₁ y

  toRegular : {R : Set}(C : Regular.Code)
            → (Multirec.⟦ r2m C ⟧ (λ _ → R) unit)
            → (Regular.⟦_⟧ C R)
  toRegular Regular.U x = tt
  toRegular Regular.I' x = x
  toRegular (c Regular.⊕ c₁) (inj₁ x) = inj₁ (toRegular c x)
  toRegular (c Regular.⊕ c₁) (inj₂ y) = inj₂ (toRegular c₁ y)
  toRegular (c Regular.⊗ c₁) (x , y) = toRegular c x , toRegular c₁ y

  iso : {R : Set}(C : Regular.Code)(x : Regular.⟦_⟧ C R)
      → toRegular C (fromRegular C x) ≡ x
  iso Regular.U tt = refl
  iso Regular.I' x = refl
  iso (c Regular.⊕ c₁) (inj₁ x) = cong inj₁ (iso c x)
  iso (c Regular.⊕ c₁) (inj₂ y) = cong inj₂ (iso c₁ y)
  iso (c Regular.⊗ c₁) (x , y)
    rewrite iso c x | iso c₁ y = refl

  unit-is-unique : (i : Unit) → i ≡ unit
  unit-is-unique unit = refl

  fromμRegular : (C : Regular.Code)(i : Unit) → Regular.μ C
               → Multirec.μ (r2m C) i
  fromμRegular C unit Regular.⟨ x ⟩
    = Multirec.⟨ Multirec.map (r2m C) (fromμRegular C) unit (fromRegular C x) ⟩      

  toμRegular : (C : Regular.Code)(i : Unit) → Multirec.μ (r2m C) i 
             → Regular.μ C
  toμRegular C unit Multirec.⟨ x ⟩ 
    = Regular.⟨ toRegular C (Multirec.map (r2m C) (toμRegular C) unit x) ⟩

  lemma : {R S : Set}(C : Regular.Code)
        → {f : R → S}(x : Multirec.⟦_⟧ (r2m C) (λ _ → R ) unit )
        → toRegular C (Multirec.map (r2m C) (const f) unit x)
        ≡ Regular.map C f (toRegular C x)
  lemma Regular.U x = refl
  lemma Regular.I' x = refl
  lemma (C Regular.⊕ C₁) (inj₁ x) = cong inj₁ (lemma C x)
  lemma (C Regular.⊕ C₁) (inj₂ y) =  cong inj₂ (lemma C₁ y)
  lemma (C Regular.⊗ C₁) (x , y)  = cong₂ _,_ (lemma C x) (lemma C₁ y)

  open ≡-Reasoning

  multirec-id
    : {R : Multirec.Indexed Unit}(F : Multirec.Code Unit)
    → (x : Multirec.⟦ F ⟧ R unit)
    → Multirec.map F (λ _ → id) unit x ≡ x
  multirec-id Multirec.U tt = refl
  multirec-id (Multirec.I' x) x₁ = refl
  multirec-id (Multirec.! x) x₁ = refl
  multirec-id (F Multirec.⊕ F₁) (inj₁ x) 
    = cong inj₁ (multirec-id F x)
  multirec-id (F Multirec.⊕ F₁) (inj₂ y) 
    = cong inj₂ (multirec-id F₁ y)
  multirec-id (F Multirec.⊗ F₁) (x , y) 
    = cong₂ _,_ (multirec-id F x) (multirec-id F₁ y)

  multirec-map-join
    : {R S T : Multirec.Indexed Unit}(F : Multirec.Code Unit)
    → (x : Multirec.⟦ F ⟧ (λ _ → T unit) unit)
    → {f : Unit → R unit → S unit}{g : Unit → T unit → R unit}
    → Multirec.map F f unit (Multirec.map F g unit x)
    ≡ Multirec.map F (λ _ → f unit ∘ g unit) unit x
  multirec-map-join Multirec.U x = refl
  multirec-map-join (Multirec.I' unit) x₁ = refl
  multirec-map-join (Multirec.! x) x₁ = refl
  multirec-map-join {R} {S} {T} (F Multirec.⊕ F₁) (inj₁ x)
    = cong inj₁ (multirec-map-join {R} {S} {T} F x)
  multirec-map-join {R} {S} {T} (F Multirec.⊕ F₁) (inj₂ y) 
    = cong inj₂ (multirec-map-join {R} {S} {T} F₁ y)
  multirec-map-join {R} {S} {T} (F Multirec.⊗ F₁) (x , y) 
    = cong₂ _,_ (multirec-map-join {R} {S} {T} F x) 
                (multirec-map-join {R} {S} {T} F₁ y)

  -- For some unkown reason, Agda really doesn't
  -- like (r2m C) to fill the hole. I also do not understand
  -- why I still have unsolved metas in this...
  lemma-2 : (C : Regular.Code)(x : Regular.⟦ C ⟧ (Regular.μ C))
          → Multirec.map (r2m C) (toμRegular C) unit
              (Multirec.map (r2m C) (fromμRegular C) unit 
                (fromRegular C x))
          ≡ Multirec.map (r2m C) 
              (λ _ → toμRegular C unit ∘ fromμRegular C unit)
              unit
              (fromRegular C x)
  lemma-2 C x = multirec-map-join 
                {R = λ { unit → Multirec.μ (r2m C) unit }} 
                {S = λ x₁ → Regular.μ C} 
                {T = λ _ → Regular.μ C} 
                {!r2m C!} 
                (fromRegular C x)
                {f = λ { unit r → toμRegular C unit r}}
                {g = λ { unit r → fromμRegular C unit r } }

  mutual 
    isoμ : (C : Regular.Code)(x : Regular.μ C) 
         → toμRegular C unit (fromμRegular C unit x) ≡ x 
    isoμ C Regular.⟨ x ⟩ = cong Regular.⟨_⟩
      $ begin
        toRegular C
          (Multirec.map (r2m C) (toμRegular C) unit
           (Multirec.map (r2m C) (fromμRegular C) unit (fromRegular C x)))
      ≡⟨ cong (toRegular C) (lemma-2 C x) ⟩
        toRegular C
          (Multirec.map (r2m C)
           (λ i z → toμRegular C unit (fromμRegular C unit z)) unit
           (fromRegular C x))
      ≡⟨ cong (toRegular C) (lemma-3 C x) ⟩
        toRegular C (fromRegular C x)
      ≡⟨ iso C x ⟩
        x
      ∎
 
    lemma-3 : (C : Regular.Code)(x : Regular.⟦ C ⟧ (Regular.μ C))
            → Multirec.map (r2m C)
               (λ i z → toμRegular C unit (fromμRegular C unit z)) unit
               (fromRegular C x)
            ≡ fromRegular C x
    lemma-3 C x 
      = subst 
        (λ Z → Multirec.map (r2m C) Z unit (fromRegular C x) ≡ fromRegular C x)
        (cong (λ f → λ _ → f) (fun-ext (λ x₁ → sym (isoμ C x₁)))) 
        (multirec-id (r2m C) (fromRegular C x))
      where
        postulate
          fun-ext : {A B : Set}{f g : A → B}
                  → (∀ x → f x ≡ g x)
                  → f ≡ g
     
