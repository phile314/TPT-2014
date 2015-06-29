module Regular2Multirec where

  open import fcadgp

  r2mC :  Regular.Code -> Multirec.Code ⊤
  r2mC Regular.U = Multirec.U
  r2mC Regular.I' = Multirec.I' tt
  r2mC (x Regular.⊕ x₁) = r2mC x Multirec.⊕ r2mC x₁
  r2mC (x Regular.⊗ x₁) = r2mC x Multirec.⊗ r2mC x₁
  fromRegular : {R : Set} ->  (C : Regular.Code) -> Regular.⟦ C ⟧ R -> Multirec.⟦ r2mC C ⟧ (λ _ -> R) tt
  fromRegular Regular.U y = y
  fromRegular Regular.I' y = y
  fromRegular (x Regular.⊕ x₁) (inj₁ x₂) = inj₁ (fromRegular x x₂)
  fromRegular (x Regular.⊕ x₁) (inj₂ y) = inj₂ (fromRegular x₁ y)
  fromRegular (x Regular.⊗ x₁) (proj₁ , proj₂) = fromRegular x proj₁ , fromRegular x₁ proj₂

  --fromμRegular : (C : Regular.Code) -> Regular.μ C -> Multirec.μ (r2mC C) tt
  --fromμRegular C (Regular.⟨_⟩ x) = (Multirec.⟨_⟩ (fromRegular C (Regular.map C (fromμRegular C) x)))
 
  toRegular : {R : Set} (C : Regular.Code) -> Multirec.⟦ r2mC C ⟧  (λ _ → R) tt -> Regular.⟦ C ⟧ R
  toRegular Regular.U x = x
  toRegular Regular.I' x = x
  toRegular (x Regular.⊕ x₁) (inj₁ x₂) = inj₁ (toRegular x x₂)
  toRegular (x Regular.⊕ x₁) (inj₂ y) = inj₂ (toRegular x₁ y)
  toRegular (x Regular.⊗ x₁) (proj₁ , proj₂) = toRegular x proj₁ , toRegular x₁ proj₂

  toμRegular : (C : Regular.Code) -> Multirec.μ (r2mC C) tt -> Regular.μ C
  toμRegular x Multirec.⟨ x₁ ⟩ = Regular.⟨_⟩ (toRegular x (Multirec.map (r2mC x) (const (toμRegular x)) tt x₁)) 

  iso₁ : {R : Set} -> (C : Regular.Code) → (x : Regular.⟦ C ⟧ R) -> toRegular C (fromRegular C x) ≡ x
  iso₁ Regular.U y = refl
  iso₁ Regular.I' y = refl
  iso₁ (x Regular.⊕ x₁) (inj₁ x₂) = cong inj₁ (iso₁ x x₂)
  iso₁ (x Regular.⊕ x₁) (inj₂ y) =  cong inj₂ (iso₁ x₁ y)
  iso₁ (x Regular.⊗ x₁) (proj₁ , proj₂) = {!!}
