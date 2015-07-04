I wrote and tested this (Exercise3-5.lagda) using Agda 2.4.2.2 and
Standard Library 0.9. I used the "new" fcadgp.agda from the web site,
placed in the same folder as this file.

Please excuse the improper use of the LaTeX literate commands
(\begin{code}, \end{code}). If Literate Agda is like Literate Haskell,
I can only choose between placing a > before each line - which is not
very readable - or doing this. I'm not sure the Literate Agda
requirement is very sensible for this assignment.

--------------------------------------------------------------------------------

The termination check needs to be disabled because of the use of
"complex" higher-order functions (in fromμRegular and toμRegular).
Note that fcadgp does this too.

\begin{code}
{-# OPTIONS --no-termination-check #-}

module Exercise3-5 where

open import fcadgp

module Regular2Multirec where
\end{code}

First up: the code converter. Since Regular can only talk about a single type,
we use the type with a single inhabitant - ⊤ - as the index set for Multirec.

\begin{code}
  r2mC : Regular.Code → Multirec.Code ⊤
  r2mC Regular.U = Multirec.U
  r2mC Regular.I' = Multirec.I' tt
  r2mC (C₁ Regular.⊕ C₂) = r2mC C₁ Multirec.⊕ r2mC C₂
  r2mC (C₁ Regular.⊗ C₂) = r2mC C₁ Multirec.⊗ r2mC C₂
\end{code}

The use of ⊤ also means that the indexing function always takes tt as a
parameter, and it needs to return the single type Regular currently discusses.
That's simply const... but it needs the following specific type to work.

\begin{code}
  index : Set → Multirec.Indexed ⊤
  index R tt = R
\end{code}

Because the constructors line up so well (Multirec being an extension of
Regular), translating from and to Regular is now easy, and works a lot
like the translation to PolyP in fcadgp.

\begin{code}
  fromRegular : {R : Set} (C : Regular.Code) → (Regular.⟦_⟧ C R) → (Multirec.⟦_⟧ (r2mC C) (index R) tt)
  fromRegular Regular.U tt = tt
  fromRegular Regular.I' v = v
  fromRegular (C₁ Regular.⊕ C₂) (inj₁ x) = inj₁ (fromRegular C₁ x)
  fromRegular (C₁ Regular.⊕ C₂) (inj₂ y) = inj₂ (fromRegular C₂ y)
  fromRegular (C₁ Regular.⊗ C₂) (proj₁ , proj₂) = fromRegular C₁ proj₁ , fromRegular C₂ proj₂
  fromμRegular : (C : Regular.Code) → Regular.μ C → Multirec.μ (r2mC C) tt
  fromμRegular C Regular.⟨ x ⟩ = Multirec.⟨ (fromRegular C (Regular.map C (fromμRegular C) x)) ⟩

  toRegular : {R : Set} (C : Regular.Code) → (Multirec.⟦_⟧ (r2mC C) (index R) tt) → (Regular.⟦_⟧ C R)
  toRegular Regular.U tt = tt
  toRegular Regular.I' x = x
  toRegular (C₁ Regular.⊕ C₂) (inj₁ x) = inj₁ (toRegular C₁ x)
  toRegular (C₁ Regular.⊕ C₂) (inj₂ y) = inj₂ (toRegular C₂ y)
  toRegular (C₁ Regular.⊗ C₂) (proj₁ , proj₂) = toRegular C₁ proj₁ , toRegular C₂ proj₂
  toμRegular : (C : Regular.Code) → Multirec.μ (r2mC C) tt → Regular.μ C
  toμRegular C Multirec.⟨ x ⟩ = Regular.⟨ toRegular C (Multirec.map (r2mC C) (λ _ → toμRegular C) tt x) ⟩
\end{code}

Finally, we need to prove that toRegular after fromRegular is the identity;
the same must hold for the μ (fixed point) versions. These proofs are also very
similar to the Regular2PolyP proofs.

\begin{code}
  iso₁ : {R : Set} → (C : Regular.Code) → (x : (Regular.⟦_⟧ C) R) → toRegular C (fromRegular C x) ≡ x
  iso₁ Regular.U tt = refl
  iso₁ Regular.I' x = refl
  iso₁ (C₁ Regular.⊕ C₂) (inj₁ x) = cong inj₁ (iso₁ C₁ x)
  iso₁ (C₁ Regular.⊕ C₂) (inj₂ y) = cong inj₂ (iso₁ C₂ y)
  iso₁ (C₁ Regular.⊗ C₂) (proj₁ , proj₂) = cong₂ _,_ (iso₁ C₁ proj₁) (iso₁ C₂ proj₂)

  lemma₁ : {R₁ R₂ : Set} (C : Regular.Code)
           {f : R₁ → R₂} (x : Multirec.⟦_⟧ (r2mC C) (index R₁) tt)
         → toRegular C (Multirec.map (r2mC C) (λ _ → f) tt x)
         ≡ Regular.map C f (toRegular C x)
  lemma₁ Regular.U tt = refl
  lemma₁ Regular.I' x = refl
  lemma₁ (C₁ Regular.⊕ C₂) (inj₁ x) = cong inj₁ (lemma₁ C₁ x)
  lemma₁ (C₁ Regular.⊕ C₂) (inj₂ y) = cong inj₂ (lemma₁ C₂ y)
  lemma₁ (C₁ Regular.⊗ C₂) (proj₁ , proj₂) = cong₂ _,_ (lemma₁ C₁ proj₁) (lemma₁ C₂ proj₂)

  open ≡-Reasoning

  isoμ₁ : (C : Regular.Code) (x : Regular.μ C) → toμRegular C (fromμRegular C x) ≡ x
  isoμ₁ C Regular.⟨ x ⟩ = cong Regular.⟨_⟩ $

      begin

        toRegular C (Multirec.map (r2mC C) (λ _ → toμRegular C) tt (fromRegular C (Regular.map C (fromμRegular C) x)))

      ≡⟨ lemma₁ C _ ⟩

        Regular.map C (toμRegular C) (toRegular C (fromRegular C (Regular.map C (fromμRegular C) x)))

      ≡⟨ cong (Regular.map C (toμRegular C)) (iso₁ C (Regular.map C (fromμRegular C) x)) ⟩

        Regular.map C (toμRegular C) (Regular.map C (fromμRegular C) x)

      ≡⟨ Regular.map∘ C ⟩

        Regular.map C (toμRegular C ∘ fromμRegular C) x

      ≡⟨ Regular.map∀ C (isoμ₁ C) x ⟩

        Regular.map C id x

      ≡⟨ Regular.mapId C ⟩

        x ∎
\end{code}

Considering Regular's feature set has been fully described, and the assignment
does not specify details, the embedding can now be considered complete.

