{-# OPTIONS --safe --without-K --exact-split #-}
-- Closed corollary: the only remaining input is ConOpenInt ( Lstar := 0 ).
module T4.SurpriseGIIClosed where
open import T4.Base
open import T4.Code using ( falseF )
open import T4.SurpriseG2.ConOpenIntDef using ( ConOpenInt )
import T4.SurpriseGIINum

surpriseGII : ConOpenInt -> Deriv falseF
surpriseGII con = T4.SurpriseGIINum.surpriseGII_num 0 con
