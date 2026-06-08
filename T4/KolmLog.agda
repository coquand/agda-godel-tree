{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KolmLog -- the Kolmogorov upper bound in LOGARITHMIC form.
--
-- Combining
--   * T4.KolmRun.kolmRun       : a program p describing x, with p < 3^(nodes+1) ;
--   * T4.KolmSize.nodes_*bound : nodes (mcode1 (horner (digits3 x))) is LINEAR in
--                                the number of base-3 digits D = lenDL (digits3 x) ;
--   * digit_log (this file)    : 3 ^ (D - 1) <= x , i.e. D <= log_3 x + 1 ,
-- we obtain:  for every x >= 1 there is a program p and fuel N with
--
--     p < 3 ^ (baseN + PDmax * D + 1)     and     3 ^ (D - 1) <= x ,
--
-- so the program length (in base-3 digits) is  <= PDmax * log_3 x + (PDmax + baseN + 1) ,
-- and  runProgN (natCode p) (natCode N) = s (natCode x)  ( p describes x ).

module T4.KolmLog where

open import T4.Base
open import BRA3.Code.Tag       using ( addN )
open import BRA3.RuleInst2       using ( NatLe ; le-zero ; le-suc ; le-refl
                                       ; le-suc-right ; le-trans )
open import T4.ProgEnc          using ( nodes )
open import T4.EvalU            using ( mcode1 )
open import T4.TreeDigitsSize   using ( pow3 )
open import T4.NatExp           using ( le_self_addN_r ; le_self_addN_l )
open import T4.KolmHorner       using ( DL ; dnil ; dcons ; horner ; threeT )
open import T4.KolmDigits       using ( div3 ; mod3 ; div3_suc_le ; euclid3
                                      ; digitsFuel ; digits3 )
open import T4.KolmSize         using ( le_addN_1st ; le_addN_2nd
                                      ; lenDL ; AllLt3 ; allNil ; allCons
                                      ; baseN ; PDmax ; repAdd ; nodes_horner_bound )
open import T4.KolmRun          using ( Sg ; sg ; Pr ; pr ; Describes ; kolmRun )

------------------------------------------------------------------------
-- small helpers.

pr0 : Nat -> Nat
pr0 zero    = zero
pr0 (suc n) = n

noLe : {A : Set} {n : Nat} -> NatLe (suc n) zero -> A
noLe ()

-- addN monotone in both arguments.
le_addN_both : {a b c d : Nat} -> NatLe a b -> NatLe c d -> NatLe (addN a c) (addN b d)
le_addN_both {a} {b} {c} {d} h1 h2 =
  le-trans (le_addN_1st c h1) (le_addN_2nd b h2)

-- threeT v = v + (v + v) is monotone.
threeT_mono : {a b : Nat} -> NatLe a b -> NatLe (threeT a) (threeT b)
threeT_mono h = le_addN_both h (le_addN_both h h)

------------------------------------------------------------------------
-- pow3 facts.

-- pow3 n >= 1.
pow3_ge1 : (n : Nat) -> NatLe (suc zero) (pow3 n)
pow3_ge1 zero    = le-suc (le-zero zero)
pow3_ge1 (suc k) =
  -- pow3 (suc k) = threeT (pow3 k) >= pow3 k >= 1
  le-trans (pow3_ge1 k) (le_self_addN_l (pow3 k) (addN (pow3 k) (pow3 k)))

-- pow3 monotone in the exponent.
pow3_mono : {a b : Nat} -> NatLe a b -> NatLe (pow3 a) (pow3 b)
pow3_mono (le-zero n)  = pow3_ge1 n
pow3_mono (le-suc h)   = threeT_mono (pow3_mono h)

-- pow3 L <= threeT (pow3 (pr0 L))   (for L = 0 : 1 <= 3 ; for L = suc k : equality).
pow3_le_threeT_pred : (L : Nat) -> NatLe (pow3 L) (threeT (pow3 (pr0 L)))
pow3_le_threeT_pred zero    =
  -- pow3 0 = 1 ;  threeT (pow3 0) = threeT 1 = 3 .
  le-suc (le-zero (suc (suc zero)))
pow3_le_threeT_pred (suc k) =
  -- pow3 (suc k) = threeT (pow3 k) = threeT (pow3 (pr0 (suc k))) .
  le-refl (threeT (pow3 k))

------------------------------------------------------------------------
-- 3 * div3 v <= v   (from Euclid).

threeT_div3_le : (vv : Nat) -> NatLe (threeT (div3 vv)) vv
threeT_div3_le vv =
  eqSubst (\ z -> NatLe (threeT (div3 vv)) z) (euclid3 vv)
          (le_self_addN_r (mod3 vv) (threeT (div3 vv)))

------------------------------------------------------------------------
-- lenDL (digitsFuel f 0) = 0 .

lenDL_digitsFuel_zero : (f : Nat) -> Eq (lenDL (digitsFuel f zero)) zero
lenDL_digitsFuel_zero zero    = refl
lenDL_digitsFuel_zero (suc f) = refl

------------------------------------------------------------------------
-- THE digit-count logarithm bound:  3 ^ (D - 1) <= x   for x >= 1 ,
-- where D = lenDL (digitsFuel f x)  (any fuel f >= x).

digit_log :
  (f x : Nat) -> NatLe (suc zero) x -> NatLe x f ->
  NatLe (pow3 (pr0 (lenDL (digitsFuel f x)))) x
digit_log zero    x p1 le = noLe (le-trans p1 le)
digit_log (suc f) zero p1 _ = noLe p1
digit_log (suc f) (suc x) _ le =
  -- digitsFuel (suc f) (suc x) = dcons (mod3 (suc x)) (digitsFuel f (div3 (suc x)))
  -- lenDL = suc (lenDL (digitsFuel f y'))  with y' = div3 (suc x) ; pr0 (suc _) = _ .
  yCase (div3 (suc x)) refl
  where
    y0 : Nat
    y0 = div3 (suc x)

    -- x <= f  (strip the suc from le).
    lexf : NatLe x f
    lexf = lePred le
      where
        lePred : {m n : Nat} -> NatLe (suc m) (suc n) -> NatLe m n
        lePred (le-suc h) = h

    -- goal, after dcons :  pow3 (lenDL (digitsFuel f y0)) <= suc x .
    yCase : (y : Nat) -> Eq y0 y ->
            NatLe (pow3 (pr0 (lenDL (digitsFuel (suc f) (suc x))))) (suc x)
    yCase zero ey =
      -- y0 = 0 :  lenDL (digitsFuel f 0) = 0 ,  pow3 0 = 1 <= suc x .
      eqSubst (\ z -> NatLe (pow3 (pr0 (suc (lenDL (digitsFuel f z))))) (suc x))
        (eqSym ey)
        (eqSubst (\ z -> NatLe (pow3 z) (suc x))
          (eqSym (lenDL_digitsFuel_zero f))
          (le-suc (le-zero x)))
    yCase (suc y') ey =
      -- y0 = suc y' >= 1 :  use IH at y0 .
      let L : Nat
          L = lenDL (digitsFuel f y0)
          -- y0 <= f  (y0 = div3 (suc x) <= x <= f).
          ley0f : NatLe y0 f
          ley0f = le-trans (div3_suc_le x) lexf
          y0ge1 : NatLe (suc zero) y0
          y0ge1 = eqSubst (\ z -> NatLe (suc zero) z) (eqSym ey) (le-suc (le-zero y'))
          ih : NatLe (pow3 (pr0 L)) y0
          ih = digit_log f y0 y0ge1 ley0f
          -- pow3 L <= threeT (pow3 (pr0 L)) <= threeT y0 <= suc x
          c1 : NatLe (pow3 L) (threeT (pow3 (pr0 L)))
          c1 = pow3_le_threeT_pred L
          c2 : NatLe (threeT (pow3 (pr0 L))) (threeT y0)
          c2 = threeT_mono ih
          c3 : NatLe (threeT y0) (suc x)
          c3 = threeT_div3_le (suc x)
      in le-trans c1 (le-trans c2 c3)

------------------------------------------------------------------------
-- All digits of digits3 are < 3.

mod3_le2 : (vv : Nat) -> NatLe (mod3 vv) (suc (suc zero))
mod3_le2 zero                = le-zero (suc (suc zero))
mod3_le2 (suc zero)          = le-suc (le-zero (suc zero))
mod3_le2 (suc (suc zero))    = le-suc (le-suc (le-zero zero))
mod3_le2 (suc (suc (suc n))) = mod3_le2 n

allLt3_digitsFuel : (f x : Nat) -> AllLt3 (digitsFuel f x)
allLt3_digitsFuel zero    x       = allNil
allLt3_digitsFuel (suc f) zero    = allNil
allLt3_digitsFuel (suc f) (suc x) =
  allCons (mod3_le2 (suc x)) (allLt3_digitsFuel f (div3 (suc x)))

allLt3_digits3 : (x : Nat) -> AllLt3 (digits3 x)
allLt3_digits3 x = allLt3_digitsFuel x x

------------------------------------------------------------------------
-- THE LOGARITHMIC UPPER BOUND.

kolmLog :
  (x : Nat) -> NatLe (suc zero) x ->
  Sg Nat (\ p -> Sg Nat (\ N ->
    Pr (Pr (NatLe (suc p)
                  (pow3 (suc (addN baseN (repAdd PDmax (lenDL (digits3 x)))))))
           (NatLe (pow3 (pr0 (lenDL (digits3 x)))) x))
       (Describes p N x)))
kolmLog x x1 =
  let r  = kolmRun x
      p  = Sg.fstS r
      pr1 = Sg.sndS r
      -- p < 3 ^ (nodes (mcode1 (horner (digits3 x))) + 1)
      sizeLt : NatLe (suc p) (pow3 (suc (nodes (mcode1 (horner (digits3 x))))))
      sizeLt = Pr.fstP pr1
      rest = Pr.sndP pr1
      N  = Sg.fstS rest
      describes : Describes p N x
      describes = Sg.sndS rest
      -- nodes <= baseN + PDmax * D
      nb : NatLe (nodes (mcode1 (horner (digits3 x))))
                 (addN baseN (repAdd PDmax (lenDL (digits3 x))))
      nb = nodes_horner_bound (digits3 x) (allLt3_digits3 x)
      -- lift through (suc . pow3) and chain with sizeLt.
      sizeLog : NatLe (suc p)
                      (pow3 (suc (addN baseN (repAdd PDmax (lenDL (digits3 x))))))
      sizeLog = le-trans sizeLt (pow3_mono (le-suc nb))
      -- 3 ^ (D - 1) <= x
      dlog : NatLe (pow3 (pr0 (lenDL (digits3 x)))) x
      dlog = digit_log x x x1 (le-refl x)
  in sg p (sg N (pr (pr sizeLog dlog) describes))
