{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Bin -- right-recursive (Snd-decreasing) bit-list numerals, the
-- compressed-numeral substrate for the Berry argument (Phase A of
-- KRIVINE-BERRY-PLAN.md).
--
-- A bit-list  [b0, b1, ..., b_{k-1}]  is encoded as the right-nested
-- Cantor structure
--
--   binMetaFromBits = pi (s (bitVal b0)) (pi (s (bitVal b1)) (... O))
--
-- Each cons cell is  pi (s _) rest  -- the first component is a successor
-- (so the node is a proper  s P_outer  and  BRA4.LenR.lenR_at_node fires)
-- and  rest  is the SECOND child (so  lenR  descends right, which is
-- well-founded).  The bit value is carried in the first component
-- (recoverable later for  bin2nat ).
--
-- THE POINT (validated below):  lenR  measures bit-list LENGTH, not value:
--
--   lenR_binMeta :  ap1 lenR (binMetaFromBits bs) = natCode (bitsLength bs)
--
-- so a number stored as a  k-bit list has  Len = k = O(log value) , unlike
-- the unary  natCode m  whose  lenR-ish length is  Theta(m) .  This is the
-- compressed length that keeps the Berry counting finite and makes the
-- self-reference  Len(B) < m0  achievable.
--
-- (The numeric layer -- bitsOf : Nat -> Bits via division by two, and the
-- bound  bitsLength (bitsOf m) <= c + log2 m  -- is deferred to a follow-up;
-- it is self-contained meta-arithmetic with the usual div-by-2 fuel.)

module BRA4.Bin where

open import BRA4.Base
open import BRA4.LenR using ( lenR ; lenR_at_O ; lenR_at_node )

open import BRA3.Church using ( pi )
open import BRA3.RuleInst2 using
  ( NatLe ; le-zero ; le-suc ; le-refl ; le-suc-right ; le-trans )

------------------------------------------------------------------------
-- Bit lists.

data Bits : Set where
  bnil  : Bits
  bcons : Bool -> Bits -> Bits

bitsLength : Bits -> Nat
bitsLength bnil         = zero
bitsLength (bcons _ bs) = suc (bitsLength bs)

------------------------------------------------------------------------
-- The bit value placed in a cons cell's first component.
--   bitVal false = O ,  bitVal true = s O .
-- The cell is then  pi (s (bitVal b)) rest , a proper node (first
-- component  s (bitVal b) >= 1 ).

bitVal : Bool -> Term
bitVal false = O
bitVal true  = ap1 s O

------------------------------------------------------------------------
-- The right-recursive bit-list encoding.

binMetaFromBits : Bits -> Term
binMetaFromBits bnil         = O
binMetaFromBits (bcons b bs) =
  ap2 pi (ap1 s (bitVal b)) (binMetaFromBits bs)

------------------------------------------------------------------------
-- lenR measures bit-list length.
--
--   ap1 lenR (binMetaFromBits bs) = natCode (bitsLength bs)
--
-- Meta-induction on the list:  nil = lenR_at_O ;  cons = lenR_at_node
-- then the inductive hypothesis under  s  (using  s (natCode n) =
-- natCode (suc n)  definitionally).

lenR_binMeta :
  (bs : Bits) ->
  Deriv (eqF (ap1 lenR (binMetaFromBits bs)) (natCode (bitsLength bs)))
lenR_binMeta bnil = lenR_at_O
lenR_binMeta (bcons b bs) =
  ruleTrans (lenR_at_node (bitVal b) (binMetaFromBits bs))
            (cong1 s (lenR_binMeta bs))

------------------------------------------------------------------------
-- The numeric layer: a bit-list denotes a value (LSB first), and a
-- list of length  n  can denote a value as large as  2^n - 1 .  This is
-- the COMPRESSION fact: length is logarithmic in value.  Worked with the
-- bit-list as the primary object (structural, no division-by-two), since
-- the Berry argument chooses  m0  as the value of a fixed bit-list.

------------------------------------------------------------------------
-- Meta doubling and powers of two.

double : Nat -> Nat
double zero    = zero
double (suc n) = suc (suc (double n))

double_mono : {a b : Nat} -> NatLe a b -> NatLe (double a) (double b)
double_mono (le-zero n) = le-zero (double n)
double_mono (le-suc le) = le-suc (le-suc (double_mono le))

m_le_double : (m : Nat) -> NatLe m (double m)
m_le_double zero    = le-zero zero
m_le_double (suc m) = le-suc (le-suc-right (m_le_double m))

pow2 : Nat -> Nat
pow2 zero    = suc zero
pow2 (suc n) = double (pow2 n)

-- n < 2^n  (strict, as  suc n <= pow2 n ).
n_lt_pow2 : (n : Nat) -> NatLe (suc n) (pow2 n)
n_lt_pow2 zero    = le-refl (suc zero)
n_lt_pow2 (suc n) =
  le-trans (le-suc (le-suc (m_le_double n)))
           (double_mono (n_lt_pow2 n))

------------------------------------------------------------------------
-- Value of a bit-list (LSB first):  valOf [b0,b1,...] = b0 + 2*valOf[b1,...].

valOf : Bits -> Nat
valOf bnil            = zero
valOf (bcons false bs) =          double (valOf bs)
valOf (bcons true  bs) = suc      (double (valOf bs))

------------------------------------------------------------------------
-- The all-ones list of length  n  (value  2^n - 1 ).

onesList : Nat -> Bits
onesList zero    = bnil
onesList (suc n) = bcons true (onesList n)

bitsLength_onesList : (n : Nat) -> Eq (bitsLength (onesList n)) n
bitsLength_onesList zero    = refl
bitsLength_onesList (suc n) = eqCong suc (bitsLength_onesList n)

-- The compression bound:  2^n <= 1 + valOf (onesList n) , i.e. an
-- n-bit list reaches values  >= 2^n - 1 .
valOf_onesList_lower :
  (n : Nat) -> NatLe (pow2 n) (suc (valOf (onesList n)))
valOf_onesList_lower zero    = le-refl (suc zero)
valOf_onesList_lower (suc n) = double_mono (valOf_onesList_lower n)

------------------------------------------------------------------------
-- HEADLINE (compression works):  the compressed code of  onesList n  has
--  lenR-length exactly  n , while its value is  >= 2^n - 1 > n .  So the
-- compressed numeral is exponentially shorter than its (unary) value.
--
--   lenR_onesList :  ap1 lenR (binMetaFromBits (onesList n)) = natCode n
--   (value bound:   pow2 n <= suc (valOf (onesList n))   [valOf_onesList_lower]
--    with          suc n  <= pow2 n                      [n_lt_pow2])

lenR_onesList :
  (n : Nat) ->
  Deriv (eqF (ap1 lenR (binMetaFromBits (onesList n))) (natCode n))
lenR_onesList n =
  eqSubst (\ k -> Deriv (eqF (ap1 lenR (binMetaFromBits (onesList n))) (natCode k)))
          (bitsLength_onesList n)
          (lenR_binMeta (onesList n))

-- Length is strictly below value (for these lists):  suc n <= suc (valOf ..),
-- i.e.  n <= valOf (onesList n)  -- and the gap is exponential by the two
-- bounds above.
length_le_value :
  (n : Nat) -> NatLe (suc n) (suc (valOf (onesList n)))
length_le_value n = le-trans (n_lt_pow2 n) (valOf_onesList_lower n)
