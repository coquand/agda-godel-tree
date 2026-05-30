{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.PeterRec -- Rosa Peter's iterated-parameter-transformer
-- induction principle, derived in BRA via the binary-pairing
-- backward-iterate encoding.
--
-- The principle (informal).  Given a step combinator  g : Fun2  and
-- a predicate  P  with var 2 = position slot, var 3 = value slot,
-- plus Term parameters  x  (upper bound) and  y  (base value):
--
--   (B)   P[2 := 0]                       -- "P(0, y) for any y"
--   (S)   P[3 := g v2 v3]  ->  P[2 := s v2]   -- "P(n, g(n,y)) -> P(s n, y)"
--   ----------------------------------------------------------------
--                  P[2 := x, 3 := y]      -- "P(x, y)"
--
-- Construction (per Rosa Peter):
--
--   u    := pi x y
--   H g  := R Snd g (Fan (Lift1 Fst) (Lift2 s) sub)     -- forward iterate
--   G(u, n) := ap2 (H g) u (sub (Fst u) n)               -- backward iterate
--
-- Two algebra lemmas about G :
--
--   G-top  : G(pi x y, x) = y .
--   G-step : leq (s n) (Fst u) -> G(u, n) = g(n, G(u, s n)) .
--
-- Motive of the induction:
--
--   Q := imp (leq (var 2) x) (substF 3 (G(u, var 2)) P)
--
-- ruleIndNat 2 on Q .  Base discharges via (B) instantiated at
-- v3 := G(u, O) = y  (G-top + cleanup).  Step uses IH + T80 +
-- G-step + (S) instantiated at v3 := G(u, s var 2) ; the rewriting
-- of the value slot uses  BRA4.SubstCongInternal.substF_cong_imp .
--
-- Endpoint specialisation : ruleInst 2 x  on Q ; discharge  leq x x
-- via T73 ; rewrite value slot via G-top + substF_cong  --> the
-- conclusion  Deriv (substF 3 y (substF 2 x P)) .
--
-- Side conditions (Carneiro):  x  and  y  must be CLOSED at vars 2
-- and 3 (so that the motive's substitutions don't accidentally walk
-- into them).  The user provides  ClosedAtVar  witnesses.

module BRA4.PeterRec where

open import BRA4.Base
open import BRA4.SubLeqIdentities
  using ( identityA ; identityB ; transUnderOne )
open import BRA4.LoopReaches
  using ( ClosedAtVar ; mkCAV ; cavSubst ; cav_O ; cav_ap1 ; cav_ap2 ; cav_var )
open import BRA4.SubstCongInternal using ( substF_cong_imp )

open import BRA3.Church       using ( pi ; sub )
open import BRA3.ChurchLeq    using ( leq ; T76 )
open import BRA3.ChurchSubSucc using ( T_sub_O )
open import BRA3.ChurchT73    using ( T73 )
open import BRA3.ChurchT80    using ( T80 )
open import BRA3.PairAlgebra  using ( Fst ; Snd ; axFst ; axSnd )
open import BRA3.Fan
  using ( Lift1 ; Lift2 ; Fan ; Lift1_eq ; Lift2_eq ; Fan_eq )
open import BRA3.Logic        using ( impTrans ; eqSymImp ; prependEqLeft ; appendEqRight )
open import BRA3.Equational   using ( axRefl ; ruleSym ; ruleTrans ; cong1 ; congL ; congR )
open import BRA3.Substitutivity using ( substF_cong )
open import BRA3.Contrapositive
  using ( identP ; liftP ; bComb ; bCombTwo ; compI )
open import BRA3.RuleInst2    using ( ruleInst2 )

------------------------------------------------------------------------
-- Section 1.  Meta-Eq lemmas about substT / substF.
--
-- Two facts at the META (Agda) level:
--
--   COMMUTATION  (different indices):
--     substF k1 a (substF k2 b F) = substF k2 (substT k1 a b) (substF k1 a F)
--   under  natEq k1 k2 = false  and  ClosedAtVar k2 a .
--
--   IDEMPOTENCE  (same index):
--     substF k X (substF k Y F) = substF k (substT k X Y) F .

private

  ----------------------------------------------------------------------
  -- substT commutation at  var m .

  substT-comm-var :
    (k1 k2 : Nat) -> Eq (natEq k1 k2) false ->
    (a b : Term) -> ClosedAtVar k2 a ->
    (m : Nat) ->
    Eq (substT k1 a (substT k2 b (var m)))
       (substT k2 (substT k1 a b) (substT k1 a (var m)))
  substT-comm-var k1 k2 neq a b cav m = top (natEq k1 m) refl
    where
      a-fresh-k2 : (X : Term) -> Eq (substT k2 X a) a
      a-fresh-k2 = cavSubst cav

      top : (e1 : Bool) -> Eq (natEq k1 m) e1 ->
            Eq (substT k1 a (substT k2 b (var m)))
               (substT k2 (substT k1 a b) (substT k1 a (var m)))
      top true eq1 = mid1 (natEq k2 m) refl
        where
          mid1 : (e2 : Bool) -> Eq (natEq k2 m) e2 ->
                 Eq (substT k1 a (substT k2 b (var m)))
                    (substT k2 (substT k1 a b) (substT k1 a (var m)))
          mid1 true eq2 =
            -- m = k1 AND m = k2 ; contradicts neq.
            let k1_eq_m : Eq k1 m
                k1_eq_m = natEqTrue_implies_eq k1 m eq1
                k2_eq_m : Eq k2 m
                k2_eq_m = natEqTrue_implies_eq k2 m eq2
                k1_eq_k2 : Eq k1 k2
                k1_eq_k2 = eqTrans k1_eq_m (eqSym k2_eq_m)
                k12_true : Eq (natEq k1 k2) true
                k12_true =
                  eqSubst (\ z -> Eq (natEq k1 z) true) k1_eq_k2 (natEq-refl k1)
            in emptyElim (true_neq_false (eqTrans (eqSym k12_true) neq))
            where
              -- Local re-bindings (these lemmas are in BRA3.RuleInst2).
              open import BRA3.RuleInst2
                using ( natEqTrue_implies_eq ; natEq-refl ; true_neq_false )
          mid1 false eq2 =
            -- m = k1 , m =/= k2 .
            let iLHS-eq : Eq (substT k2 b (var m)) (var m)
                iLHS-eq = eqCong (\ bb -> boolCase bb b (var m)) eq2

                substK1_at_m : Eq (substT k1 a (var m)) a
                substK1_at_m = eqCong (\ bb -> boolCase bb a (var m)) eq1

                lhs-final : Eq (substT k1 a (substT k2 b (var m))) a
                lhs-final = eqTrans (eqCong (substT k1 a) iLHS-eq) substK1_at_m

                rhs-final : Eq (substT k2 (substT k1 a b) (substT k1 a (var m))) a
                rhs-final =
                  eqTrans
                    (eqCong (substT k2 (substT k1 a b)) substK1_at_m)
                    (a-fresh-k2 (substT k1 a b))
            in eqTrans lhs-final (eqSym rhs-final)
      top false eq1 = mid2 (natEq k2 m) refl
        where
          mid2 : (e2 : Bool) -> Eq (natEq k2 m) e2 ->
                 Eq (substT k1 a (substT k2 b (var m)))
                    (substT k2 (substT k1 a b) (substT k1 a (var m)))
          mid2 true eq2 =
            -- m =/= k1 , m = k2 .
            let iLHS-eq : Eq (substT k2 b (var m)) b
                iLHS-eq = eqCong (\ bb -> boolCase bb b (var m)) eq2

                lhs-final : Eq (substT k1 a (substT k2 b (var m)))
                               (substT k1 a b)
                lhs-final = eqCong (substT k1 a) iLHS-eq

                rhs-inner : Eq (substT k1 a (var m)) (var m)
                rhs-inner = eqCong (\ bb -> boolCase bb a (var m)) eq1

                rhs-final : Eq (substT k2 (substT k1 a b) (substT k1 a (var m)))
                               (substT k1 a b)
                rhs-final =
                  eqTrans
                    (eqCong (substT k2 (substT k1 a b)) rhs-inner)
                    (eqCong (\ bb -> boolCase bb (substT k1 a b) (var m)) eq2)
            in eqTrans lhs-final (eqSym rhs-final)
          mid2 false eq2 =
            -- m =/= k1 , m =/= k2 .  Both sides reduce to  var m .
            let iLHS-eq : Eq (substT k2 b (var m)) (var m)
                iLHS-eq = eqCong (\ bb -> boolCase bb b (var m)) eq2

                lhs-final-var : Eq (substT k1 a (var m)) (var m)
                lhs-final-var = eqCong (\ bb -> boolCase bb a (var m)) eq1

                lhs-final : Eq (substT k1 a (substT k2 b (var m))) (var m)
                lhs-final =
                  eqTrans (eqCong (substT k1 a) iLHS-eq) lhs-final-var

                rhs-final : Eq (substT k2 (substT k1 a b) (substT k1 a (var m))) (var m)
                rhs-final =
                  eqTrans
                    (eqCong (substT k2 (substT k1 a b)) lhs-final-var)
                    (eqCong (\ bb -> boolCase bb (substT k1 a b) (var m)) eq2)
            in eqTrans lhs-final (eqSym rhs-final)

  substT-comm :
    (k1 k2 : Nat) -> Eq (natEq k1 k2) false ->
    (a b : Term) -> ClosedAtVar k2 a ->
    (t : Term) ->
    Eq (substT k1 a (substT k2 b t))
       (substT k2 (substT k1 a b) (substT k1 a t))
  substT-comm k1 k2 neq a b cav O           = refl
  substT-comm k1 k2 neq a b cav (var m)     = substT-comm-var k1 k2 neq a b cav m
  substT-comm k1 k2 neq a b cav (ap1 f t)   =
    eqCong (ap1 f) (substT-comm k1 k2 neq a b cav t)
  substT-comm k1 k2 neq a b cav (ap2 g t1 t2) =
    eqTrans
      (eqCong (\ x -> ap2 g x (substT k1 a (substT k2 b t2)))
              (substT-comm k1 k2 neq a b cav t1))
      (eqCong (\ y -> ap2 g (substT k2 (substT k1 a b) (substT k1 a t1)) y)
              (substT-comm k1 k2 neq a b cav t2))

  substEq-comm :
    (k1 k2 : Nat) -> Eq (natEq k1 k2) false ->
    (a b : Term) -> ClosedAtVar k2 a ->
    (e : Equation) ->
    Eq (substEq k1 a (substEq k2 b e))
       (substEq k2 (substT k1 a b) (substEq k1 a e))
  substEq-comm k1 k2 neq a b cav (eqn l r) =
    eqTrans
      (eqCong (\ x -> eqn x (substT k1 a (substT k2 b r)))
              (substT-comm k1 k2 neq a b cav l))
      (eqCong (\ y -> eqn (substT k2 (substT k1 a b) (substT k1 a l)) y)
              (substT-comm k1 k2 neq a b cav r))

  substF-comm :
    (k1 k2 : Nat) -> Eq (natEq k1 k2) false ->
    (a b : Term) -> ClosedAtVar k2 a ->
    (F : Formula) ->
    Eq (substF k1 a (substF k2 b F))
       (substF k2 (substT k1 a b) (substF k1 a F))
  substF-comm k1 k2 neq a b cav (atomic e) =
    eqCong atomic (substEq-comm k1 k2 neq a b cav e)
  substF-comm k1 k2 neq a b cav (neg p) =
    eqCong neg (substF-comm k1 k2 neq a b cav p)
  substF-comm k1 k2 neq a b cav (imp p q) =
    eqTrans
      (eqCong (\ p' -> imp p' (substF k1 a (substF k2 b q)))
              (substF-comm k1 k2 neq a b cav p))
      (eqCong (\ q' -> imp (substF k2 (substT k1 a b) (substF k1 a p)) q')
              (substF-comm k1 k2 neq a b cav q))

  ----------------------------------------------------------------------
  -- substT  idempotence at the same index.

  substT-idem :
    (k : Nat) (X Y : Term) (t : Term) ->
    Eq (substT k X (substT k Y t)) (substT k (substT k X Y) t)
  substT-idem k X Y O = refl
  substT-idem k X Y (var m) = aux (natEq k m) refl
    where
      aux : (bb : Bool) -> Eq (natEq k m) bb ->
            Eq (substT k X (boolCase bb Y (var m)))
               (boolCase bb (substT k X Y) (var m))
      aux true  _   = refl
      aux false eqb =
        eqCong (\ b' -> boolCase b' X (var m)) eqb
  substT-idem k X Y (ap1 f t) =
    eqCong (ap1 f) (substT-idem k X Y t)
  substT-idem k X Y (ap2 g t1 t2) =
    eqTrans
      (eqCong (\ x -> ap2 g x (substT k X (substT k Y t2))) (substT-idem k X Y t1))
      (eqCong (\ y -> ap2 g (substT k (substT k X Y) t1) y) (substT-idem k X Y t2))

  substEq-idem :
    (k : Nat) (X Y : Term) (e : Equation) ->
    Eq (substEq k X (substEq k Y e)) (substEq k (substT k X Y) e)
  substEq-idem k X Y (eqn l r) =
    eqTrans
      (eqCong (\ a' -> eqn a' (substT k X (substT k Y r))) (substT-idem k X Y l))
      (eqCong (\ b' -> eqn (substT k (substT k X Y) l) b') (substT-idem k X Y r))

  substF-idem :
    (k : Nat) (X Y : Term) (F : Formula) ->
    Eq (substF k X (substF k Y F)) (substF k (substT k X Y) F)
  substF-idem k X Y (atomic e) = eqCong atomic (substEq-idem k X Y e)
  substF-idem k X Y (neg p)    = eqCong neg    (substF-idem k X Y p)
  substF-idem k X Y (imp p q)  =
    eqTrans
      (eqCong (\ p' -> imp p' (substF k X (substF k Y q))) (substF-idem k X Y p))
      (eqCong (\ q' -> imp (substF k (substT k X Y) p) q') (substF-idem k X Y q))

  ----------------------------------------------------------------------
  -- Self-var:  substF k (var k) F = F .

  substT-self-var : (k : Nat) (t : Term) -> Eq (substT k (var k) t) t
  substT-self-var k O = refl
  substT-self-var k (var m) = aux (natEq k m) refl
    where
      open import BRA3.RuleInst2 using ( natEqTrue_implies_eq )
      aux : (bb : Bool) -> Eq (natEq k m) bb ->
            Eq (boolCase bb (var k) (var m)) (var m)
      aux true  eqb = eqCong var (natEqTrue_implies_eq k m eqb)
      aux false _   = refl
  substT-self-var k (ap1 f t) = eqCong (ap1 f) (substT-self-var k t)
  substT-self-var k (ap2 g t1 t2) =
    eqTrans
      (eqCong (\ x -> ap2 g x (substT k (var k) t2)) (substT-self-var k t1))
      (eqCong (\ y -> ap2 g t1 y) (substT-self-var k t2))

  substEq-self-var : (k : Nat) (e : Equation) -> Eq (substEq k (var k) e) e
  substEq-self-var k (eqn l r) =
    eqTrans
      (eqCong (\ a' -> eqn a' (substT k (var k) r)) (substT-self-var k l))
      (eqCong (\ b' -> eqn l b') (substT-self-var k r))

  substF-self-var : (k : Nat) (F : Formula) -> Eq (substF k (var k) F) F
  substF-self-var k (atomic e) = eqCong atomic (substEq-self-var k e)
  substF-self-var k (neg p)    = eqCong neg    (substF-self-var k p)
  substF-self-var k (imp p q)  =
    eqTrans
      (eqCong (\ p' -> imp p' (substF k (var k) q)) (substF-self-var k p))
      (eqCong (\ q' -> imp p q') (substF-self-var k q))

  ----------------------------------------------------------------------
  -- Round-trip:  under  c =/= k  and  NatLe (maxVarT t) c ,
  --   substT c X (substT k (var c) t) = substT k X t .
  -- (The freshness of c in t prevents the m = c sub-case at  var .)

  open import BRA3.RuleInst2
    using ( NatLe ; le-zero ; le-suc ; le-trans
          ; maxVarT ; maxVarEq ; maxVarF
          ; maxN ; maxN-le-left ; maxN-le-right
          ; natEq-lt-false )

  substT-roundtrip :
    (c k : Nat) -> Eq (natEq c k) false ->
    (X : Term) (t : Term) ->
    NatLe (maxVarT t) c ->
    Eq (substT c X (substT k (var c) t)) (substT k X t)
  substT-roundtrip c k cNeK X O _ = refl
  substT-roundtrip c k cNeK X (var m) le = aux (natEq k m) refl
    where
      cNeM : Eq (natEq c m) false
      cNeM = natEq-lt-false c m le

      aux : (bb : Bool) -> Eq (natEq k m) bb ->
            Eq (substT c X (boolCase bb (var c) (var m)))
               (boolCase bb X (var m))
      aux true  _ =
        -- LHS: substT c X (var c) = X (boolCase natEq c c = true).  Use natEq-refl c.
        eqCong (\ b' -> boolCase b' X (var c)) (natEq-refl c)
        where
          open import BRA3.RuleInst2 using ( natEq-refl )
      aux false _ =
        -- LHS: substT c X (var m) = var m (since natEq c m = false via cNeM).
        eqCong (\ b' -> boolCase b' X (var m)) cNeM
  substT-roundtrip c k cNeK X (ap1 f t) le =
    eqCong (ap1 f) (substT-roundtrip c k cNeK X t le)
  substT-roundtrip c k cNeK X (ap2 g t1 t2) le =
    let le_a : NatLe (maxVarT t1) c
        le_a = le-trans (maxN-le-left (maxVarT t1) (maxVarT t2)) le
        le_b : NatLe (maxVarT t2) c
        le_b = le-trans (maxN-le-right (maxVarT t1) (maxVarT t2)) le
    in eqTrans
         (eqCong (\ x -> ap2 g x (substT c X (substT k (var c) t2)))
                 (substT-roundtrip c k cNeK X t1 le_a))
         (eqCong (\ y -> ap2 g (substT k X t1) y)
                 (substT-roundtrip c k cNeK X t2 le_b))

  substEq-roundtrip :
    (c k : Nat) -> Eq (natEq c k) false ->
    (X : Term) (e : Equation) ->
    NatLe (maxVarEq e) c ->
    Eq (substEq c X (substEq k (var c) e)) (substEq k X e)
  substEq-roundtrip c k cNeK X (eqn l r) le =
    let le_l : NatLe (maxVarT l) c
        le_l = le-trans (maxN-le-left (maxVarT l) (maxVarT r)) le
        le_r : NatLe (maxVarT r) c
        le_r = le-trans (maxN-le-right (maxVarT l) (maxVarT r)) le
    in eqTrans
         (eqCong (\ a' -> eqn a' (substT c X (substT k (var c) r)))
                 (substT-roundtrip c k cNeK X l le_l))
         (eqCong (\ b' -> eqn (substT k X l) b')
                 (substT-roundtrip c k cNeK X r le_r))

  substF-roundtrip :
    (c k : Nat) -> Eq (natEq c k) false ->
    (X : Term) (F : Formula) ->
    NatLe (maxVarF F) c ->
    Eq (substF c X (substF k (var c) F)) (substF k X F)
  substF-roundtrip c k cNeK X (atomic e) le =
    eqCong atomic (substEq-roundtrip c k cNeK X e le)
  substF-roundtrip c k cNeK X (neg p) le =
    eqCong neg (substF-roundtrip c k cNeK X p le)
  substF-roundtrip c k cNeK X (imp p q) le =
    let le_p : NatLe (maxVarF p) c
        le_p = le-trans (maxN-le-left (maxVarF p) (maxVarF q)) le
        le_q : NatLe (maxVarF q) c
        le_q = le-trans (maxN-le-right (maxVarF p) (maxVarF q)) le
    in eqTrans
         (eqCong (\ p' -> imp p' (substF c X (substF k (var c) q)))
                 (substF-roundtrip c k cNeK X p le_p))
         (eqCong (\ q' -> imp (substF k X p) q')
                 (substF-roundtrip c k cNeK X q le_q))

------------------------------------------------------------------------
-- Section 2.  The forward H : Fun2 -> Fun2 iterated transformer.
--
--   ap2 (H g) u O      = ap1 Snd u
--   ap2 (H g) u (s d)  = ap2 g (sub (Fst u) (s d)) (ap2 (H g) u d)
--
-- Construction:  H g = R Snd g (Fan (Lift1 Fst) (Lift2 s) sub) .

H : Fun2 -> Fun2
H g = R Snd g (Fan (Lift1 Fst) (Lift2 s) sub)

H-base : (g : Fun2) (up : Term) -> Deriv (eqF (ap2 (H g) up O) (ap1 Snd up))
H-base g up = ax_R_base Snd g (Fan (Lift1 Fst) (Lift2 s) sub) up

H-step :
  (g : Fun2) (up d : Term) ->
  Deriv (eqF (ap2 (H g) up (ap1 s d))
              (ap2 g (ap2 sub (ap1 Fst up) (ap1 s d)) (ap2 (H g) up d)))
H-step g up d =
  let h2body : Fun2
      h2body = Fan (Lift1 Fst) (Lift2 s) sub

      e1 : Deriv (eqF (ap2 (H g) up (ap1 s d))
                       (ap2 g (ap2 h2body up d) (ap2 (H g) up d)))
      e1 = ax_R_step Snd g h2body up d

      eFan : Deriv (eqF (ap2 h2body up d)
                         (ap2 sub (ap2 (Lift1 Fst) up d) (ap2 (Lift2 s) up d)))
      eFan = Fan_eq (Lift1 Fst) (Lift2 s) sub up d

      eL1 : Deriv (eqF (ap2 (Lift1 Fst) up d) (ap1 Fst up))
      eL1 = Lift1_eq Fst up d

      eL2 : Deriv (eqF (ap2 (Lift2 s) up d) (ap1 s d))
      eL2 = Lift2_eq s up d

      e_h2body : Deriv (eqF (ap2 h2body up d)
                             (ap2 sub (ap1 Fst up) (ap1 s d)))
      e_h2body =
        ruleTrans eFan
          (ruleTrans (congL sub (ap2 (Lift2 s) up d) eL1)
                      (congR sub (ap1 Fst up) eL2))

      e_cong_g : Deriv (eqF (ap2 g (ap2 h2body up d) (ap2 (H g) up d))
                             (ap2 g (ap2 sub (ap1 Fst up) (ap1 s d))
                                     (ap2 (H g) up d)))
      e_cong_g = congL g (ap2 (H g) up d) e_h2body
  in ruleTrans e1 e_cong_g

------------------------------------------------------------------------
-- Section 3.  G-top : G(pi x y, x) = y .
--
-- We state G's value at  (u, n)  via the descent counter  sub x n
-- (using  x  directly rather than  Fst u  -- bridged inside if needed).

G-top :
  (g : Fun2) (x y : Term) ->
  Deriv (eqF (ap2 (H g) (ap2 pi x y) (ap2 sub x x)) y)
G-top g x y =
  let up : Term
      up = ap2 pi x y

      eT73 : Deriv (eqF (ap2 sub x x) O)
      eT73 = ruleInst zero x T73

      eH_to_O : Deriv (eqF (ap2 (H g) up (ap2 sub x x)) (ap2 (H g) up O))
      eH_to_O = congR (H g) up eT73

      eHbase : Deriv (eqF (ap2 (H g) up O) (ap1 Snd up))
      eHbase = H-base g up

      eSnd : Deriv (eqF (ap1 Snd up) y)
      eSnd = axSnd x y
  in ruleTrans eH_to_O (ruleTrans eHbase eSnd)

------------------------------------------------------------------------
-- Section 4.  G-step (in x-form) :  under  leq (s n) x ,
--   G(pi x y, n) = g(n, G(pi x y, s n))
-- where  G(pi x y, n) := ap2 (H g) (pi x y) (sub x n) .
--
-- The proof uses H-step at  (u, sub x (s n)) , then bridges via
-- identityA / identityB to clean the "sub x ..." arithmetic.
-- The bridge from H-step's  sub (Fst u) (...)  to  sub x (...)
-- uses  axFst .

G-step :
  (g : Fun2) (x y n : Term) ->
  Deriv (imp (leq (ap1 s n) x)
              (eqF (ap2 (H g) (ap2 pi x y) (ap2 sub x n))
                    (ap2 g n
                          (ap2 (H g) (ap2 pi x y) (ap2 sub x (ap1 s n))))))
G-step g x y n =
  let up : Term
      up = ap2 pi x y

      Hyp : Formula
      Hyp = leq (ap1 s n) x

      d_next : Term       -- = sub x (s n)
      d_next = ap2 sub x (ap1 s n)

      d_curr : Term       -- = sub x n
      d_curr = ap2 sub x n

      G_n : Term
      G_n = ap2 (H g) up d_curr

      G_sn : Term
      G_sn = ap2 (H g) up d_next

      -- identityA at  (var 0 := x, var 1 := n) :
      --   imp (leq (s n) x) (eqF (sub x n) (s (sub x (s n))))
      --   = imp Hyp (eqF d_curr (s d_next)) .
      idA_at : Deriv (imp Hyp (eqF d_curr (ap1 s d_next)))
      idA_at = ruleInst2 zero x (suc zero) n refl identityA

      -- Lift to:  imp Hyp (eqF G_n (H u (s d_next))) .
      eH_imp : Deriv (imp Hyp (eqF G_n (ap2 (H g) up (ap1 s d_next))))
      eH_imp =
        bComb (liftP Hyp (ax_eqCongR (H g) d_curr (ap1 s d_next) up)) idA_at

      -- H-step (unconditional):
      --   H(u, s d_next) = g(sub (Fst u) (s d_next), G_sn) .
      hStep_FstU : Deriv (eqF (ap2 (H g) up (ap1 s d_next))
                               (ap2 g (ap2 sub (ap1 Fst up) (ap1 s d_next)) G_sn))
      hStep_FstU = H-step g up d_next

      -- Bridge  sub (Fst u) (s d_next) -> sub x (s d_next)  via  axFst .
      eFst : Deriv (eqF (ap1 Fst up) x)
      eFst = axFst x y

      e_sub_FstU_to_x : Deriv (eqF (ap2 sub (ap1 Fst up) (ap1 s d_next))
                                    (ap2 sub x (ap1 s d_next)))
      e_sub_FstU_to_x = congL sub (ap1 s d_next) eFst

      e_g_bridge : Deriv (eqF (ap2 g (ap2 sub (ap1 Fst up) (ap1 s d_next)) G_sn)
                                (ap2 g (ap2 sub x (ap1 s d_next)) G_sn))
      e_g_bridge = congL g G_sn e_sub_FstU_to_x

      hStep_x : Deriv (eqF (ap2 (H g) up (ap1 s d_next))
                            (ap2 g (ap2 sub x (ap1 s d_next)) G_sn))
      hStep_x = ruleTrans hStep_FstU e_g_bridge

      hStep_x_imp : Deriv (imp Hyp (eqF (ap2 (H g) up (ap1 s d_next))
                                          (ap2 g (ap2 sub x (ap1 s d_next)) G_sn)))
      hStep_x_imp = liftP Hyp hStep_x

      -- T80 at (var 0 := n, var 1 := x) :  imp Hyp (leq n x) .
      T80_at : Deriv (imp Hyp (leq n x))
      T80_at = ruleInst2 zero n (suc zero) x refl T80

      -- identityB at (var 0 := x, var 1 := n) :
      --   imp (leq n x) (eqF (sub x (sub x n)) n) .
      idB_at : Deriv (imp (leq n x) (eqF (ap2 sub x (ap2 sub x n)) n))
      idB_at = ruleInst2 zero x (suc zero) n refl identityB

      idB_under_Hyp : Deriv (imp Hyp (eqF (ap2 sub x (ap2 sub x n)) n))
      idB_under_Hyp = impTrans T80_at idB_at

      -- d_curr  IS  ap2 sub x n  syntactically (by definition).
      -- idA_at reversed:  imp Hyp (eqF (s d_next) d_curr) .
      idA_sym_imp : Deriv (imp Hyp (eqF (ap1 s d_next) d_curr))
      idA_sym_imp =
        bComb (liftP Hyp (eqSymImp d_curr (ap1 s d_next))) idA_at

      -- cong sub x on idA_sym_imp:
      --   imp Hyp (eqF (sub x (s d_next)) (sub x d_curr)) .
      step1 : Deriv (imp Hyp (eqF (ap2 sub x (ap1 s d_next))
                                   (ap2 sub x d_curr)))
      step1 =
        bComb (liftP Hyp (ax_eqCongR sub (ap1 s d_next) d_curr x))
              idA_sym_imp

      -- Combine step1 and idB_under_Hyp -- sub x d_curr ≡ sub x (sub x n) :
      n_eq : Deriv (imp Hyp (eqF (ap2 sub x (ap1 s d_next)) n))
      n_eq = transUnderOne step1 idB_under_Hyp

      step2 : Deriv (imp Hyp (eqF G_n (ap2 g (ap2 sub x (ap1 s d_next)) G_sn)))
      step2 = transUnderOne eH_imp hStep_x_imp

      cong_g_imp : Deriv (imp Hyp (eqF (ap2 g (ap2 sub x (ap1 s d_next)) G_sn)
                                        (ap2 g n G_sn)))
      cong_g_imp =
        bComb (liftP Hyp (ax_eqCongL g (ap2 sub x (ap1 s d_next)) n G_sn))
              n_eq
  in transUnderOne step2 cong_g_imp

------------------------------------------------------------------------
-- Section 5.  PeterRec : the abstract induction principle.
--
-- Statement (clean -- no  x, y  args, no  ClosedAtVar  args, conclusion
-- is  Deriv P  with var 0 = n , var 1 = y  free for later  ruleInst ).
--
-- Construction:
--   * Fresh BRA var c := freshC P O 0 1  (so  c > maxVarF P ,  c > 1 ,
--     c > 0 ; hence  c >= 2  and  P  is closed at  c ).
--   * uu := pi (var 0) (var 1) -- packed pair at the user's slots.
--   * V_at n := H g uu (sub (var 0) n)  -- the backward iterate.
--   * Motive
--       Q := imp (leq (var c) (var 0))
--                 (substF 1 (V_at (var c)) (substF 0 (var c) P)) .
--   * ruleIndNat c on Q .
--   * Endpoint:  ruleInst c (var 0) Q  ; discharge  leq (var 0) (var 0)
--     via T73 ; bridge via  G-top  +  substF_cong  ; collapse
--     substF 0 (var 0) P  via round-trip and substF-self-var .

open import BRA3.RuleInst2
  using ( freshC ; freshC_above_P ; freshC_above_k1 ; freshC_above_k2
        ; natEq_sym ; natEq-refl ; substF_above_max )

PeterRec :
  (g : Fun2) (P : Formula) ->
  Deriv (substF zero O P) ->
  Deriv (imp (substF (suc zero) (ap2 g (var zero) (var (suc zero))) P)
              (substF zero (ap1 s (var zero)) P)) ->
  Deriv P
PeterRec g P premiseB premiseS =
  let
      ------------------------------------------------------------------
      -- Section 5a.  Fresh BRA var c and closedness facts.

      c : Nat
      c = freshC P O zero (suc zero)

      cAboveP : NatLe (maxVarF P) c
      cAboveP = freshC_above_P P O zero (suc zero)

      cAboveK1 : NatLe (suc zero) c
      cAboveK1 = freshC_above_k1 P O zero (suc zero)

      cAboveK2 : NatLe (suc (suc zero)) c
      cAboveK2 = freshC_above_k2 P O zero (suc zero)

      cNe0 : Eq (natEq c zero) false
      cNe0 = natEq-lt-false c zero cAboveK1

      cNe1 : Eq (natEq c (suc zero)) false
      cNe1 = natEq-lt-false c (suc zero) cAboveK2

      ne0c : Eq (natEq zero c) false
      ne0c = eqTrans (natEq_sym zero c) cNe0

      ne1c : Eq (natEq (suc zero) c) false
      ne1c = eqTrans (natEq_sym (suc zero) c) cNe1

      -- substF c X P = P  for any X.
      P-fresh : (X : Term) -> Eq (substF c X P) P
      P-fresh X = substF_above_max c P X cAboveP

      ------------------------------------------------------------------
      -- Section 5b.  Setup uu, V_at, ClosedAtVar witnesses.

      uu : Term
      uu = ap2 pi (var zero) (var (suc zero))

      cav-var0 : ClosedAtVar c (var zero)
      cav-var0 = cav_var c zero cNe0

      cav-var1 : ClosedAtVar c (var (suc zero))
      cav-var1 = cav_var c (suc zero) cNe1

      cav-uu : ClosedAtVar c uu
      cav-uu = cav_ap2 c pi (var zero) (var (suc zero)) cav-var0 cav-var1

      V_at : Term -> Term
      V_at n = ap2 (H g) uu (ap2 sub (var zero) n)

      ------------------------------------------------------------------
      -- Section 5c.  The motive Q.

      Q : Formula
      Q = imp (leq (var c) (var zero))
               (substF (suc zero) (V_at (var c)) (substF zero (var c) P))

      ------------------------------------------------------------------
      -- Section 5d.  General Eq:  substT c X (var c) = X .
      --   (by  boolCase  on  natEq c c = true .)

      substT-c-X-varc : (X : Term) -> Eq (substT c X (var c)) X
      substT-c-X-varc X =
        eqCong (\ b -> boolCase b X (var c)) (natEq-refl c)

      ------------------------------------------------------------------
      -- Section 5e.  General Eq:  substT c X (V_at (var c)) = V_at X
      --   (provided  cavSubst cav-var0 X  and  cavSubst cav-uu X  hold,
      --    which they do for ANY X by our cav witnesses).

      substT-c-X-Vat-varc :
        (X : Term) -> Eq (substT c X (V_at (var c))) (V_at X)
      substT-c-X-Vat-varc X =
        eqTrans
          (eqCong (\ U -> ap2 (H g) U
                            (ap2 sub (substT c X (var zero))
                                      (substT c X (var c))))
                  (cavSubst cav-uu X))
          (eqTrans
            (eqCong (\ V -> ap2 (H g) uu (ap2 sub V (substT c X (var c))))
                    (cavSubst cav-var0 X))
            (eqCong (\ W -> ap2 (H g) uu (ap2 sub (var zero) W))
                    (substT-c-X-varc X)))

      ------------------------------------------------------------------
      -- Section 5f.  baseQ -- Deriv (substF c O Q).
      --
      -- Target-clean:  imp (leq O (var 0)) (substF 1 (V_at O) (substF 0 O P))
      --   -- built directly from premiseB.

      baseQ : Deriv (substF c O Q)
      baseQ =
        let target-clean : Formula
            target-clean =
              imp (leq O (var zero))
                   (substF (suc zero) (V_at O) (substF zero O P))

            base-deriv : Deriv target-clean
            base-deriv =
              mp (axK (substF (suc zero) (V_at O) (substF zero O P))
                       (leq O (var zero)))
                 (ruleInst (suc zero) (V_at O) premiseB)

            -- Meta-Eq bridge:  target-clean = substF c O Q .
            --
            -- substF c O Q  =  imp (substF c O (leq (var c) (var 0)))
            --                        (substF c O (substF 1 (V_at (var c)) (substF 0 (var c) P)))
            --   [Agda computation step].

            -- (i) leq part:  substT c O (var c) = O ;  substT c O (var 0) = var 0  (cav-var0).
            eq-leq : Eq (substF c O (leq (var c) (var zero))) (leq O (var zero))
            eq-leq =
              let eq-sub-l : Eq (substT c O (var c)) O
                  eq-sub-l = substT-c-X-varc O
                  eq-sub-r : Eq (substT c O (var zero)) (var zero)
                  eq-sub-r = cavSubst cav-var0 O
              in eqTrans
                   (eqCong (\ L -> atomic (eqn (ap2 sub L (substT c O (var zero))) O))
                           eq-sub-l)
                   (eqCong (\ R -> atomic (eqn (ap2 sub O R) O))
                           eq-sub-r)

            -- (ii) inner part bridge.
            --   substF c O (substF 1 (V_at (var c)) (substF 0 (var c) P))
            --     = substF 1 (substT c O (V_at (var c))) (substF c O (substF 0 (var c) P))   [comm c with 1]
            --     = substF 1 (V_at O) (substF c O (substF 0 (var c) P))                       [substT-c-X-Vat-varc O]
            --     = substF 1 (V_at O) (substF 0 (substT c O (var c)) (substF c O P))           [comm c with 0]
            --     = substF 1 (V_at O) (substF 0 O (substF c O P))                              [substT-c-X-varc O]
            --     = substF 1 (V_at O) (substF 0 O P)                                            [P-fresh O].

            eq-inner-comm-1 :
              Eq (substF c O (substF (suc zero) (V_at (var c)) (substF zero (var c) P)))
                 (substF (suc zero) (substT c O (V_at (var c)))
                          (substF c O (substF zero (var c) P)))
            eq-inner-comm-1 =
              substF-comm c (suc zero) cNe1 O (V_at (var c)) (cav_O (suc zero))
                           (substF zero (var c) P)

            eq-inner-Vat :
              Eq (substF (suc zero) (substT c O (V_at (var c)))
                          (substF c O (substF zero (var c) P)))
                 (substF (suc zero) (V_at O) (substF c O (substF zero (var c) P)))
            eq-inner-Vat =
              eqCong (\ T -> substF (suc zero) T (substF c O (substF zero (var c) P)))
                     (substT-c-X-Vat-varc O)

            eq-inner-comm-0 :
              Eq (substF c O (substF zero (var c) P))
                 (substF zero (substT c O (var c)) (substF c O P))
            eq-inner-comm-0 =
              substF-comm c zero cNe0 O (var c) (cav_O zero) P

            eq-inner-comm-0-simp :
              Eq (substF zero (substT c O (var c)) (substF c O P))
                 (substF zero O (substF c O P))
            eq-inner-comm-0-simp =
              eqCong (\ T -> substF zero T (substF c O P))
                     (substT-c-X-varc O)

            eq-inner-Pfresh :
              Eq (substF zero O (substF c O P)) (substF zero O P)
            eq-inner-Pfresh = eqCong (substF zero O) (P-fresh O)

            eq-inner-substF-O-c-c :
              Eq (substF c O (substF zero (var c) P)) (substF zero O P)
            eq-inner-substF-O-c-c =
              eqTrans eq-inner-comm-0
                (eqTrans eq-inner-comm-0-simp eq-inner-Pfresh)

            eq-inner-substF-Vat-O :
              Eq (substF (suc zero) (V_at O) (substF c O (substF zero (var c) P)))
                 (substF (suc zero) (V_at O) (substF zero O P))
            eq-inner-substF-Vat-O =
              eqCong (substF (suc zero) (V_at O)) eq-inner-substF-O-c-c

            eq-inner :
              Eq (substF c O (substF (suc zero) (V_at (var c)) (substF zero (var c) P)))
                 (substF (suc zero) (V_at O) (substF zero O P))
            eq-inner =
              eqTrans eq-inner-comm-1
                (eqTrans eq-inner-Vat eq-inner-substF-Vat-O)

            -- Combine eq-leq and eq-inner into eq-Q .
            eq-Q :
              Eq target-clean (substF c O Q)
            eq-Q =
              eqTrans
                (eqCong (\ L -> imp L (substF (suc zero) (V_at O) (substF zero O P)))
                        (eqSym eq-leq))
                (eqCong (imp (substF c O (leq (var c) (var zero))))
                        (eqSym eq-inner))

        in eqSubst Deriv eq-Q base-deriv

      ------------------------------------------------------------------
      -- Section 5g.  stepQ -- Deriv (imp Q (substF c (s var c) Q)).
      --
      -- Target-clean:  imp Q (imp (leq (s v_c) var0)
      --                            (substF 1 (V_at (s v_c)) (substF 0 (s v_c) P))) .
      --
      -- Proof:
      --   (a) IH (Q applied with T80) gives  imp Q (imp HypNew (substF 1 (V_at v_c) (substF 0 v_c P))) .
      --   (b) G-step at  (x := var 0, y := var 1, n := var c) :
      --       imp HypNew (eqF (V_at v_c) (g v_c (V_at (s v_c)))) .
      --   (c) substF_cong_imp on (b) at value-slot var 1 :
      --       imp HypNew (imp (substF 1 (V_at v_c) F0) (substF 1 (g v_c V_sv_c) F0))
      --       where F0 = substF 0 v_c P .
      --   (d) Combine (a) and (c) -> imp Q (imp HypNew (substF 1 (g v_c V_sv_c) F0)) .
      --   (e) premiseS instantiated at  (var 0 := v_c , var 1 := V_sv_c)  via two
      --       successive ruleInsts, plus meta-Eq commutation / idempotence bridges,
      --       gives:
      --         imp (substF 1 (g v_c V_sv_c) (substF 0 v_c P))
      --             (substF 1 V_sv_c (substF 0 (s v_c) P)) .
      --   (f) Combine (d) and (e) under (Q, HypNew) -> step-target-pre .
      --   (g) Meta-Eq bridge to  substF c (s v_c) Q .

      stepQ : Deriv (imp Q (substF c (ap1 s (var c)) Q))
      stepQ =
        let HypNew : Formula
            HypNew = leq (ap1 s (var c)) (var zero)

            Hyp_vc : Formula
            Hyp_vc = leq (var c) (var zero)

            V_vc : Term
            V_vc = V_at (var c)

            V_svc : Term
            V_svc = V_at (ap1 s (var c))

            g-vc-V_svc : Term
            g-vc-V_svc = ap2 g (var c) V_svc

            F0 : Formula
            F0 = substF zero (var c) P

            ----------------------------------------------------------
            -- (a) IH applied.
            --
            -- T80 at (var 0 := var c, var 1 := var 0) : imp HypNew Hyp_vc.
            -- The original T80 has var 0, var 1; we ruleInst2 to put c in var 0's
            -- position and var 0 in var 1's position.  natEq 0 1 = false : refl.

            T80-at : Deriv (imp HypNew Hyp_vc)
            T80-at = ruleInst2 zero (var c) (suc zero) (var zero) refl T80

            idQ : Deriv (imp Q (imp Hyp_vc (substF (suc zero) V_vc F0)))
            idQ = identP Q

            idQ-w-HypNew :
              Deriv (imp Q (imp HypNew (imp Hyp_vc (substF (suc zero) V_vc F0))))
            idQ-w-HypNew =
              bComb (liftP Q
                      (axK (imp Hyp_vc (substF (suc zero) V_vc F0)) HypNew))
                    idQ

            T80-under-Q : Deriv (imp Q (imp HypNew Hyp_vc))
            T80-under-Q = liftP Q T80-at

            IH-applied : Deriv (imp Q (imp HypNew (substF (suc zero) V_vc F0)))
            IH-applied = bCombTwo idQ-w-HypNew T80-under-Q

            ----------------------------------------------------------
            -- (b) G-step at (x := var 0, y := var 1, n := var c).

            gstep : Deriv (imp HypNew (eqF V_vc g-vc-V_svc))
            gstep = G-step g (var zero) (var (suc zero)) (var c)

            ----------------------------------------------------------
            -- (c) substF_cong_imp.

            rewrite-V_vc :
              Deriv (imp HypNew (imp (substF (suc zero) V_vc F0)
                                       (substF (suc zero) g-vc-V_svc F0)))
            rewrite-V_vc = substF_cong_imp HypNew (suc zero) V_vc g-vc-V_svc gstep F0

            ----------------------------------------------------------
            -- (d) Combine.

            rewrite-under-Q :
              Deriv (imp Q (imp HypNew (imp (substF (suc zero) V_vc F0)
                                              (substF (suc zero) g-vc-V_svc F0))))
            rewrite-under-Q = liftP Q rewrite-V_vc

            IH-rewritten :
              Deriv (imp Q (imp HypNew (substF (suc zero) g-vc-V_svc F0)))
            IH-rewritten = bCombTwo rewrite-under-Q IH-applied

            ----------------------------------------------------------
            -- (e) premiseS instantiated and bridged.
            --
            -- Step 1: ruleInst 0 (var c) premiseS.  natEq 0 c = false : ne0c.
            --   Hmm wait, ruleInst takes any Nat and Term; it doesn't need the neq.
            --   ruleInst zero (var c) premiseS :
            --     Deriv (substF zero (var c) (imp (substF 1 (g v0 v1) P) (substF 0 (s v0) P))).
            --   = Deriv (imp (substF 0 (var c) (substF 1 (g v0 v1) P))
            --                  (substF 0 (var c) (substF 0 (s v0) P))).
            --
            -- Bridge antecedent via commutation:
            --   substF 0 (var c) (substF 1 (g v0 v1) P)
            --     = substF 1 (substT 0 (var c) (g v0 v1)) (substF 0 (var c) P)   [comm 0,1; cav 1 (var c) = ne1c]
            --     = substF 1 (g (var c) (var 1)) F0 .
            --   [substT 0 (var c) (g v0 v1) = g (var c) (var 1).]
            --
            -- Bridge consequent via idempotence:
            --   substF 0 (var c) (substF 0 (s v0) P)
            --     = substF 0 (substT 0 (var c) (s v0)) P  [idem]
            --     = substF 0 (s (var c)) P .

            ps-inst-0 : Deriv (substF zero (var c)
                                (imp (substF (suc zero) (ap2 g (var zero) (var (suc zero))) P)
                                      (substF zero (ap1 s (var zero)) P)))
            ps-inst-0 = ruleInst zero (var c) premiseS

            -- After Agda computation:
            --   ps-inst-0 : Deriv (imp (substF 0 (var c) (substF 1 (g v0 v1) P))
            --                            (substF 0 (var c) (substF 0 (s v0) P))).

            -- Bridge antecedent.
            eq-ps0-antec-comm :
              Eq (substF zero (var c) (substF (suc zero) (ap2 g (var zero) (var (suc zero))) P))
                 (substF (suc zero)
                          (substT zero (var c) (ap2 g (var zero) (var (suc zero))))
                          (substF zero (var c) P))
            eq-ps0-antec-comm =
              substF-comm zero (suc zero) refl (var c)
                           (ap2 g (var zero) (var (suc zero)))
                           (cav_var (suc zero) c ne1c) P

            -- substT 0 (var c) (g v0 v1) = g (var c) (var 1).
            -- substT 0 (var c) (var 0) = var c (boolCase true).
            -- substT 0 (var c) (var 1) = var 1 (boolCase natEq 0 1 = false).
            eq-substT-0-vc-gv0v1 :
              Eq (substT zero (var c) (ap2 g (var zero) (var (suc zero))))
                 (ap2 g (var c) (var (suc zero)))
            eq-substT-0-vc-gv0v1 = refl

            eq-ps0-antec-simp :
              Eq (substF (suc zero)
                          (substT zero (var c) (ap2 g (var zero) (var (suc zero))))
                          (substF zero (var c) P))
                 (substF (suc zero) (ap2 g (var c) (var (suc zero))) F0)
            eq-ps0-antec-simp =
              eqCong (\ T -> substF (suc zero) T F0) eq-substT-0-vc-gv0v1

            eq-ps0-antec :
              Eq (substF zero (var c) (substF (suc zero) (ap2 g (var zero) (var (suc zero))) P))
                 (substF (suc zero) (ap2 g (var c) (var (suc zero))) F0)
            eq-ps0-antec = eqTrans eq-ps0-antec-comm eq-ps0-antec-simp

            -- Bridge consequent.
            eq-ps0-conseq-idem :
              Eq (substF zero (var c) (substF zero (ap1 s (var zero)) P))
                 (substF zero (substT zero (var c) (ap1 s (var zero))) P)
            eq-ps0-conseq-idem =
              substF-idem zero (var c) (ap1 s (var zero)) P

            eq-substT-0-vc-s-v0 : Eq (substT zero (var c) (ap1 s (var zero))) (ap1 s (var c))
            eq-substT-0-vc-s-v0 = refl

            eq-ps0-conseq :
              Eq (substF zero (var c) (substF zero (ap1 s (var zero)) P))
                 (substF zero (ap1 s (var c)) P)
            eq-ps0-conseq =
              eqTrans eq-ps0-conseq-idem
                (eqCong (\ T -> substF zero T P) eq-substT-0-vc-s-v0)

            -- Combined: ps-inst-0 has type imp Ant Conseq (computed by Agda).
            -- Bridge via eqSubst to clean form.
            ps-inst-0-clean :
              Deriv (imp (substF (suc zero) (ap2 g (var c) (var (suc zero))) F0)
                          (substF zero (ap1 s (var c)) P))
            ps-inst-0-clean =
              eqSubst (\ AntF ->
                        Deriv (imp AntF
                                    (substF zero (ap1 s (var c)) P)))
                       eq-ps0-antec
                       (eqSubst (\ ConsF ->
                                  Deriv (imp (substF zero (var c)
                                                (substF (suc zero) (ap2 g (var zero) (var (suc zero))) P))
                                              ConsF))
                                eq-ps0-conseq
                                ps-inst-0)

            -- Step 2: ruleInst 1 V_svc on ps-inst-0-clean.
            ps-inst-01 :
              Deriv (substF (suc zero) V_svc
                      (imp (substF (suc zero) (ap2 g (var c) (var (suc zero))) F0)
                            (substF zero (ap1 s (var c)) P)))
            ps-inst-01 = ruleInst (suc zero) V_svc ps-inst-0-clean

            -- After Agda computation:
            --   imp (substF 1 V_svc (substF 1 (g v_c v1) F0))
            --        (substF 1 V_svc (substF 0 (s v_c) P)).

            -- Bridge antecedent via idempotence.
            eq-ps01-antec-idem :
              Eq (substF (suc zero) V_svc (substF (suc zero) (ap2 g (var c) (var (suc zero))) F0))
                 (substF (suc zero) (substT (suc zero) V_svc (ap2 g (var c) (var (suc zero)))) F0)
            eq-ps01-antec-idem =
              substF-idem (suc zero) V_svc (ap2 g (var c) (var (suc zero))) F0

            -- substT 1 V_svc (g v_c v1) = g (substT 1 V_svc v_c) (substT 1 V_svc v1) = g v_c V_svc.
            -- substT 1 V_svc v_c = var c (since natEq 1 c = false via ne1c).
            -- substT 1 V_svc v1 = V_svc.
            -- Need to bridge substT 1 V_svc (var c) = var c (cav-var1 (...) — wait, var c is closed at 1 via cav_var 1 c ne1c).
            cav-varc-1 : ClosedAtVar (suc zero) (var c)
            cav-varc-1 = cav_var (suc zero) c ne1c

            eq-substT-1-Vsvc-vc : Eq (substT (suc zero) V_svc (var c)) (var c)
            eq-substT-1-Vsvc-vc = cavSubst cav-varc-1 V_svc

            eq-substT-1-Vsvc-gvcv1 :
              Eq (substT (suc zero) V_svc (ap2 g (var c) (var (suc zero))))
                 g-vc-V_svc
            eq-substT-1-Vsvc-gvcv1 =
              eqCong (\ V -> ap2 g V V_svc) eq-substT-1-Vsvc-vc

            eq-ps01-antec :
              Eq (substF (suc zero) V_svc (substF (suc zero) (ap2 g (var c) (var (suc zero))) F0))
                 (substF (suc zero) g-vc-V_svc F0)
            eq-ps01-antec =
              eqTrans eq-ps01-antec-idem
                (eqCong (\ T -> substF (suc zero) T F0)
                        eq-substT-1-Vsvc-gvcv1)

            -- Bridge to clean form.
            ps-inst-01-clean :
              Deriv (imp (substF (suc zero) g-vc-V_svc F0)
                          (substF (suc zero) V_svc (substF zero (ap1 s (var c)) P)))
            ps-inst-01-clean =
              eqSubst (\ AntF -> Deriv (imp AntF
                                              (substF (suc zero) V_svc
                                                       (substF zero (ap1 s (var c)) P))))
                       eq-ps01-antec
                       ps-inst-01

            ----------------------------------------------------------
            -- (f) Combine IH-rewritten with ps-inst-01-clean.

            premiseS-under-Q :
              Deriv (imp Q (imp HypNew
                              (imp (substF (suc zero) g-vc-V_svc F0)
                                    (substF (suc zero) V_svc
                                             (substF zero (ap1 s (var c)) P)))))
            premiseS-under-Q = liftP Q (liftP HypNew ps-inst-01-clean)

            step-target-pre :
              Deriv (imp Q (imp HypNew
                              (substF (suc zero) V_svc
                                       (substF zero (ap1 s (var c)) P))))
            step-target-pre = bCombTwo premiseS-under-Q IH-rewritten

            ----------------------------------------------------------
            -- (g) Bridge step-target-pre to substF c (s var c) Q.

            -- Eq from step-target-pre's CONSEQUENT to substF c (s v_c) Q's
            -- (computed) consequent.
            --
            -- substF c (s v_c) Q  (Agda)
            --   = imp (substF c (s v_c) (leq (var c) (var 0)))
            --          (substF c (s v_c) (substF 1 V_vc F0)).
            -- leq part:  substT c (s v_c) (var c) = s v_c.  substT c (s v_c) (var 0) = var 0 (cav-var0).
            --   So = leq (s v_c) (var 0) = HypNew.
            -- Inner part:  substF c (s v_c) (substF 1 V_vc F0)
            --   = substF 1 (substT c (s v_c) V_vc) (substF c (s v_c) F0)
            --       [comm c with 1 ; ClosedAtVar 1 (s v_c) via cav_ap1 1 s _ cav-varc-1]
            --   = substF 1 V_svc (substF c (s v_c) F0)
            --       [substT-c-X-Vat-varc (s v_c) gives V_at (s v_c) = V_svc]
            --   = substF 1 V_svc (substF 0 (substT c (s v_c) (var c)) (substF c (s v_c) P))
            --       [comm c with 0 ; ClosedAtVar 0 (s v_c) via cav_ap1 0 s _ cav-varc-0]
            --   = substF 1 V_svc (substF 0 (s v_c) P)        [substT-c-X-varc (s v_c) gives s v_c; P-fresh].

            cav-varc-0 : ClosedAtVar zero (var c)
            cav-varc-0 = cav_var zero c ne0c

            cav-svc-0 : ClosedAtVar zero (ap1 s (var c))
            cav-svc-0 = cav_ap1 zero s (var c) cav-varc-0

            cav-svc-1 : ClosedAtVar (suc zero) (ap1 s (var c))
            cav-svc-1 = cav_ap1 (suc zero) s (var c) cav-varc-1

            -- leq part bridge.
            eq-step-leq :
              Eq (substF c (ap1 s (var c)) (leq (var c) (var zero))) HypNew
            eq-step-leq =
              let eq-sub-l : Eq (substT c (ap1 s (var c)) (var c)) (ap1 s (var c))
                  eq-sub-l = substT-c-X-varc (ap1 s (var c))
                  eq-sub-r : Eq (substT c (ap1 s (var c)) (var zero)) (var zero)
                  eq-sub-r = cavSubst cav-var0 (ap1 s (var c))
              in eqTrans
                   (eqCong (\ L -> atomic
                              (eqn (ap2 sub L (substT c (ap1 s (var c)) (var zero))) O))
                           eq-sub-l)
                   (eqCong (\ R -> atomic (eqn (ap2 sub (ap1 s (var c)) R) O))
                           eq-sub-r)

            -- Inner bridge.
            eq-step-comm-1 :
              Eq (substF c (ap1 s (var c)) (substF (suc zero) V_vc F0))
                 (substF (suc zero) (substT c (ap1 s (var c)) V_vc)
                          (substF c (ap1 s (var c)) F0))
            eq-step-comm-1 =
              substF-comm c (suc zero) cNe1 (ap1 s (var c)) V_vc cav-svc-1 F0

            eq-step-Vat :
              Eq (substF (suc zero) (substT c (ap1 s (var c)) V_vc)
                          (substF c (ap1 s (var c)) F0))
                 (substF (suc zero) V_svc (substF c (ap1 s (var c)) F0))
            eq-step-Vat =
              eqCong (\ T -> substF (suc zero) T (substF c (ap1 s (var c)) F0))
                     (substT-c-X-Vat-varc (ap1 s (var c)))

            eq-step-comm-0 :
              Eq (substF c (ap1 s (var c)) F0)
                 (substF zero (substT c (ap1 s (var c)) (var c))
                          (substF c (ap1 s (var c)) P))
            eq-step-comm-0 =
              substF-comm c zero cNe0 (ap1 s (var c)) (var c) cav-svc-0 P

            eq-step-comm-0-simp :
              Eq (substF zero (substT c (ap1 s (var c)) (var c))
                          (substF c (ap1 s (var c)) P))
                 (substF zero (ap1 s (var c)) (substF c (ap1 s (var c)) P))
            eq-step-comm-0-simp =
              eqCong (\ T -> substF zero T (substF c (ap1 s (var c)) P))
                     (substT-c-X-varc (ap1 s (var c)))

            eq-step-Pfresh :
              Eq (substF zero (ap1 s (var c)) (substF c (ap1 s (var c)) P))
                 (substF zero (ap1 s (var c)) P)
            eq-step-Pfresh =
              eqCong (substF zero (ap1 s (var c))) (P-fresh (ap1 s (var c)))

            eq-step-F0-final :
              Eq (substF c (ap1 s (var c)) F0)
                 (substF zero (ap1 s (var c)) P)
            eq-step-F0-final =
              eqTrans eq-step-comm-0
                (eqTrans eq-step-comm-0-simp eq-step-Pfresh)

            eq-step-Vat-final :
              Eq (substF (suc zero) V_svc (substF c (ap1 s (var c)) F0))
                 (substF (suc zero) V_svc (substF zero (ap1 s (var c)) P))
            eq-step-Vat-final =
              eqCong (substF (suc zero) V_svc) eq-step-F0-final

            eq-step-inner :
              Eq (substF c (ap1 s (var c)) (substF (suc zero) V_vc F0))
                 (substF (suc zero) V_svc (substF zero (ap1 s (var c)) P))
            eq-step-inner =
              eqTrans eq-step-comm-1
                (eqTrans eq-step-Vat eq-step-Vat-final)

            -- Combine to get full Q-bridge.
            target-step-clean : Formula
            target-step-clean =
              imp HypNew (substF (suc zero) V_svc
                                  (substF zero (ap1 s (var c)) P))

            eq-step-Q :
              Eq target-step-clean (substF c (ap1 s (var c)) Q)
            eq-step-Q =
              eqTrans
                (eqCong (\ L -> imp L (substF (suc zero) V_svc
                                                (substF zero (ap1 s (var c)) P)))
                        (eqSym eq-step-leq))
                (eqCong (imp (substF c (ap1 s (var c)) (leq (var c) (var zero))))
                        (eqSym eq-step-inner))

            step-target :
              Deriv (imp Q (substF c (ap1 s (var c)) Q))
            step-target =
              eqSubst (\ F -> Deriv (imp Q F)) eq-step-Q step-target-pre

        in step-target

      ------------------------------------------------------------------
      -- Section 5h.  Apply ruleIndNat c to get Deriv Q.

      Q-derived : Deriv Q
      Q-derived = ruleIndNat c {P = Q} baseQ stepQ

      ------------------------------------------------------------------
      -- Section 5i.  Endpoint specialisation: Deriv P.

      Q-at-v0 : Deriv (substF c (var zero) Q)
      Q-at-v0 = ruleInst c (var zero) Q-derived

      -- Bridge:
      --   substF c (var 0) Q
      --     = imp (leq (substT c (var 0) (var c)) (substT c (var 0) (var 0)))
      --            (substF c (var 0) (substF 1 V_vc F0))
      --     = imp (leq (var 0) (var 0))
      --            (substF 1 (V_at (var 0)) (substF c (var 0) F0))    [comm 1 ; substT-c-X-Vat-varc]
      --     = imp (leq (var 0) (var 0))
      --            (substF 1 (V_at (var 0)) P)                          [round-trip + self-var on F0].

      eq-end-leq :
        Eq (substF c (var zero) (leq (var c) (var zero)))
           (leq (var zero) (var zero))
      eq-end-leq =
        let eq-sub-l : Eq (substT c (var zero) (var c)) (var zero)
            eq-sub-l = substT-c-X-varc (var zero)
            eq-sub-r : Eq (substT c (var zero) (var zero)) (var zero)
            eq-sub-r = cavSubst cav-var0 (var zero)
        in eqTrans
             (eqCong (\ L -> atomic (eqn (ap2 sub L (substT c (var zero) (var zero))) O))
                     eq-sub-l)
             (eqCong (\ R -> atomic (eqn (ap2 sub (var zero) R) O))
                     eq-sub-r)

      eq-end-comm-1 :
        Eq (substF c (var zero) (substF (suc zero) (V_at (var c)) (substF zero (var c) P)))
           (substF (suc zero) (substT c (var zero) (V_at (var c)))
                    (substF c (var zero) (substF zero (var c) P)))
      eq-end-comm-1 =
        substF-comm c (suc zero) cNe1 (var zero) (V_at (var c))
                     (cav_var (suc zero) zero refl) (substF zero (var c) P)

      eq-end-Vat :
        Eq (substF (suc zero) (substT c (var zero) (V_at (var c)))
                    (substF c (var zero) (substF zero (var c) P)))
           (substF (suc zero) (V_at (var zero))
                    (substF c (var zero) (substF zero (var c) P)))
      eq-end-Vat =
        eqCong (\ T -> substF (suc zero) T
                          (substF c (var zero) (substF zero (var c) P)))
               (substT-c-X-Vat-varc (var zero))

      -- Round-trip:  substF c (var 0) (substF 0 (var c) P) = substF 0 (var 0) P.
      eq-end-roundtrip :
        Eq (substF c (var zero) (substF zero (var c) P))
           (substF zero (var zero) P)
      eq-end-roundtrip = substF-roundtrip c zero cNe0 (var zero) P cAboveP

      -- Self-var:  substF 0 (var 0) P = P.
      eq-end-selfvar : Eq (substF zero (var zero) P) P
      eq-end-selfvar = substF-self-var zero P

      eq-end-F0-final :
        Eq (substF c (var zero) (substF zero (var c) P)) P
      eq-end-F0-final = eqTrans eq-end-roundtrip eq-end-selfvar

      eq-end-Vat-final :
        Eq (substF (suc zero) (V_at (var zero))
                    (substF c (var zero) (substF zero (var c) P)))
           (substF (suc zero) (V_at (var zero)) P)
      eq-end-Vat-final =
        eqCong (substF (suc zero) (V_at (var zero))) eq-end-F0-final

      eq-end-inner :
        Eq (substF c (var zero) (substF (suc zero) (V_at (var c)) (substF zero (var c) P)))
           (substF (suc zero) (V_at (var zero)) P)
      eq-end-inner =
        eqTrans eq-end-comm-1
          (eqTrans eq-end-Vat eq-end-Vat-final)

      target-end-clean : Formula
      target-end-clean =
        imp (leq (var zero) (var zero))
             (substF (suc zero) (V_at (var zero)) P)

      eq-end-Q :
        Eq (substF c (var zero) Q) target-end-clean
      eq-end-Q =
        eqTrans
          (eqCong (\ L -> imp L (substF c (var zero) (substF (suc zero) (V_at (var c)) (substF zero (var c) P))))
                  eq-end-leq)
          (eqCong (imp (leq (var zero) (var zero))) eq-end-inner)

      Q-at-v0-clean : Deriv target-end-clean
      Q-at-v0-clean = eqSubst Deriv eq-end-Q Q-at-v0

      -- Discharge leq (var 0) (var 0) via T73.
      leq-refl : Deriv (leq (var zero) (var zero))
      leq-refl = ruleInst zero (var zero) T73

      stage-Vat-v0 : Deriv (substF (suc zero) (V_at (var zero)) P)
      stage-Vat-v0 = mp Q-at-v0-clean leq-refl

      -- Bridge V_at (var 0) -> var 1 via G-top.
      gtop : Deriv (eqF (V_at (var zero)) (var (suc zero)))
      gtop = G-top g (var zero) (var (suc zero))

      bridge-to-var1 :
        Deriv (imp (substF (suc zero) (V_at (var zero)) P)
                    (substF (suc zero) (var (suc zero)) P))
      bridge-to-var1 = substF_cong (suc zero) (V_at (var zero)) (var (suc zero)) gtop P

      stage-var1 : Deriv (substF (suc zero) (var (suc zero)) P)
      stage-var1 = mp bridge-to-var1 stage-Vat-v0

      -- substF 1 (var 1) P = P via substF-self-var.
      final : Deriv P
      final = eqSubst Deriv (substF-self-var (suc zero) P) stage-var1
  in final
