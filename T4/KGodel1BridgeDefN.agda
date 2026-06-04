{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KGodel1BridgeDefN -- the number-code re-pointing of T4.KGodel1BridgeDef :
-- pins the symbolic node-accounting to  tc := thmT  and DEFINES the canonical
-- description-length threshold
--
--   L* := exp2 (natCode (fst boundDefN))         ( the inner bound, = 2^k )
--   N  := predNof (fst boundDefN) = exp3 (s L*)   ( the guard threshold, 3^(L*+1) )
--
-- together with the HONEST size bound on the REAL diagonal  KdefDiagN.gLcodeDefN N :
--
--   domBDefN : NatLe (nodes (gLcodeDefN N)) (powN (fst boundDefN))   ( = L* as Nat ).
--
-- This is exactly Chaitin's  c + log n < n  fixed point ( affine_dom ) at the
-- honest p<N guard -- it CLOSES, mirroring KGodel1BridgeDef.domBDef.

module T4.KGodel1BridgeDefN where

open import T4.Base
open import T4.ThmT      using ( thmT )
open import T4.Exp       using ( exp2 ; powN )
open import T4.ProgEnc   using ( nodes )
open import T4.ProgNodes using ( plug )
open import T4.GLCodeNodesN using ( predNof ; H'N )
open import T4.NatExp    using ( Sg ; fst ; snd )

import T4.GLCodePDefN
import T4.KdefDiagN

open import BRA3.RuleInst2 using ( NatLe )

-- ONE shared instantiation of SizeDefN at the real checker  thmT .
module SzDefN = T4.GLCodePDefN.SizeDefN thmT
open SzDefN public using ( CmcodebDefN ; boundDefN )

------------------------------------------------------------------------
-- The thresholds.

LstarN : Term
LstarN = ap1 exp2 (natCode (fst boundDefN))

NthrN : Term
NthrN = predNof (fst boundDefN)        -- = exp3 (s (exp2 (natCode (fst boundDefN)))) = 3^(L*+1)

------------------------------------------------------------------------
-- The bridge to the REAL diagonal ( SizeDefN's tc-rebuild at thmT IS
-- KdefDiagN.gLcodeDefN definitionally ), kept abstract.

abstract
  bridgeRealN :
    Eq (T4.KdefDiagN.gLcodeDefN NthrN)
       (plug CmcodebDefN (H'N (fst boundDefN)))
  bridgeRealN = SzDefN.bridgeDefN

------------------------------------------------------------------------
-- The honest size bound on the real diagonal.

abstract
  transportNodesN :
    (X Y : Term) (c : Nat) -> Eq X Y -> NatLe (nodes X) c -> NatLe (nodes Y) c
  transportNodesN X Y c eq le = eqSubst (\ m -> NatLe m c) (eqCong nodes eq) le

domBDefN : NatLe (nodes (T4.KdefDiagN.gLcodeDefN NthrN)) (powN (fst boundDefN))
domBDefN =
  transportNodesN (plug CmcodebDefN (H'N (fst boundDefN)))
                  (T4.KdefDiagN.gLcodeDefN NthrN)
                  (powN (fst boundDefN))
                  (eqSym bridgeRealN) (snd boundDefN)
