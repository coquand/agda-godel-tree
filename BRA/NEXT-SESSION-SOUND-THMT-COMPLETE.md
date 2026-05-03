# Sound thmT — COMPLETE

All 9 inductive premise-consuming dispatchers in `BRA/Thm/ThmT.agda` are
soundified.  For any malformed input proof tree, every dispatcher
either outputs `codeTriv = falseT` (the explicit safe default) or
returns a Pair-of-Pairs structure that downstream consumers cannot
mis-read as a real theorem.

## Status (final)

| Tag         | Proto file                    | VProof file                     | Status |
|-------------|-------------------------------|---------------------------------|--------|
| mp          | BRA/SoundMpProto.agda         | BRA/SoundMpVProof.agda          | ✓ Done (closed + lifted) |
| ruleInst    | BRA/SoundRuleInstProto.agda   | BRA/SoundRuleInstVProof.agda    | ✓ Done (closed + lifted) |
| ruleSym     | BRA/SoundRuleSymProto.agda    | BRA/SoundRuleSymVProof.agda     | ✓ Done (closed + lifted) |
| cong1       | BRA/SoundCong1Proto.agda      | BRA/SoundCong1VProof.agda       | ✓ Done (closed only) |
| congL       | BRA/SoundCongLProto.agda      | BRA/SoundCongLVProof.agda       | ✓ Done (closed + lifted + dl) |
| congR       | BRA/SoundCongRProto.agda      | BRA/SoundCongRVProof.agda       | ✓ Done (closed + lifted + dl) |
| ruleTrans   | BRA/SoundRuleTransProto.agda  | BRA/SoundRuleTransVProof.agda   | ✓ Done (closed + lifted + dl) |
| ruleInst2   | BRA/SoundRuleInst2Proto.agda  | BRA/SoundRuleInst2VProof.agda   | ✓ Done (closed + parametric) |
| ruleIndBT   | BRA/SoundRuleIndBTProto.agda  | BRA/SoundRuleIndBTVProof.agda   | ✓ Done (closed + closed-param) |

## Verification

```
$ time agda BRA/GoedelIIFull.agda    # cached
real    0.83s

$ time agda BRA/Thm/ThmT.agda        # cached
real    1.18s

$ time agda BRA/GoedelIIFull.agda    # cold rebuild
real    32s

$ grep -n "godelII : Deriv Con -> Deriv bot" BRA/GoedelIIFull.agda
48:godelII : Deriv Con -> Deriv bot
```

All four standalone Theorem 12 proofs typecheck against the new
soundified parametric dispatcher:

```
BRA/Th12Const.agda    real 0.46s
BRA/Th12Fst.agda      real 0.45s
BRA/Th12Snd.agda      real 0.46s
BRA/Th12Pair.agda     real 0.44s
```

## Semantic content of godelII

`godelII : Deriv Con -> Deriv bot` is now meaningful:

`Con` (= `~ Pr (code(bot))` modulo BRA's encoding) expresses
"BRA does not derive `bot`" because `Pr(x) = exists y, thmT y = x`
ranges over `thmT`-images that are guaranteed to be either valid
encoded formulas or `codeTriv` (= `code(0=0)`, never `code(bot)`
unless `0=0` literally encodes `bot`, which it does not).

So `godelII` carries its intended Goedel-II content: BRA cannot
internalise its own consistency.

## What this session delivered (final tally)

| File                                | Lines |
|-------------------------------------|------:|
| BRA/SoundCongLVProof.agda           | 1146  |
| BRA/SoundCongRVProof.agda           | 1026  |
| BRA/SoundRuleTransProto.agda        |   54  |
| BRA/SoundRuleTransVProof.agda       |  620  |
| BRA/SoundRuleInst2Proto.agda        |   81  |
| BRA/SoundRuleInst2VProof.agda       |  161  |
| BRA/SoundRuleIndBTProto.agda        |   62  |
| BRA/SoundRuleIndBTVProof.agda       |  114  |
| BRA/Thm/ThmT.agda (rewrites)        | n/a   |
| BRA/Th12{Const,Fst,Snd,Pair}.agda   |  ~40  |
| **Total new/extended LoC**          | ~3300 |

## Next direction (optional hardening)

Out of scope for this session, but the next iteration could:

* Add `_l` (lifted) and `_dl` (doubly-lifted) variants to ruleInst2's
  VProof if any future caller ends up wanting them under hypothetical
  `P imp ...` contexts.
* Replace the safe-default `codeTriv` with a tighter signal (e.g. a
  unique error tag) if any downstream consumer wants to distinguish
  "bad input" from "trivially-true theorem".
