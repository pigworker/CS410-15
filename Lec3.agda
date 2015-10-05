module Lec3 where

open import CS410-Prelude

not : Two -> Two
not tt = ff
not ff = tt

data TwoTestable (b : Two) : (x : Two) -> Set where
  same : TwoTestable b b
  diff : TwoTestable b (not b)

twoTest : (b x : Two) -> TwoTestable b x
twoTest tt tt = same
twoTest tt ff = diff
twoTest ff tt = diff
twoTest ff ff = same

twoTest' : (b x : Two) -> TwoTestable b x
twoTest' = caseTwo (caseTwo same diff) (caseTwo diff same)

xor : Two -> Two -> Two
xor b x with twoTest b x
xor b .b       | same = ff
xor b .(not b) | diff = tt

xorHelp : (b x : Two) -> TwoTestable b x -> Two
xorHelp b .b       same = ff
xorHelp b .(not b) diff = tt

xor' : Two -> Two -> Two
xor' b x = xorHelp b x (twoTest b x)
