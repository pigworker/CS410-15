module McK-B where

open import CS410-Prelude
open import CS410-Nat
open import CS410-Vec

data Bit : Set where O I : Bit

exp2 : Nat -> Nat
exp2 zero    = 1
exp2 (suc n) = exp2 n +N exp2 n

WordNZ : Nat -> Set
data Word (n : Nat) : Set where
  O : Word n
  [_]  : WordNZ n -> Word n
WordNZ zero    = One
WordNZ (suc n) = (WordNZ n * Word n) + WordNZ n

_!_ : {n : Nat} -> Word n -> Word n -> Word (suc n)
O  ! O   = O
O  ! [ x ]  = [ inr x ]
[ x ] ! y      = [ inl (x , y) ]

_!+_ : {n : Nat} -> Word n -> WordNZ n -> WordNZ (suc n)
O  !+ y  = inr y
[ x ] !+ y  = inl (x , [ y ])

iNZ : (n : Nat) -> WordNZ n
iNZ zero = <>
iNZ (suc n) = inr (iNZ n)
i : {n : Nat} -> Word n
i {n} = [ iNZ n ] where

data WViewable : {n : Nat} -> Word n -> Set where
  O0 : WViewable {zero} O
  I0  : WViewable {zero} i
  _!!_  : {n : Nat}(x y : Word n) -> WViewable (x ! y)

wView : {n : Nat}(x : Word n) -> WViewable x
wView {zero} O    = O0
wView {zero} [ <> ]  = I0
wView {suc n} O   = O !! O
wView {suc n} [ inl (x , y) ] = [ x ] !! y
wView {suc n} [ inr      y  ] = O !! [ y ]

expand : {n : Nat} -> Word n -> Vec Bit (exp2 n)
expand x with wView x
expand .O      | O0   = O :: []
expand .([ <> ])  | I0    = I :: []
expand .(x ! y)   | x !! y  = expand x +V expand y

inc : {n : Nat}(x : Word n) -> One + WordNZ n
inc x with wView x
inc .O     | O0   = inr (iNZ zero)
inc .([ <> ]) | I0    = inl <>
inc .(x ! y)  | x !! y  with inc y
inc .(x ! y)  | x !! y  | inr y' = inr (x !+ y')
inc .(x ! y)  | x !! y  | inl <> with inc x
inc .(x ! y)  | x !! y  | inl <> | inr x'  = inr (inl (x' , O))
inc .(x ! y)  | x !! y  | inl <> | inl <>  = inl <>

incm : {n : Nat}(x : Word n) -> Word n
incm x with inc x
incm x | inl <> = O
incm x | inr x' = [ x' ]

fiveW2 : Word 2
fiveW2 = incm (incm (incm (incm (incm O))))

adc : {n : Nat} -> Word n -> Word n -> Bit -> Bit * Word n
adc x y c with wView x | wView y
adc .O .O O | O0 | O0 = O , O
adc .O .O I | O0 | O0 = O , i
adc .O .i O | O0 | I0 = O , i
adc .O .i I | O0 | I0 = I , O
adc .i .O O | I0 | O0 = O , i
adc .i .O I | I0 | O0 = I , O
adc .i .i O | I0 | I0 = I , O
adc .i .i I | I0 | I0 = I , i
adc .(xh ! xl) .(yh ! yl) c | xh !! xl | yh !! yl with adc xl yl c
... | cl , zl with adc xh yh cl
... | ch , zh = ch , zh ! zl
