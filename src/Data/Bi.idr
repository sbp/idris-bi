module Data.Bi

%default total

-- Binary P, Positive

||| Positive binary number, little endian
public export
data Bip =
  ||| One, acting like a most-significant one digit.
  ||| (Mnemonic: U for Unit)
  U |
  ||| Twice the inner term, acting like a zero digit.
  ||| (Mnemonic: O for digit 0)
  O Bip |
  ||| Twice the inner term plus one, acting like a non-most-sig one digit.
  ||| (Mnemonic: I for digit 1)
  I Bip

%name Bip a,b,c,d,e

-- Binary N, Natural

||| Natural binary number
public export
data Bin =
  ||| Zero
  BinO |
  ||| Plus signed number
  BinP Bip

%name Bin k,j,l,m,n

-- Binary Z, Integer

||| Binary integer
public export
data Biz =
  ||| Zero
  BizO |
  ||| Plus signed number
  BizP Bip |
  ||| Minus signed number
  BizM Bip

%name Biz p,q,r,s,t
