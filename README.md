# Port of a subset of ZArith from Coq to Idris

Using `Nat` for arithmetic on large numbers in Idris causes significant performance degradation when type checking, compiling, evaluating, and executing code. Consider the example of taking the remainder of dividing the current unixtime by the number of seconds in a day:

```haskell
main : IO ()
main = do printLn (show (modNatNZ 1501857320 (S 86399) SIsNotZ))
```

This file takes so long to type check or to compile that the duration would have to be extrapolated from smaller examples. Instead, we can use `%freeze` after lifting the slow terms to the top level:

```haskell
n1501857320 : Nat
n1501857320 = 1501857320

n86399 : Nat
n86399 = 86399

%freeze n1501857320
%freeze n86399

main : IO ()
main = do printLn (show (modNatNZ n1501857320 (S n86399) SIsNotZ))
```

This file is reasonably fast to type check and to compile, but now the runtime takes so long to execute that once again the actual duration could only be extrapolated from smaller examples. The code is also extremely ugly.

Instead, it would be useful if Idris provided an implementation of **[ZArith](https://coq.inria.fr/library/Coq.ZArith.ZArith.html)** from Coq. An element of ZArith is already mentioned several times in the Idris literature:

* [In the examples directory](https://github.com/idris-lang/idris-tutorial/blob/master/examples/binary.idr)
* [Talking about erasure of Nat in binary numbers](https://github.com/idris-lang/Idris-dev/blob/master/docs/reference/erasure.rst#binary-numbers)
* [In an old tutorial](https://github.com/edwinb/Idris-old/blob/master/web/tutorial/provisional.idr)

There's also a different element of it in [Data.ZZ](https://github.com/idris-lang/Idris-dev/blob/master/libs/contrib/Data/ZZ.idr).

This is somewhat related to Issue [#3516](https://github.com/idris-lang/Idris-dev/issues/3516), *The cost of computing Nat equality proofs at type check time*, but doesn't solve that issue directly since here a new type is proposed to sidestep the issue altogether. Indeed, @edwinb [suggested](https://github.com/idris-lang/Idris-dev/issues/3516#issuecomment-263139429) an orthogonal solution there:

> You know, I think I'm going to take back that comment about "little point in hard coding things for Nat" because realistically that's the biggest problem we're going to encounter at compile time, and given that we say that Nat is for unbounded unsigned things, we probably ought to be a bit cleverer about it.

## Proof of concept

To see what performance gains may be made, this is a small but usable port of a subset of ZArith to Idris, called `Bi`.

The code is based on [Coq.Numbers.BinNums](https://coq.inria.fr/library/Coq.Numbers.BinNums.html), [Coq.PArith.BinPosDef](https://coq.inria.fr/library/Coq.PArith.BinPosDef.html), [Coq.NArith.BinNatDef](https://coq.inria.fr/library/Coq.NArith.BinNatDef.html), and [Coq.ZArith.Zdiv](https://coq.inria.fr/library/Coq.ZArith.Zdiv.html). The [tutorial](https://www.cs.princeton.edu/~appel/vfa/Trie.html) in VFA explains why such arithmetic is necessary and how it is constructed for anybody missing the background. The main types are as follows:

```haskell
data Bip = U | O Bip | I Bip
data Bin = BinZ | BinP Bip
data Biz = BizZ | BizP Bip | BizM Bip
```

These correspond to the Coq types `positive` for PArith, `N` for NArith, and `Z` for ZArith. We can now rewrite the poorly-performing example above as:

```haskell
import Bi

main : IO ()
main = do printLn (show (the Integer (cast (binMod 1501857320 86400))))
```

Which compiles in reasonable time:

```
$ time idris Performance.idr -o Performance
idris Performance.idr -o Performance
   5.09s user 0.48s system 108% cpu 5.147 total
```

And runs with blazing speed:

```
$ time ./Performance
"52520"
./Performance
   0.00s user 0.00s system 40% cpu 0.013 total
```

None of the Coq proofs have been ported, so this port may contain bugs. As a proof of concept, however, it shows that if Idris used ZArith like Coq then there would be significant performance gains at all stages of code development involving large numbers.
