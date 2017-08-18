# Idris Binary Integer Arithmetic

This work-in-progress package implements [structurally inductive](https://en.wikipedia.org/wiki/Structural_induction) [arbitrary-precision](https://en.wikipedia.org/wiki/Arbitrary-precision_arithmetic) binary integer arithmetic in [Idris](https://www.idris-lang.org/), a [dependently typed](https://en.wikipedia.org/wiki/Dependent_type) [pure functional programming](https://en.wikipedia.org/wiki/Purely_functional_programming) language.

Idris already contains types for [unary integer arithmetic](https://www.idris-lang.org/docs/1.0/prelude_doc/docs/Prelude.Nat.html) and [fixed-precision binary integer arithmetic](https://www.idris-lang.org/docs/1.0/base_doc/docs/Data.Bits.html), but it does not contain types for arbitrary-precision binary integer arithmetic. This package fills that gap. Once completed, the authors hope for this package to be incorporated into the Idris standard library per feature request [#3976](https://github.com/idris-lang/Idris-dev/issues/3976).

This package implements arithmetics based on [PArith](https://coq.inria.fr/library/Coq.PArith.PArith.html), [NArith](https://coq.inria.fr/library/Coq.NArith.NArith.html), and [ZArith](https://coq.inria.fr/library/Coq.ZArith.ZArith.html) from the Coq programming language. In Coq the [primary types](https://coq.inria.fr/library/Coq.Numbers.BinNums.html) of these arithmetics are called `positive`, `N`, and `Z` respectively, but in this package those types are renamed [Bip](https://github.com/sbp/idris-bi/blob/master/src/Data/Bip.idr), [Bin](https://github.com/sbp/idris-bi/blob/master/src/Data/Bin.idr), and [Biz](https://github.com/sbp/idris-bi/blob/master/src/Data/Biz.idr) for consistency.

Because Idris is dependently typed, it is possible to assert arbitrary properties about the code that the type checker will verify at compile time. This means that it is possible to prove characteristics of code, equivalent to running tests for all possible inputs (even an infinite number) simultaneously. We are porting dozens of proofs specifying the behaviour of the three arithmetics from Coq, making it possible to rely on those proven specifications when using the code.

## Motivation

Using `Nat`, the unary arithmetic type, for arithmetic on large numbers in Idris causes significant performance degradation when type checking, compiling, evaluating, and executing code. Consider the example of taking the remainder of dividing the current unixtime by the number of seconds in a day:

```idris
main : IO ()
main = printLn (modNatNZ 1501857320 (S 86399) SIsNotZ)
```

This file takes so long to type check or to compile that the duration would have to be extrapolated from smaller examples. Instead, we can use `%freeze` after lifting the slow terms to the top level:

```idris
n1501857320 : Nat
n1501857320 = 1501857320

n86399 : Nat
n86399 = 86399

%freeze n1501857320
%freeze n86399

main : IO ()
main = printLn (modNatNZ n1501857320 (S n86399) SIsNotZ)
```

This file is reasonably fast to type check and to compile, but now the runtime takes so long to execute that once again the actual duration could only be extrapolated from smaller examples. The code is also extremely ugly.

If we use the P, N, and Z arithmetics from Coq, this code can be made to work much faster. The [tutorial in VFA](https://www.cs.princeton.edu/~appel/vfa/Trie.html) explains why these arithmetics are necessary and how they are constructed. An element of ZArith is already mentioned several times in the Idris literature:

* [In the examples directory](https://github.com/idris-lang/idris-tutorial/blob/master/examples/binary.idr)
* [Talking about erasure of Nat in binary numbers](https://github.com/idris-lang/Idris-dev/blob/master/docs/reference/erasure.rst#binary-numbers)
* [In an old tutorial](https://github.com/edwinb/Idris-old/blob/master/web/tutorial/provisional.idr)

There's also a different element of it in [Data.ZZ](https://github.com/idris-lang/Idris-dev/blob/master/libs/contrib/Data/ZZ.idr).

This is somewhat related to Issue [#3516](https://github.com/idris-lang/Idris-dev/issues/3516), *The cost of computing Nat equality proofs at type check time*, but doesn't solve that issue directly since here a new type is proposed to sidestep the issue altogether. Indeed, @edwinb  [suggested](https://github.com/idris-lang/Idris-dev/issues/3516#issuecomment-263139429) an orthogonal solution there:

> You know, I think I'm going to take back that comment about "little point in
> hard coding things for Nat" because realistically that's the biggest problem
> we're going to encounter at compile time, and given that we say that Nat is
> for unbounded unsigned things, we probably ought to be a bit cleverer about
> it.

## Overview

The main types are as follows:

```idris
data Bip = U | O Bip | I Bip
data Bin = BinO | BinP Bip
data Biz = BizO | BizP Bip | BizM Bip
```

We can now rewrite the poorly-performing example above as:

```idris
import Bin

main : IO ()
main = printLn (the Integer (cast (binMod 1501857320 86400)))
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

## Contributors and licensing

See [contributors](https://github.com/sbp/idris-bi/graphs/contributors) for the definitive list of contributors. Since the intention is for this package to be incorporated into Idris, we intend also to use the same license as Idris itself.
