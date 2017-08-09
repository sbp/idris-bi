import Data.Bin

main : IO ()
main = printLn (the Integer (cast (binMod 1501857320 86400)))
