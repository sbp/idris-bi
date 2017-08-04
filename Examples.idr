import Bin

main : IO ()
main = do printLn (show (the Integer (cast (binMod 1501857320 86400))))
