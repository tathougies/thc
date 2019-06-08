let tokens = scanl (lexHaskell . snd) (Nothing, ThcLexStateWhitespace) s
    finalState = snd (last tokens)
    (lastToken, finalState') = finalToken finalState
    tokens' = catMaybes (map fst tokens ++ [ lastToken ])
in (tokens', finalState')
