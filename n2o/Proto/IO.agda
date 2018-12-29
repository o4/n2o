module n2o.Proto.IO where 

open import Agda.Primitive using ( Level )
open import Agda.Builtin.String public using ( String )
open import Agda.Builtin.Unit public 
open import Agda.Builtin.IO public 

variable 
    ℓ  : Level 
    ℓ₁ : Level
    ℓ₂ : Level
  
{-

{-# FOREIGN GHC
  import qualified Data.Text.IO as Text
  import qualified System.IO as IO
#-}

postulate FileHandle : Set
{-# COMPILE GHC FileHandle = type System.IO.Handle #-}

postulate
  stdout    : FileHandle
  hPutStrLn : FileHandle → String → IO ⊤
{-# COMPILE GHC stdout    = IO.stdout #-}
{-# COMPILE GHC hPutStrLn = Text.hPutStrLn #-}

-}

infixl 1 _>>=_ _>>_

postulate 
    return : ∀ {a : Set ℓ₁}              →    a              → IO a
    _>>=_  : ∀ {a : Set ℓ₁} {b : Set ℓ₂} → IO a → (a → IO b) → IO b
    _>>_   : ∀ {a : Set ℓ₁} {b : Set ℓ₂} → IO a →      IO b  → IO b
    
{-# COMPILE GHC return = \ _ _         -> return :: a    ->                IO a #-}
{-# COMPILE GHC _>>=_  = \ _ _ _ _     -> (>>=)  :: IO a -> (a -> IO b) -> IO b #-}
{-# COMPILE GHC _>>_   = \ _ _ _ _     -> (>>)   :: IO a ->       IO b  -> IO b #-}
{-# COMPILE UHC return = \ _ _ x       -> UHC.Agda.Builtins.primReturn x        #-}
{-# COMPILE UHC _>>=_  = \ _ _ _ _ x y -> UHC.Agda.Builtins.primBind x y        #-}

postulate 
    getLine  : IO String 
    putStrLn : String → IO ⊤

{-# COMPILE GHC putStrLn = \ s -> putStrLn (Data.Text.unpack s) #-}
