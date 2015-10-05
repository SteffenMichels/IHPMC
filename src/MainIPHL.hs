module MainIPHL where
import BasicTypes
import Exception
import Text.Printf (printf)
import Control.Monad.Exception.Synchronous -- TODO: remove, should be included by Exception

main = do
    result <- runExceptionalT exeMain'
    case result of
        Exception e -> putStrLn (printf "\nError: %s" e)
        Success x   -> print x
    where
        exeMain' = do
            doIO $ putStrLn "hello"
