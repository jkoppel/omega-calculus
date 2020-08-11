{-# LANGUAGE DerivingVia, FlexibleInstances, GeneralizedNewtypeDeriving, OverloadedStrings,
    ScopedTypeVariables, StandaloneDeriving, TypeOperators, TypeSynonymInstances #-}

module Language.Omega (
    Var(..)
  , ΩType(..)
  , BinOp(..)
  , ΩTerm(..)

  , Closure(..)
  , Env
  , emptyEnv

  , Domain
  , BoundedInt(..)
  , MonadΩ(..)
  , runExhaustiveSearch
  , eval

  , (.>)
  , (.>=)
  , (.==)
  , (.<=)
  , (.<)
  , (.=)
  , inn
  , lett
  , thenn
  , elsee
  , iff
  , rand
  ) where

import Control.Monad ( when )
import Control.Monad.State ( MonadState(..), gets, modify, StateT, evalStateT )
import Control.Monad.Trans ( lift )

import           Data.Map  ( Map )
import qualified Data.Map as Map
import Data.String ( IsString(..) )
import Data.Text ( Text )

import Data.Text.Prettyprint.Doc ( Doc, Pretty(..), (<+>), align, parens, encloseSep, group, nest, indent, sep, hang, cat )

import Debug.Trace ( traceM )

--------------------------------------------------------------
------------------------ Syntax ------------------------------
--------------------------------------------------------------

newtype Var = Var Text
  deriving (Eq, Ord)
  deriving (Show) via Text

data ΩType = ΩTInt
           | ΩTBool
           | ΩTReal
           | (:->:) ΩType ΩType
           | Ω
  deriving (Eq, Ord, Show)
  
data Lit = LitInt Integer
         | LitBool Bool
         | LitReal Double
         | LitBottom
  deriving (Eq, Ord, Show)

data BinOp = Plus | Minus | Times | GreaterThan | GTE | Equal | LTE | LessThan
  deriving (Eq, Ord, Show)

data ΩTerm = ΩLit Lit
           | ΩClosure Closure --- Can occur inside terms at runtime
           | ΩVar Var
           | Ωλ Var ΩType ΩTerm
           | ΩIf ΩTerm ΩTerm ΩTerm
           | ΩBinOp BinOp ΩTerm ΩTerm
           | ΩApp ΩTerm ΩTerm
           | ΩLet Var ΩTerm ΩTerm
           | ΩCond ΩTerm ΩTerm
           | ΩDo ΩTerm Var ΩTerm
           | ΩRand ΩTerm
  deriving (Eq, Ord, Show)

--------------------------------------------------------------
------------------- Runtime environments ---------------------
--------------------------------------------------------------

data Closure = Clo Env ΩTerm
  deriving ( Eq, Ord, Show )

type Env = Map Var Closure

emptyEnv :: Env
emptyEnv = Map.empty

--------------------------------------------------------------
------------------------ Evaluation --------------------------
--------------------------------------------------------------


------------- Runtime values ---------------

data ΩVal = ValLit Lit
          | ValClosure Closure
 deriving (Eq, Ord, Show)


valToTerm :: ΩVal -> ΩTerm
valToTerm (ValLit l)     = ΩLit l
valToTerm (ValClosure c) = ΩClosure c

------------------ Monad --------------------

class Domain d where
  getAll :: d -> [ΩTerm]

data BoundedInt = BoundedInt Integer Integer -- low, hi (inclusive)

instance Domain BoundedInt where
  getAll (BoundedInt low hi) = map (ΩLit . LitInt) [low..hi]

class (MonadFail m) => MonadΩ m where
  gensym :: Text -> m Var

  getDebugDepth :: m Int
  setDebugDepth :: Int -> m ()

  getRandom :: m ΩTerm
  reject :: m ()


data InterpreterState dom = InterpreterState { nextId :: Int
                                             , debugDepth :: Int
                                             , domain :: dom
                                             }

startState :: dom -> InterpreterState dom
startState dom = InterpreterState { nextId = 0, debugDepth = 0, domain = dom}

newtype ExhaustiveSearch dom a = ExhaustiveSearch { unExhaustiveSearch :: StateT (InterpreterState dom) [] a}
  deriving (Functor, Applicative, Monad, MonadState (InterpreterState dom))


instance MonadFail (ExhaustiveSearch dom) where
  fail = error

instance (Domain dom) => MonadΩ (ExhaustiveSearch dom) where
  gensym prefix = do
    idx <- nextId <$> get
    modify (\s -> s { nextId = idx + 1})
    return $ Var $ prefix <> (fromString $ show idx)

  getDebugDepth = gets debugDepth
  setDebugDepth d = modify (\s -> s {debugDepth = d})

  getRandom = gets domain >>= \dom -> ExhaustiveSearch $ lift $ getAll dom
  reject = ExhaustiveSearch $ lift []

runExhaustiveSearch :: ExhaustiveSearch dom a -> dom -> [a]
runExhaustiveSearch es dom = evalStateT (unExhaustiveSearch es) (startState dom)

------------------ Helpers --------------------

runBinOp :: (MonadΩ m) => BinOp -> Lit -> Lit -> m Lit
runBinOp Equal  (LitBool a) (LitBool b) = pure $ LitBool (a == b)

runBinOp Plus        (LitInt a) (LitInt b) = pure $ LitInt (a+b)
runBinOp Minus       (LitInt a) (LitInt b) = pure $ LitInt (a-b)
runBinOp Times       (LitInt a) (LitInt b) = pure $ LitInt (a*b)
runBinOp GreaterThan (LitInt a) (LitInt b) = pure $ LitBool (a > b)
runBinOp GTE         (LitInt a) (LitInt b) = pure $ LitBool (a >= b)
runBinOp Equal       (LitInt a) (LitInt b) = pure $ LitBool (a ==  b)
runBinOp LTE         (LitInt a) (LitInt b) = pure $ LitBool (a <= b)
runBinOp LessThan    (LitInt a) (LitInt b) = pure $ LitBool (a < b)

runBinOp Plus        (LitReal a) (LitReal b) = pure $ LitReal (a+b)
runBinOp Minus       (LitReal a) (LitReal b) = pure $ LitReal (a-b)
runBinOp Times       (LitReal a) (LitReal b) = pure $ LitReal (a*b)
runBinOp GreaterThan (LitReal a) (LitReal b) = pure $ LitBool (a > b)
runBinOp GTE         (LitReal a) (LitReal b) = pure $ LitBool (a >= b)
runBinOp Equal       (LitReal a) (LitReal b) = pure $ LitBool (a == b)
runBinOp LTE         (LitReal a) (LitReal b) = pure $ LitBool (a <= b)
runBinOp LessThan    (LitReal a) (LitReal b) = pure $ LitBool (a < b)

runBinOp _ LitBottom _         = pure LitBottom
runBinOp _ _         LitBottom = pure LitBottom

runBinOp op a b = fail ("Malformed binop: " ++ show a ++ " " ++ show op ++ " " ++ show b)

-- | subst t v x == t[v/x]
subst :: ΩTerm -> ΩTerm -> Var -> ΩTerm
subst (ΩLit l)          v x = ΩLit l
subst (ΩVar y)          v x = if y == x then v else ΩVar y
subst (Ωλ y typ e)      v x = Ωλ y typ (if y == x then e else subst e v x)
subst (ΩIf t1 t2 t3)    v x = ΩIf (subst t1 v x) (subst t2 v x) (subst t3 v x)
subst (ΩBinOp op t1 t2) v x = ΩBinOp op (subst t1 v x) (subst t2 v x)
subst (ΩApp t1 t2)      v x = ΩApp (subst t1 v x) (subst t2 v x)
subst (ΩLet y t1 t2)    v x = ΩLet y (subst t1 v x) (if y == x then t2 else subst t2 v x)
subst (ΩCond t1 t2)     v x = ΩCond (subst t1 v x) (subst t2 v x)
subst (ΩDo t1 y t2)     v x = ΩDo (if y == x then t1 else subst t1 v x) y (subst t2 v x) -- TODO: double-check this line
subst (ΩRand t)         v x = ΩRand (subst t v x)


---------- Core semantics (as in paper) -----------


retroUpd :: Env -> Var -> Closure -> Env
retroUpd gamma x c = Map.adjust (const c) x $
                       Map.map (\(Clo gamma' t')
                                    -> Clo (retroUpd gamma' x c) t')
                               gamma


lookupEnv :: (MonadΩ m) => Env -> Var -> m ΩVal
lookupEnv gamma v = case Map.lookup v gamma of
                      Just (Clo gamma' e) -> eval gamma' e
                      Nothing             -> fail ("Variable " ++ show v ++ " not in env")


eval' :: (MonadΩ m) => Env -> ΩTerm -> m ΩVal
eval' _ (ΩLit l) = pure $ ValLit l
eval' _ (ΩClosure c) = pure $ ValClosure c
eval' gamma t@(Ωλ _ _ _) = pure $ ValClosure (Clo gamma t)

eval' gamma (ΩBinOp op t1 t2) = do
  ValLit l1 <- eval gamma t1
  ValLit l2 <- eval gamma t2
  ValLit <$> runBinOp op l1 l2
eval' gamma (ΩIf t1 t2 t3) = do b <- eval gamma t1
                                case b of
                                  ValLit (LitBool True)  -> eval gamma t2
                                  ValLit (LitBool False) -> eval gamma t3
                                  ValLit LitBottom       -> pure $ ValLit LitBottom

                                  _ -> fail ("Conditional "
                                              ++ show t1
                                              ++ " must evaluate to bool or bottom")

eval' gamma (ΩVar v) = lookupEnv gamma v
eval' gamma (ΩApp t1 t2) = do
  t1Evalled <- eval gamma t1
  case t1Evalled of
    ValLit LitBottom -> pure $ ValLit LitBottom

    (ValClosure (Clo gamma' (Ωλ x _ t3))) -> do
      v1 <- eval gamma t2
      eval gamma' (subst t3 (valToTerm v1) x)

    _ -> fail ("Should have evaluated to a function closure, but did not: " ++ show t1)

eval' gamma (ΩLet x t1 t2) = if Map.member x gamma then
                               fail ("Cannot rebind var " ++ show x)
                             else
                               let gamma' = Map.insert x (Clo gamma t1) gamma in
                               eval gamma' t2
eval' gamma (ΩDo t1 x t2) = let gamma' = retroUpd gamma x (Clo gamma t2) in
                            eval gamma' t1
eval' gamma (ΩCond t1 t2) = do v <- gensym "ω"
                               eval gamma $ Ωλ v Ω $
                                              iff (ΩApp t2 (ΩVar v)) thenn
                                                (ΩApp t1 (ΩVar v))
                                              elsee
                                                (ΩLit LitBottom)

eval' gamma (ΩRand t) = do
  ω <- getRandom
  v <- eval gamma (ΩApp t ω)
  when (v == ValLit LitBottom) $ reject
  pure v


eval :: (MonadΩ m) => Env -> ΩTerm -> m ΩVal
eval gamma t = do
  depth <- getDebugDepth
  traceM $ show $ indent (depth * 2) $ "Evaluating: " <+> align (pretty t)

  setDebugDepth (depth + 1)
  res <- eval' gamma t
  setDebugDepth depth

  traceM $ show $ indent (depth * 2) $ "Result: " <+> align (pretty res)

  return res

--------------------------------------------------------------
---------------------- Embedded DSL sugar --------------------
--------------------------------------------------------------


deriving via Text instance (IsString Var)

instance IsString ΩTerm where
  fromString s = ΩVar (fromString s)

(.>) :: ΩTerm -> ΩTerm -> ΩTerm
a .> b = ΩBinOp GreaterThan a b

(.>=) :: ΩTerm -> ΩTerm -> ΩTerm
a .>= b = ΩBinOp GTE a b

(.==) :: ΩTerm -> ΩTerm -> ΩTerm
a .== b = ΩBinOp Equal a b

(.<=) :: ΩTerm -> ΩTerm -> ΩTerm
a .<= b = ΩBinOp LTE a b

(.<) :: ΩTerm -> ΩTerm -> ΩTerm
a .< b = ΩBinOp LessThan a b

instance Num ΩTerm where
  a + b = ΩBinOp Plus  a b
  a - b = ΩBinOp Minus a b
  a * b = ΩBinOp Times a b

  negate (ΩLit (LitInt n)) = ΩLit (LitInt $ negate n)

  fromInteger n = ΩLit (LitInt n)

instance Fractional ΩTerm where
  fromRational r = ΩLit (LitReal $ fromRational r)


-- | With much abuse of notation, allows writing
--   `lett "x" (=:) (a+b) inn x + 1`

data AssnToken = AssnToken
data InnToken = InnToken

(.=) :: AssnToken
(.=) = AssnToken

inn :: InnToken
inn = InnToken

lett :: Var -> AssnToken -> ΩTerm -> InnToken -> ΩTerm -> ΩTerm
lett v _ t1 _ t2 = ΩLet v t1 t2


-- | With much abuse of notation, allows writing
--   `iff t1 thenn t2 elsee t3`

data ThennToken = ThennToken
data ElseeToken = ElseeToken

thenn :: ThennToken
thenn = ThennToken

elsee :: ElseeToken
elsee = ElseeToken

iff :: ΩTerm -> ThennToken -> ΩTerm -> ElseeToken -> ΩTerm -> ΩTerm
iff t1 _ t2 _ t3 = ΩIf t1 t2 t3

rand :: ΩTerm -> ΩTerm
rand = ΩRand

--------------------------------------------------------------
---------------------- Pretty-printing -----------------------
--------------------------------------------------------------

-------- Terms -------

deriving via Text instance (Pretty Var)

instance Pretty ΩType where
  pretty ΩTInt      = "Int"
  pretty ΩTBool     = "Bool"
  pretty ΩTReal     = "Real"
  pretty (a :->: b) = pretty a <+> "->" <+> pretty b
  pretty Ω          = "Ω"

instance Pretty BinOp where
  pretty Plus        = "+"
  pretty Minus       = "-"
  pretty Times       = "*"
  pretty GreaterThan = ">"
  pretty GTE         = ">="
  pretty Equal       = "="
  pretty LTE         = "<="
  pretty LessThan    = "<"
  
instance Pretty Lit where
  pretty (LitInt    t)     = pretty t
  pretty (LitBool   True)  = "true"
  pretty (LitBool   False) = "false"
  pretty (LitReal   t)     = pretty t
  pretty LitBottom         = "⊥"

instance Pretty ΩTerm where
  pretty (ΩLit l)          = pretty l
  pretty (ΩVar v)          = pretty v
  pretty (Ωλ v typ term)   = sep [ "λ" <> pretty v <+> ":" <+> pretty typ <> "."
                                 , nest 4 $ pretty term
                                 ]
  pretty (ΩIf t1 t2 t3)    = sep [ "if" <+> pretty t1 <+> "then"
                                 , nest 4 $ pretty t2
                                 , "else"
                                 , nest 4 $ pretty t3
                                 ]
  pretty (ΩBinOp op t1 t2) = pretty t1 <+> pretty op <+> pretty t2
  pretty (ΩApp t1 t2)      = pretty t1 <> "(" <> pretty t2 <> ")"
  pretty (ΩLet v t1 t2)    = group $ nest 2 $ sep [ "let" <+> pretty v <+> "=" <+> hang 2 (pretty t1)
                                                  , nest 2 $ sep ["in", pretty t2]]
  pretty (ΩCond t1 t2)     = sep [ pretty t1
                                 , nest 2 ("|" <+> pretty t2)
                                 ]
  pretty (ΩDo t1 v t2)     = sep [ pretty t1
                                 , nest 2 $ "| do(" <+> pretty v <+> "→"
                                 , nest 4 $ pretty t2 <> ")"
                                 ]
  pretty (ΩRand t)         = "rand(" <> pretty t <> ")"


-------- Values -------

instance Pretty Closure where
  pretty (Clo gamma t) = "clo" <> align (parens $ cat [pretty gamma <> ",", pretty t])

instance Pretty Env where
  pretty gamma = encloseSep "{" "}" ", " (map prettyBinding (Map.toList gamma))
    where
      prettyBinding (v, clo) = pretty v <> "→" <> pretty clo

instance Pretty ΩVal where
  pretty (ValLit l)      = pretty l
  pretty (ValClosure c) = pretty c
