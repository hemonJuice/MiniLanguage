--IMPORTANT!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
--I MSAF this project :)
--I change eval::T -> T to eval::(T,m) -> (T,m) according to piazza question@387.

module Q1
    (


    sub,
    isNF,
    ssos,
    eval,
    run,
    typeCheck,
    freeVars,
    relabel,

    t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,

    ) where


import Data.List
import Debug.Trace

data T = App T T
       | If T T T 
       | Succ T
       | Pred T
       | IsZero T
       | Val V
       | Let Label T T
       | Seq T T
       | Alloc T
       | DeRef T
       | Assign T T 
  deriving (Show, Eq)
  
data V = Tru | Fls | Z | SuccNV V | UnitV | Location Loc | Var Label | L Label Type T deriving(Show, Eq)

data Label = A | C | D | E | F | G | H | I | J | K 
    | M | O | P | Q | R | S | U | W | X | Y  
    deriving (Show, Eq)
    
data Loc = L0 | L1 | L2 | L3 | L4 | L5 | L6 | L7 | L8 | L9
    deriving (Show, Eq)

data Type = BOOL | NAT | Unit | Arrow Type Type | Ref Type deriving (Show, Eq)

type Gamma = [(Label, Type)] 

type Mu = [(Loc, V)]






freeVars :: T -> [Label] 
freeVars (Val (Var l)) = [l]
freeVars (Val (L l ty t)) = (freeVars t) \\ [l]
freeVars (App t1 t2) = (freeVars(t1)) `union` (freeVars(t2))
freeVars otherwise = []


relabel :: T -> Label -> Label -> T 
relabel (Val (Var l)) a b | l == a = (Val (Var b))
                          | otherwise = (Val (Var l))
relabel (Val (L l ty t)) a b | l == a && b `notElem` (freeVars (Val (L l ty t))) = (Val (L b ty (relabel (t) a b)))  
                             | l == a && b `elem` (freeVars (Val (L l ty t))) = (Val (L l ty t))
                             | l /= a && b == l = (Val (L l ty t))
                             | otherwise = (Val (L l ty (relabel (t) a b )))
                             
relabel (App t1 t2) a b = App (relabel t1 a b) (relabel t2 a b)




vList:: [Label]
vList = [ A, C, D, E, F, G, H, I, J, K, M, O, P, Q, R, S, U, W, X, Y] 


-----




sub :: T -> Label -> T -> T 
sub (Val Tru) x s = (Val Tru)
sub (Val Fls) x s = (Val Fls)
sub (Val (Var l)) x s | x == l = s 
                      | otherwise = (Val (Var l))
--sub (Val t) x s = case t of (Var l) | x == l -> s 
--                                    | otherwise -> (Val (Var l))
--                            otherwise -> (Val t)
sub (Val (L l ty t)) x s 
    | x == l = (Val (L l ty t))
    | x /= l && l `notElem` (freeVars s) = (Val (L l ty (sub t x s)))
    | x /= l && l `elem` (freeVars s) = (sub (relabel (Val (L l ty t)) l (head ((vList\\freeVars(s))\\freeVars(t))) ) x s)

sub (App t1 t2) x s = (App (sub t1 x s) (sub t2 x s))
sub (IsZero t) x s = IsZero (sub t x s)
sub (Val Z) x s = (Val Z)
--few more succ
sub (Seq t1 t2) x s = (Seq (sub t1 x s) (sub t2 x s))
sub (Alloc t) x s = (Alloc (sub t x s))
sub (Assign t1 t2) x s = (Assign (sub t1 x s) (sub t2 x s))
sub (Succ t) x s = (Succ (sub t x s))
sub (Pred t) x s = (Pred (sub t x s))
sub (DeRef t) x s = (DeRef (sub t x s))
sub (Val UnitV) x s = (Val UnitV)
sub (Val (Location l)) x s = (Val (Location l))




isNF :: T -> Bool 
isNF (App (Val (L l ty t1)) t2) = False 
isNF (App t1 t2) = (isNF t1) && (isNF t2)
--isNF (Lam x t) = isNF t
--isNF (Val (Location l)) = True
isNF (Alloc (Val v)) = False
isNF otherwise = True










ssos :: (T, Mu) -> (T, Mu)
ssos (Val Tru, m) = (Val Tru, m)
ssos (Val Fls, m) = (Val Fls, m)
ssos (Val Z, m) = (Val Z, m)
ssos (Val (SuccNV a), m) = (Val (SuccNV a), m)

ssos (Val a, m) = (Val a, m)

ssos ((If (Val Tru) a b), m) = (a, m)   --E-IFTRUE
ssos ((If (Val Fls) a b), m) = (b, m)   --E-IFFALSE
ssos ((If x y z), m) = (If (fst(ssos (x, m))) y z, snd(ssos (x, m)))    --E-if
ssos (Succ (Val a), m) = (Val (SuccNV a), m)   
ssos (Succ t, m) = (Succ (fst(ssos (t, m))), snd(ssos (t, m))) --E-SUCC


ssos (Pred (Val Z), m) = (Val Z, m) --E-PREDZERO
ssos (Pred (Val (SuccNV v)), m) = (Val v, m) --E-PREDSUCC
ssos (Pred t, m) = (Pred (fst(ssos (t, m))), snd(ssos (t, m))) --E-PRED



ssos (IsZero (Val Z), m) = (Val Tru, m) --E-ISZEROZERO
ssos (IsZero (Val (SuccNV v)), m) = (Val Fls, m)  --E-ISZEROSUCC
ssos (IsZero t, m) = (IsZero (fst(ssos (t, m))), snd(ssos (t, m))) --E-ISZERO


ssos ((App (Val (L l ty t12)) t2), m) = if (isNF t2) then ((sub t12 l t2), m) else ((App (Val (L l ty t12)) (fst(ssos (t2, m))) ), snd(ssos (t2, m)))   --E-APPABS
ssos ((App t1 t2), m) = if (isNF t1) then ((App t1 (fst(ssos (t2, m)))), snd(ssos (t2, m))) else ((App (fst(ssos (t1, m))) t2), snd(ssos (t1, m)))  --E-APP1/E-APP2

--let
ssos (Let l v t2, m) = if (isNF v) then ((sub t2 l v), m) else ((Let l (fst(ssos (v, m))) t2), snd(ssos (v, m)))   --E-LETV / E-LET

--sequrncing
ssos (Seq t1 t2, m) = if (t1 == Val UnitV) then (t2, m) else (Seq (fst(ssos (t1, m))) t2, snd(ssos (t1, m)))    --E-Seq/E-SeqNext




--referencing
ssos (Alloc (Val v), m) = (Val (Location (head(llist\\(convert m)))), (addMu (head(llist\\(convert m))) v m)) --E-REFV
ssos (Alloc t, m) = (Alloc (fst(ssos(t,m))), snd(ssos(t,m)))  --E-REF

ssos ((Assign (Val (Location l)) (Val v)), m) = (Val UnitV, replace l v m) --E-ASSIGN
ssos (Assign t1 t2, m) = if (isNF t1) then (Assign t1 (fst(ssos (t2,m))), snd(ssos (t2,m))) else (Assign (fst(ssos (t1,m))) t2, snd(ssos (t1,m))) --E-ASSIGN1/2


ssos (DeRef t, m) = case t of (Val (Location l)) -> (Val (findV l m), m) --E-DEREFLOC
                              otherwise -> ( DeRef (fst(ssos (t,m))), (snd(ssos (t,m)))) --E-DEREF




--------------------helper functions-----------------------------------------------------------

findV:: Loc -> Mu -> V
findV l ((l1,v):m) = if (l==l1) then v else (findV l m)  



replace:: Loc -> V -> Mu -> Mu
replace l v [] = []
replace l v ((l1,v1):m) = if (l==l1) then ((l1,v):m) else ((l1,v1):(replace l v m))

llist:: [Loc]
llist = [L0, L1, L2, L3, L4, L5, L6, L7, L8, L9]

convert:: Mu -> [Loc]
convert [] = []
convert ((l,v):m) = fst(l,v):(convert m)

addMu :: Loc -> V -> Mu -> Mu
addMu l v m = (l,v):m



addGamma :: Label -> Type -> Gamma -> Gamma
addGamma v t ga = (v,t):ga

getType :: Gamma -> Label -> Maybe Type
getType [] _ = Nothing
getType ((v,t):ga) v1 | v == v1 = Just t
                      | otherwise = getType ga v1


removeMaybe :: Maybe a -> a
removeMaybe Nothing = error "Nothing"
removeMaybe (Just x) = x



---------------------------------------------------------------------------------------------------------------------------------------------


--typing rules

typeCheck :: Gamma -> T -> Maybe Type
typeCheck _ (Val Tru) = Just BOOL 
typeCheck _ (Val Fls) = Just BOOL 
typeCheck _ (Val Z) = Just NAT --T-ZERO
typeCheck g (If x y z) | (typeCheck g x) == Just BOOL && (typeCheck g y) == (typeCheck g z) = typeCheck g y
                       | otherwise = Nothing 
typeCheck g (Succ t) | (typeCheck g t) == Just NAT = Just NAT  --T-SUCC
typeCheck g (Pred t) | (typeCheck g t) == Just NAT = Just NAT   --T-PRED
typeCheck g (IsZero t) | (typeCheck g t) == Just NAT = Just BOOL  --T-ISZERO
typeCheck g (Val (Var l)) = case (getType g l) of Just t -> Just t
                                                  otherwise -> error "not in Gamma"
typeCheck g (Val (L l t1 t12)) = case (typeCheck (addGamma l t1 g) t12) of Just t -> Just (Arrow t1 t)

typeCheck g (App t1 t2) = case (typeCheck g t1) of (Just (Arrow a b)) | (typeCheck g t2) == (Just a) -> Just b                                    
typeCheck g (Val UnitV) = Just Unit


typeCheck g (Let l v t) = case (typeCheck (addGamma l (removeMaybe(typeCheck g v)) g) t) of (Just b) -> Just b



typeCheck g (Seq t1 t2) = case (typeCheck g t2) of (Just a) | (typeCheck g t1) == (Just Unit) -> Just a 

typeCheck g otherwise = error "Typechecking fails"


eval :: (T, Mu) -> (T, Mu)
--eval (Val Z) = Val Z
--eval (Val (SuccNV Z)) = Val (SuccNV Z)
--eval t
--    | t == (fst(ssos (t,[]))) = t
--    | otherwise = eval(fst(ssos(t,[])))

--eval t = if t == (fst(ssos (t,[]))) then t else (eval (fst(ssos (t,m))))
--eval t = if (isNF t == True) then t else (eval (fst(ssos (t,[]))))
eval (t,m) = if (t,m) == ssos (t,m) then (t,m) else (eval (ssos (t,m)))



run :: T -> T
run t | typeCheck [] t /= Nothing = fst(eval (t,[]))



t1 = run((Val Fls))
t2 = run((If (Val Tru) (Val Fls) (Val Z)))
t3 = run((If (Val Tru) (Val Fls) (Val Tru)))
t4 = run(Pred $ Succ $ Succ $ Pred $ Succ $ Succ $ Val Z)
t5 = run((Val Z))
t6 = run(IsZero $ Pred $ Pred $ Succ $ Succ $ Val Z)
t7 = run(IsZero $ Pred $ Pred $ Succ $ Succ $ Succ $ Val Z)
t8 = run(IsZero $ Val UnitV)
t9 = run(If (IsZero (Val Z)) (Val Tru) (Val Fls))
t10 = run(Val $ L Q NAT $ Val $ L F NAT $ Val $ Var Q )
t11 = run((App (Val (L Q NAT (Val (L F NAT (Val (Var Q)))))) (Val Z)))
t12 = run(Val $ L Q BOOL $ Val $ L R BOOL $ Val $ Var R)
t13 = run(Val (L X (Arrow NAT BOOL) (App (Val (Var X)) (Val Z))))
t14 = run(App (Val (L X (Arrow NAT BOOL) (App (Val (Var X)) (Val Z)))) (Val (L Y NAT (IsZero (Val (Var Y))))))
t15 = run(Val UnitV)
t16 = run((Let X (Val UnitV) (App (Val (L X Unit (Val (Var X)))) (Val (Var X)))))
t17 = run((Seq (Val UnitV) (IsZero (Val Z))))
t18 = run(Seq (Val UnitV) $ Seq (Val UnitV) $ Seq (Val UnitV) $ (Val Tru))
t19 = run(Seq (Val UnitV) $ Seq (Val Fls) $ Seq (Val UnitV) $ (Val Tru))


y = DeRef $ Val $ Var X
z = Assign (Val (Var X)) $ Val Fls
x = Let X (Alloc (Val Tru)) (Seq z y)
t20 = eval (x,[])


t21 = eval (Let I (Alloc (Val Z)) $ Seq (App (Val (L X Unit (Assign (Val (Var I)) (Succ (DeRef (Val (Var I))))))) (Val UnitV)) (DeRef (Val (Var I))),[])










