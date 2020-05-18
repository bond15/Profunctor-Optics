{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}

-- https://github.com/ekmett/lens/wiki/History-of-Lenses
-- Laarhoven Lenses



main :: IO ()
main = print "test"


data Lens a b s t = Lens { view :: s -> a, update :: (b ,s) -> t}

p1 :: Lens a b (a,c) (b,c)
p1 = Lens view update where
    view (x,y) = x
    update (x', (x,y)) = (x',y)

-- ex
e :: (Int,Int)
e = update p1 (3,(4,5)) -- (3,5)

-- you can change the result type
e2 :: (String, Int)
e2 = update p1 ("hello",(4,5)) -- ("hello",5)

v1 :: Int
v1 = view p1 (4,5) -- 4

data Prism a b s t = Prism {match :: s -> Either t a, build :: b -> t}

the :: Prism a b (Maybe a) (Maybe b)
the = Prism match build where
    match (Just x) = Right x
    match Nothing = Left Nothing
    build x = Just x

tt :: Maybe Int
tt = build the 7

-- claim, this representation is lacking compositionality 

data Adapter a b s t = Adapter {from  :: s -> a, to :: b -> t}

-- used for 'plumbing' 
-- ex) to convert between isomorphic tuple types
flatten :: Adapter (a,b,c) (a',b',c') ((a,b),c) ((a',b'),c')
flatten = Adapter from to where
    from ((x,y),z) = (x,y,z)
    to (x,y,z) = ((x,y),z)

f1 = to flatten (1,2,3) -- ((1,2),3)

iso = (from flatten) $ (to flatten) $ (1,2,3)
--i1 = iso (1,2,3) -- (1,2,3)



-- Traversal

-- A traversable datatype is a containter datatype 
-- where the constructors of the container have an ordering

-- ex1) Maybe = Nothing | Just _ has a trivial traversal
-- with the ordering Just -> Nothing

-- ex2) List = Nil | Cons _ List, there is a linear traversal 
-- from the ordering of Cons to Nil

-- ex3) Tree = Leaf | Node Tree _ Tree
-- can have a preorder, inorder, postorder traversal

data Tree a = Leaf | Node (Tree a) a (Tree a) deriving (Show, Eq)

tree :: Tree Integer
tree =  Node (Node (Node Leaf 3 Leaf) 4 (Node Leaf 5 Leaf)) 6 (Node Leaf 7 Leaf)

-- (A -> F B) -> (S -> F T)
-- traversals can also be effectful
inorder :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
inorder m Leaf = pure Leaf
inorder m (Node l x r) = pure Node <*> inorder m l <*> m x <*> inorder m r

preorder :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
preorder m Leaf = pure Leaf
preorder m (Node l x r) = undefined 

-- trivial 'effect'
data Id a = Id a deriving Show
get (Id a) = a

instance Functor Id where
    fmap f a = Id (f $ get a)

-- fmap not $ Id True  ==> Id False
instance Applicative Id where
    pure x = Id x
    (<*>) f a = Id (get f $ get a)
-- Id not <*> Id True ==> Id False

-- inorder traversal of Tree using trivial effect
truu = tree == (get $ inorder Id tree)


-- Example State useage

data State s a = State {run :: s -> (a,s)}

instance Functor (State s) where
    fmap f m = State(\s -> let (x ,s') = run m s in (f x, s'))

instance Applicative (State s) where
    pure x = State(\s -> (x,s))
    (<*>) m n = State(\s -> let (f,s') = run m s
                                (x,s'')= run n s'
                            in (f x,s''))

-- a State that keeps a record of every element it sees
app :: a -> State [a] a
app = \a -> State(\s -> (a,s ++ [a]))


-- choose the starting state to be an empty list
runEmpty = \state -> run state []

-- Do an inorder traversal of a tree, 
-- using State to keep a log of the elements visited 
logTree = runEmpty $ inorder app tree
logg = snd logTree

-- For an applicative functor F, 
--  a traversal takes an effectful opperation of type A -> F B 
-- on the elements of a container and lifts this to an effectful
-- computation of types S -> F T over the whole container



-- 2.3 Traversals as concrete optics
-- Ovserve the type (A -> F B) -> (S -> F T) 
--   of witnesses to traversability of the container S

-- is almost equivalent to a pair of functions

-- contents :: S -> A^n
    -- yileds the sequence of elements in the container
        -- in the order specified by a traversal
-- fill :: S x B^n -> T
    -- takes an old container and a new sequence of elements
        -- upddates the old container with new elements

-- where n is the number of elements in the container

-- when n = 1,   S -> A    S x B -> T

-- no dependent types here so cant index a type with n
-- workaround involves an existentially quantified length and 
-- tupling the contents and fill functions

-- Claim : S is equivalent to  Exists n. A^n x (B^n -> T)

-- encoding that types as...
data FunList a b t = Done t | More a (FunList a b (b -> t))
-- from Larhoven lenses

instance Functor (FunList a b) where
    fmap f (Done t) = Done (f t)
    fmap f (More x l) = More x (fmap (f.) l)

instance Applicative (FunList a b) where
    pure = Done
    Done f <*> l = fmap f l
    More x l <*> l' = More x (fmap flip l <*> l')

-- wtf?
single :: a -> FunList a b b
single x = More x (Done id)

fuse :: FunList b b t -> t
fuse (Done t) = t
fuse (More x l) = fuse l x

data Traversal a b s t = Traversal {extract :: s -> FunList a b t}

inorderC :: Traversal a b (Tree a) (Tree b)
inorderC = Traversal(inorder single)

v :: FunList Integer b (Tree b)
v = extract inorderC tree

truuu = fuse v == tree

doublee x = More x (Done (2*))

-- double every element in the tree
dtree = fuse $ inorder doublee tree

-- 3 Profunctors

class Profunctor p where 
    dimap :: (a' -> a) -> (b -> b') -> p a b -> p a' b'


    -- laws
        -- dimap id id = id
        -- dimap (f' . f) (g . g') = dimap f g . dimap f' g'

-- P A B is a type that represents 'function like' things,
--      each taking As to Bs
-- ex)
    -- P := Linear maps
    -- P := (->)
    -- P := Circuits

-- Think of dimap f g h    AS   dimap pre post transform

-- The post processor is covariant
-- The pre processer is contravariant

instance Profunctor (->) where
    dimap f g h = g . h . f

-- not only vanilla function types, but also anything of the form
    -- A -> F B, where F is a functor

-- a wrapper around ^^ form of arrow type
data UpStar f a b = UpStar {unUpStar :: a -> f b}

instance Functor f => Profunctor (UpStar f) where
    dimap f g (UpStar h) = UpStar(fmap g . h . f)

-- dualizes functions of the form F A -> B
-- both can be combined for functions of form F A -> G B

-- 3 refinement of profunctors

-- Cartesian
    -- where the additional context is a product type
class Profunctor p => Cartesian p where
    first :: p a b -> p (a,c) (b,c)
    second :: p a b -> p (c,a) (c,b)
        -- laws
            -- dimap runit runit' h = first h
                -- runit :: a x 1 -> a
                -- runit' :: a -> a x 1

            -- dimap lunit lunit h = ...
                -- ..
        
            -- dimap assoc assoc' (first $ first h) = first h
                -- assoc :: a x (b x c) -> (a x b) x c
                -- assoc':: (a x b) x c -> a x (b x c)

cross :: (a ->b) -> (c -> d) -> (a,c) -> (b,d)
cross f g = \p -> (f $ fst p, g $ snd p) 

instance Cartesian (->) where
    first h = cross h id
    second h = cross id h

rstrength :: Functor f => ((f a),b) -> f(a,b)
rstrength (fx, y) = fmap (,y) fx

lstrength :: Functor f => (a,(f b)) -> f(a,b)
lstrength (x,fy) = fmap (x,) fy

-- functions of form A -> F B, where F is a functor, is also cartesian
instance Functor f => Cartesian (UpStar f) where
    first (UpStar unUpStar) = UpStar(rstrength . cross unUpStar id)
    second (UpStar unUpStar) = UpStar(lstrength . cross id unUpStar)

-- Profunctors on Sum types
class Profunctor p => CoCartesian p where
    left :: p a b -> p (Either a c) (Either b c)
    right :: p a b -> p (Either c a) (Either c b)

    -- laws
        -- dimap rzero rzero' h = left h
            -- rzero :: a + 0 -> a
            -- rzero':: a -> a + 0
        -- dimap lzero lzero' h ...
            -- ..
        -- dimap coassoc' coassoc (left (left h)) = left h
            -- coassoc :: a + (b + c) -> (a + b) + c
            -- coassoc'

plus :: (a -> b) -> (c -> d) -> Either a c -> Either b d
plus f g = \s -> case s of
    Left x -> Left $ f x
    Right x -> Right $ g x

-- function types are Cocartesian
instance CoCartesian (->) where
    left h = plus h id
    right h = plus id h


-- the function type with sum context is CoCartesian
instance Applicative f => CoCartesian (UpStar f) where
    left (UpStar unUpStar) = UpStar(either (fmap Left . unUpStar)(pure . Right))
    right (UpStar unUpStar)= UpStar(either (pure . Left) (fmap Right . unUpStar))

-- third refinement Monoidal
-- "independent" parallel 
class Profunctor p => Monoidal p where
    par :: p a b -> p c d -> p (a,c) (b,d)
    empty :: p () ()

instance Monoidal (->) where
    par = cross
    empty = id


pair::Applicative f => (a -> f b) -> (c -> f d) -> (a,c) -> f (b,d)
pair h k (x,y) = pure (,) <*> h x <*> k y

instance Applicative f => Monoidal (UpStar f) where
    empty = UpStar pure
    par h k = UpStar(pair(unUpStar h)(unUpStar k))

-- in summary, Profunctors describe an abstract mapping P from type A to B
-- A dimap let the tranformation be wrapped in a preprocessor and a postprocessor
    -- the preprocessor is contravairant
    -- the postprocessor is covariant
-- Profunctors can have Cartesian, CoCartisian, and Monoidal structure
    -- Cartesian profunctors pair the input and output transformation types with 
        -- a constant transformation
    -- CoCartesian profunctors sum the input and output transformation types
        -- with a constant transformation
    -- Monoidal profunctors pair 2 transforms into one transform on producs
        -- of their input and output types.
-- Instances
    -- (->) regular funtion types
    -- (A -> F B) funtion types enhanced with effects

-- 4) Optics in terms of Profunctors
-- Insight, Represent optics as "mappings between transformers"

type Optic p a b s t = p a b -> p s t

-- Interpret as
-- S and T are composite types
-- S has components of type A
-- T has components of type B
-- P A B is a transformation from A to B
-- An Optic lifts , for some particual choice of p, the transformation 
    -- from A to B into a transformation from S to T

-- Recall the Adapter s t a b = Adapter {from :: s -> a, to :: b -> t}

type AdapterP a b s t = forall p. Profunctor p => Optic p a b s t

-- these two definitions are equivalent  (see appendix C)

-- conversion
adapterC2P :: Adapter a b s t -> AdapterP a b s t
adapterC2P (Adapter from to) = dimap from to

instance Profunctor (Adapter a b) where
    dimap f g (Adapter from to) = Adapter (from . f) (g . to)

adapterP2C :: AdapterP a b s t -> Adapter a b s t
adapterP2C l = l (Adapter id id)


-- Lenses

-- Recall Lens a b s t = Lens {view :: s -> a, updat b x s -> t}

type LensP a b s t = forall p. Cartesian p => Optic p a b s t

type PrismP a b s t = forall p. CoCartesian p => Optic p a b s t

type TraversalP a b s t = forall p. (Cartesian p, CoCartesian p, Monoidal p)
    => Optic p a b s t

-- 5 Composing Optics
fork f g x = (f x, g x)


πP1 :: Cartesian p => p a b -> p (a,c) (b,c)
πP1 = dimap (fork fst id) (cross id snd) . first

false = πP1 not (True,6) -- (False,6)

πP11 :: LensP a b ((a,c),d) ((b,c),d)
πP11 = πP1 . πP1

fallse = πP11 not ((True, 6), "hello") -- ((False,6),"hello")

