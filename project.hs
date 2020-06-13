import Data.List
import System.IO
import Data.Char
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Maybe as MB
import qualified Control.Monad as MON
import System.Environment


type State = S.Set Int


data NFA = 
    NFA { delta :: M.Map Int (M.Map Char (S.Set Int))
         ,initial_states :: S.Set Int
         ,accepting_states :: S.Set Int } deriving (Show)

-- This is a dfa, where states are subsets of states of NFA
data TRANSITION_DFA = 
    TRANSITION_DFA { transition_dfa_delta :: M.Map State (M.Map Char State)
                    ,transition_dfa_initial_state :: State
                    ,transition_dfa_accepting_states :: S.Set State } deriving (Show)

data DFA = 
    DFA { dfa_delta :: M.Map Int (M.Map Char Int)
         ,dfa_initial_state :: Int
         ,dfa_accepting_states :: S.Set Int } deriving (Show)


{-==========================================================================================================================================-}
-- Next functions are for creating NFA based on the input

parse_contents_to_nfa :: String->NFA
parse_contents_to_nfa string =
    case lines string of
        (number : initial : accepting : rest) ->
            let number_of_states = read number
                initial_states = map read $ words $ initial
                accepting_states = map read $ words $ accepting
                transitions = map parse_line rest
                p k (x,y) = k==x
                f k = M.fromList $ snd $ unzip $ filter (p k) transitions
                delta = [ (i, m) | i <- [0 .. number_of_states - 1], let m = f i]
             in NFA (M.fromList delta) (S.fromList initial_states) (S.fromList accepting_states)
        _ -> error "bad input"


parse_line :: String->(Int, (Char, S.Set Int))
parse_line line = 
    case words line of
        (state : char : states) ->
            let st = read state :: Int
                ch = head char :: Char
                int_states = S.fromList $ map (read) states
             in (st, (ch, int_states))
        _ -> error "bad input"


{-==========================================================================================================================================-}
-- These functions are for getting info from NFA and converting NFA to TRANSITION_DFA


get_delta_transition_of_state :: NFA->Int->M.Map Char (S.Set Int)
get_delta_transition_of_state nfa state_num = MB.fromJust $ M.lookup state_num $ delta nfa


get_delta_transition_of_subset_of_states :: NFA->S.Set Int->M.Map Char State
get_delta_transition_of_subset_of_states nfa subset = 
    let maps = map (get_delta_transition_of_state nfa) (S.toList subset)
     in foldl (M.unionWith S.union) M.empty maps


get_tr_func :: NFA->[State]->[State]->M.Map State (M.Map Char State)->M.Map State (M.Map Char State)
get_tr_func nfa [] visited result = result
get_tr_func nfa (h:t) visited result = 
    let tr = get_delta_transition_of_subset_of_states nfa h
        states = M.elems tr
        new_queue = t ++ (states \\ visited)
        new_visited = visited ++ states
        new_result = M.insert h tr result
     in get_tr_func nfa new_queue new_visited new_result


nfa_to_transition_dfa :: NFA->TRANSITION_DFA
nfa_to_transition_dfa nfa = 
    let initial_state = initial_states nfa
        visited = [initial_state]
        tr_dfa_transition_function = get_tr_func nfa [initial_state] visited M.empty
        states = M.keysSet tr_dfa_transition_function
        acc_states = accepting_states nfa
        p x y = not (x `S.disjoint` y)
        accepting_states_for_transition_dfa = [x | x<-(S.toList states), (p x acc_states)]
        tr_dfa_acc_states = S.fromList accepting_states_for_transition_dfa
     in TRANSITION_DFA tr_dfa_transition_function initial_state tr_dfa_acc_states


{-==========================================================================================================================================-}
-- These next function are responsible for converting TRANSITION_DFA to DFA.



transition_dfa_to_dfa :: TRANSITION_DFA->DFA
transition_dfa_to_dfa tr_dfa = 
    let states = M.keysSet (transition_dfa_delta tr_dfa)
        map_for_renaming_subsets = M.fromList $ zip (S.toList states) [0..S.size states]
        f subset = MB.fromJust $ M.lookup subset map_for_renaming_subsets
        tr_fn = transition_dfa_delta tr_dfa
        maps_for_dfa = [((f x), M.map f (MB.fromJust $ M.lookup x tr_fn))| x<-(S.toList states)]
        ini_state = transition_dfa_initial_state tr_dfa
        dfa_initial_state = f ini_state
        acc_state = transition_dfa_accepting_states tr_dfa
        dfa_accepting_states = S.map f acc_state
    in DFA (M.fromList maps_for_dfa) dfa_initial_state dfa_accepting_states


{-==========================================================================================================================================-}
-- These function for constructing String representation of DFA


list_to_string :: (Show a)=>[a]->String
list_to_string list = unwords (map show list)


dfa_to_string_helper_inner :: (Int, [(Char, Int)]) -> String
dfa_to_string_helper_inner (from, transitions) =
    let line char to = unwords [show from, char:"", show to] in
    unlines [line char to | (char, to) <- transitions]


dfa_to_string_helper :: [(Int, [(Char, Int)])] -> String
dfa_to_string_helper list = concatMap (dfa_to_string_helper_inner) list


dfa_to_string :: DFA->String
dfa_to_string dfa = 
    let map = dfa_delta dfa
        list = M.toList map
        list_up = [(state, M.toList $ map)| (state, map)<-list]
        number_of_states = length list
        initial_state_of_dfa = dfa_initial_state dfa
        accepting_states_of_dfa = dfa_accepting_states dfa
        str1 = (show initial_state_of_dfa)
        str2 = (list_to_string $ S.toList accepting_states_of_dfa)
        string = str1 ++ "\n" ++ str2 ++ "\n"
     in string ++ dfa_to_string_helper list_up


{-==========================================================================================================================================-}
-- These functions a for processing a string by a DFA


process_string' :: DFA->String->Int->Bool
process_string' dfa [] current_state = S.member current_state (dfa_accepting_states dfa)
process_string' dfa (x:xs) current_state = 
    let next_state = M.lookup x (MB.fromJust $ M.lookup current_state (dfa_delta dfa))
     in if MB.isNothing next_state then False
                                   else process_string' dfa xs (MB.fromJust next_state)


process_string :: DFA->String->Bool
process_string dfa string = process_string' dfa string (dfa_initial_state dfa)


{-==========================================================================================================================================-}


nfa_to_dfa :: NFA->DFA
nfa_to_dfa = transition_dfa_to_dfa . nfa_to_transition_dfa


process_args :: [String] -> IO ()
process_args args = 
    case (args) of
        [] -> do
            putStr "Enter file path: " 
            file_path <- getLine
            nfa <- read_nfa_from_file file_path
            start_dfa_processing $ nfa_to_dfa nfa
        (dir:[]) -> do
            nfa <- read_nfa_from_file dir
            start_dfa_processing $ nfa_to_dfa nfa
        _ -> putStrLn "Incorrect usage"


read_nfa_from_file :: FilePath->IO (NFA)
read_nfa_from_file file_path = do
    contents <- readFile file_path
    let nfa = parse_contents_to_nfa contents
    return nfa


start_dfa_processing :: DFA->IO ()
start_dfa_processing dfa = do
    putStrLn $ dfa_to_string dfa
    MON.forever $ do
        l <- getLine
        putStrLn $ show $ process_string dfa l


main = do
    args <- getArgs
    process_args args