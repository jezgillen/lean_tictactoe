import «Tictactoe»

-- Fin range (useful for indexing) ----------------------
def Fin.range (n: Nat) : List (Fin n) :=
  if h: n > 0 then
    (List.range n).map (fun x:Nat => {val:=x%n,isLt:= by apply Nat.mod_lt; assumption})
  else
    []

#eval Fin.range 9

-- Vect type --------------------------------------------

inductive Vect (α : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n+1)
deriving Repr

def Vect.toList (a : Vect α n) : List α :=
  match a with
    | .nil => .nil
    | .cons head tail => .cons head tail.toList

def Vect.length (xs : Vect α n) : Nat :=
  match xs with
    | .nil => 0
    | .cons _ tail => tail.length + 1

abbrev Vect.inBounds (xs : Vect α n) (idx : Nat) : Prop :=
  idx < n

def Vect.get (xs : Vect α n) (idx : Nat) (ok: xs.inBounds idx) : α :=
    have h : idx < n := ok
    match xs, idx with
      | .nil, k => False.elim ((Nat.not_lt_zero k) (ok)) -- unnecessary, apparently it works this out by itself
      | .cons head tail, 0 => head
      | .cons _ tail, k+1 => tail.get k (Nat.lt_of_succ_lt_succ ok)

instance : GetElem (Vect α n) (Nat) α Vect.inBounds where
  getElem := Vect.get

def Vect.set (xs : Vect α n) (idx : Nat) (item : α) (ok: xs.inBounds idx) : Vect α n :=
  match xs, idx with
    | .cons head tail, 0 => .cons item tail
    | .cons head tail, k+1 => .cons head (tail.set k item (Nat.lt_of_succ_lt_succ ok))

def listToVec (x: List α) : (Vect α x.length) :=
   match x with
    | .nil => Vect.nil
    | .cons head tail =>  Vect.cons head (listToVec tail)

-- Test
def x : Vect Nat 4 := .cons 1 (.cons 2 (.cons 3 (.cons 4 .nil)))
#eval x[2]
#eval (listToVec [8,7,6,5,4,3,3])[3]

-- A 2d_array type --------------------------------------------------------

structure Vect2d (α : Type u) (n m :Nat) where
  array : Vect α (n*m)

abbrev Vect2d.inBounds (xs : Vect2d α n m) (idx : Nat×Nat) : Prop :=
  idx.fst < n ∧ idx.snd < m

theorem add_le_add_lt_implies_lt {a b c d: Nat} (h1 : a ≤ c) (h2 : b < d) : a + b < c + d :=
  by
    apply Nat.lt_of_le_of_lt
    case m => exact c+(d-1)
    case h₁ => apply Nat.add_le_add
               apply h1
               apply Nat.le_sub_of_add_le
               apply h2
    case h₂ => apply Nat.add_lt_add_left
               apply Nat.sub_lt
               apply Nat.lt_of_le_of_lt
               case h.a.h₂ => apply h2
               case h.a.h₁ => apply Nat.zero_le
               case h.a => simp



theorem bounded_square_idx {x y n m :Nat} (h: x < n ∧ y < m): x*m + y < n*m :=
  have h1 : x < n := h.left
  have h2 : y < m := h.right
  match n with
  | 1 => (have h3: x = 0 := (by
                              rw [←Nat.le_zero_eq]
                              apply Nat.le_of_lt_succ
                              exact h1)
          by simp [h3, h2])
  | k+1 => (
          by rw [Nat.add_mul, Nat.one_mul]
             apply add_le_add_lt_implies_lt
             case h2 => exact h2
             case h1 => apply Nat.mul_le_mul_right
                        apply Nat.le_of_lt_succ
                        apply h1
)

def Vect2d.get (xs : Vect2d α n m) (idx: Nat×Nat) (ok: inBounds xs idx) : α :=
  have h : idx.fst*m + idx.snd < n*m := bounded_square_idx ok
  xs.array[idx.fst*m + idx.snd]

instance : GetElem (Vect2d α n m) (Nat×Nat) α (Vect2d.inBounds) where
  getElem := Vect2d.get

def Vect2d.set (xs : Vect2d α n m) (idx: Nat×Nat) (item: α) (ok: inBounds xs idx) : Vect2d α n m :=
  have h : idx.fst*m + idx.snd < n*m := bounded_square_idx ok
  {array := xs.array.set (idx.fst*m + idx.snd) item h}

-- Test
def t_2d : Vect2d Nat 2 2 := {array := x}
#eval Vect2d.inBounds t_2d (0,0)
#eval t_2d[(0,0)]
#eval t_2d[(0,1)]
#eval t_2d[(1,0)]
#eval t_2d[(1,1)]

---------------------------------------------------------------------------

-- make a type for storing a tic-tac-toe square
structure Square where
  x : Bool
  o : Bool
  only_one : (¬x) ∨ (¬o)
deriving Repr

def squareToString (s : Square) : String :=
  if s.x then
    "x"
  else if s.o then
    "o"
  else
    "_"

def mks (s: Char) : Square :=
  match s with
    | 'x' => {x := True, o := False, only_one := by simp}
    | 'o' => {x := False, o := True, only_one := by simp}
    | _ => {x := False, o := False, only_one := by simp}


instance : ToString Square where
  toString := squareToString

-- Test
def x_square : Square := {x := True, o := False, only_one := by simp}

#eval x_square

--Tic-Tac-Toe board -----------------------------------------------
abbrev BoardState := Vect2d Square 3 3

instance : Inhabited BoardState where
  default := let l := "         ".data.map mks
             {array := listToVec l}

def listToBoardState (l:List Square) : BoardState :=
  if h: l.length = 9 then
    {array := by apply h ▸ listToVec l}
  else
    panic! "Wrong length list"

#eval (3 : Fin 4)
-- make it printable

def boardStateToString (b : BoardState) : String :=
  Id.run do
    let mut out := ""
    for h: i in [:3] do
      for h2: j in [:3] do
        have h1 : i < 3 := Membership.mem.upper h
        have h2 : j < 3 := Membership.mem.upper h2
        out := out ++ (if j>0 then "|" else "") ++ toString b[(i,j)]
      out := out ++ "\n"
    out

#eval boardStateToString (listToBoardState (" x       ".data.map mks))

instance: ToString BoardState where
  toString := boardStateToString

#eval (listToBoardState (" x       ".data.map mks))


def stringToState? (s:String) : Option BoardState :=
  do
  let mut squares : List Square := .nil
  for c in s.data do
    squares := squares ++ [mks c]
  if h: (List.length squares) = 9 then
    some ((listToBoardState squares))
  else
    none

#eval stringToState? "x        "

def stringToState! (s:String) : BoardState :=
  let squares : List Square := s.data.map mks
  if h : squares.length = 9 then
    listToBoardState squares
  else
    panic! "error: Invalid string"

#eval stringToState! "ooooooooo"

-- Evaluate whether a state is winning for either player -----------

def BoardState.sizeOf (b: BoardState): Nat :=
  -- count number of free spaces left
  (b.array.toList.filter (fun x => not (x.o || x.x))).length

def BoardState.row (b: BoardState) (n : Fin 3) : List Square :=
  ((fun x : Fin 3 => (b.get (n,x) (
    by simp [Vect2d.inBounds, n.isLt, x.isLt]
  ))) <$> ([0,1,2]: List (Fin 3)))

def BoardState.col (b: BoardState) (n : Fin 3) : List Square :=
  ((fun x : Fin 3 => (b.get (x, n) (
    by simp [Vect2d.inBounds, n.isLt, x.isLt]
  ))) <$> ([0,1,2]: List (Fin 3)))

def BoardState.diag1 (b: BoardState) : List Square :=
  ((fun x : Fin 3 => (b.get (x, x) (
    by simp [Vect2d.inBounds, x.isLt];
  ))) <$> ([0,1,2]: List (Fin 3)))

def BoardState.diag2 (b: BoardState) : List Square :=
  ((fun x : Fin 3 => (b.get (2-x, x) (
    by simp [Vect2d.inBounds, x.isLt];
       apply Nat.lt_succ_of_le;
       apply Nat.sub_le
  ))) <$> ([0,1,2]: List (Fin 3)))

instance : BEq Square where
  beq (s1 s2: Square) := s1.x == s2.x ∧ s1.o == s2.o

def b1 := stringToState! "ooo      "
def b2 :=  stringToState! "   ooo   "
def b3 :=  stringToState! "      ooo"
def b4 :=  stringToState! "o  o  o  "
def b5 :=  stringToState! "ox ox ox "
#eval ((stringToState! "  x  x  x").col 2).all (· == (mks 'x'))
def b6 :=  (stringToState! "x   x   o")
#eval (stringToState! "  x x x  ").diag2.all (· == (mks 'x'))

inductive WinState where
  | x_wins : WinState
  | o_wins : WinState
  | drawn : WinState
  | in_progress : WinState
  | invalid : WinState
deriving Repr, BEq

def BoardState.getWinState (b : BoardState) : WinState :=
  let triple (s : Square) : Bool :=
    let in_rows := [0,1,2].any (fun x => (b.row x).all (· == s))
    let in_cols := [0,1,2].any (fun x => (b.col x).all (· == s))
    let in_diags := b.diag1.all (· == s) || b.diag2.all (· == s)
    in_rows || in_cols || in_diags
  let x_wins := triple (mks 'x')
  let o_wins := triple (mks 'o')
  if x_wins && o_wins then WinState.invalid else
  if x_wins then WinState.x_wins else
  if o_wins then WinState.o_wins else
  if b.sizeOf == 0 then WinState.drawn else
  WinState.in_progress

#eval b6.getWinState

-- Get available moves and check move validity -----------------------------------------


def BoardState.isValidMove (b: BoardState) (x y : Fin 3) : Bool :=
  have h: Vect2d.inBounds b (x,y) := by simp [Vect2d.inBounds, x.isLt, y.isLt]
  have s := b[(x.val,y.val)]
  not (s.x || s.o)

def BoardState.makeMove (b : BoardState) (x y : Fin 3) (turn : Nat) : BoardState :=
  let s := if turn % 2 == 0 then mks 'x' else mks 'o'
  have h: Vect2d.inBounds b (x,y) := by simp [Vect2d.inBounds, x.isLt, y.isLt]
  b.set (x.val,y.val) s h

def all_indices := ((fun x => ((fun y => (x,y)) <$> Fin.range 3)) <$> Fin.range 3).foldl (fun x y => x ++ y) []

#eval b6

def BoardState.validMoves (b: BoardState) : List (Fin 3 × Fin 3) :=
  all_indices.filter (fun i => b.isValidMove i.fst i.snd)

#eval b6.validMoves

def BoardState.curr_move (b: BoardState) : Nat :=
  (b.array.toList.filter (fun x => (x == mks 'x' || x == mks 'o'))).length

-- Implement recursive state-value function evaluation-------------------------------

def List.argmax (l : List α) (f: α → Int) : Option α :=
  match l with
    | .nil => none
    | .cons h t =>
      let best_in_tail := t.argmax f
      match best_in_tail with
        | .none => h
        | .some a => if f a > f h then a else h


def BoardState.value (b: BoardState) : Int :=
  let status := b.getWinState
  if status == .x_wins then
    1
  else if status == .o_wins then
    -1
  else if status == .drawn then
    0
  else if status == .invalid then
    panic! "Invalid board state"
  else
    let is_negative := if b.curr_move%2==0 then 1 else -1
    -- create list of all valid next boardstates
    let next_states := (fun i => (b.makeMove i.fst i.snd b.curr_move)) <$> b.validMoves
    -- otherwise recurse on all boardstates, and return max
    let next_values := ((fun x => is_negative*BoardState.value x) <$> next_states)
    match next_values.maximum? with
    | none => 0
    | some val => is_negative*val
  termination_by b.sizeOf
  decreasing_by sorry

def BoardState.value3 (b: BoardState) : Int :=
  let status := b.getWinState
  if status == .x_wins then
    1
  else if status == .o_wins then
    -1
  else if status == .drawn then
    0
  else if status == .invalid then
    panic! "Invalid board state"
  else
    let is_negative := if b.curr_move%2==0 then 1 else -1
    -- create list of all valid next boardstates
    let next_states := (fun i => (b.makeMove i.fst i.snd b.curr_move)) <$> b.validMoves
    have h2 : ∀ (s: BoardState), s ∈ next_states → s.sizeOf < b.sizeOf := sorry
    -- otherwise recurse on all boardstates, and return max
    let next_values := Id.run do
      let mut next_values : List Int := []
      for h : s in next_states do
        have h3 : s.sizeOf < b.sizeOf := by apply h2; apply h
        let val := s.value3
        next_values := .cons val next_values
      next_values
    match next_values.maximum? with
    | none => 0
    | some val => is_negative*val
  termination_by b.sizeOf


def b7 := stringToState! "xx xoxo o"

#eval b7
#eval b7.getWinState
#eval b7.value

-- Interacting with the user ------------------------------------------

def validate_input (input : String) : Option (Fin 3 × Fin 3) :=
  if input.length != 3 then
    none
  else
    let l := input.split (λ x => x == ',')
    if h4: l.length = 2 then
      have h : 0 < l.length := by simp [h4]
      have h2 : 1 < l.length := by simp [h4]
      let first := l[0].toNat?
      let second := l[1].toNat?
      match first, second with
      | _, none => none
      | none, _ => none
      | some x, some y => if h3: x < 3 ∧ y < 3 then some (⟨x,by simp [h3]⟩,⟨y,by simp [h3]⟩) else none
    else
      none

def b : BoardState := default

def BoardState.makeBestMove (b:BoardState) (turn: Nat) : Option BoardState :=
  let next_states := (fun i => (b.makeMove i.fst i.snd turn)) <$> b.validMoves
  next_states.argmax (λ x => -BoardState.value x)

partial def user_loop (b: BoardState) (turn : Nat) : IO Unit := do
  match b.getWinState with
  | .x_wins => IO.println "X wins"
  | .o_wins => IO.println "O wins"
  | .drawn => IO.println "Draw"
  | .invalid => IO.println "Error 1"
  | .in_progress =>
    let stdin ← IO.getStdin
    IO.print "Enter move (e.g. '0,2'): "
    let string ← stdin.getLine
    match validate_input string.trimRight with
    | none => IO.println "Invalid input"; user_loop b turn
    | some (x,y) =>
      if b.isValidMove x y then
        let new_b := b.makeMove x y turn
        IO.print new_b
        match new_b.makeBestMove (turn+1) with
        | none => user_loop new_b (turn+1) -- No moves possible, need to evaluate winstate
        | some new_new_b =>
          IO.println "Computer move:"
          IO.print new_new_b
          user_loop (new_new_b) (turn+2)
      else
        IO.println "Invalid move"; user_loop b turn

def main : IO Unit := do
  IO.print b
  user_loop b 0
