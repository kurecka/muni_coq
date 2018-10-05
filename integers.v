Module Integers.

Inductive pos : Type :=
| U : pos
| S : pos -> pos.

Inductive int : Type :=
| Z : int
| N : pos -> int
| P : pos -> int.

Definition succ (z: int) : int :=
match z with
| Z => P U
| N U => Z
| N (S n) => N n
| P n => P (S n)
end.

Definition pred (z: int) : int :=
match z with
| Z => N U
| P U => Z
| P (S n) => P n
| N n => N (S n)
end.

Fixpoint add (a b : int) : int :=
match a, b with
| Z, b' => b'
| P (S a'), b' => add (P a') (succ b')
| P U, b' => succ b'
| N (S a'), b' => add (N a') (pred b')
| N U, b' => pred b'
end.

End Integers.