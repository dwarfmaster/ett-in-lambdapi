Definition teq_shift_shift0 := 
fun (i : nat) (u : Term) => teq_shift_shift 0 i u (le_0_n i)
     : forall (i : nat) (u : Term), Shift (shift i u) = shift (S i) (Shift u).
