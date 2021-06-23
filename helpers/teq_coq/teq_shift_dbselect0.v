Definition teq_shift_dbselect0 := 
fun (i j : nat) (eqT gtT ltT : Term) => teq_shift_dbselect 0 i j eqT gtT ltT
     : forall (i j : nat) (eqT gtT ltT : Term),
       Shift (dbselect i j eqT gtT ltT) = dbselect i j (Shift eqT) (Shift gtT) (Shift ltT).
