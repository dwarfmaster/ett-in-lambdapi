Definition teq_shift_dbselect := 
fun (n i j : nat) (eqT gtT ltT : Term) =>
nat_ind
  (fun i0 : nat =>
   forall j0 : nat,
   shift n (dbselect i0 j0 eqT gtT ltT) = dbselect i0 j0 (shift n eqT) (shift n gtT) (shift n ltT))
  (fun j0 : nat =>
   match
     j0 as n0
     return
       (shift n (dbselect 0 n0 eqT gtT ltT) = dbselect 0 n0 (shift n eqT) (shift n gtT) (shift n ltT))
   with
   | 0 => eq_refl
   | S j1 => eq_refl
   end)
  (fun (i0 : nat)
     (IHi : forall j0 : nat,
            shift n (dbselect i0 j0 eqT gtT ltT) =
            dbselect i0 j0 (shift n eqT) (shift n gtT) (shift n ltT)) (j0 : nat) =>
   match
     j0 as n0
     return
       (shift n (dbselect (S i0) n0 eqT gtT ltT) =
        dbselect (S i0) n0 (shift n eqT) (shift n gtT) (shift n ltT))
   with
   | 0 => eq_refl
   | S j1 => IHi j1
   end) i j
     : forall (n i j : nat) (eqT gtT ltT : Term),
       shift n (dbselect i j eqT gtT ltT) = dbselect i j (shift n eqT) (shift n gtT) (shift n ltT).
