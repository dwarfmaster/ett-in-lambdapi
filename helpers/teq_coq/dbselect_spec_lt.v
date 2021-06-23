Definition dbselect_spec_lt := 
fun (i j : nat) (eqT gtT ltT : Term) =>
nat_ind (fun j0 : nat => forall i0 : nat, i0 < j0 -> dbselect i0 j0 eqT gtT ltT = ltT)
  (fun (i0 : nat) (H : i0 < 0) =>
   match i0 as n return (n < 0 -> dbselect n 0 eqT gtT ltT = ltT) with
   | 0 =>
       fun H0 : 0 < 0 =>
       let H1 : 0 = 0 -> eqT = ltT :=
         match H0 in (_ <= n) return (n = 0 -> eqT = ltT) with
         | le_n _ =>
             fun H1 : 1 = 0 =>
             (fun H2 : 1 = 0 =>
              let H3 : False :=
                eq_ind 1 (fun e : nat => match e with
                                         | 0 => False
                                         | S _ => True
                                         end) I 0 H2 in
              False_ind (eqT = ltT) H3) H1
         | le_S _ m H1 =>
             fun H2 : S m = 0 =>
             (fun H3 : S m = 0 =>
              let H4 : False :=
                eq_ind (S m) (fun e : nat => match e with
                                             | 0 => False
                                             | S _ => True
                                             end) I 0 H3 in
              False_ind (1 <= m -> eqT = ltT) H4) H2 H1
         end in
       H1 eq_refl
   | S i1 =>
       fun H0 : S i1 < 0 =>
       let H1 : 0 = 0 -> gtT = ltT :=
         match H0 in (_ <= n) return (n = 0 -> gtT = ltT) with
         | le_n _ =>
             fun H1 : S (S i1) = 0 =>
             (fun H2 : S (S i1) = 0 =>
              let H3 : False :=
                eq_ind (S (S i1)) (fun e : nat => match e with
                                                  | 0 => False
                                                  | S _ => True
                                                  end) I 0 H2 in
              False_ind (gtT = ltT) H3) H1
         | le_S _ m H1 =>
             fun H2 : S m = 0 =>
             (fun H3 : S m = 0 =>
              let H4 : False :=
                eq_ind (S m) (fun e : nat => match e with
                                             | 0 => False
                                             | S _ => True
                                             end) I 0 H3 in
              False_ind (S (S i1) <= m -> gtT = ltT) H4) H2 H1
         end in
       H1 eq_refl
   end H)
  (fun (j0 : nat) (IHj : forall i0 : nat, i0 < j0 -> dbselect i0 j0 eqT gtT ltT = ltT) 
     (i0 : nat) (H : i0 < S j0) =>
   match i0 as n return (n < S j0 -> dbselect n (S j0) eqT gtT ltT = ltT) with
   | 0 => fun _ : 0 < S j0 => eq_refl
   | S i1 => fun H0 : S i1 < S j0 => IHj i1 (le_S_n (S i1) j0 H0)
   end H) j i
     : forall (i j : nat) (eqT gtT ltT : Term), i < j -> dbselect i j eqT gtT ltT = ltT.

