Definition dbselect_spec_gt := 
fun (i j : nat) (eqT gtT ltT : Term) =>
nat_ind (fun j0 : nat => forall i0 : nat, S j0 <= i0 -> dbselect i0 j0 eqT gtT ltT = gtT)
  (fun (i0 : nat) (H : 1 <= i0) =>
   match i0 as n return (1 <= n -> dbselect n 0 eqT gtT ltT = gtT) with
   | 0 =>
       fun H0 : 1 <= 0 =>
       let H1 : 0 = 0 -> eqT = gtT :=
         match H0 in (_ <= n) return (n = 0 -> eqT = gtT) with
         | le_n _ =>
             fun H1 : 1 = 0 =>
             (fun H2 : 1 = 0 =>
              let H3 : False :=
                eq_ind 1 (fun e : nat => match e with
                                         | 0 => False
                                         | S _ => True
                                         end) I 0 H2 in
              False_ind (eqT = gtT) H3) H1
         | le_S _ m H1 =>
             fun H2 : S m = 0 =>
             (fun H3 : S m = 0 =>
              let H4 : False :=
                eq_ind (S m) (fun e : nat => match e with
                                             | 0 => False
                                             | S _ => True
                                             end) I 0 H3 in
              False_ind (1 <= m -> eqT = gtT) H4) H2 H1
         end in
       H1 eq_refl
   | S i1 => fun _ : 1 <= S i1 => eq_refl
   end H)
  (fun (j0 : nat) (IHj : forall i0 : nat, S j0 <= i0 -> dbselect i0 j0 eqT gtT ltT = gtT) 
     (i0 : nat) (H : S (S j0) <= i0) =>
   match i0 as n return (S (S j0) <= n -> dbselect n (S j0) eqT gtT ltT = gtT) with
   | 0 =>
       fun H0 : S (S j0) <= 0 =>
       let H1 : 0 = 0 -> ltT = gtT :=
         match H0 in (_ <= n) return (n = 0 -> ltT = gtT) with
         | le_n _ =>
             fun H1 : S (S j0) = 0 =>
             (fun H2 : S (S j0) = 0 =>
              let H3 : False :=
                eq_ind (S (S j0)) (fun e : nat => match e with
                                                  | 0 => False
                                                  | S _ => True
                                                  end) I 0 H2 in
              False_ind (ltT = gtT) H3) H1
         | le_S _ m H1 =>
             fun H2 : S m = 0 =>
             (fun H3 : S m = 0 =>
              let H4 : False :=
                eq_ind (S m) (fun e : nat => match e with
                                             | 0 => False
                                             | S _ => True
                                             end) I 0 H3 in
              False_ind (S (S j0) <= m -> ltT = gtT) H4) H2 H1
         end in
       H1 eq_refl
   | S i1 => fun H0 : S (S j0) <= S i1 => IHj i1 (le_S_n (S j0) i1 H0)
   end H) j i
     : forall (i j : nat) (eqT gtT ltT : Term), i > j -> dbselect i j eqT gtT ltT = gtT.

