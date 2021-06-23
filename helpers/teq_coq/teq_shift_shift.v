Definition teq_shift_shift := 
fun (i j : nat) (u : Term) =>
Term_ind
  (fun u0 : Term =>
   forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u0) = shift (S j0) (shift i0 u0))
  (fun (n i0 j0 : nat) (H : i0 <= j0) =>
   let H0 :
     dbshift i0 (dbshift j0 n) = match dbshift i0 n with
                                 | 0 => 0
                                 | S m => S (dbshift j0 m)
                                 end :=
     nat_ind
       (fun n0 : nat =>
        forall i1 j1 : nat,
        i1 <= j1 ->
        dbshift i1 (dbshift j1 n0) = match dbshift i1 n0 with
                                     | 0 => 0
                                     | S m => S (dbshift j1 m)
                                     end)
       (fun (i1 j1 : nat) (Hij : i1 <= j1) =>
        match
          i1 as n0
          return
            (n0 <= j1 ->
             dbshift n0 (dbshift j1 0) =
             match dbshift n0 0 with
             | 0 => 0
             | S m => S (dbshift j1 m)
             end)
        with
        | 0 => fun _ : 0 <= j1 => eq_refl
        | S i2 =>
            fun Hij0 : S i2 <= j1 =>
            match
              Hij0 in (_ <= n0)
              return (match dbshift n0 0 with
                      | 0 => 0
                      | S m => S (dbshift i2 m)
                      end = 0)
            with
            | le_n _ => eq_refl
            | le_S _ m _ => eq_refl
            end
        end Hij)
       (fun (n0 : nat)
          (IHn : forall i1 j1 : nat,
                 i1 <= j1 ->
                 dbshift i1 (dbshift j1 n0) =
                 match dbshift i1 n0 with
                 | 0 => 0
                 | S m => S (dbshift j1 m)
                 end) (i1 j1 : nat) (Hij : i1 <= j1) =>
        match
          i1 as n1
          return
            (n1 <= j1 ->
             dbshift n1 (dbshift j1 (S n0)) =
             match dbshift n1 (S n0) with
             | 0 => 0
             | S m => S (dbshift j1 m)
             end)
        with
        | 0 =>
            fun Hij0 : 0 <= j1 =>
            match
              j1 as n1
              return
                (0 <= n1 ->
                 dbshift 0 (dbshift n1 (S n0)) =
                 match dbshift 0 (S n0) with
                 | 0 => 0
                 | S m => S (dbshift n1 m)
                 end)
            with
            | 0 => fun _ : 0 <= 0 => eq_refl
            | S j2 => fun _ : 0 <= S j2 => eq_refl
            end Hij0
        | S i2 =>
            fun Hij0 : S i2 <= j1 =>
            match
              j1 as n1
              return
                (S i2 <= n1 ->
                 dbshift (S i2) (dbshift n1 (S n0)) =
                 match dbshift (S i2) (S n0) with
                 | 0 => 0
                 | S m => S (dbshift n1 m)
                 end)
            with
            | 0 =>
                fun Hij1 : S i2 <= 0 =>
                let H0 : 0 = 0 -> S (dbshift i2 (S n0)) = S (S (dbshift i2 n0)) :=
                  match
                    Hij1 in (_ <= n1) return (n1 = 0 -> S (dbshift i2 (S n0)) = S (S (dbshift i2 n0)))
                  with
                  | le_n _ =>
                      fun H0 : S i2 = 0 =>
                      (fun H1 : S i2 = 0 =>
                       let H2 : False :=
                         eq_ind (S i2) (fun e : nat => match e with
                                                       | 0 => False
                                                       | S _ => True
                                                       end) I 0 H1 in
                       False_ind (S (dbshift i2 (S n0)) = S (S (dbshift i2 n0))) H2) H0
                  | le_S _ m H0 =>
                      fun H1 : S m = 0 =>
                      (fun H2 : S m = 0 =>
                       let H3 : False :=
                         eq_ind (S m) (fun e : nat => match e with
                                                      | 0 => False
                                                      | S _ => True
                                                      end) I 0 H2 in
                       False_ind (S i2 <= m -> S (dbshift i2 (S n0)) = S (S (dbshift i2 n0))) H3) H1
                        H0
                  end in
                H0 eq_refl
            | S j2 =>
                fun Hij1 : S i2 <= S j2 =>
                eq_ind_r
                  (fun n1 : nat =>
                   S n1 = S match dbshift i2 n0 with
                            | 0 => 0
                            | S m => S (dbshift j2 m)
                            end) eq_refl (IHn i2 j2 (le_S_n i2 j2 Hij1))
            end Hij0
        end Hij) n i0 j0 H in
   (fun
      H1 : dbshift i0 (dbshift j0 n) = match dbshift i0 n with
                                       | 0 => 0
                                       | S m => S (dbshift j0 m)
                                       end =>
    eq_trans (f_equal (fun f : nat -> Term => f (dbshift i0 (dbshift j0 n))) eq_refl) (f_equal var H1))
     H0)
  (fun (u1 : Term)
     (IHu1 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u1) = shift (S j0) (shift i0 u1))
     (u2 : Term)
     (IHu2 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u2) = shift (S j0) (shift i0 u2))
     (u3 : Term)
     (IHu3 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u3) = shift (S j0) (shift i0 u3))
     (i0 j0 : nat) (H : i0 <= j0) =>
   eq_ind_r
     (fun t : Term =>
      tabs (shift i0 (shift j0 u1)) (shift (S i0) (shift (S j0) u2)) t =
      tabs (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2))
        (shift (S (S j0)) (shift (S i0) u3)))
     (eq_ind_r
        (fun t : Term =>
         tabs (shift i0 (shift j0 u1)) t (shift (S (S j0)) (shift (S i0) u3)) =
         tabs (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2))
           (shift (S (S j0)) (shift (S i0) u3)))
        (eq_ind_r
           (fun t : Term =>
            tabs t (shift (S (S j0)) (shift (S i0) u2)) (shift (S (S j0)) (shift (S i0) u3)) =
            tabs (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2))
              (shift (S (S j0)) (shift (S i0) u3))) eq_refl (IHu1 i0 j0 H))
        (IHu2 (S i0) (S j0) (le_n_S i0 j0 H))) (IHu3 (S i0) (S j0) (le_n_S i0 j0 H)))
  (fun (u1 : Term)
     (IHu1 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u1) = shift (S j0) (shift i0 u1))
     (u2 : Term)
     (IHu2 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u2) = shift (S j0) (shift i0 u2))
     (u3 : Term)
     (IHu3 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u3) = shift (S j0) (shift i0 u3))
     (u4 : Term)
     (IHu4 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u4) = shift (S j0) (shift i0 u4))
     (i0 j0 : nat) (H : i0 <= j0) =>
   eq_ind_r
     (fun t : Term =>
      tapp (shift i0 (shift j0 u1)) (shift (S i0) (shift (S j0) u2)) (shift i0 (shift j0 u3)) t =
      tapp (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2))
        (shift (S j0) (shift i0 u3)) (shift (S j0) (shift i0 u4)))
     (eq_ind_r
        (fun t : Term =>
         tapp (shift i0 (shift j0 u1)) (shift (S i0) (shift (S j0) u2)) t (shift (S j0) (shift i0 u4)) =
         tapp (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2))
           (shift (S j0) (shift i0 u3)) (shift (S j0) (shift i0 u4)))
        (eq_ind_r
           (fun t : Term =>
            tapp (shift i0 (shift j0 u1)) t (shift (S j0) (shift i0 u3)) (shift (S j0) (shift i0 u4)) =
            tapp (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2))
              (shift (S j0) (shift i0 u3)) (shift (S j0) (shift i0 u4)))
           (eq_ind_r
              (fun t : Term =>
               tapp t (shift (S (S j0)) (shift (S i0) u2)) (shift (S j0) (shift i0 u3))
                 (shift (S j0) (shift i0 u4)) =
               tapp (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2))
                 (shift (S j0) (shift i0 u3)) (shift (S j0) (shift i0 u4))) eq_refl 
              (IHu1 i0 j0 H)) (IHu2 (S i0) (S j0) (le_n_S i0 j0 H))) (IHu3 i0 j0 H)) 
     (IHu4 i0 j0 H))
  (fun (u1 : Term)
     (IHu1 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u1) = shift (S j0) (shift i0 u1))
     (u2 : Term)
     (IHu2 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u2) = shift (S j0) (shift i0 u2))
     (i0 j0 : nat) (H : i0 <= j0) =>
   eq_ind_r
     (fun t : Term =>
      tfun (shift i0 (shift j0 u1)) t =
      tfun (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2)))
     (eq_ind_r
        (fun t : Term =>
         tfun t (shift (S (S j0)) (shift (S i0) u2)) =
         tfun (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2))) eq_refl
        (IHu1 i0 j0 H)) (IHu2 (S i0) (S j0) (le_n_S i0 j0 H)))
  (fun (n i0 j0 : nat) (_ : i0 <= j0) => eq_refl)
  (fun (u1 : Term)
     (IHu1 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u1) = shift (S j0) (shift i0 u1))
     (u2 : Term)
     (IHu2 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u2) = shift (S j0) (shift i0 u2))
     (u3 : Term)
     (IHu3 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u3) = shift (S j0) (shift i0 u3))
     (u4 : Term)
     (IHu4 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u4) = shift (S j0) (shift i0 u4))
     (i0 j0 : nat) (H : i0 <= j0) =>
   eq_ind_r
     (fun t : Term =>
      tpair (shift i0 (shift j0 u1)) (shift (S i0) (shift (S j0) u2)) (shift i0 (shift j0 u3)) t =
      tpair (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2))
        (shift (S j0) (shift i0 u3)) (shift (S j0) (shift i0 u4)))
     (eq_ind_r
        (fun t : Term =>
         tpair (shift i0 (shift j0 u1)) (shift (S i0) (shift (S j0) u2)) t
           (shift (S j0) (shift i0 u4)) =
         tpair (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2))
           (shift (S j0) (shift i0 u3)) (shift (S j0) (shift i0 u4)))
        (eq_ind_r
           (fun t : Term =>
            tpair (shift i0 (shift j0 u1)) t (shift (S j0) (shift i0 u3)) (shift (S j0) (shift i0 u4)) =
            tpair (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2))
              (shift (S j0) (shift i0 u3)) (shift (S j0) (shift i0 u4)))
           (eq_ind_r
              (fun t : Term =>
               tpair t (shift (S (S j0)) (shift (S i0) u2)) (shift (S j0) (shift i0 u3))
                 (shift (S j0) (shift i0 u4)) =
               tpair (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2))
                 (shift (S j0) (shift i0 u3)) (shift (S j0) (shift i0 u4))) eq_refl 
              (IHu1 i0 j0 H)) (IHu2 (S i0) (S j0) (le_n_S i0 j0 H))) (IHu3 i0 j0 H)) 
     (IHu4 i0 j0 H))
  (fun (u1 : Term)
     (IHu1 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u1) = shift (S j0) (shift i0 u1))
     (u2 : Term)
     (IHu2 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u2) = shift (S j0) (shift i0 u2))
     (u3 : Term)
     (IHu3 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u3) = shift (S j0) (shift i0 u3))
     (i0 j0 : nat) (H : i0 <= j0) =>
   eq_ind_r
     (fun t : Term =>
      tp1 (shift i0 (shift j0 u1)) (shift (S i0) (shift (S j0) u2)) t =
      tp1 (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2))
        (shift (S j0) (shift i0 u3)))
     (eq_ind_r
        (fun t : Term =>
         tp1 (shift i0 (shift j0 u1)) t (shift (S j0) (shift i0 u3)) =
         tp1 (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2))
           (shift (S j0) (shift i0 u3)))
        (eq_ind_r
           (fun t : Term =>
            tp1 t (shift (S (S j0)) (shift (S i0) u2)) (shift (S j0) (shift i0 u3)) =
            tp1 (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2))
              (shift (S j0) (shift i0 u3))) eq_refl (IHu1 i0 j0 H))
        (IHu2 (S i0) (S j0) (le_n_S i0 j0 H))) (IHu3 i0 j0 H))
  (fun (u1 : Term)
     (IHu1 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u1) = shift (S j0) (shift i0 u1))
     (u2 : Term)
     (IHu2 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u2) = shift (S j0) (shift i0 u2))
     (u3 : Term)
     (IHu3 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u3) = shift (S j0) (shift i0 u3))
     (i0 j0 : nat) (H : i0 <= j0) =>
   eq_ind_r
     (fun t : Term =>
      tp2 (shift i0 (shift j0 u1)) (shift (S i0) (shift (S j0) u2)) t =
      tp2 (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2))
        (shift (S j0) (shift i0 u3)))
     (eq_ind_r
        (fun t : Term =>
         tp2 (shift i0 (shift j0 u1)) t (shift (S j0) (shift i0 u3)) =
         tp2 (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2))
           (shift (S j0) (shift i0 u3)))
        (eq_ind_r
           (fun t : Term =>
            tp2 t (shift (S (S j0)) (shift (S i0) u2)) (shift (S j0) (shift i0 u3)) =
            tp2 (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2))
              (shift (S j0) (shift i0 u3))) eq_refl (IHu1 i0 j0 H))
        (IHu2 (S i0) (S j0) (le_n_S i0 j0 H))) (IHu3 i0 j0 H))
  (fun (u1 : Term)
     (IHu1 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u1) = shift (S j0) (shift i0 u1))
     (u2 : Term)
     (IHu2 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u2) = shift (S j0) (shift i0 u2))
     (i0 j0 : nat) (H : i0 <= j0) =>
   eq_ind_r
     (fun t : Term =>
      tsum (shift i0 (shift j0 u1)) t =
      tsum (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2)))
     (eq_ind_r
        (fun t : Term =>
         tsum t (shift (S (S j0)) (shift (S i0) u2)) =
         tsum (shift (S j0) (shift i0 u1)) (shift (S (S j0)) (shift (S i0) u2))) eq_refl
        (IHu1 i0 j0 H)) (IHu2 (S i0) (S j0) (le_n_S i0 j0 H)))
  (fun (u1 : Term)
     (IHu1 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u1) = shift (S j0) (shift i0 u1))
     (u2 : Term)
     (IHu2 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u2) = shift (S j0) (shift i0 u2))
     (i0 j0 : nat) (H : i0 <= j0) =>
   eq_ind_r
     (fun t : Term =>
      trefl (shift i0 (shift j0 u1)) t =
      trefl (shift (S j0) (shift i0 u1)) (shift (S j0) (shift i0 u2)))
     (eq_ind_r
        (fun t : Term =>
         trefl t (shift (S j0) (shift i0 u2)) =
         trefl (shift (S j0) (shift i0 u1)) (shift (S j0) (shift i0 u2))) eq_refl 
        (IHu1 i0 j0 H)) (IHu2 i0 j0 H))
  (fun (u1 : Term)
     (IHu1 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u1) = shift (S j0) (shift i0 u1))
     (u2 : Term)
     (IHu2 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u2) = shift (S j0) (shift i0 u2))
     (u3 : Term)
     (IHu3 : forall i0 j0 : nat, i0 <= j0 -> shift i0 (shift j0 u3) = shift (S j0) (shift i0 u3))
     (i0 j0 : nat) (H : i0 <= j0) =>
   eq_ind_r
     (fun t : Term =>
      teq (shift i0 (shift j0 u1)) (shift i0 (shift j0 u2)) t =
      teq (shift (S j0) (shift i0 u1)) (shift (S j0) (shift i0 u2)) (shift (S j0) (shift i0 u3)))
     (eq_ind_r
        (fun t : Term =>
         teq (shift i0 (shift j0 u1)) t (shift (S j0) (shift i0 u3)) =
         teq (shift (S j0) (shift i0 u1)) (shift (S j0) (shift i0 u2)) (shift (S j0) (shift i0 u3)))
        (eq_ind_r
           (fun t : Term =>
            teq t (shift (S j0) (shift i0 u2)) (shift (S j0) (shift i0 u3)) =
            teq (shift (S j0) (shift i0 u1)) (shift (S j0) (shift i0 u2)) (shift (S j0) (shift i0 u3)))
           eq_refl (IHu1 i0 j0 H)) (IHu2 i0 j0 H)) (IHu3 i0 j0 H)) u i j
     : forall (i j : nat) (u : Term), i <= j -> shift i (shift j u) = shift (S j) (shift i u).
