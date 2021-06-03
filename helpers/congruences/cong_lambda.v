Definition cong_lambda := 
fun (A1 A2 : Type) (B1 : A1 -> Type) (B2 : A2 -> Type) (f1 : forall x : A1, B1 x)
  (f2 : forall x : A2, B2 x) (pA : A1 ≅ A2)
  (hB : forall p : Pack A1 A2, B1 (ProjT1 p) ≅ B2 (ProjT2 p))
  (hf : forall p : Pack A1 A2, f1 (ProjT1 p) ≅ f2 (ProjT2 p)) =>
match pA with
| @heqPair _ _ _ _ pT pA0 =>
    let pA1 : transport eq_refl A1 = A2 :=
      Logic.eq_ind pT (fun pT0 : Type = Type => transport pT0 A1 = A2) pA0 eq_refl (K pT) in
    match
      pA1 in (_ = y)
      return
        (forall (B3 : y -> Type) (f3 : forall x : y, B3 x),
         (forall p : Pack A1 y, B1 (ProjT1 p) ≅ B3 (ProjT2 p)) ->
         (forall p : Pack A1 y, f1 (ProjT1 p) ≅ f3 (ProjT2 p)) ->
         (fun x : A1 => f1 x) ≅ (fun x : y => f3 x))
    with
    | eq_refl =>
        fun (B3 : A1 -> Type) (f3 : forall x : A1, B3 x)
          (hB0 : forall p : Pack A1 A1, B1 (ProjT1 p) ≅ B3 (ProjT2 p))
          (hf0 : forall p : Pack A1 A1, f1 (ProjT1 p) ≅ f3 (ProjT2 p)) =>
        let pB : B1 = B3 :=
          funext
            (fun x : A1 =>
             let h :
               B1 (ProjT1 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |})
               ≅ B3 (ProjT2 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |}) :=
               hB0 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |} in
             match h with
             | @heqPair _ _ _ _ pT0 pB =>
                 let pB0 :
                   transport eq_refl
                     (B1 (ProjT1 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |})) =
                   B3 (ProjT2 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |}) :=
                   Logic.eq_ind pT0
                     (fun pT1 : Type = Type =>
                      transport pT1 (B1 (ProjT1 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |})) =
                      B3 (ProjT2 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |})) pB eq_refl
                     (K pT0) in
                 pB0
             end) in
        match
          pB in (_ = y)
          return
            (forall f4 : forall x : A1, y x,
             (forall p : Pack A1 A1, B1 (ProjT1 p) ≅ y (ProjT2 p)) ->
             (forall p : Pack A1 A1, f1 (ProjT1 p) ≅ f4 (ProjT2 p)) ->
             (fun x : A1 => f1 x) ≅ (fun x : A1 => f4 x))
        with
        | eq_refl =>
            fun (f4 : forall x : A1, B1 x) (_ : forall p : Pack A1 A1, B1 (ProjT1 p) ≅ B1 (ProjT2 p))
              (hf1 : forall p : Pack A1 A1, f1 (ProjT1 p) ≅ f4 (ProjT2 p)) =>
            heqPair (fun x : A1 => f1 x) (fun x : A1 => f4 x) eq_refl
              (funext
                 (fun x : A1 =>
                  let h :
                    f1 (ProjT1 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |})
                    ≅ f4 (ProjT2 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |}) :=
                    hf1 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |} in
                  match h with
                  | @heqPair _ _ _ _ p pf =>
                      let pf0 :
                        transport eq_refl
                          (f1 (ProjT1 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |})) =
                        f4 (ProjT2 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |}) :=
                        Logic.eq_ind p
                          (fun
                             p0 : B1 (ProjT1 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |}) =
                                  B1 (ProjT1 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |}) =>
                           transport p0
                             (f1 (ProjT1 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |})) =
                           f4 (ProjT2 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |})) pf
                          eq_refl (K p) in
                      pf0
                  end))
        end f3 hB0 hf0
    end B2 f2 hB hf
end
     : forall (A1 A2 : Type) (B1 : A1 -> Type) (B2 : A2 -> Type) (f1 : forall x : A1, B1 x)
         (f2 : forall x : A2, B2 x),
       A1 ≅ A2 ->
       (forall p : Pack A1 A2, B1 (ProjT1 p) ≅ B2 (ProjT2 p)) ->
       (forall p : Pack A1 A2, f1 (ProjT1 p) ≅ f2 (ProjT2 p)) ->
       (fun x : A1 => f1 x) ≅ (fun x : A2 => f2 x).

