Definition cong_app := 
fun (A1 A2 : Type) (B1 : A1 -> Type) (B2 : A2 -> Type) (f1 : forall x : A1, B1 x)
  (f2 : forall x : A2, B2 x) (u1 : A1) (u2 : A2) (pA : A1 ≅ A2)
  (hB : forall p : Pack A1 A2, B1 (ProjT1 p) ≅ B2 (ProjT2 p)) (pf : f1 ≅ f2) 
  (pu : u1 ≅ u2) =>
match pA with
| @heqPair _ _ _ _ pT pA0 =>
    let pA1 : transport eq_refl A1 = A2 :=
      Logic.eq_ind pT (fun pT0 : Type = Type => transport pT0 A1 = A2) pA0 eq_refl (K pT) in
    match
      pA1 in (_ = y)
      return
        (forall (B3 : y -> Type) (f3 : forall x : y, B3 x) (u3 : y),
         (forall p : Pack A1 y, B1 (ProjT1 p) ≅ B3 (ProjT2 p)) -> f1 ≅ f3 -> u1 ≅ u3 -> f1 u1 ≅ f3 u3)
    with
    | eq_refl =>
        fun (B3 : A1 -> Type) (f3 : forall x : A1, B3 x) (u3 : A1)
          (hB0 : forall p : Pack A1 A1, B1 (ProjT1 p) ≅ B3 (ProjT2 p)) (pf0 : f1 ≅ f3) 
          (pu0 : u1 ≅ u3) =>
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
             (forall p : Pack A1 A1, B1 (ProjT1 p) ≅ y (ProjT2 p)) -> f1 ≅ f4 -> f1 u1 ≅ f4 u3)
        with
        | eq_refl =>
            fun (f4 : forall x : A1, B1 x) (_ : forall p : Pack A1 A1, B1 (ProjT1 p) ≅ B1 (ProjT2 p))
              (pf1 : f1 ≅ f4) =>
            match pf1 with
            | @heqPair _ _ _ _ p pf2 =>
                let pf3 : transport eq_refl f1 = f4 :=
                  Logic.eq_ind p
                    (fun p0 : (forall x : A1, B1 x) = (forall x : A1, B1 x) => transport p0 f1 = f4)
                    pf2 eq_refl (K p) in
                match pf3 in (_ = y) return (f1 u1 ≅ y u3) with
                | eq_refl =>
                    match pu0 with
                    | @heqPair _ _ _ _ p0 pu1 =>
                        let pu2 : transport eq_refl u1 = u3 :=
                          Logic.eq_ind p0 (fun p1 : A1 = A1 => transport p1 u1 = u3) pu1 eq_refl
                            (K p0) in
                        match pu2 in (_ = y) return (f1 u1 ≅ f1 y) with
                        | eq_refl => heq_refl (f1 u1)
                        end
                    end
                end
            end
        end f3 hB0 pf0
    end B2 f2 u2 hB pf pu
end
     : forall (A1 A2 : Type) (B1 : A1 -> Type) (B2 : A2 -> Type) (f1 : forall x : A1, B1 x)
         (f2 : forall x : A2, B2 x) (u1 : A1) (u2 : A2),
       A1 ≅ A2 ->
       (forall p : Pack A1 A2, B1 (ProjT1 p) ≅ B2 (ProjT2 p)) -> f1 ≅ f2 -> u1 ≅ u2 -> f1 u1 ≅ f2 u2.
