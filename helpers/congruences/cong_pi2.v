Definition cong_pi2 := 
fun (A1 A2 : Type) (B1 : A1 -> Type) (B2 : A2 -> Type) (p1 : ∑ x : A1, B1 x) 
  (p2 : ∑ x : A2, B2 x) (hA : A1 ≅ A2) (hB : forall p : Pack A1 A2, B1 (ProjT1 p) ≅ B2 (ProjT2 p))
  (hp : p1 ≅ p2) =>
match hA with
| @heqPair _ _ _ _ pT pA =>
    let pA0 : transport eq_refl A1 = A2 :=
      Logic.eq_ind pT (fun pT0 : Type = Type => transport pT0 A1 = A2) pA eq_refl (K pT) in
    match
      pA0 in (_ = y)
      return
        (forall (B3 : y -> Type) (p3 : ∑ x : y, B3 x),
         (forall p : Pack A1 y, B1 (ProjT1 p) ≅ B3 (ProjT2 p)) -> p1 ≅ p3 -> pi2 p1 ≅ pi2 p3)
    with
    | eq_refl =>
        fun (B3 : A1 -> Type) (p3 : ∑ x : A1, B3 x)
          (hB0 : forall p : Pack A1 A1, B1 (ProjT1 p) ≅ B3 (ProjT2 p)) (hp0 : p1 ≅ p3) =>
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
            (forall p4 : ∑ x : A1, y x,
             (forall p : Pack A1 A1, B1 (ProjT1 p) ≅ y (ProjT2 p)) -> p1 ≅ p4 -> pi2 p1 ≅ pi2 p4)
        with
        | eq_refl =>
            fun (p4 : ∑ x : A1, B1 x) (_ : forall p : Pack A1 A1, B1 (ProjT1 p) ≅ B1 (ProjT2 p))
              (hp1 : p1 ≅ p4) =>
            match hp1 with
            | @heqPair _ _ _ _ pT0 pp =>
                let pp0 : transport eq_refl p1 = p4 :=
                  Logic.eq_ind pT0
                    (fun pT1 : (∑ x : A1, B1 x) = (∑ x : A1, B1 x) => transport pT1 p1 = p4) pp
                    eq_refl (K pT0) in
                match pp0 in (_ = y) return (pi2 p1 ≅ pi2 y) with
                | eq_refl => heq_refl (pi2 p1)
                end
            end
        end p3 hB0 hp0
    end B2 p2 hB hp
end
     : forall (A1 A2 : Type) (B1 : A1 -> Type) (B2 : A2 -> Type) (p1 : ∑ x : A1, B1 x)
         (p2 : ∑ x : A2, B2 x),
       A1 ≅ A2 -> (forall p : Pack A1 A2, B1 (ProjT1 p) ≅ B2 (ProjT2 p)) -> p1 ≅ p2 -> pi2 p1 ≅ pi2 p2.
