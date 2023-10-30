Parameter bytes32: Set.
Parameter address: Set.

Axiom address_eq_dec : forall (x y: address), {x = y} + {x <> y}.

Module Mapping.
  Parameter mapping : Set -> Set -> Set.
  Definition t := mapping.
  Section Def.
    Variable K V : Set.
    Parameter empty : mapping K V.
    Parameter find : K -> mapping K V -> option V.
    Parameter delete : K -> mapping K V -> mapping K V.
    Parameter upsert : K -> V -> mapping K V -> mapping K V.
    Definition unit k v := upsert k v empty.
  End Def.

  Arguments empty {K V}.
  Arguments find [K V].
  Arguments delete [K V].
  Arguments upsert [K V].
  Arguments unit [K V].
End Mapping.

Definition mapping := Mapping.t.
