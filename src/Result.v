Inductive result (A E: Type) : Type :=
| Success (x : A)
| Error (error : E).

Arguments Success [A E].
Arguments Error [A E].
