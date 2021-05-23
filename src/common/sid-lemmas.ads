------------------------------------------------------------------------------
--                                                                          --
-- A verified resolution checker written in SPARK 2014 based on functional  --
-- data structures.                                                         --
--                                                                          --
------------------------------------------------------------------------------
--                                                                          --
-- Copyright (C) 2021, Tobias Philipp                                       --
--                                                                          --
------------------------------------------------------------------------------

package Sid.Lemmas
  with SPARK_Mode => On,
  Annotate => (GNATprove, Terminating),
  Ghost
is
   use type Literal_Type;

   -- The addition of a resolvent preserves equisatisfiability.
   procedure Resolvent_Redundancy
     (F : Formula_Type;
      C : Clause_Type;
      D : Clause_Type;
      L : Literal_Type;
      R : Clause_Type)
   with
     Pre => Contains (F, C) and then
            Contains (F, D) and then
            Resolve_Spec (C, D, L, R),
     Post => Equisatisfiable (F, Clause_Vector.Add (F, R));

   -- If a formula contains the empty clause, it is unsatisfiable.
   procedure Unsatisfiable_Empty_Clause
     (F : Formula_Type)
   with
     Pre  => Contains (F, Empty_Clause),
     Post => not Satisfiable (F);

   -- Equisatisfiability is transitive.
   procedure Equisatisfiability_Transitivity
     (F, G, H : Formula_Type)
   with
     Pre  => Equisatisfiable (F, G) and then Equisatisfiable (G, H),
     Post => Equisatisfiable (F, H);

   procedure Equivalent_Transitivity
     (F : Formula_Type;
      A1, A2, A3 : Assignment_Type)
   with
     Pre => Equivalent (A1, A2, F, F) and then Equivalent (A2, A3, F, F),
     Post =>  Equivalent (A1, A3, F, F),
     Ghost;

   procedure Equivalent_Reflexive
     (F : Formula_Type;
      A : Assignment_Type)
   with
     Post =>  Equivalent (A, A, F, F),
     Ghost;


   -- A /\ F   EQUIV  A[L] /\ F if L is propagates from F and A
   procedure Propagate_Lemma
     (A  : in Assignment_Type;
      Ap : in Assignment_Type;
      F  : in Formula_Type)
   with
     Pre  => Assignment_Vector.Last (A) < Positive'Last and then Propagate (A, Ap, F),
     Post => Equivalent (A, Ap, F, F),
     Ghost;

   procedure RUP_Lemma
     (A  : in Assignment_Type;
      Ap : in Assignment_Type;
      F  : in Formula_Type;
      C  : in Clause_Type)
   with
     Pre  => Has_Empty_Clause (F, Ap) and
             Equivalent (A, Ap, F, F) and
             Assignment_Clause_Rel (A, C),
     Post => Equisatisfiable (F, Clause_Vector.Add (F, C)),
     Ghost;

end Sid.Lemmas;
