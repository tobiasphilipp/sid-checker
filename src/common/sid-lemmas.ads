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

end Sid.Lemmas;
