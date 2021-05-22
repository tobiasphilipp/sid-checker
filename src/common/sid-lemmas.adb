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

package body Sid.Lemmas
  -- We do not provide proofs and turns off SPARK mode in this package
  -- to make the VC report more clear.
  with SPARK_Mode => Off
is
   procedure Resolvent_Redundancy
     (F : Formula_Type;
      C : Clause_Type;
      D : Clause_Type;
      L : Literal_Type;
      R : Clause_Type)
   is null;

   procedure Unsatisfiable_Empty_Clause
     (F : Formula_Type)
   is null;

   procedure Equisatisfiability_Transitivity
     (F, G, H : Formula_Type)
   is null;

end Sid.Lemmas;
