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
  -- with SPARK_Mode => Off
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

   procedure Equivalent_Transitivity
     (F : Formula_Type;
      A1, A2, A3 : Assignment_Type)
   is null;

   procedure RUP_Lemma
     (A  : in Assignment_Type;
      Ap : in Assignment_Type;
      F  : in Formula_Type;
      C  : in Clause_Type)
   is null;

   procedure Propagate_Lemma
     (A  : in Assignment_Type;
      Ap : in Assignment_Type;
      F  : in Formula_Type)
   is null;

   procedure Equivalent_Reflexive
     (F : Formula_Type;
      A : Assignment_Type)
   is null;
end Sid.Lemmas;
