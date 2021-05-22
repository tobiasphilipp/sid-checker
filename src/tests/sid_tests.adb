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

with AUnit;              use AUnit;
with AUnit.Test_Cases;   use AUnit.Test_Cases;
with AUnit.Assertions;   use AUnit.Assertions;

with Ada.Text_IO;

with Sid;                use Sid;

package body Sid_Tests
  with SPARK_Mode => Off
is

   -- --------------------------------------------------------------------------

   procedure Test_Literal (T : in out Test_Cases.Test_Case'Class)
   is
      L : Literal_Type := 5;
   begin
      Assert (Compl (L) = -5,
	      "Complement does not give expected result");

      Assert (Compl (Compl (L)) = L,
	      "Complement of complement of a literal equals the literal");
   end Test_Literal;

   -- --------------------------------------------------------------------------

   procedure Test_Clause (T : in out Test_Cases.Test_Case'Class)
   is
      C : Clause_Type (0 .. 2) := (1, 2, -3);
      D : Clause_Type (0 .. 1) := (-3, 1);
      E : Clause_Type (0 .. 3) := (1, 2, -3, 2);
      F : Clause_Type (0 .. 1) := (3, 2);
      R : Clause_Type (0 .. 1) := (1, 2);
   begin
      Assert (Appears (C, 1),
	      "literal 1 appears in clause");

      Assert (not Appears (C, -1),
	      "literal -1 does not appear in clause");

      Assert (not Subset (C, D),
	      "subset incorrect");

      Assert (Subset (D, C),
	      "subset incorrect");

      Assert (Equivalent (C, E),
	      "subset equivalence");

      Assert (not Equivalent (D, E),
	      "subset equivalence");

      Assert (Resolve_Spec(D, F, -3, R),
	      "resolution spec");

      Assert (Has_No_Duplicates (C),
	      "clause has no duplicates");

      Assert (not Has_No_Duplicates (E),
	      "clause has duplicates");

      Assert (Remove_Duplicate_Literals (E) = C,
	     "removing duplicate literals");

      Assert (Equivalent (C, E),
	      "equivalence");

      Assert (Remove_Duplicate_Literals (Resolve (C, F, -3)) = R,
	      "resolution");
   end Test_Clause;

   -- --------------------------------------------------------------------------

   -- We do not show completeness; this should be demonstrated by real world
   -- examples
   procedure Test_Check_Success (T : in out Test_Cases.Test_Case'Class)
   is
      F : Formula_Type;
      P : Proof_Type;
      R : Result_Type;

      procedure Create_Formula
      is
	 C1 : Clause_Type (0 .. 2) := (1, 2, -3);
	 C2 : Clause_Type (0 .. 1) := (1, -2);
	 C3 : Clause_Type (0 .. 1) := (-1, 3);
	 C4 : Clause_Type (0 .. 0) := (1 => -3);
	 C5 : Clause_Type (0 .. 0) := (0 => 2);
	 C6 : Clause_Type (0 .. 4) := (5, 6, 7, 8, 9); -- placeholder
	 C7 : Clause_Type (0 .. 4) := (5, 6, 7, 8, 9); -- placeholder
	 C8 : Clause_Type (0 .. 4) := (5, 6, 7, 8, 9); -- placeholder
	 C9 : Clause_Type (0 .. 4) := (5, 6, 7, 8, 9); -- placeholder

	 procedure Add (C : Clause_Type)
	 is
	 begin
	    F := Clause_Vector.Add (F, C);
	 end Add;

      begin

	 Add (C1);
	 Add (C2);
	 Add (C3);
	 Add (C4);
	 Add (C5);
	 Add (C6);
	 Add (C7);
	 Add (C8);
	 Add (C9);
      end Create_Formula;

      procedure Create_Proof
      is
	 P10 : Proof_Step_Type := Proof_Step_Type'
	   (C_Ref => 1, D_Ref => 2, Lit => 2); -- 1 -3 0

	 P11 : Proof_Step_Type := Proof_Step_Type'
	   (C_Ref => 2, D_Ref => 3, Lit => 1); -- -2 3 0

	 P12 : Proof_Step_Type := Proof_Step_Type'
	   (C_Ref => 11, D_Ref => 4, Lit => 3); -- -2 0

	 P13 : Proof_Step_Type := Proof_Step_Type'
	   (C_Ref => 12, D_Ref => 5, Lit => -2); -- empty

	 procedure Add (X : Proof_Step_Type)
	 is
	 begin
	    P := Proof_Step_Vector.Add (P, X);
	 end Add;

      begin
	 Add(P10);
	 Add(P11);
	 Add(P12);
	 Add(P13); -- no empty clause

      end Create_Proof;

   begin
      Create_Formula;
      Create_Proof;

      Check (F, P, R);

      Assert (R.Kind = Success,
	     "P is a correct proof");
   end Test_Check_Success;

   -- --------------------------------------------------------------------------

   procedure Register_Tests
     (T : in out Sid_Test)
   is
   begin
      Registration.Register_Routine
	(T,
	 Test_Literal'Access,
	 "Test literals");

      Registration.Register_Routine
	(T,
	 Test_Clause'Access,
	 "Test clause");

      Registration.Register_Routine
	(T,
	 Test_Check_Success'Access,
	 "Test successfull checking");
   end Register_Tests;

   -- --------------------------------------------------------------------------

   function Name
     (T : Sid_Test) return Message_String
   is
   begin
      return Format ("Sid Checker Tests");
   end Name;

end Sid_Tests;
