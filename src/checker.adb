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

with Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;

with Sid;              use Sid;
with Sid.IO;           use Sid.IO;

procedure Checker
with
  SPARK_Mode => Off
is

   F          : Sid.Formula_Type;
   P          : Sid.Proof_Type;
   Result     : Sid.Result_Type;

   RV_Success : constant := 0;
   RV_Failure : constant := 10;

begin

   if Argument_Count /= 2 then
      Ada.Text_IO.Put_Line ("cnf proof");
      Set_Exit_Status (RV_Failure);
      return;
   end if;

   declare
      File_Name  : String := Argument (1);
      Proof_Name : String := Argument (2);
   begin
      Sid.IO.Read_CNF (File_Name, F);
      Sid.IO.Read_Proof (Proof_Name, P);

      Sid.Check (F, P, Result);

      case Result.Kind is
	 when Sid.Success =>
	    Ada.Text_IO.Put_Line
	      ("s VERIFIED");
	    Set_Exit_Status (RV_Success);

	 when Illegal_Shape =>
	    Ada.Text_IO.Put_Line
	      ("s NOT VERIFIED");
	    Ada.Text_IO.Put_Line
	      ("v error: illegal shape " & Integer'Image (Result.Step_ID));
	    Set_Exit_Status (RV_Failure);

	 when Non_Resolvable =>
	    Ada.Text_IO.Put_Line
	      ("s NOT VERIFIED");
	    Ada.Text_IO.Put_Line
	      ("v error: non resolvable " & Integer'Image (Result.Step_ID));
	    Set_Exit_Status (RV_Failure);

	 when No_Empty_Clause =>
	    Ada.Text_IO.Put_Line
	      ("s NOT VERIFIED");
	    Ada.Text_IO.Put_Line
	      ("v error: no empty clause");
	    Set_Exit_Status (RV_Failure);
      end case;
   end;
end Checker;
