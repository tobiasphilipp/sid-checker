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

   Result     : Sid.Result_Type;

   RV_Success : constant := 0;
   RV_Failure : constant := 10;

begin

   if Argument_Count /= 3 then
      Ada.Text_IO.Put_Line ("type cnf proof");
      Set_Exit_Status (RV_Failure);
      return;
   end if;

   declare
      Proof_Type : String := Argument (1);
      File_Name  : String := Argument (2);
      Proof_Name : String := Argument (3);
   begin

      if Proof_Type = "resolution" then
	 declare
	    F : Sid.Formula_Type;
	    P : Sid.Proof_Type;
	 begin
	    Sid.IO.Read_CNF (File_Name, F);
	    Sid.IO.Read_Proof (Proof_Name, P);

	    Sid.Check_Resolution_Proof (F, P, Result);
	 end;

      elsif Proof_Type = "rup" then
	 declare
	    F : Sid.Formula_Type;
	    P : Sid.Formula_Type;
	 begin
	    Sid.IO.Read_CNF (File_Name, F);
	    Sid.IO.Read_CNF (Proof_Name, P);

	    Sid.Check_RUP_Proof (F, P, Result);
	 end;
      end if;

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
