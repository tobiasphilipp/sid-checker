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
with Ada.Streams.Stream_IO; use Ada.Streams.Stream_IO;
with Ada.Containers.Vectors;

package body Sid.IO
  -- As this package handles IO, we turn off verification conditions
  with SPARK_Mode => Off
is

   -- --------------------------------------------------------------------------

   procedure Read_CNF
     (File_Name  : in     String;
      Formula : in out Formula_Type)
   is
      F         : File_Type;
      S         : Stream_Access;

      procedure Consume
      is
	 package P is new Ada.Containers.Vectors
	   (Index_Type   => Natural,
	    Element_Type => Integer);

	 Vec : P.Vector := P.Empty_Vector;

	 Lit : Integer := Integer'Input (S);
      begin
	 while not End_Of_File (F) and then Lit /= 0 loop
	    P.Append (Container => Vec,
		      New_Item  => Lit);

	    Lit := Integer'Input (S);
	 end loop;

	 -- Translate into clause
	 declare
	    C : Clause_Type (0 .. Integer(P.Length (Vec)) - 1);
	    I : Natural := C'First;
	 begin
	    for Lit of Vec loop
	       C (I) := Literal_Type(Lit);
	       I := I + 1;
	    end loop;

	    Formula := Clause_Vector.Add (Formula, C);
	 end;


      end Consume;

   begin
      Open (F, In_File, File_Name);

      S := Stream (F);

      while not End_Of_File (F) loop
	 Consume;
      end loop;

      Close (F);
   end Read_CNF;

   -- --------------------------------------------------------------------------

   procedure Write_CNF
     (File_Name  : in String;
      Formula  : in Formula_Type)
   is
      F         : File_Type;
      S         : Stream_Access;
   begin
      Open (F, Out_File, File_Name);
      S := Stream (F);

      for I in 1 .. Clause_Vector.Length (Formula) loop
	 declare
	    C : Clause_Type := Clause_Vector.Get (Formula, Integer(I));
	 begin
	    for Lit of C loop
	       Integer'Write (S, Integer(Lit));
	    end loop;

	    Integer'Write (S, 0);
	 end;
      end loop;

      Close (F);
   end Write_CNF;

   procedure Read_Proof
     (File_Name : in     String;
      Proof     : in out Proof_Type)
   is
      F         : File_Type;
      S         : Stream_Access;

   begin
      Open (F, In_File, File_Name);

      S := Stream (F);

      while not End_Of_File (F) loop
	 Proof := Proof_Step_Vector.Add
	   (Proof,
	    Proof_Step_Type'(C_Ref => Integer'Input (S),
			     D_Ref => Integer'Input (S),
			     Lit   => Literal_Type(Integer'Input (S))));
      end loop;

      Close (F);
   end Read_Proof;

   -- --------------------------------------------------------------------------

   procedure Write_Proof
     (File_Name : in String;
      Proof     : in Proof_Type)
   is
      F         : File_Type;
      S         : Stream_Access;
   begin
      Open (F, Out_File, File_Name);
      S := Stream (F);

      for I in 1 .. Proof_Step_Vector.Length (Proof) loop
	 declare
	    C : Proof_Step_Type := Proof_Step_Vector.Get (Proof, Integer(I));
	 begin
	    Integer'Write (S, C.C_Ref);
	    Integer'Write (S, C.D_Ref);
	    Integer'Write (S, Integer(C.Lit));
	 end;
      end loop;

      Close (F);

   end Write_Proof;

end Sid.IO;
