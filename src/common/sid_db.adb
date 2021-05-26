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

package body Sid_DB
  with SPARK_Mode => On,
  Refined_State => (The_DB => (Contents, Number_Clauses, Formula, Indices))
is

   -- --------------------------------------------------------------------------

   procedure Insert
     (Clause  : in     Clause_Type;
      Result  :    out Insert_Result_Type)
   is
      use type Ada.Containers.Count_Type;
      Index : Positive;
   begin

      -- All index positions are within the container bounds
      pragma Assert
	(for all I of Indices => I < Natural (P.Length (Contents)));

      pragma Assert
	(for all I of Indices =>
	   P.Element (Contents, I) > 0 and P.Element (Contents, I) <= Max_Clause_Size);


      if P.Length (Contents) >= P.Capacity (Contents) then
        if P.Capacity (Contents) + Clause'Length + 1 < Ada.Containers.Count_Type'Last / 2 then
	 P.Reserve_Capacity (Container => Contents,
			     Capacity  => Clause'Length + 1 + P.Capacity (Contents) * 2);
        else
	   Result := Insert_Result_Type' (Success => False);
	   return;
        end if;
      end if;

      -- All index positions are within the container bounds
      pragma Assert
	(for all I of Indices => I < Natural (P.Length (Contents)));

      pragma Assert
	(for all I of Indices =>
	   P.Element (Contents, I) > 0 and P.Element (Contents, I) <= Max_Clause_Size);


      pragma Assert (P.Length (Contents) + Clause'Length + 1 < P.Capacity (Contents));

      P.Append (Container => Contents,
		New_Item  => Clause'Length);

      Index := P.Last_Index (Contents);
      pragma Assert (P.Element (Contents, Index) = Clause'Length);
      pragma Assert (Clause'Length <= Max_Clause_Size);
      pragma Assert (P.Element (Contents, Index) > 0 and P.Element (Contents, Index) <= Max_Clause_Size);

      pragma Assert (Index <= Natural (P.Length (Contents)));

      for I in Clause'First .. Clause'Last
      loop
	 P.Append (Container => Contents,
		   New_Item => Clause (I));

	 pragma Assert (Clause (I) /= 0);
	 pragma Assert (Clause (I) > -2**31 + 1);
	 pragma Assert (Clause (I) < 2**31 - 1);

	 pragma Loop_Invariant (Natural (P.Length (Contents))'Loop_entry + I + 1 = Natural (P.Length (Contents)));

	 pragma Loop_Invariant (Natural (P.Length (Contents)) - I + Clause'Length + 1 < Natural (P.Capacity (Contents)));
	 pragma Loop_Invariant (Natural (P.Length (Contents)'Loop_entry) < Natural (P.Length (Contents)));

	 pragma Loop_Invariant (for all I of Indices => P.Element (Contents, I) > 0 and P.Element (Contents, I) <= Max_Clause_Size);

	 pragma Loop_Invariant (P.Element (Contents, Index) > 0 and P.Element (Contents, Index) = Clause'Length);

	 -- All indices and lengths are within the container bounds
	 pragma Loop_Invariant (for all I of Indices => I + P.Element (Contents, I) <= Natural (P.Length (Contents)));

	 pragma Loop_Invariant (for all I of Indices => (for all J in 1 .. P.Element (Contents, I) =>
	 					   P.Element (Contents, I + J) /= 0 and
	 					   P.Element (Contents, I + J) > -2**31 + 1 and
	 					   P.Element (Contents, I + J) < 2**31 - 1));


	 pragma Loop_Invariant (for all J in 1 .. I + 1 =>
				  P.Element (Contents, Index + J) /= 0 and
				  P.Element (Contents, Index + J) > -2**31 + 1 and
				  P.Element (Contents, Index + J) < 2**31 - 1);


	 pragma Loop_Invariant (for all J in Clause'First .. I =>
				     P.Element (Contents, Index + 1 + J) /= 0 and
				     P.Element (Contents, Index + 1 + J) > -2**31 + 1 and
				  P.Element (Contents, Index + 1 + J) < 2**31 - 1);


	 pragma Loop_Invariant (for all I in 1 .. Indices_Seq.Last (Indices) =>
	    I <= Clause_Vector.Last (Formula) and then
	    Clause_Vector.Get (Formula, I)'Length = P.Element (Contents, Indices_Seq.Get (Indices, I)) and then
	       (for all J in 1 .. Clause_Vector.Get (Formula, I)'Length =>
	 	  Clause_Vector.Get (Formula, I)(J - 1) = P.Element (Contents, Indices_Seq.Get (Indices, I) + J)));

	 pragma Loop_Invariant (for all J in Clause'First .. I =>
		  Clause (J) = P.Element (Contents, Index + J + 1));
      end loop;

      pragma Assert (for all J in Clause'First .. Clause'Last =>
		       P.Element (Contents, Index + 1 + J) /= 0 and
		       P.Element (Contents, Index + 1 + J) > -2**31 + 1 and
		       P.Element (Contents, Index + 1 + J) < 2**31 - 1);


      pragma Assert (Index <= Natural (P.Length (Contents)));

             -- After indices, we have correct literals
      pragma Assert (for all I of Indices => (for all J in 1 .. P.Element (Contents, I) =>
				     P.Element (Contents, I + J) /= 0 and
				     P.Element (Contents, I + J) > -2**31 + 1 and
				     P.Element (Contents, I + J) < 2**31 - 1));

      -- After indices, we have correct literals
      pragma Assert ((for all J in 1 .. P.Element (Contents, Index) =>
				     P.Element (Contents, Index + J) /= 0 and
				     P.Element (Contents, Index + J) > -2**31 + 1 and
			P.Element (Contents, Index + J) < 2**31 - 1));


      pragma Assert (for all I in 1 .. Indices_Seq.Last (Indices) =>
	    I <= Clause_Vector.Last (Formula) and then
	    Clause_Vector.Get (Formula, I)'Length = P.Element (Contents, Indices_Seq.Get (Indices, I)) and then
	       (for all J in 1 .. Clause_Vector.Get (Formula, I)'Length =>
		  Clause_Vector.Get (Formula, I)(J - 1) = P.Element (Contents, Indices_Seq.Get (Indices, I) + J)));

      pragma Assert  (for all J in 1 .. Clause'Length =>
		  Clause(J - 1) = P.Element (Contents, Index + J));

      Result := Insert_Result_Type' (Success => True,
				     Index => Index);

      Number_Clauses := Number_Clauses + 1;

      Indices := Indices_Seq.Add (Indices, Index);
      Formula := Clause_Vector.Add (Formula, Clause);

      pragma Assert (Number_Clauses = Natural (Indices_Seq.Length (Indices)));
      pragma Assert (Number_Clauses = Natural (Clause_Vector.Length (Formula)));



       -- All index positions are within the container bounds
      pragma Assert (for all I of Indices => I < Natural (P.Length (Contents)));
       -- At index position we have the length argument and of correct size
      pragma Assert (for all I of Indices => P.Element (Contents, I) > 0 and P.Element (Contents, I) <= Max_Clause_Size);
       -- All indices and lengths are within the container bounds
      pragma Assert (for all I of Indices => I + P.Element (Contents, I) <= Natural (P.Length (Contents)));


      -- After indices, we have correct literals
      pragma Assert (for all I of Indices => (for all J in 1 .. P.Element (Contents, I) =>
				     P.Element (Contents, I + J) /= 0));
      
      -- After indices, we have correct literals
      pragma Assert (for all I of Indices => (for all J in 1 .. P.Element (Contents, I) =>
				     P.Element (Contents, I + J) /= 0 and
				     P.Element (Contents, I + J) > -2**31 + 1));

      -- After indices, we have correct literals
      pragma Assert (for all I of Indices => (for all J in 1 .. P.Element (Contents, I) =>
				     P.Element (Contents, I + J) /= 0 and
				     P.Element (Contents, I + J) > -2**31 + 1 and
				     P.Element (Contents, I + J) < 2**31 - 1));

      
       -- After indices, we have correct literals
      pragma Assert (for all I of Indices => (for all J in 1 .. P.Element (Contents, I) =>
				     P.Element (Contents, I + J) /= 0 and
				     P.Element (Contents, I + J) > -2**31 + 1 and

						P.Element (Contents, I + J) < 2**31 - 1));

      pragma Assert (for all I in 1 .. Indices_Seq.Last (Indices) - 1 =>
	    I <= Clause_Vector.Last (Formula) and then
	    Clause_Vector.Get (Formula, I)'Length = P.Element (Contents, Indices_Seq.Get (Indices, I)) and then
	       (for all J in 1 .. Clause_Vector.Get (Formula, I)'Length =>
		  Clause_Vector.Get (Formula, I)(J - 1) = P.Element (Contents, Indices_Seq.Get (Indices, I) + J)));

      pragma Assert (
	    Indices_Seq.Last (Indices) <= Clause_Vector.Last (Formula) and then
	    Clause_Vector.Get (Formula, Indices_Seq.Last (Indices))'Length = P.Element (Contents, Indices_Seq.Get (Indices, Indices_Seq.Last (Indices))));



      pragma Assert (for all I in 1 .. Indices_Seq.Last (Indices) =>
	    I <= Clause_Vector.Last (Formula) and then
	    Clause_Vector.Get (Formula, I)'Length = P.Element (Contents, Indices_Seq.Get (Indices, I)) and then
	       (for all J in 1 .. Clause_Vector.Get (Formula, I)'Length =>
		  Clause_Vector.Get (Formula, I)(J - 1) = P.Element (Contents, Indices_Seq.Get (Indices, I) + J)));
   end Insert;

   -- --------------------------------------------------------------------------

   procedure Clear
   is
      use type Ada.Containers.Count_Type;
      F : Formula_Type;
      I : Indices_Seq.Sequence;

   begin
      P.Clear (Contents);

      Formula := F;
      Indices := I;
      Number_Clauses := 0;

   end Clear;

   -- --------------------------------------------------------------------------

   function Element
     (Index : Positive)
     return Clause_Type
   is
      L : constant Natural := P.Element (Contents, Index);
      R :  Clause_Type (0 .. L - 1) := (others => Magic_Literal);
   begin

      for I in 1 .. L
      loop
   	 R (I - 1) := P.Element (Contents, Index + I);
	 pragma Loop_Invariant (for all J in 1 .. I =>
				  R (J - 1) = P.Element (Contents, Index + J));
      end loop;

      return R;
   end Element;

   -- --------------------------------------------------------------------------

   procedure Swap
     (Clause_Index : Positive;
      I, J         : Natural)
   is
      L1 : Literal_Type := Element (Clause_Index, I);
      L2 : Literal_Type := Element (Clause_Index, J);
   begin
      P.Replace_Element (Contents, Clause_Index + 1 + J, L1);
      P.Replace_Element (Contents, Clause_Index + 1 + I, L2);
   end Swap;


end Sid_DB;
