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

with Ada.Containers;
with Sid.Lemmas;

package body Sid
  with SPARK_Mode => On
is

   -- --------------------------------------------------------------------------

   function Remove_Duplicate_Literals
     (C : in Clause_Type) return Clause_Type
   is
      D : Clause_Type (C'First .. C'Last) := C;
      J : Natural := D'First;
   begin

      for I in C'First .. C'Last
      loop
	 pragma Loop_Invariant
	   (J <= I);

	 -- No duplicates so far
	 pragma Loop_Invariant
	   (for all K in D'First .. J - 1 =>
	      (for all Kp in D'First .. J - 1 =>
		 (if K /= Kp then D (K) /= D (Kp))));

	 -- we preserve set equality
	 pragma Loop_Invariant
	   (Subset (D (D'First .. J - 1), C));
	 pragma Loop_Invariant
	   (Subset (C (C'First .. I - 1), D (D'First .. J - 1)));

	 if
	   (for all K in D'First .. J - 1 => D (K) /= C (I))
	 then
	    D (J) := C (I);
	    J := J + 1;
	 end if;
      end loop;

      return D (D'First .. J - 1);
   end Remove_Duplicate_Literals;

   -- --------------------------------------------------------------------------

   -- We use the following Copy operation to copy parts of clause into the
   -- resolvent.
   procedure Copy
     (Data   : in     Clause_Type;
      From   : in     Natural;
      Length : in     Natural;
      Dest   : in out Clause_Type;
      Index  : in     Natural)
     with
     Pre  =>
     (Length = 0 or  --  If the length is zero, nothing is done and therefore
	             --  all other conditions can be arbitrary
	(Dest'First <= Index and then
	 Index + Length - 1 <= Dest'Last and then
	 Data'First <= From and then
	 From + Length - 1 <= Data'Last)),
     Post =>
     -- We copied parts of the clause
     (for all I in 0 .. Length - 1 => Dest (Index + I) = Data (From + I)) and
     -- And the rest remains unchanged:
       (for all I in Dest'Range =>
	  (if I < Index or I > Index + Length then Dest (I) = Dest'Old (I)))
   is
   begin
      for L in 0 .. Length - 1
      loop
	 Dest (Index + L) := Data (From + L);

	 -- Copy
	 pragma Loop_Invariant
	   (for all J in 0 .. L =>
	      Dest (Index + J) = Data (From + J));

	 -- No change
	 pragma Loop_Invariant
	   (for all I in Dest'Range =>
	      (if I < Index or I > Index + Length
		 then Dest (I) = Dest'Loop_Entry (I)));
      end loop;

   end Copy;

   -- --------------------------------------------------------------------------

   -- Gets the position of a literal L in a clause C
   function Get_Literal_Pos
     (C : Clause_Type;
      L : Literal_Type)
     return Natural
   with
     Pre => Appears (C, L),
     Post => (Get_Literal_Pos'Result in C'Range and
	      C (Get_Literal_Pos'Result) = L)
   is
   begin
      for I in C'Range
      loop
	 if
	   C (I) = L
	 then
	    return I;
	 end if;

	 -- Literal not found
	 pragma Loop_Invariant
	   (for all J in C'First .. I =>
	      C (J) /= L);
      end loop;

      return C'First;
   end Get_Literal_Pos;

   -- --------------------------------------------------------------------------

   function Resolve (C : Clause_Type;
		     D : Clause_Type;
		     L : Literal_Type)
		    return Clause_Type
   is
      -- Workaround as relaxed initialization with predicate on type is not
      -- supported
      Result      : Clause_Type (0 .. C'Length + D'Length - 3)
	:= (others => Magic_Literal);
      L_Pos       : constant Natural := Get_Literal_Pos (C, L);
      Compl_L_Pos : constant Natural := Get_Literal_Pos (D, Compl (L));
   begin
      -- In the following we copy parts of the clauses C and D into the
      -- resulting clause Result. After each Copy operation we add
      -- assertations to state what we already know about the clause Result,
      -- and translate these statements using the 'Appears' function.
      Copy (Data   => C,
	    From   => C'First,
	    Length => L_Pos - C'First,
	    Dest   => Result,
	    Index  => Result'First);

      pragma Assert
	(for all I in C'First .. L_Pos - 1 =>
	   Result (I) = C (I));

      Copy (Data   => C,
      	    From   => L_Pos - C'First + 1,
      	    Length => C'Last - (L_Pos - C'First),
      	    Dest   => Result,
      	    Index  => Result'First + L_Pos - C'First);

      pragma Assert
	(for all I in C'First .. L_Pos - 1 =>
	   Result (I) = C (I));

      pragma Assert
	(for all I in L_Pos + 1 .. C'Last =>
	   Result (L_Pos + (I - L_Pos - 1)) = C (I));

      pragma Assert
	(for all I in C'First .. L_Pos - 1 =>
	   (Appears (Result, C (I))));

      pragma Assert
	(for all I in L_Pos + 1 .. C'Last =>
	   (Appears (Result, C (I))));

      Copy (Data   => D,
      	    From   => D'First,
      	    Length => Compl_L_Pos - D'First,
      	    Dest   => Result,
      	    Index  => Result'First + C'Length - 1);

      pragma Assert
	(for all I in C'First .. L_Pos - 1 =>
	   Result (I) = C (I));

      pragma Assert
	(for all I in L_Pos + 1 .. C'Last =>
	   Result (L_Pos + (I - L_Pos - 1)) = C (I));

      pragma Assert
	(for all I in D'First .. Compl_L_Pos - 1 =>
	   Result (C'Length - 1 + I) = D (I));

      Copy (Data   => D,
      	    From   => Compl_L_Pos - D'First + 1,
      	    Length => D'Last - (Compl_L_Pos - D'First),
      	    Dest   => Result,
      	    Index  => Result'First + C'Length - 1 + Compl_L_Pos - D'First);

      pragma Assert
	(for all I in C'First .. L_Pos - 1 =>
	   Result (I) = C (I));

      pragma Assert
	(for all I in L_Pos + 1 .. C'Last =>
	   Result (L_Pos + (I - L_Pos - 1)) = C (I));

      pragma Assert
      	(for all Lp of C =>
      	   (if L /= Lp then Appears (Result, Lp)));

      pragma Assert
	(for all I in D'First .. Compl_L_Pos - 1 =>
	   Result (C'Length - 1 + I) = D (I));

      pragma Assert
	(for all I in Compl_L_Pos + 1 .. D'Last =>
	   Result (C'Length - 1 + Compl_L_Pos + (I - Compl_L_Pos - 1)) = D (I));

      pragma Assert
      	(for all Lp of D =>
      	   (if Compl (L) /= Lp then Appears (Result, Lp)));

      pragma Assert (Resolve_Spec (C, D, L, Result));

      return Result;
   end Resolve;

   -- --------------------------------------------------------------------------

   function Get_Unit (C : Clause_Type;
		      A : Assignment_Type)
		     return Get_Unit_Result_Type
   is
      Found         : Boolean := False;
      Found_Literal : Literal_Type := Magic_Literal;
   begin
      for I in C'Range
      loop
         pragma Loop_Invariant (for all J in C'First .. I - 1 => not Is_True (A, C (J)));
         pragma Loop_Invariant (if not Found then (for all J in C'First .. I - 1 => Is_False (A, C (J))));
         pragma Loop_Invariant (if Found then (for all J in C'First .. I - 1 => (if C (J) /= Found_Literal then Is_False (A, C (J)))));
         pragma Loop_Invariant (if Found then Appears (C, Found_Literal));

	 if Is_True (A, C (I)) then
	    return Get_Unit_Result_Type' (Found_Unit => False);
	 end if;

         if Is_False (A, C (I)) then
            null;
         else
	    if Found then
	       return Get_Unit_Result_Type' (Found_Unit => False);
	    else

	       Found := True;
	       Found_Literal := C (I);

	    end if;
	 end if;
     end loop;

     if Found then
        return Get_Unit_Result_Type' (Found_Unit => True, L => Found_Literal);
     else
        return Get_Unit_Result_Type' (Found_Unit => False); -- TODO: It is an empty clause!
     end if;

   end Get_Unit;

   -- --------------------------------------------------------------------------

   function Is_RUP (F : Formula_Type;
                    C : Clause_Type) return Boolean
   is
      Input_A : Assignment_Type
        with Ghost;

      A     : Assignment_Type;
      Found : Boolean := True;

   begin

      for I in C'First .. C'Last loop
	 pragma Loop_Invariant (I = Natural (Assignment_Vector.Length (A)));
	 pragma Loop_Invariant (for all L of A => Appears (C (C'First .. I - 1), Compl (L)));
	 A := Assignment_Vector.Add (A, Compl (C (I)));
      end loop;

      Input_A := A;

      pragma Assert (Assignment_Clause_Rel (Input_A, C));
      Lemmas.Equivalent_Reflexive (F, A);

      while Found loop
         -- We only add propagation literals
         pragma Loop_Invariant (Equivalent (Input_A, A, F, F));

	 Found := False;

	 for D of F loop
            -- We only add propagation literals
            pragma Loop_Invariant (Equivalent (Input_A, A, F, F));

	    if Is_Empty_Clause (D, A) then
               Lemmas.RUP_Lemma (Input_A, A, F, C);

	       pragma Assert (Equisatisfiable (F, Clause_Vector.Add (F, C)));
	       return True;
	    end if;

	    declare
	       R : constant Get_Unit_Result_Type := Get_Unit (D, A);
	    begin
	       if R.Found_Unit then
		  Found := True;

		  -- TODO: This should not happen
		  if Assignment_Vector.Last (A) >= Positive'Last then
		     return False;
		  end if;

                  pragma Assert (Propagate (A, Assignment_Vector.Add (A, R.L), F));
                  Lemmas.Propagate_Lemma (A, Assignment_Vector.Add (A, R.L), F);
                  Lemmas.Equivalent_Transitivity (F, Input_A, A, Assignment_Vector.Add (A, R.L));

		  A := Assignment_Vector.Add (A, R.L);
	       end if;
	    end;
	 end loop;
      end loop;

      return False;
   end Is_RUP;

   -- --------------------------------------------------------------------------

   procedure Check_RUP_Proof
     (F       : in     Formula_Type;
      P       : in     RUP_Proof_Type;
      Result  :    out Result_Type)
   is
      Input_Formula      : constant Formula_Type := F;
      Working_Formula    : Formula_Type := F;
      Found_Empty_Clause : Boolean      := False;
      Proof_Length       : constant Natural
	:= Natural(Clause_Vector.Length (P));

      use type Ada.Containers.Count_Type;

   begin
      for Step_ID in Positive'First .. Proof_Length
      loop
	 -- Input_Formula is equisatisfiable to Working_Formula
	 pragma Loop_Invariant
	   (Equisatisfiable (Input_Formula, Working_Formula));

	 -- If the empty clause is found, the input formula is unsatisfiable
	 pragma Loop_Invariant
	   (if Found_Empty_Clause then not Satisfiable (Input_Formula));

	 -- Technical lemma to enssure that the result kind is not constrained
	 pragma Loop_Invariant
	   (not Result'Constrained);

	 -- Workaround: Necessary termination order as
	 --   `for Step_ID in P`
	 -- does not work
	 pragma Loop_Variant
	   (Increases => Step_ID);

	 if not (
	      -- Check that we do not exceed the maximum formula length (preconditions of Add)
	      Clause_Vector.Length (Working_Formula) < Ada.Containers.Count_Type'Last and then
	      Clause_Vector.Last (Working_Formula) < Positive'Last)
         then
	    Result := (Kind => Illegal_Shape, Step_ID => Step_ID);
	    return;
	 end if;

	 declare
	    C : constant Clause_Type
	      := Clause_Vector.Get (P, Step_ID);
	 begin
	    if not Is_RUP (Working_Formula, C)
	    then
	       Result := (Kind => Non_Resolvable, Step_ID => Step_ID);
	       return;
	    end if;

	    Working_Formula := Clause_Vector.Add (Working_Formula, C);

	    if C = Empty_Clause then
	       Found_Empty_Clause := True;

	       -- Working formula is unsatisfiable
	       Lemmas.Unsatisfiable_Empty_Clause (Working_Formula);
	    end if;
	 end;

      end loop;

      if
	Found_Empty_Clause
      then
         Result := (Kind => Success);
      else
	 Result := (Kind => No_Empty_Clause);
      end if;
   end Check_RUP_Proof;

   -- --------------------------------------------------------------------------


   procedure Check_Resolution_Proof
     (F       : in     Formula_Type;
      P       : in     Proof_Type;
      Result  :    out Result_Type)
   is
      Input_Formula      : constant Formula_Type := F;
      Working_Formula    :          Formula_Type := F;
      Found_Empty_Clause :          Boolean      := False;

      Proof_Length       : constant Natural
	:= Natural(Proof_Step_Vector.Length (P));

      use type Ada.Containers.Count_Type;
   begin
      for Step_ID in Positive'First .. Proof_Length
      loop
	 -- Input_Formula is equisatisfiable to Working_Formula
	 pragma Loop_Invariant
	   (Equisatisfiable (Input_Formula, Working_Formula));

	 -- If the empty clause is found, the input formula is unsatisfiable
	 pragma Loop_Invariant
	   (if Found_Empty_Clause then not Satisfiable (Input_Formula));

	 -- Technical lemma to enssure that the result kind is not constrained
	 pragma Loop_Invariant
	   (not Result'Constrained);

	 -- Workaround: Necessary termination order as
	 --   `for Step_ID in P`
	 -- does not work
	 pragma Loop_Variant
	   (Increases => Step_ID);

	 declare
	    Step : constant Proof_Step_Type
	      := Proof_Step_Vector.Get (P, Step_ID);
	 begin
	    if not (
	      -- Check that the references exist
	      Step.C_Ref in Positive'First .. Clause_Vector.Last (Working_Formula) and then
	      Step.D_Ref in Positive'First .. Clause_Vector.Last (Working_Formula) and then
	      -- Check that we do not exceed the maximum formula length (preconditions of Add)
	      Clause_Vector.Length (Working_Formula) < Ada.Containers.Count_Type'Last and then
	      Clause_Vector.Last (Working_Formula) < Positive'Last)
	    then
	       Result := (Kind => Illegal_Shape, Step_ID => Step_ID);
	       return;
	    end if;

	    declare
	       C : constant Clause_Type  := Clause_Vector.Get (Working_Formula, Step.C_Ref);
	       D : constant Clause_Type  := Clause_Vector.Get (Working_Formula, Step.D_Ref);
	       L : constant Literal_Type := Step.Lit;
	    begin
	       if not(
		 Appears (C, L) and then
		 Appears (D, Compl (L)) and then
		 C'Length + D'Length - 2 < 2 ** 16)
	       then
		  Result := (Kind => Non_Resolvable, Step_ID => Step_ID);
		  return;
	       end if;

	       declare
		  R : constant Clause_Type
		    := Resolve (Remove_Duplicate_Literals (C),
				Remove_Duplicate_Literals (D),
				L);
	       begin
		  pragma Assert (Contains (Working_Formula, C));
		  pragma Assert (Contains (Working_Formula, D));
		  pragma Assert (Resolve_Spec (C, D, L, R));

		  -- R is redundant to Working Formula
		  Lemmas.Resolvent_Redundancy (Working_Formula, C, D, L, R);

		  pragma Assert
		    (Equisatisfiable (Working_Formula, Clause_Vector.Add (Working_Formula, R)));

		  Working_Formula := Clause_Vector.Add (Working_Formula, R);

		  if R = Empty_Clause then
		     Found_Empty_Clause := True;

		     -- Working formula is unsatisfiable
		     Lemmas.Unsatisfiable_Empty_Clause (Working_Formula);
		  end if;
	       end;
	    end;
	 end;
      end loop;

      if
	Found_Empty_Clause
      then
         Result := (Kind => Success);
      else
	 Result := (Kind => No_Empty_Clause);
      end if;
   end Check_Resolution_Proof;
end Sid;
