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


with Ada.Unchecked_Deallocation;

package body Sid.Watcher
  with SPARK_Mode => On
--  Refined_State => (The_Watcher => (Watchers, References, Heap.Dynamic_Memory))
is

   use type Ada.Containers.Count_Type;

   -- --------------------------------------------------------------------------

   procedure Insert
     (L       : in Literal_Type;
      R       : in Clause_Ref_Type;
      Success :    out Boolean)
   is
   begin
      if L not in Watchers.all'Range then
	 Resize ((if L > 0 then L else -L), Success);

	 if not Success then
	    return;
	 end if;
      end if;

      if P.Length (Watchers.all (Watcher_Index (L))) >= P.Capacity (Watchers.all (Watcher_Index (L))) then
        if P.Capacity (Watchers.all (Watcher_Index (L))) < Ada.Containers.Count_Type'Last / 2 then
	 P.Reserve_Capacity (Container => Watchers.all (Watcher_Index (L)),
			     Capacity  => P.Capacity (Watchers.all (Watcher_Index (L))) * 2);
        else
	   Success := False;
	   return;
        end if;
      end if;

      Success := True;
      P.Append (Watchers.all (Watcher_Index (L)), R);
      -- The following code results in undefined reference to `___ghost_sid__watcher__references'
      -- References.all (L) := Sid_DB.Indices_Seq.Add (References.all (L), R);
   end Insert;

   -- --------------------------------------------------------------------------

   procedure Print
     with SPARK_Mode => Off
   is
   begin
      for I in Watchers.all'First .. Watchers.all'Last
      loop
	 Ada.Text_IO.Put (Natural'Image (I));
	 Ada.Text_IO.Put (": ");

	 for J in 1 .. P.Last_Index (Watchers.all (I))
	 loop
	    Ada.Text_IO.Put (Positive'Image (P.Element (Watchers.all (I), J)));
	 end loop;

	 Ada.Text_IO.Put_Line ("");

      end loop;
   end Print;

   -- --------------------------------------------------------------------------

   procedure Resize
     (Num_Literals : in Natural;
      Success : out Boolean)
   is
      New_Watchers : QVec := new QTy (-Num_Literals .. Num_Literals);
      pragma Annotate (GNATprove, Intentional,
		       "memory leak", "Use Clear for avoiding memory leaks");


      procedure Free is new Ada.Unchecked_Deallocation (Object => QTy, Name => QVec);

   begin
      for I in Watchers.all'First .. Watchers.all'Last
      loop

	 for J in 1 .. P.Last_Index (Watchers.all (I))
	 loop

	    if P.Length (New_Watchers.all (I)) >= P.Capacity (New_Watchers.all (I)) then
	       if P.Capacity (New_Watchers.all (I)) < Ada.Containers.Count_Type'Last / 2 then
		  P.Reserve_Capacity (Container => New_Watchers.all (I),
				      Capacity  => P.Capacity (New_Watchers.all (I)) * 2);
	       else
		  Success := False;
		  return;
	       end if;
	    end if;

	    P.Append (New_Watchers.all (I), P.Element (Watchers.all (I), J));
	 end loop;
      end loop;

      Success := True;

      Free (Watchers);

      Watchers := New_Watchers;
   end Resize;

   -- --------------------------------------------------------------------------

   procedure Remove_Occurence
     (L   : in Literal_Type;
      Ref : in     Clause_Ref_Type)
   is
      Idx : constant Natural := P.Find_Index (Watchers.all (L), Ref);
   begin
      if Idx /= P.No_Index then
	 P.Delete (Watchers.all (L), Idx);
      end if;
   end Remove_Occurence;

   -- --------------------------------------------------------------------------


   -- --------------------------------------------------------------------------

   procedure Propagate
     (Prop_Lit : in     Literal_Type;
      Ref      : in     Clause_Ref_Type;
      A        : in     Assignment_Type;
      Result   :    out Clause_Propagate_Type)
   is
   begin
      -- Make sure the false literal is lits[1]
      -- if (lits[0] == -p) then {lits[0] = lits[1], lits[1] = -p}
      if Sid_DB.Element (Ref, 0) = Compl (Prop_Lit) then
	 Sid_DB.Swap (Ref, 0, 1);
      end if;

      -- If the 0th watch is true, then clause is already satisfied
      if (Is_True (A, Sid_DB.Element (Ref, 0))) then
	 Result := Clause_Propagate_Type' (Kind => Reinsert);
	 return;
      end if;

      -- Loop for a new literal to watch
      for I in 2 .. Sid_DB.Length (Ref) - 1
      loop
	 Ada.Text_IO.Put_Line ("Accessing ... " & Natural'Image (Ref) & ":" & Natural'Image (I));
	 if not Is_False (A, Sid_DB.Element (Ref, I))
	 then
	    Sid_DB.Swap (Ref, 1, I); -- TODO: Corret?

	    Result := Clause_Propagate_Type' (Kind => Insert, Watch_L => Sid_DB.Element (Ref, 1));
	    return;
	 end if;
      end loop;

      -- Clause is unit under assignment
      Result := Clause_Propagate_Type' (Kind => Enqueue, Prop_L => Sid_DB.Element (Ref, 0));
   end Propagate;

   -- --------------------------------------------------------------------------

   procedure Propagate
     (A       : in     Assignment_Type;
      Success :    out Boolean)
   is
      Ap : Assignment_Type;
   begin
      -- Go through the assignment and propagate
      for L of A
      loop
	 Ada.Text_IO.Put_Line ("Propagating " & Literal_Type'Image (L));

	 declare
	    Refs_To_Remove : Sid_DB.Indices_Seq.Sequence;
	 begin
	    for I in Line_First_Index .. Line_Last_Index (-L)
	    loop
	       declare
		  Ref : Clause_Ref_Type := Element (-L, I);
		  C : Clause_Type := Sid_DB.Element (Ref);

		  Propagate_Result : Clause_Propagate_Type;
	       begin
		  pragma Assert (C (C'First) = -L or else C (C'First + 1) = -L);

		  Ada.Text_IO.Put_Line ("Considerung " & Clause_Ref_Type'Image (Ref));


		  Propagate (L, Ref, A, Propagate_Result);
		  Ada.Text_IO.Put_Line ("Propagation Kind " & Clause_Propagate_Kind'Image (Propagate_Result.Kind));

		  case Propagate_Result.Kind is
		     when Reinsert =>
			null;
		     when Insert =>
			Ada.Text_IO.Put_Line ("Insert " & Clause_Ref_Type'Image (Ref) & " at " & Literal_Type'Image (Propagate_Result.Watch_L));
			Insert (Propagate_Result.Watch_L,
				Ref,
				Success);

			Refs_To_Remove := Sid_DB.Indices_Seq.Add (Refs_To_Remove, Ref);

			if not Success then
			   Ada.Text_IO.Put_Line ("Something really bad happened");
			   return;
			end if;
		     when Enqueue =>
			Ada.Text_IO.Put_Line ("Enqueue " & Literal_Type'Image (Propagate_Result.Prop_L));
			Ap := Assignment_Vector.Add (Ap, Propagate_Result.Prop_L);
		  end case;
	       end;
	    end loop;

	    for I of Refs_To_Remove
	    loop
	       Ada.Text_IO.Put_Line ("Removing occurence");
	       Remove_Occurence (-L, I);
	    end loop;
	 end;
      end loop;

      Success := True;
   end;

begin
   Watchers := new QTy (-3 .. 3);
   References := new Reference_Array_Type (-3 .. 3);

end Sid.Watcher;
