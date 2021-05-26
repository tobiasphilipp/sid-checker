------------------------------------------------------------------------------
--                                                                          --
--                                Sid Checker                               --
--                                                                          --
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

with Ada.Containers.Formal_Indefinite_Vectors;
with Ada.Containers.Functional_Vectors;

with Sid_DB;

package Sid.Watcher
with
  SPARK_Mode => On
--  Annotate          => (GNATprove, Terminating)
--  Abstract_State    => The_Watcher,
--  Initializes       => The_Watcher
is
   pragma Elaborate_Body;

   package P is new Ada.Containers.Formal_Indefinite_Vectors
     (Index_Type                   => Positive,
      Element_Type                 => Positive,
      Max_Size_In_Storage_Elements => Positive'Size, -- TODO
      Bounded                      => False);

   -- Note: Using two formal indefinite vectors in stack does not work
   -- as the Element_Type cannot be a limited type.
   -- This is why we store the vectors in an array
   type QTy is array (Integer range <>) of P.Vector (8);
   type QVec is access QTy;

   subtype Clause_Ref_Type is Positive;

   function Watcher_Index (L : Literal_Type)
			  return Integer
   is (L);

   function Invariant return Boolean
     with Ghost;

   procedure Insert
     (L       : in     Literal_Type;
      R       : in     Clause_Ref_Type;
      Success :    out Boolean)
     with
     Pre => Invariant and then
            Sid_DB.Valid_Index (R),
     Post => (if Success
		then Invariant);

   -- Just fo debugging...
   procedure Print;

   function First_Index
     return Integer
     with Pre => Invariant;

   function Last_Index
     return Integer
     with Pre => Invariant;

   function Line_First_Index
     return Positive;

   function Line_Last_Index
     (L : Literal_Type) return Natural
   with Pre => Invariant and then
     (if L > 0 then Last_Index >= L else Last_Index <= L);

   function Element
     (L : Literal_Type;
      I : Positive)
     return Clause_Ref_Type
     with Pre => Invariant and then
     (if L > 0 then Last_Index >= L else Last_Index <= L) and then
       I <= Line_Last_Index (L),
       Post => Sid_DB.Valid_Index (Element'Result);

   -- Removes one occurence in the line, if it exists
   procedure Remove_Occurence
     (L   : in Literal_Type;
      Ref : in     Clause_Ref_Type)
   with
     Pre => Invariant and then (if L > 0 then Last_Index >= L else Last_Index <= L),
     Post => Invariant;

   procedure Resize
     (Num_Literals : in     Natural;
      Success      :    out Boolean)
   with
     Pre => Invariant and then
            Num_Literals > Last_Index and then
            Num_Literals < 2**31 - 1,
     Post => (if Success then
                Invariant and then
                First_Index = -Num_Literals and then
                Last_Index = Num_Literals);

   type Clause_Propagate_Kind is
     (Reinsert,
      Insert,
      Enqueue -- Enqueue means reinsert and propagate
     );

   type Clause_Propagate_Type (Kind : Clause_Propagate_Kind := Reinsert) is
      record
	 case Kind is
	    when Reinsert =>
	       null;
	    when Insert =>
	       Watch_L : Literal_Type;
	    when Enqueue =>
	       Prop_L : Literal_Type;
	 end case;
      end record;


   procedure Propagate
     (Prop_Lit : in     Literal_Type;
      Ref      : in     Clause_Ref_Type;
      A        : in     Assignment_Type;
      Result   :    out Clause_Propagate_Type)
   with Pre =>
     Invariant and then
     Sid_DB.Valid_Index (Ref) and then
     (if Prop_Lit > 0 then Last_Index >= Prop_Lit else Last_Index <= Prop_Lit) and then
     (not Result'Constrained);

   procedure Propagate
     (A : in Assignment_Type;
      Success : out Boolean)
   with
     Pre =>
     -- literals in A are within the watcher bounds
     (for all L of A => (if L > 0 then Last_Index >= L else Last_Index <= L));

private

   Watchers : QVec;
--       with Part_Of => The_Watcher;

   --
   type Reference_Array_Type is array (Integer range <>) of Sid_DB.Indices_Seq.Sequence;
   type Reference_Array_Access_Type is access Reference_Array_Type;

   References : Reference_Array_Access_Type
       with Ghost; --, Part_Of => The_Watcher;

   function Invariant return Boolean
   is (-- Watcher is not too large, is symmetric and initialized
       Watchers /= null and then
       Watchers'First > -2**31 + 1 and then
       Watchers'Last < 2**31 - 1 and then
       Watchers'First < Watchers'Last and then
       Watchers'Last = -Watchers'First and then
	 -- Model Correspondance
	 -- all indices are valid
	 (for all I in References'Range =>
	    (for all J in 1 .. Sid_DB.Indices_Seq.Last (References (I)) =>
	       Sid_DB.Valid_Index (Sid_DB.Indices_Seq.Get (References (I), J)))) and then
	 -- the watcher contains a line for each literal
	 (for all I in References'Range =>
	    (for all J in 1 .. Sid_DB.Indices_Seq.Last (References (I)) =>
	       (for all L of Sid_DB.Element (Sid_DB.Indices_Seq.Get (References (I), J)) =>
		  L in First_Index .. Last_Index))) and then
	 -- model corresponds to data structure
	 (for all L in First_Index .. Last_Index =>
	    (for all I in Line_First_Index .. Line_Last_Index (L) =>
	       P.Element (Watchers.all (L), I) = Sid_DB.Indices_Seq.Get (References (L), I)))
      )

     ;

   function First_Index
      return Integer
   is (Watchers.all'First);

   function Last_Index
     return Integer
   is (Watchers.all'Last);

   function Line_First_Index return Positive
   is (1);

   function Line_Last_Index
     (L : Literal_Type) return Natural
   is (P.Last_Index (Watchers.all (L)));

   function Element
     (L : Literal_Type;
      I : Positive) return Clause_Ref_Type
   is (P.Element (Watchers.all (L), I));
end Sid.Watcher;
