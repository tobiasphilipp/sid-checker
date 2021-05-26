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

with Sid; use Sid;

-- Workaround: type invariant in child unit is not yet supported
package Sid_DB
with
  SPARK_Mode        => On,
  Annotate          => (GNATprove, Terminating),
  Abstract_State    => The_DB,
  Initializes       => The_DB
  -- Workaround: "Failed to verify: m_util.is_numeral(rhs, _k)"
  -- Use Clear initially
  --  Initial_Condition => Invariant
is
   package P is new Ada.Containers.Formal_Indefinite_Vectors
     (Index_Type                   => Positive,
      Element_Type                 => Integer,
      Max_Size_In_Storage_Elements => Integer'Size / 8,
      Bounded                      => False);

   package Indices_Seq is new Ada.Containers.Functional_Vectors
     (Index_Type   => Positive,
      Element_Type => Positive);

   pragma Unevaluated_Use_Of_Old (Allow);

   function Enough_Space
     (C : Clause_Type) return Boolean;

   function Get_Indices return Indices_Seq.Sequence
     with Ghost;

   function Get_Formula return Formula_Type
     with Ghost;

   function Invariant return Boolean
     with Ghost;

   function Is_Empty return Boolean;

   type Insert_Result_Type (Success : Boolean := False) is
      record
	 case Success is
	    when True =>
	       Index : Positive;
	    when False =>
	       null;
	 end case;
      end record;

   use type Indices_Seq.Sequence;
   use type Clause_Vector.Sequence;

   procedure Insert
     (Clause  : in     Clause_Type;
      Result  :    out Insert_Result_Type)
   with
     Pre  => Enough_Space (Clause) and then
             not Result'Constrained and then
             Clause'Length > 0 and then
             Invariant,
     Post => (if Result.Success then
                Get_Indices = Indices_Seq.Add (Get_Indices'Old, Result.Index) and
                Get_Formula = Clause_Vector.Add (Get_Formula'Old, Clause)) and then
              Invariant;

   procedure Clear
   with
     Post => Invariant and then Is_Empty;

   function Valid_Index
     (Index : Positive) return Boolean
   with Ghost;

   function Element
     (Index : Positive) return Clause_Type
   with
     Pre => Invariant and then Valid_Index (Index),
     Post => (for Some I in 1 .. Indices_Seq.Last (Get_Indices) =>
		Indices_Seq.Get (Get_Indices, I) = Index and
		Element'Result = Clause_Vector.Get (Get_Formula, I));

   function Element
     (Index : Positive;
      I     : Natural) return Literal_Type
   with Pre => Invariant and then Valid_Index (Index) and then I < Length (Index);

   procedure Swap
     (Clause_Index : Positive;
      I, J         : Natural)
     with Pre => Invariant and then Valid_Index (Clause_Index) and then I < Length (Clause_Index) and then J < Length (Clause_Index),
     Post => Invariant and
     (
      Get_Indices = Get_Indices'Old and
      Get_Formula = Get_Formula'Old -- TODO: This is not completely true!
     );

   function Length
     (Index : Positive)
     return Natural
     with Pre => Invariant;
private

   Contents : P.Vector (128)
   with Part_Of => The_DB;

   Number_Clauses : Natural := 0
   with Part_Of => The_DB;
    
   Formula : Formula_Type
   with Ghost,
       Part_Of => The_DB;

    Indices : Indices_Seq.Sequence
	with Ghost,
	Part_Of => The_DB;

   function Get_Indices return Indices_Seq.Sequence
   is (Indices);

   function Get_Formula return Formula_Type
   is (Formula);

   function Invariant return Boolean
   is (Number_Clauses = Natural (Indices_Seq.Length (Indices)) and then
       Number_Clauses = Natural (Clause_Vector.Length (Formula)) and then
       -- All index positions are within the container bounds
       (for all I of Indices => I < Natural (P.Length (Contents))) and then
       -- At index position we have the length argument and of correct size
       (for all I of Indices => P.Element (Contents, I) > 0 and P.Element (Contents, I) <= Max_Clause_Size) and then
       -- All indices and lengths are within the container bounds
       (for all I of Indices => I <= Positive'Last - P.Element (Contents, I) and then I + P.Element (Contents, I) <= Natural (P.Length (Contents))) and then
       -- After indices, we have correct literals
       (for all I of Indices => (for all J in 1 .. P.Element (Contents, I) =>
				     P.Element (Contents, I + J) /= 0 and
				     P.Element (Contents, I + J) > -2**31 + 1 and
				   P.Element (Contents, I + J) < 2**31 - 1)) and then
       -- Model Correspondance
	 (for all I in 1 .. Indices_Seq.Last (Indices) =>
	    I <= Clause_Vector.Last (Get_Formula) and then
	    Clause_Vector.Get (Get_Formula, I)'Length = P.Element (Contents, Indices_Seq.Get (Get_Indices, I)) and then
	       (for all J in 1 .. Clause_Vector.Get (Get_Formula, I)'Length =>
		  Clause_Vector.Get (Get_Formula, I)(J - 1) = P.Element (Contents, Indices_Seq.Get (Get_Indices, I) + J)))
      );



   function Enough_Space
     (C : Clause_Type) return Boolean
   is (P.Last_Index (Contents) <= Positive'Last - C'Length and then
	 P.Last_Index (Contents) + C'Length < 2**18 and then
       Number_Clauses < Natural'Last);

   function Valid_Index
     (Index : Positive) return Boolean
   is (for Some I of Indices => I = Index);

   function Is_Empty return Boolean
   is (Number_Clauses = 0);

   function Element
     (Index : Positive;
      I     : Natural) return Literal_Type
   is (P.Element (Contents, Index + 1 + I));

   function Length
     (Index : Positive)
     return Natural
   is (P.Element (Contents, Index));
end Sid_DB;
