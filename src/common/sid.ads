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

pragma Ada_2012;

with Ada.Containers.Functional_Vectors;

package Sid
with
  SPARK_Mode => On
is

   ---------------------------------------------------------------------------
   --                                                                       --
   -- Data Types and Helpers                                                --
   --                                                                       --
   ---------------------------------------------------------------------------

   subtype Literal_Type is Integer
     with Static_Predicate =>
     Literal_Type /= 0 and then
     Literal_Type > -2**31 + 1 and then
     Literal_Type < 2**31 - 1;

   -- Workaround for initialization of the empty clause due to
   -- missing support for advanced relaxed initialization.
   Magic_Literal : constant Literal_Type := 123;

   type Clause_Type is array (Natural range <>) of Literal_Type
     with Dynamic_Predicate => Clause_Type'First = 0
     and then Clause_Type'Last < 2 ** 16;

   Empty_Clause : constant Clause_Type (0 .. -1)  := (others => Magic_Literal);

   package Clause_Vector is new Ada.Containers.Functional_Vectors
     (Index_Type   => Positive,
      Element_Type => Clause_Type);

   subtype Formula_Type is Clause_Vector.Sequence;

   -- Complemenets a literal
   function Compl
     (Literal : Literal_Type) return Literal_Type
   is (-Literal)
   with Pre => Literal /= 0 and then Literal > Integer'First and then
     Literal < Integer'Last,
     Post => Compl'Result /= 0 and then Compl'Result > Integer'First and then
     Compl'Result < Integer'Last;

   -- States that a literal L appears in the clause C
   function Appears
     (C : Clause_Type;
      L : Literal_Type) return Boolean
   is (for some Lp of C => L = Lp)
     with Post => Appears'Result = (for some Lp of C => L = Lp);

   function Contains
     (F : Formula_Type;
      C : Clause_Type) return Boolean
   is (for some I in Positive'First .. Clause_Vector.Last (F) => Clause_Vector.Get (F, I) = C);

   function Subset
     (C, D : Clause_Type) return Boolean
   is (for all L of C => Appears (D, L));

   function Equivalent
     (C, D : Clause_Type) return Boolean
   is ((for all L of C => Appears (D, L)) and
       (for all L of D => Appears (C, L)));

   function Has_No_Duplicates
     (C : Clause_Type)
     return Boolean
   is
      (for all I in C'First .. C'Last =>
	 (for all J in C'First .. C'Last =>
	    (if I /= J then C (I) /= C (J))));

   function Remove_Duplicate_Literals
     (C : in Clause_Type) return Clause_Type
   with Post =>
     -- The set representation is equal
     Equivalent (C, Remove_Duplicate_Literals'Result) and then
     -- no duplicate entries
     Has_No_Duplicates (Remove_Duplicate_Literals'Result) and then
     -- size can decrease, not increase
     Remove_Duplicate_Literals'Result'Length <= C'Length;

   type Proof_Step_Type is
      record
	 C_Ref : Natural;
	 D_Ref : Natural;
	 Lit   : Literal_Type;
      end record;

   package Proof_Step_Vector is new Ada.Containers.Functional_Vectors
     (Index_Type   => Positive,
      Element_Type => Proof_Step_Type);

   subtype Proof_Type is Proof_Step_Vector.Sequence;

   ---------------------------------------------------------------------------
   --                                                                       --
   -- Logical Specification                                                 --
   --                                                                       --
   ---------------------------------------------------------------------------

   -- A formula is satisfiable if there exists an interpretation that
   -- satisfies a formula.
   -- We cannot represent this directly in SPARK as no existential
   -- quantification of arrays is possible. Instead, we do not give a
   -- meaning to this property.
   function Satisfiable
     (F : Formula_Type) return Boolean
     with Import, Ghost;

   -- Two formulas are equisatisfiable if they are both either satisfiable
   -- or both unsatisfiable
   function Equisatisfiable
     (F, G : Formula_Type) return Boolean
   is ((Satisfiable (F) and Satisfiable (G)) or
       (not Satisfiable (F) and not Satisfiable (G)))
     with Ghost;

   -- These are the required condition for resolution to be logically entailed
   -- by two other clauses.
   --
   -- Please note that this condition is rather weak, for instance:
   -- - R might be the clause that contains all literals
   -- - R might be the clause C \/ D
   function Resolve_Spec
     (C : Clause_Type;
      D : Clause_Type;
      L : Literal_Type;
      R : Clause_Type) return Boolean
   is ((for all Lit of C => (if Lit /= L then Appears (R, Lit))) and
       (for all Lit of D => (if Lit /= -L then Appears (R, Lit))));

   package Assignment_Vector is new Ada.Containers.Functional_Vectors
     (Index_Type   => Positive,
      Element_Type => Literal_Type);

   use type Assignment_Vector.Sequence;

   subtype Assignment_Type is Assignment_Vector.Sequence;

   -- A literal appears in an assignment
   function Appears
     (A : Assignment_Type;
      L : Literal_Type) return Boolean
   is (for some Lp of A => L = Lp);

   -- A literal L appears in the assignment and thus is true under A
   function Is_True
     (A : Assignment_Type;
      L : Literal_Type) return Boolean
   is (Appears (A, L));

   -- The complement of L appears in an assignment and thus is false under A
   function Is_False
     (A : Assignment_Type;
      L : Literal_Type) return Boolean
   is (Appears (A, Compl (L)));

   -- A clause is unit clause of the form [L] under A (reduct)
   function Unit
     (C : Clause_Type;
      A : Assignment_Type;
      L : Literal_Type) return Boolean
   is ( -- the clause is not satisfied under A
	(for all Lp of C => not Is_True (A, Lp)) and then
	-- all literals except L are false under A
	(for all Lp of C => (if Lp /= L then Is_False (A, Lp))) and then
        -- L appears in C
        Appears (C, L)
      );

   type Get_Unit_Result_Type (Found_Unit : Boolean) is
      record
	 case Found_Unit is
	    when True =>
	       L : Literal_Type;
	    when False =>
	       null;
	 end case;
      end record;

   function Get_Unit
     (C : Clause_Type;
      A : Assignment_Type) return Get_Unit_Result_Type
   with Post => (if Get_Unit'Result.Found_Unit then Unit (C, A, Get_Unit'Result.L));

   function Is_Empty_Clause
     (C : Clause_Type;
      A : Assignment_Type) return Boolean
   is (for all Lp of C => Is_False (A, Lp));

   function Has_Empty_Clause
     (F : Formula_Type;
      A : Assignment_Type) return Boolean
   is (for some C of F => Is_Empty_Clause (C, A));

   function Propagate
     (A  : Assignment_Type;
      Ap : Assignment_Type;
      C  : Clause_Type) return Boolean
   is (for some L of C => (Unit (C, A, L) and then Ap = Assignment_Vector.Add (A, L)))
   with Pre => Assignment_Vector.Last (A) < Positive'Last, Ghost;

   function Propagate
     (A  : Assignment_Type;
      Ap : Assignment_Type;
      F  : Formula_Type) return Boolean
   is (for some C of F => (for some L of C => (Unit (C, A, L) and then
						 Ap = Assignment_Vector.Add (A, L))))
   with Pre => Assignment_Vector.Last (A) < Positive'Last, Ghost;

   -- A1 /\ F1   EQUIV  A2 /\ F2
   function Equivalent
     (A1, A2 : Assignment_Type;
      F1, F2 : Formula_Type)
     return Boolean
     with Ghost, Import;

   -- We can represent an assignment A as a clause containing its complementary
   -- literals. Here we generalize it that the clause may contain further literals.
   -- This is OK since if C represent A and C is RUP, then any clause containing D
   -- is RUP as well.
   function Assignment_Clause_Rel
     (A : Assignment_Type;
      C : Clause_Type)
     return Boolean
   is (for all L of A => Appears (C, Compl (L)));

   -- Checks whether the clause C is RUP w.r.t. F
   function Is_RUP
     (F : Formula_Type;
      C : Clause_Type) return Boolean
   with
     Pre  => Clause_Vector.Last (F) < Positive'Last, -- enough space
     Post => (if Is_RUP'Result then Equisatisfiable (F, Clause_Vector.Add (F, C)));

   -- A RUP refutation can be represented as a sequence of clauses (i.e.
   -- a formula)
   subtype RUP_Proof_Type is Formula_Type;

   ---------------------------------------------------------------------------
   --                                                                       --
   -- Implementation                                                        --
   --                                                                       --
   ---------------------------------------------------------------------------

   -- Resolves two clauses C and D upon the literal L
   -- We quitely assume here that literals L and the complement of L occury
   -- at most once. 'Quitely' since this does not affect correctness, so even
   -- if you do not ensure it, the resultig clause may not be a resolvent, but
   -- is logically entailed by C and D.
   --
   -- Note: As a post condition, we state that C /\ D entails
   -- the result, i.e. we have to use to the above Resolution_Lemma to obtain
   -- this result.
   function Resolve (C : Clause_Type;
		     D : Clause_Type;
		     L : Literal_Type)
		    return Clause_Type
     with
     Pre  =>
       C'Length + D'Length - 2 < 2 ** 16  and then
       Appears (C, L) and then
       Appears (D, Compl (L)),
     Post =>
       Resolve'Result'Last = C'Length + D'Length - 3 and
       Resolve_Spec (C, D, L, Resolve'Result),
     Annotate => (GNATprove, Terminating);

   type Result_Kind is
     (Success,          -- The proof is checked and the empty clause is found
      Illegal_Shape,    -- References do not exist, literal is incorrect or memory exceeded
      Non_Resolvable,   -- Given clauses cannot be resolved upon specified literal
      No_Empty_Clause); -- The empty clause did not appeared

   type Result_Type (Kind : Result_Kind := Success) is
      record
	 case Kind is
	    when Success =>
	       null;
	    when Illegal_Shape .. Non_Resolvable =>
	       Step_ID : Positive := Positive'First;
	    when No_Empty_Clause =>
	       null;
	 end case;
      end record;

   -- Checks whether P is a propositional resolution refutation of F
   procedure Check_Resolution_Proof
     (F      : in     Formula_Type;
      P      : in     Proof_Type;
      Result :    out Result_Type)
   with
     Global   => null,
     Pre      => (not Result'Constrained),
     Post     => (if Result.Kind = Success then not Satisfiable (F)),
     Annotate => (GNATprove, Terminating);

   -- Checks whether P is a RUP refutation of F
   procedure Check_RUP_Proof
     (F       : in     Formula_Type;
      P       : in     RUP_Proof_Type;
      Result  :    out Result_Type)
   with
     Global => null,
     Pre    => (not Result'Constrained),
     Post   => (if Result.Kind = Success then not Satisfiable (F));

end Sid;
