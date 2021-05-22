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

package Sid.IO
  with SPARK_Mode => On
is
   -- Reads a CNF representation of a formula from a file
   -- Note: This is not the DIMACS format
   procedure Read_CNF
     (File_Name : in     String;
      Formula   : in out Formula_Type);

   -- Writes a CNF representation of a formula to a file
   -- Note: This is not the DIMACS format
   procedure Write_CNF
     (File_Name : in String;
      Formula   : in Formula_Type);

   -- Reads a proof from a file
   procedure Read_Proof
     (File_Name : in     String;
      Proof     : in out Proof_Type);

   -- Writes a proof to a file
   procedure Write_Proof
     (File_Name : in String;
      Proof     : in Proof_Type);
end Sid.IO;
