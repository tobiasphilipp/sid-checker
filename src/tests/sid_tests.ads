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

with AUnit; use AUnit;
with AUnit.Test_Cases; use AUnit.Test_Cases;

package Sid_Tests
is

   pragma Elaborate_Body;

   type Sid_Test is new Test_Cases.Test_Case with null record;

   procedure Register_Tests
     ( T: in out Sid_Test);

   function Name
     (T : Sid_Test) return Message_String;

end Sid_Tests;
