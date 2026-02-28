-- filepath: c:\Users\galax\Desktop\programs\mizogutiken\RelationalCalculus\lakefile.lean
import Lake
open Lake DSL


package RelationalCalculus where
  -- add package configuration options here
  require mathlib from git
    "https://github.com/leanprover-community/mathlib4"

lean_lib Dedekind_Axioms where
  -- add library configuration options here

lean_lib Dedekind where

lean_lib Function where
lean_lib Schroder where
lean_lib Bernstein where
lean_lib MyTac where
lean_lib Dedekind_Formula where
lean_lib Domain where
lean_lib Sum_Product where
lean_lib Point where
lean_lib Conjugate where
lean_lib Residual where
lean_lib Cantor where
-- lean_lib rapply where
-- lean_lib rconv where
-- lean_lib mytactic where
