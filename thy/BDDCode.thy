section\<open>Code export\<close>
theory BDDCode
imports LevelCollapse
begin

text\<open>For convenience reasons, the code export is in a separate theory. For Haskell, we require no special code printings. We only have to reactivate the original equation for @{term blit}\<close>

lemma [code del]:
    "blit src si dst di len
      = blit' src (integer_of_nat si) dst (integer_of_nat di)
          (integer_of_nat len)" by (simp add: blit'_def)
declare blit_def[code]

export_code open iteci_lu notci andci orci nandci norci biimpci xorci ifci tci fci tautci emptyci graphifyci litci in Haskell module_name IBDD file "../hs/gen"

end
