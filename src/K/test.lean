import .tableau
open fml

-- A simple workaround for fml.iff.
-- Unlike fml.impl, this is really a trusted string-level translation 
-- similar to a bash script modifiying the benchmark text.
-- Only k_poly_p and k_poly_n contain iffs.

def fml.iff (φ ψ : fml) := and (impl φ ψ) (impl ψ φ) 

def test (ϕ : fml) := fml_is_sat [neg ϕ]

local infix ` ∨ `:1000 := fml.or
local infix ` ∧ `:1000 := fml.and
local infix ` -> `:1000 := fml.impl
local infix ` <-> `:1000 := fml.iff

local prefix `~` := fml.neg

precedence `p`:max
local prefix ` p ` := fml.var

set_option profiler true

-- #eval test ()
