import .tableau
open fml

def test (ϕ : fml) := fml_is_sat [neg ϕ]

local infix ` ∨ `:1000 := fml.or
local infix ` ∧ `:1000 := fml.and
local infix ` -> `:1000 := fml.impl
local prefix `~` := fml.neg

precedence `p`:max
local prefix ` p ` := fml.var

set_option profiler true
